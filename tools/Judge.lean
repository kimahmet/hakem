import Lean

/-!
# Hakem — judge (trusted tool)

Usage: `lake env lean --run tools/Judge.lean <comparator.json> <nanoda-output> <nanoda-exit-code>`

Conditions checked for every claim:
1. `Challenge` and `Solution` contain a constant of the same name whose types (statements)
   are identical as terms. Text is not compared.
2. The statement's meaning base, i.e. the trusted definitions it depends on (every module
   outside Lean's own libraries), is identical in type and value in both environments.
3. The proof in `Solution` uses only permitted axioms.
4. The independent kernel (nanoda) re-checked the `Solution` export without error.
   `tools/hakem.sh` runs this step and passes the result here.

Only when all four hold is "FORMALLY ACCEPTED" written. Readings (docstrings) are copied
into the report marked "unchecked".

This tool loads `.olean` files into memory, so on its own it is not sufficient against
adversarial input. For adversarial input use `lake comparator --paranoid` on Linux
(see DESIGN.md §5); CI runs it on every push.
-/

open Lean Meta

def permittedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

/-- Lean's own libraries (the prelude shared by all parties). -/
def coreRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- A constant enters a statement's meaning base if it is defined in any module outside the
prelude. (An earlier version counted only the `Hakem`/`Challenge` roots, so new trusted
modules such as the corpus trees escaped the meaning base. Self-test `SelfTest.Swap` caught it.) -/
def isTrusted (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => !coreRoots.contains m.getRoot
  | none   => false

/-- Constants occurring in a constant's type and value (for theorems, in the proof).
Note: `ConstantInfo.value?` returns `none` for theorems, so values are matched explicitly. -/
def valueOf : ConstantInfo → Option Expr
  | .defnInfo d   => some d.value
  | .thmInfo t    => some t.value
  | .opaqueInfo o => some o.value
  | _             => none

def constsOf (ci : ConstantInfo) : Array Name :=
  let fromVal := match valueOf ci with
    | some v => v.getUsedConstants
    | none   => #[]
  let extra := match ci with
    | .inductInfo i => i.ctors.toArray
    | .ctorInfo c   => #[c.induct]
    | _             => #[]
  ci.type.getUsedConstants ++ fromVal ++ extra

/-- Constants defined in trusted modules that the statement (transitively) depends on. -/
partial def meaningBase (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut todo := roots.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n || !isTrusted env n then continue
    seen := seen.insert n
    out := out.push n
    if let some ci := env.find? n then
      todo := (constsOf ci).toList ++ todo
  return out

/-- Axioms a constant transitively depends on. -/
partial def axiomsOf (env : Environment) (n : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut axs : Array Name := #[]
  let mut todo := [n]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | some (.axiomInfo _) => axs := axs.push c
    | some ci => todo := (constsOf ci).toList ++ todo
    | none => axs := axs.push (c ++ `«NOT_FOUND»)
  return axs

def sameDecl (a b : ConstantInfo) (compareValue : Bool) : Bool :=
  a.type == b.type && a.levelParams == b.levelParams &&
    (!compareValue || valueOf a == valueOf b)

def ppIn (env : Environment) (e : Expr) : IO String := do
  let ctx : Core.Context := { fileName := "<hakem>", fileMap := default }
  let st : Core.State := { env }
  let (fmt, _) ← (Meta.MetaM.run' (ppExpr e)).toIO ctx st
  return toString fmt

def firstLine (s : String) : String :=
  (s.splitOn "\n").head!.trimAscii.toString

/-- Find the `theorem <name> ...` block in nanoda's output. -/
def nanodaBlock (out : String) (n : Name) : Option String :=
  (out.splitOn "\n\n").find? fun b => b.startsWith s!"theorem {n} "

structure Row where
  name    : Name
  ok      : Bool
  reasons : Array String
  stmt    : String
  axioms  : Array Name
  base    : Array (Name × String)
  reading : String
  nanoda  : Option String

def judge (chal sol : Environment) (nanodaOut : String) (nanodaOk : Bool) (n : Name) : IO Row := do
  let mut reasons := #[]
  let some cc := chal.find? n | return ⟨n, false, #["missing in Challenge"], "", #[], #[], "", none⟩
  let stmt ← ppIn chal cc.type
  let reading := (((← findDocString? chal n).getD "(no reading)").trimAscii.toString).replace "READING: " ""
  let base := meaningBase chal (cc.type.getUsedConstants)
  let mut baseDocs := #[]
  for b in base do
    let d := (← findDocString? chal b).getD ""
    -- Fingerprint: a structural digest of the definition's type and value. Human reviews
    -- are pinned to it; if the definition changes, the review is void.
    -- shortcut: 64-bit structural digest, not cryptographic; for independent reviews,
    -- switch to the SHA-256 of the declaration in the (ndjson) export.
    let fp := match chal.find? b with
      | some ci =>
        let ctorHash := match ci with
          | .inductInfo i => i.ctors.foldl (fun h c =>
              mixHash h (mixHash (hash c) (((chal.find? c).map (fun (k : ConstantInfo) => k.type.hash)).getD 0))) 0
          | _ => 0
        let h := mixHash (hash b) (mixHash ci.type.hash
          (mixHash (((valueOf ci).map (fun (e : Expr) => e.hash)).getD 0) ctorHash))
        s!"{h.toUInt32}"
      | none => "?"
    if !b.isInternal then baseDocs := baseDocs.push (b, s!"[{fp}] {firstLine d}")
  let mut axs := #[]
  match sol.find? n with
  | none => reasons := reasons.push "missing in Solution"
  | some sc =>
    if !(sameDecl cc sc false) then reasons := reasons.push "STATEMENT DIFFERS (Challenge ≠ Solution)"
    if !sc.isTheorem then reasons := reasons.push "not a theorem in Solution"
    for b in base do
      match chal.find? b, sol.find? b with
      | some x, some y =>
        if !(sameDecl x y true) then reasons := reasons.push s!"meaning base differs: {b}"
      | _, _ => reasons := reasons.push s!"meaning base missing: {b}"
    axs := axiomsOf sol n
    for a in axs do
      if !permittedAxioms.contains a then reasons := reasons.push s!"unpermitted axiom: {a}"
  let nb := nanodaBlock nanodaOut n
  if !nanodaOk then reasons := reasons.push "independent kernel (nanoda) rejected the export"
  if nb.isNone then reasons := reasons.push "nanoda did not print this claim"
  return ⟨n, reasons.isEmpty, reasons, stmt, axs, baseDocs, reading, nb⟩

def render (rows : Array Row) (nanodaOk : Bool) : String := Id.run do
  let okCount := (rows.filter (·.ok)).size
  let mut s := "# VERDICT\n\n"
  s := s ++ "Generated by `tools/hakem.sh`. Do not edit by hand.\n\n"
  s := s ++ s!"**{okCount} / {rows.size} claims formally accepted.**\n\n"
  s := s ++ "## What this verdict means\n\n"
  s := s ++ "\"FORMALLY ACCEPTED\" says only this:\n\n"
  s := s ++ "1. The Lean statement printed below was accepted by Lean's kernel (`lake build`).\n"
  s := s ++ s!"2. It was re-checked by an independent kernel (nanoda, Rust): {if nanodaOk then "passed" else "FAILED"}.\n"
  s := s ++ "3. The statement is identical, as a term, to the one in the trusted `Challenge.lean`.\n"
  s := s ++ "4. The definitions it depends on (its meaning base) are identical on both sides.\n"
  s := s ++ "5. The proof uses only the axioms `propext`, `Quot.sound`, `Classical.choice`.\n\n"
  s := s ++ "This verdict does **not** say:\n\n"
  s := s ++ "- That the READING line describes the statement correctly. Readings are open to human review.\n"
  s := s ++ "- That the definitions in the meaning base faithfully represent the real discipline.\n"
  s := s ++ "- That empirical values or value choices are right.\n"
  s := s ++ "- Full protection against adversarial input. This local run uses no sandbox; CI runs `lake comparator --paranoid` (sandbox, six kernels) on every push.\n\n"
  for r in rows do
    s := s ++ s!"---\n\n## `{r.name}`\n\n"
    s := s ++ (if r.ok then "**STATUS: FORMALLY ACCEPTED**\n\n" else s!"**STATUS: REJECTED**: {", ".intercalate r.reasons.toList}\n\n")
    s := s ++ s!"**Statement** (printed in the trusted environment):\n\n```lean\n{r.stmt}\n```\n\n"
    if let some nb := r.nanoda then
      s := s ++ s!"**Statement** (printed by the independent kernel, without notation):\n\n```lean\n{nb}\n```\n\n"
    s := s ++ s!"**Aksiyomlar:** {", ".intercalate (r.axioms.toList.map toString)}\n\n"
    s := s ++ s!"**READING (unchecked):** {r.reading}\n\n"
    s := s ++ "**Meaning base** (definitions humans should read; [fingerprint]):\n\n"
    for (b, d) in r.base do
      s := s ++ s!"- `{b}`: {d}\n"
    s := s ++ "\n"
  return s

unsafe def main (args : List String) : IO UInt32 := do
  let [cfgPath, nanodaPath, nanodaCode] := args
    | IO.eprintln "usage: Judge <comparator.json> <nanoda-output> <nanoda-exit-code>"; return 2
  let cfg ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
  let names ← IO.ofExcept (cfg.getObjValAs? (Array String) "theorem_names")
  let chalMod := (← IO.ofExcept (cfg.getObjValAs? String "challenge_module")).toName
  let solMod  := (← IO.ofExcept (cfg.getObjValAs? String "solution_module")).toName
  let nanodaOut ← IO.FS.readFile nanodaPath
  let nanodaOk := nanodaCode.trimAscii.toString == "0"
  initSearchPath (← findSysroot)
  -- Untrusted side: extension state and initializers are not loaded (its code is not run).
  let sol  ← importModules #[{ module := solMod }] {} (loadExts := false)
  -- Trusted side: extensions are loaded for docstrings.
  enableInitializersExecution
  let chal ← importModules #[{ module := chalMod }] {} (loadExts := true)
  let mut rows := #[]
  for n in names do
    rows := rows.push (← judge chal sol nanodaOut nanodaOk n.toName)
  IO.println (render rows nanodaOk)
  return if rows.all (·.ok) then 0 else 1
