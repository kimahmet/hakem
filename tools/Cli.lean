import Hakem.Lang.Check
import Lean.Data.Json

/-!
# `hakem` command-line tool

* `hakem check FILE…` — check documents with the compiled checker.
* `hakem json FILE` — the same check, as one line of JSON for agents (autonomous loops).
* `hakem cert FILE NAME` — print a certificate file that states the document tree as a Lean
  term, so that `checkTree` can be computed by the kernel.
-/

partial def sexpToLean : SExp → String
  | .atom s => s!"(.atom {repr s})"
  | .list xs => "(.list [" ++ ", ".intercalate (xs.map sexpToLean) ++ "])"

def report (path : String) : IO Bool := do
  let s ← IO.FS.readFile path
  match readSExps s with
  | none => IO.println s!"{path}: UNREADABLE"; return false
  | some es =>
    match Doc.claimsTree es with
    | none => IO.println s!"{path}: UNELABORATED (unknown name, wrong arity or malformed entry)"; return false
    | some cs =>
      let mut ok := true
      for c in cs do
        let r := checkClaim c
        ok := ok && r
        IO.println s!"{path}: {c.name}: {if r then "ACCEPTED" else "REJECTED"}"
      return ok

def jsonStr (s : String) : String := (Lean.Json.str s).compress

/-- Machine-readable verdict: `{"file":…, "status":"accepted"|"rejected"|"unreadable"|"unelaborated",
"claims":[{"name":…, "kind":…, "accepted":…}]}`. -/
def reportJson (path : String) : IO Bool := do
  let s ← IO.FS.readFile path
  let kind : Claim → String
    | .lemma .. => "lemma" | .analogy .. => "analogy" | .refute .. => "refute" | .verdict .. => "verdict"
  match readSExps s with
  | none => IO.println s!"\{\"file\":{jsonStr path},\"status\":\"unreadable\",\"claims\":[]}"; return false
  | some es =>
    match Doc.claimsTree es with
    | none => IO.println s!"\{\"file\":{jsonStr path},\"status\":\"unelaborated\",\"claims\":[]}"; return false
    | some cs =>
      let items := cs.map fun c =>
        s!"\{\"name\":{jsonStr c.name},\"kind\":\"{kind c}\",\"accepted\":{if checkClaim c then "true" else "false"}}"
      let ok := cs.all checkClaim
      IO.println s!"\{\"file\":{jsonStr path},\"status\":\"{if ok then "accepted" else "rejected"}\",\"claims\":[{",".intercalate items}]}"
      return ok

def main (args : List String) : IO UInt32 := do
  match args with
  | ["json", path] => return if (← reportJson path) then 0 else 1
  | "check" :: paths =>
    let mut ok := true
    for p in paths do
      ok := (← report p) && ok
    return if ok then 0 else 1
  | ["cert", path, name] =>
    let s ← IO.FS.readFile path
    match readSExps s with
    | none => IO.eprintln "unreadable"; return 1
    | some es =>
      IO.println s!"import Hakem.Lang.Check
import Lean.Data.Json\n"
      IO.println s!"/-- Tree of `{path}` (output of the reader). -/"
      IO.println s!"def {name}_tree : List SExp := [{", ".intercalate (es.map sexpToLean)}]\n"
      return 0
  | _ => IO.eprintln "usage: hakem check FILE… | hakem json FILE | hakem cert FILE NAME"; return 2
