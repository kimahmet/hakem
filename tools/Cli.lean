import Hakem.Lang.Check
import Lean.Data.Json

/-!
# `hakem` komut satırı aracı

* `hakem check DOSYA…` — belgeleri derlenmiş denetleyiciyle denetler.
* `hakem json DOSYA` — aynı denetim, ajanlar için tek satır JSON (özerk döngüler).
* `hakem cert DOSYA AD` — belge ağacını Lean terimi olarak yazan ve
  `checkTree` hesabını çekirdeğe yaptıran bir sertifika dosyası basar.
-/

partial def sexpToLean : SExp → String
  | .atom s => s!"(.atom {repr s})"
  | .list xs => "(.list [" ++ ", ".intercalate (xs.map sexpToLean) ++ "])"

def report (path : String) : IO Bool := do
  let s ← IO.FS.readFile path
  match readSExps s with
  | none => IO.println s!"{path}: OKUNAMADI"; return false
  | some es =>
    match Doc.claimsTree es with
    | none => IO.println s!"{path}: ÇEVRİLEMEDİ (bilinmeyen ad, ikilik ya da biçim)"; return false
    | some cs =>
      let mut ok := true
      for c in cs do
        let r := checkClaim c
        ok := ok && r
        IO.println s!"{path}: {c.name}: {if r then "DENETİMDEN GEÇTİ" else "RET"}"
      return ok

def jsonStr (s : String) : String := (Lean.Json.str s).compress

/-- Makinece okunur karar: `{"file":…, "status":"accepted"|"rejected"|"unreadable"|"unelaborated",
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
    | none => IO.eprintln "okunamadı"; return 1
    | some es =>
      IO.println s!"import Hakem.Lang.Check
import Lean.Data.Json\n"
      IO.println s!"/-- `{path}` belgesinin ağacı (okuyucunun çıktısı). -/"
      IO.println s!"def {name}_tree : List SExp := [{", ".intercalate (es.map sexpToLean)}]\n"
      return 0
  | _ => IO.eprintln "kullanım: hakem check DOSYA… | hakem json DOSYA | hakem cert DOSYA AD"; return 2
