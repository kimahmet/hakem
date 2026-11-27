import Lean

/-!
# Hakem — yargıç (güvenilen araç)

Kullanım: `lake env lean --run tools/Judge.lean <comparator.json> <nanoda-çıktısı> <nanoda-çıkış-kodu>`

Her iddia için denetlenen şartlar:
1. `Challenge` ve `Solution` ortamlarında aynı adlı sabit vardır. Türleri (ifadeleri)
   terim olarak aynıdır. Metin karşılaştırılmaz.
2. İfadenin anlam tabanı, yani ifadenin dayandığı güvenilen tanımlar (`Hakem.*`,
   `Challenge`), iki ortamda da tür ve değer olarak aynıdır.
3. `Solution`'daki ispat yalnızca izinli aksiyomlara dayanır.
4. Bağımsız çekirdek (nanoda) `Solution` dökümünü hatasız yeniden denetlemiştir.
   Bu adımı `tools/hakem.sh` çalıştırır ve sonucu buraya iletir.

Yalnızca bu dört şart sağlanınca "BİÇİMSEL KABUL" yazılır. Okumalar (docstring)
rapora "denetlenmedi" etiketiyle kopyalanır.

Bu araç `.olean` dosyalarını belleğe yükler. Bu yüzden saldırgan girdiye karşı
kendi başına yeterli değildir. Saldırgan girdi için Linux üzerinde
`lake comparator --paranoid` kullanılır (bkz. TASARIM.md §6).
-/

open Lean Meta

def permittedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

/-- Lean'in kendi kütüphaneleri (bütün taraflarca paylaşılan önsöz). -/
def coreRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- İfadenin anlam tabanına giren sabit: önsöz dışındaki her modülde tanımlı sabit.
(Önceki sürüm yalnızca `Hakem`/`Challenge` köklerini sayıyordu; `Corpus` gibi yeni
güvenilen modüller anlam tabanından kaçıyordu. Öz-sınama `SelfTest.Swap` bunu yakaladı.) -/
def isTrusted (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => !coreRoots.contains m.getRoot
  | none   => false

/-- Bir sabitin türünde ve değerinde (teoremlerde ispatta) geçen sabitler.
Dikkat: `ConstantInfo.value?` teoremler için `none` döner; bu yüzden açıkça eşlenir. -/
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

/-- Güvenilen modüllerde tanımlı olup ifadenin (geçişli olarak) dayandığı sabitler. -/
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

/-- Bir sabitin geçişli olarak dayandığı aksiyomlar. -/
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
    | none => axs := axs.push (c ++ `«BULUNAMADI»)
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

/-- nanoda çıktısında `theorem <ad> ...` bloğunu bul. -/
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
  let some cc := chal.find? n | return ⟨n, false, #["Challenge'da yok"], "", #[], #[], "", none⟩
  let stmt ← ppIn chal cc.type
  let reading := (((← findDocString? chal n).getD "(okuma yok)").trimAscii.toString).replace "OKUMA: " ""
  let base := meaningBase chal (cc.type.getUsedConstants)
  let mut baseDocs := #[]
  for b in base do
    let d := (← findDocString? chal b).getD ""
    -- Parmak izi: tanımın türü ve değeri üzerinden yapısal özet. İnsan incelemeleri
    -- bu değere bağlanır; tanım değişirse inceleme geçersiz olur.
    -- shortcut: 64-bit yapısal özet, kriptografik değil; bağımsız incelemeler için
    -- dökümdeki (ndjson) bildirimin SHA-256 özetine geçilmeli.
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
  | none => reasons := reasons.push "Solution'da yok"
  | some sc =>
    if !(sameDecl cc sc false) then reasons := reasons.push "İFADE FARKLI (Challenge ≠ Solution)"
    if !sc.isTheorem then reasons := reasons.push "Solution'da teorem değil"
    for b in base do
      match chal.find? b, sol.find? b with
      | some x, some y =>
        if !(sameDecl x y true) then reasons := reasons.push s!"anlam tabanı farklı: {b}"
      | _, _ => reasons := reasons.push s!"anlam tabanı eksik: {b}"
    axs := axiomsOf sol n
    for a in axs do
      if !permittedAxioms.contains a then reasons := reasons.push s!"izinsiz aksiyom: {a}"
  let nb := nanodaBlock nanodaOut n
  if !nanodaOk then reasons := reasons.push "bağımsız çekirdek (nanoda) dökümü reddetti"
  if nb.isNone then reasons := reasons.push "nanoda bu iddiayı basmadı"
  return ⟨n, reasons.isEmpty, reasons, stmt, axs, baseDocs, reading, nb⟩

def render (rows : Array Row) (nanodaOk : Bool) : String := Id.run do
  let okCount := (rows.filter (·.ok)).size
  let mut s := "# KARAR\n\n"
  s := s ++ "Bu dosya `tools/hakem.sh` tarafından üretilir. Elle düzenlenmez.\n\n"
  s := s ++ s!"**{okCount} / {rows.size} iddia biçimsel kabul aldı.**\n\n"
  s := s ++ "## Bu kararın anlamı\n\n"
  s := s ++ "\"BİÇİMSEL KABUL\" yalnızca şunu söyler:\n\n"
  s := s ++ "1. Aşağıda basılan Lean ifadesi Lean çekirdeğince kabul edildi (`lake build`).\n"
  s := s ++ s!"2. İfade bağımsız bir çekirdekte (nanoda, Rust) yeniden denetlendi: {if nanodaOk then "geçti" else "GEÇMEDİ"}.\n"
  s := s ++ "3. İfade, güvenilen `Challenge.lean`'deki ifadeyle terim düzeyinde aynıdır.\n"
  s := s ++ "4. İfadenin dayandığı tanımlar (anlam tabanı) iki tarafta aynıdır.\n"
  s := s ++ "5. İspat yalnızca `propext`, `Quot.sound`, `Classical.choice` aksiyomlarına dayanır.\n\n"
  s := s ++ "Bu karar şunları **söylemez**:\n\n"
  s := s ++ "- OKUMA satırının ifadeyi doğru anlattığını. Okuma insan incelemesine açıktır.\n"
  s := s ++ "- Anlam tabanındaki tanımların gerçek disiplini doğru temsil ettiğini. İDEALLEŞTİRME notlarına bakınız.\n"
  s := s ++ "- Ampirik değerlerin doğru olduğunu. Değer seçimlerinin doğru olduğunu.\n"
  s := s ++ "- Saldırgan girdiye karşı tam güvenceyi. Bu yerel çalıştırma sandbox kullanmaz. Tam güvence için Linux'ta `lake comparator --paranoid` (5 çekirdek) gerekir.\n\n"
  for r in rows do
    s := s ++ s!"---\n\n## `{r.name}`\n\n"
    s := s ++ (if r.ok then "**DURUM: BİÇİMSEL KABUL**\n\n" else s!"**DURUM: RET**: {", ".intercalate r.reasons.toList}\n\n")
    s := s ++ s!"**İfade** (güvenilen ortamda basıldı):\n\n```lean\n{r.stmt}\n```\n\n"
    if let some nb := r.nanoda then
      s := s ++ s!"**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):\n\n```lean\n{nb}\n```\n\n"
    s := s ++ s!"**Aksiyomlar:** {", ".intercalate (r.axioms.toList.map toString)}\n\n"
    s := s ++ s!"**OKUMA (denetlenmedi):** {r.reading}\n\n"
    s := s ++ "**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):\n\n"
    for (b, d) in r.base do
      s := s ++ s!"- `{b}`: {d}\n"
    s := s ++ "\n"
  return s

unsafe def main (args : List String) : IO UInt32 := do
  let [cfgPath, nanodaPath, nanodaCode] := args
    | IO.eprintln "kullanım: Judge <comparator.json> <nanoda-çıktısı> <nanoda-çıkış-kodu>"; return 2
  let cfg ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
  let names ← IO.ofExcept (cfg.getObjValAs? (Array String) "theorem_names")
  let chalMod := (← IO.ofExcept (cfg.getObjValAs? String "challenge_module")).toName
  let solMod  := (← IO.ofExcept (cfg.getObjValAs? String "solution_module")).toName
  let nanodaOut ← IO.FS.readFile nanodaPath
  let nanodaOk := nanodaCode.trimAscii.toString == "0"
  initSearchPath (← findSysroot)
  -- Güvenilmeyen taraf: eklenti durumu ve başlatıcılar yüklenmez (kodu çalıştırılmaz).
  let sol  ← importModules #[{ module := solMod }] {} (loadExts := false)
  -- Güvenilen taraf: docstring'ler için eklentiler yüklenir.
  enableInitializersExecution
  let chal ← importModules #[{ module := chalMod }] {} (loadExts := true)
  let mut rows := #[]
  for n in names do
    rows := rows.push (← judge chal sol nanodaOut nanodaOk n.toName)
  IO.println (render rows nanodaOk)
  return if rows.all (·.ok) then 0 else 1
