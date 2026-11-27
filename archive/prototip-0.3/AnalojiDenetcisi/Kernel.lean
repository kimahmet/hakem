/-!
# Analoji Denetçisi — çekirdek (prototip 0.3)

Bağımlılık yok (yalnızca Lean 4 çekirdeği). İki bölüm:

**I. Analoji.** Bir disiplinde kanıtlanmış bir sonuç başka bir disipline ancak
yapıyı koruyan bir eşleme (analoji) boyunca taşınabilir.
Kavramlar: `Model`, `Model.Preserves`, `Analogy`, `Analogy.transfer`,
`Model.restrict`, `Model.Equilibrium`, `Analogy.equilibrium_transfer`.

**II. Öncül türleri.** Her öncül `tanim | ampirik | normatif` olarak etiketlenir.
Politika sonucu, normatif öncüller atılınca ayakta kalamamalıdır
("olandan olması gereken çıkmaz"). Kavramlar: `Kind`, `Premise`, `Argument`,
`PolicyArgument`, `PolicyArgument.not_facts_only`.
-/

/-! ## I. Analoji -/

/-- Bir disiplin modeli: durumlar, adımlar (dinamik) ve tamsayı bir ölçü. -/
structure Model where
  State   : Type
  Step    : State → State → Prop
  measure : State → Int

/-- Her adım ölçü üzerinde `R` ilişkisini sağlar.
Yapı türleri bunun özel hâlleridir: korunum `(· = ·)`, ikinci yasa / Lyapunov `(· < ·)`. -/
def Model.Preserves (M : Model) (R : Int → Int → Prop) : Prop :=
  ∀ s t, M.Step s t → R (M.measure s) (M.measure t)

/-- Korunum: hiçbir adım ölçüyü değiştirmez. -/
abbrev Model.Conservative (M : Model) : Prop := M.Preserves (· = ·)

/-- `Analogy A B`: hedef `B`, kaynak `A`'nın diliyle okunur.
`map` her `B` durumunu bir `A` durumuna çevirir (gözlem/soyutlama).
Her `B` adımı bir `A` adımına, ölçü ölçüye gitmelidir.
`B`'nin `A`'nın görmediği koordinatları (ör. kredi defteri) serbest kalabilir. -/
structure Analogy (A B : Model) where
  map          : B.State → A.State
  step_pres    : ∀ s t, B.Step s t → A.Step (map s) (map t)
  measure_pres : ∀ s, A.measure (map s) = B.measure s

/-- Aktarım: `A`'da ispatlanmış her ölçü ilişkisi `B`'ye taşınır. -/
theorem Analogy.transfer {A B : Model} {R : Int → Int → Prop} (h : Analogy A B)
    (hA : A.Preserves R) : B.Preserves R := by
  intro s t hst
  rw [← h.measure_pres s, ← h.measure_pres t]
  exact hA _ _ (h.step_pres s t hst)

/-- Kısmi analoji için alt model: yalnızca `P`'yi sağlayan adımlar kalır.
Kısmi analoji ayrı bir kavram değildir: alt modele tam analojidir.
"P adımları altında korunum" = `(M.restrict P).Conservative`. -/
abbrev Model.restrict (M : Model) (P : M.State → M.State → Prop) : Model where
  State   := M.State
  Step    := fun s t => M.Step s t ∧ P s t
  measure := M.measure

/-- Denge (durağan durum): hiçbir adım mümkün değil. -/
def Model.Equilibrium (M : Model) (s : M.State) : Prop :=
  ∀ t, ¬ M.Step s t

/-- Denge geriye taşınır: `B` durumu, `A`'daki görüntüsü dengedeyse dengededir.
Tersi taşınmaz; `B`, `A`'nın görmediği bir yolla hareket edemez, ama `A`
dengede olmayan bir durumu `B`'de durağan gösterebilir. -/
theorem Analogy.equilibrium_transfer {A B : Model} (h : Analogy A B) {s : B.State}
    (hs : A.Equilibrium (h.map s)) : B.Equilibrium s :=
  fun t hst => hs _ (h.step_pres s t hst)

/-! ## II. Öncül türleri -/

/-- Öncül türü. Çekirdek etiketin doğruluğuna hüküm vermez; etiketin
görünür olmasını ve kurala uyulmasını zorunlu kılar. -/
inductive Kind where
  | tanim     -- tanım: terimin anlamını sabitler
  | ampirik   -- ampirik: ölçümle sınanır; değeri çekirdeğin dışındadır
  | normatif  -- normatif: değer seçimi; değeri çekirdeğin dışındadır
  deriving DecidableEq, Repr

/-- `W` olası dünyalar (parametre atamaları) tipidir. Öncül, hangi dünyalarda
doğru olduğuyla verilir. Böylece sonuçlar koşulludur: "bu öncüller sağlanırsa...". -/
structure Premise (W : Type) where
  name  : String
  kind  : Kind
  holds : W → Prop

/-- Tüm öncüller dünyada doğru. -/
def Premise.allHold {W : Type} : List (Premise W) → W → Prop
  | [],      _ => True
  | p :: ps, w => p.holds w ∧ allHold ps w

/-- Normatif olmayan tüm öncüller dünyada doğru (normatifler göz ardı). -/
def Premise.factsHold {W : Type} : List (Premise W) → W → Prop
  | [],      _ => True
  | p :: ps, w => (p.kind = .normatif ∨ p.holds w) ∧ factsHold ps w

theorem Premise.allHold_of_factsHold {W : Type} :
    ∀ (ps : List (Premise W)) (w : W),
      (∀ p ∈ ps, p.kind ≠ .normatif) → factsHold ps w → allHold ps w
  | [],      _, _,  _ => trivial
  | p :: ps, w, hn, h =>
    ⟨h.1.resolve_left (hn p (by simp)),
     allHold_of_factsHold ps w (fun q hq => hn q (by simp [hq])) h.2⟩

/-- Argüman: etiketli öncüller ve öncüllerden sonuca geçerli çıkarım. -/
structure Argument (W : Type) (C : W → Prop) where
  premises : List (Premise W)
  valid    : ∀ w, Premise.allHold premises w → C w

/-- Politika argümanı. "Olandan olması gereken çıkmaz" kuralı tek alan olarak:
tüm olgulara (tanım + ampirik) uyan ama sonucu sağlamayan bir dünya göstermek
zorunludur. Bu, normatif öncüllerin hem var olduğunu hem de işe yaradığını
kanıtlar (bkz. `not_facts_only`). Tanık dünya, tartışmanın nerede yattığını gösterir. -/
structure PolicyArgument (W : Type) (C : W → Prop) extends Argument W C where
  hume : ∃ w, Premise.factsHold premises w ∧ ¬ C w

/-- Normatif öncülü olmayan bir politika argümanı kurulamaz. -/
theorem PolicyArgument.not_facts_only {W : Type} {C : W → Prop} (a : PolicyArgument W C)
    (h : ∀ p ∈ a.premises, p.kind ≠ .normatif) : False :=
  let ⟨w, hw, hC⟩ := a.hume
  hC (a.valid w (Premise.allHold_of_factsHold _ w h hw))
