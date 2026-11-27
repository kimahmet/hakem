import AnalojiDenetcisi.Examples.Physics

/-!
Bankacılık: iki mevduat hesabı ve bir kredi defteri.
- Virman: hesaplar arası aktarım. Korunumlu.
- Kredi açma: yeni mevduat yaratır. Korunumsuz.

Sonuç: fizikten tüm bankacılığa analoji reddedilir (metafor),
ama virman alt modeline analoji geçerlidir (kısmi analoji).
-/

structure Bank where
  mevduat1 : Int
  mevduat2 : Int
  kredi    : Int

def Bank.virman (p q : Bank) : Prop :=
  ∃ a : Int, q.mevduat1 = p.mevduat1 - a ∧ q.mevduat2 = p.mevduat2 + a ∧ q.kredi = p.kredi

def Bank.krediAc (p q : Bank) : Prop :=
  ∃ a : Int, 0 < a ∧ q.mevduat1 = p.mevduat1 + a ∧ q.mevduat2 = p.mevduat2 ∧
    q.kredi = p.kredi + a

abbrev Banking : Model where
  State   := Bank
  Step    := fun p q => Bank.virman p q ∨ Bank.krediAc p q
  measure := fun p => p.mevduat1 + p.mevduat2

theorem banking_not_conservative : ¬ Banking.Conservative := by
  intro h
  have h01 : (0 : Int) + 0 = 1 + 0 :=
    h ⟨0, 0, 0⟩ ⟨1, 0, 1⟩ (Or.inr ⟨1, by decide, rfl, rfl, rfl⟩)
  omega

/-- Tam analoji yok: "tüm adımlar altında korunum" taşınamaz. -/
theorem no_analogy_physics_banking : ¬ Nonempty (Analogy Physics Banking) :=
  fun ⟨h⟩ => banking_not_conservative (h.transfer physics_conservative)

/-! ## Kısmi analoji: yalnızca virmanlar -/

abbrev BankingVirman : Model := Banking.restrict Bank.virman

def physicsToBankingVirman : Analogy Physics BankingVirman where
  map := fun b => ⟨b.mevduat1, b.mevduat2⟩
  step_pres := by
    rintro p q ⟨_, a, h1, h2, _⟩
    exact ⟨a, h1, h2⟩
  measure_pres := fun _ => rfl

/-- "Virmanlar altında korunum" fizikten taşınır. -/
theorem banking_virman_conservative : BankingVirman.Conservative :=
  physicsToBankingVirman.transfer physics_conservative
