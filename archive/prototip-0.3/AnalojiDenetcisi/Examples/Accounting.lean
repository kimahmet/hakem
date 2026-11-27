import AnalojiDenetcisi.Examples.Physics

/-! Muhasebe: kasa ile banka arasında virman. Korunum fizikten transfer edilir. -/

structure Ledger where
  kasa  : Int
  banka : Int

abbrev Accounting : Model where
  State   := Ledger
  Step    := fun p q => ∃ a : Int, q.kasa = p.kasa - a ∧ q.banka = p.banka + a
  measure := fun p => p.kasa + p.banka

def physicsToAccounting : Analogy Physics Accounting where
  map := fun l => ⟨l.kasa, l.banka⟩
  step_pres := by
    rintro p q ⟨a, h1, h2⟩
    exact ⟨a, h1, h2⟩
  measure_pres := fun _ => rfl

theorem accounting_conservative : Accounting.Conservative :=
  physicsToAccounting.transfer physics_conservative
