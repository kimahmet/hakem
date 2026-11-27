import AnalojiDenetcisi.Kernel

/-! Fizik: iki cisim arasında enerji aktarımı. Korunumlu. -/

structure TwoBodies where
  e1 : Int
  e2 : Int

abbrev Physics : Model where
  State   := TwoBodies
  Step    := fun p q => ∃ a : Int, q.e1 = p.e1 - a ∧ q.e2 = p.e2 + a
  measure := fun p => p.e1 + p.e2

theorem physics_conservative : Physics.Conservative := by
  rintro p q ⟨a, h1, h2⟩
  show p.e1 + p.e2 = q.e1 + q.e2
  omega
