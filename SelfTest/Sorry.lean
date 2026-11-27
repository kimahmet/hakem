import Hakem
/-! KÖTÜ ÇÖZÜM: aktarım yasası eksik ispatla. Beklenen: izinsiz aksiyom sorryAx. -/
theorem transfer : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} (a : Analogy A B)
    {φ : Formula S₁}, A.Entails φ → B.Entails (a.σ.trF φ) := sorry
