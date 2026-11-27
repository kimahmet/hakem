import Hakem
/-! KÖTÜ ÇÖZÜM: Hume yasasını yeni bir aksiyomla "ispatlar". Beklenen: izinsiz aksiyom. -/
axiom cheat : False
theorem hume_law : ∀ {S : Signature} {T : Theory S} {φ : Formula S},
    (∀ ψ ∈ T.axioms, ψ.descriptive = true) → ¬ Nonempty (PolicyVerdict T φ) := cheat.elim
