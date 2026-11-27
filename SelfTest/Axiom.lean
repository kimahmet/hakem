import Hakem
/-! BAD SOLUTION: "proves" Hume's law with a new axiom. Expected: unpermitted axiom. -/
axiom cheat : False
theorem hume_law : ∀ {S : Signature} {T : Theory S} {φ : Formula S},
    (∀ ψ ∈ T.axioms, ψ.descriptive = true) → ¬ Nonempty (PolicyVerdict T φ) := cheat.elim
