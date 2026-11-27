import Hakem

/-! Güvenilmeyen ispatlar: karbonun sosyal maliyeti. -/

namespace Proofs

theorem ds_mono_v (rho n : Nat) : ∀ {v v' : Nat}, v ≤ v' →
    discountedSum rho n v ≤ discountedSum rho n v' := by
  induction n with
  | zero => intro v v' _; simp only [discountedSum]; exact Nat.le_refl _
  | succ n ih =>
    intro v v' h
    simp only [discountedSum]
    exact Nat.add_le_add h (ih (Nat.div_le_div_right (Nat.mul_le_mul_right _ h)))

theorem ds_mono_n (rho k : Nat) : ∀ (n v : Nat),
    discountedSum rho n v ≤ discountedSum rho (n + k) v := by
  intro n
  induction n with
  | zero => intro v; simp only [discountedSum]; exact Nat.zero_le _
  | succ n ih =>
    intro v
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [discountedSum]
    exact Nat.add_le_add_left (ih _) _

/-- Ölçüm kutusunda SCC, köşelerdeki değerlerle sınırlıdır. -/
theorem scc_box {e : Facts} (he : measured e) (rho : Nat) :
    scc ⟨900000, 150⟩ rho ≤ scc e rho ∧ scc e rho ≤ scc ⟨1100000, 300⟩ rho := by
  obtain ⟨d1, d2, h1, h2⟩ := he
  unfold scc
  constructor
  · have a := ds_mono_v rho 150 d1
    have b := ds_mono_n rho (e.horizon - 150) 150 e.damage
    rw [show 150 + (e.horizon - 150) = e.horizon by omega] at b
    exact Nat.le_trans a b
  · have a := ds_mono_v rho e.horizon d2
    have b := ds_mono_n rho (300 - e.horizon) e.horizon 1100000
    rw [show e.horizon + (300 - e.horizon) = 300 by omega] at b
    exact Nat.le_trans a b

-- Köşe değerleri: yalnızca çekirdekte hesaplanır (`decide +kernel`).
theorem stern_low : 120000000 ≤ scc ⟨900000, 150⟩ 10 := by decide +kernel
theorem nordhaus_high : scc ⟨1100000, 300⟩ 150 < 75000000 := by decide +kernel
theorem nordhaus_low_fails : ¬ (120000000 ≤ scc ⟨900000, 150⟩ 150) := by decide +kernel
theorem stern_low_fails : ¬ (scc ⟨900000, 150⟩ 10 < 75000000) := by decide +kernel

theorem low_measured : measured ⟨900000, 150⟩ := by unfold measured; decide

theorem scc_rho_alone_decides :
    ∀ e, measured e →
      TaxAtLeast 120000000 e ⟨10, .pigou⟩ ∧ TaxBelow 75000000 e ⟨150, .pigou⟩ := by
  intro e he
  exact ⟨Nat.le_trans stern_low (scc_box he 10).1,
         Nat.lt_of_le_of_lt (scc_box he 150).2 nordhaus_high⟩

theorem stern_verdict :
    Nonempty (Verdict SCCQuestion sternNorms (TaxAtLeast 120000000)) :=
  ⟨{ valid := by
       rintro e he ⟨rho, c⟩ ⟨hc, hr⟩
       dsimp only at hc hr
       subst hc hr
       exact (scc_rho_alone_decides e he).1
     norms_sat := ⟨⟨10, .pigou⟩, rfl, rfl⟩
     -- Aynı olgu, aynı ölçüt; yalnızca ρ = %1,5.
     open_by_facts := ⟨⟨900000, 150⟩, low_measured, ⟨150, .pigou⟩, nordhaus_low_fails⟩ }⟩

theorem nordhaus_verdict :
    Nonempty (Verdict SCCQuestion nordhausNorms (TaxBelow 75000000)) :=
  ⟨{ valid := by
       rintro e he ⟨rho, c⟩ ⟨hc, hr⟩
       dsimp only at hc hr
       subst hc hr
       exact (scc_rho_alone_decides e he).2
     norms_sat := ⟨⟨150, .pigou⟩, rfl, rfl⟩
     -- Aynı olgu, aynı ölçüt; yalnızca ρ = %0,1.
     open_by_facts := ⟨⟨900000, 150⟩, low_measured, ⟨10, .pigou⟩, stern_low_fails⟩ }⟩

end Proofs
