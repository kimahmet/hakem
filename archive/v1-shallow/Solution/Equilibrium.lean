import Hakem

/-! Güvenilmeyen ispatlar: denge. -/

namespace Proofs

/-- Yerel kesin içbükeylikten uzak artışların karşılaştırılması. -/
theorem concave_far {f : Int → Int} (h : StrictlyConcave f) (x : Int) :
    ∀ k : Nat, f (x + k + 2) - f (x + k + 1) < f (x + 1) - f x := by
  intro k
  induction k with
  | zero =>
    rw [show x + ((0 : Nat) : Int) + 2 = x + 2 by omega,
        show x + ((0 : Nat) : Int) + 1 = x + 1 by omega]
    exact h x
  | succ k ih =>
    have hk := h (x + k + 1)
    rw [show x + ((k + 1 : Nat) : Int) + 2 = x + k + 3 by omega,
        show x + ((k + 1 : Nat) : Int) + 1 = x + k + 2 by omega]
    rw [show x + (k : Int) + 1 + 2 = x + k + 3 by omega,
        show x + (k : Int) + 1 + 1 = x + k + 2 by omega] at hk
    omega

/-- Kesin içbükey potansiyelde, aralarında en az iki birim fark olan dağılımdan
bir birim aktarmak toplam potansiyeli kesin artırır. -/
theorem concave_step {f : Int → Int} (h : StrictlyConcave f) {lo hi : Int} (hd : lo + 2 ≤ hi) :
    f lo + f hi < f (lo + 1) + f (hi - 1) := by
  have := concave_far h lo (hi - lo - 2).toNat
  have hk : (((hi - lo - 2).toNat : Nat) : Int) = hi - lo - 2 := Int.toNat_of_nonneg (by omega)
  rw [show lo + (((hi - lo - 2).toNat : Nat) : Int) + 2 = hi by omega,
      show lo + (((hi - lo - 2).toNat : Nat) : Int) + 1 = hi - 1 by omega] at this
  omega

theorem thermo_equilibrium_even :
    Thermo.Thm (fun t => EquilibriumIsEven (thermoObs t)) := by
  rintro ⟨S, x1, x2⟩ ⟨hS, h1, h2⟩ heq
  dsimp only at hS h1 h2
  show -1 ≤ x1 - x2 ∧ x1 - x2 ≤ 1
  constructor
  · by_cases hc : -1 ≤ x1 - x2
    · exact hc
    · exfalso
      apply heq ⟨x1 + 1, x2 - 1⟩
      have := concave_step hS (lo := x1) (hi := x2) (by omega)
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega
  · by_cases hc : x1 - x2 ≤ 1
    · exact hc
    · exfalso
      apply heq ⟨x1 - 1, x2 + 1⟩
      have := concave_step hS (lo := x2) (hi := x1) (by omega)
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega

/-- Yan ödemeli gönüllü ticaret, toplam faydanın kesin artmasına denktir.
Analojinin asıl içeriği budur: ekonominin sözcükleri ile Clausius ölçütü örtüşür. -/
theorem voluntary_iff_process (u : Int → Int) (p q : Split) :
    voluntaryTrade u p q ↔ heatProcess u p q := by
  constructor
  · rintro ⟨hs, hf, t, ha, hb, hc⟩
    exact ⟨hs, hf, by omega⟩
  · rintro ⟨hs, hf, hlt⟩
    exact ⟨hs, hf, u p.x1 - u q.x1, by omega, by omega, Or.inr (by omega)⟩

theorem negSq_concave : StrictlyConcave (fun x => -(x * x)) := by
  intro x
  show -((x + 2) * (x + 2)) - -((x + 1) * (x + 1)) < -((x + 1) * (x + 1)) - -(x * x)
  simp only [Int.add_mul, Int.mul_add]
  omega

def thermoMarketDMU : Analogy Thermo MarketDMU thermoObs marketObs where
  red := fun (m : Exchange) => ThermoSys.mk m.u m.alloc
  ax := fun _ h => ⟨h.2, h.1⟩
  anchors := by
    intro m _
    show (_, _) = (_, _)
    congr 1
    apply propext
    exact ⟨fun h q hv => h q ((voluntary_iff_process _ _ _).1 hv),
           fun h q hp => h q ((voluntary_iff_process _ _ _).2 hp)⟩
  model := ⟨fun x => -(x * x), ⟨0, 0⟩⟩
  model_ax := ⟨⟨by decide, by decide⟩, negSq_concave⟩

theorem analogy_thermo_marketDMU :
    Nonempty (Analogy Thermo MarketDMU thermoObs marketObs) := ⟨thermoMarketDMU⟩

theorem marketDMU_equilibrium_even :
    MarketDMU.Thm (fun m => EquilibriumIsEven (marketObs m)) :=
  thermoMarketDMU.toInterp.transfer_anchored thermoMarketDMU.anchors thermo_equilibrium_even

/-- Karşı örnek: doğrusal fayda `u(x) = x` (sabit marjinal fayda; kesin azalmıyor).
`(0, 10)` dağılımında gönüllü ticaret kalmamıştır, ama dağılım eşit değildir. -/
def thermoMarket : Refutation Thermo Market thermoObs marketObs where
  claim  := EquilibriumIsEven
  thm    := thermo_equilibrium_even
  cex    := ⟨fun x => x, ⟨0, 10⟩⟩
  cex_ax := ⟨by decide, by decide⟩
  fails  := by
    intro h
    have heq : Exchange.Equilibrium ⟨fun x => x, ⟨0, 10⟩⟩ := by
      rintro ⟨y1, y2⟩ ⟨hs, ⟨h1, h2⟩, t, ha, hb, hc⟩
      dsimp only at hs h1 h2 ha hb hc
      omega
    have := h heq
    revert this
    show ¬ (-1 ≤ (0 : Int) - 10 ∧ (0 : Int) - 10 ≤ 1)
    decide

theorem metaphor_thermo_market :
    Nonempty (Refutation Thermo Market thermoObs marketObs) := ⟨thermoMarket⟩

end Proofs
