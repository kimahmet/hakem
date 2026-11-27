import Hakem
import Solution.Background

/-! Güvenilmeyen ispatlar: karbonun sosyal maliyeti (arka planlı). -/

namespace Proofs

/-! ## ℕ'de arka plan gerçekleri -/

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

theorem scc_box {d h : Nat} (d1 : 900000 ≤ d) (d2 : d ≤ 1100000) (h1 : 150 ≤ h) (h2 : h ≤ 300)
    (rho : Nat) : sccOf 900000 150 rho ≤ sccOf d h rho ∧ sccOf d h rho ≤ sccOf 1100000 300 rho := by
  unfold sccOf
  constructor
  · have a := ds_mono_v rho 150 d1
    have b := ds_mono_n rho (h - 150) 150 d
    rw [show 150 + (h - 150) = h by omega] at b
    exact Nat.le_trans a b
  · have a := ds_mono_v rho h d2
    have b := ds_mono_n rho (300 - h) h 1100000
    rw [show h + (300 - h) = 300 by omega] at b
    exact Nat.le_trans a b

theorem stern_low : 120000000 ≤ sccOf 900000 150 10 := by decide +kernel
theorem nordhaus_high : sccOf 1100000 300 150 < 75000000 := by decide +kernel
theorem nordhaus_world_low : ¬ (120000000 ≤ sccOf 900000 150 150) := by decide +kernel
theorem stern_world_high : 75000000 ≤ sccOf 900000 150 10 := by decide +kernel

theorem scc_background_stern : NatStd.Sat bgStern := by
  intro env
  show ∀ d h : Nat, 900000 ≤ d → d ≤ 1100000 → 150 ≤ h → h ≤ 300 → 120000000 ≤ sccOf d h 10
  intro d h d1 d2 h1 h2
  exact Nat.le_trans stern_low (scc_box d1 d2 h1 h2 10).1

theorem scc_background_nordhaus : NatStd.Sat bgNordhaus := by
  intro env
  show ∀ d h : Nat, 900000 ≤ d → d ≤ 1100000 → 150 ≤ h → h ≤ 300 → ¬ 75000000 ≤ sccOf d h 150
  intro d h d1 d2 h1 h2 hc
  exact absurd (Nat.lt_of_le_of_lt (scc_box d1 d2 h1 h2 150).2 nordhaus_high) (Nat.not_lt.2 hc)

/-! ## Kabul edilebilirlik: standart kısmı ℕ olan yapılar -/

theorem adm_nat (fnv : (f : CFn) → (Fin (CSig.fnArity f) → Nat) → Nat)
    (relv : (r : CRel) → (Fin (CSig.relArity r) → Nat) → Prop)
    (hfn : ∀ g v, fnv (.base g) v = NatStd.fn g v) (hrel : ∀ q v, relv (.base q) v ↔ NatStd.rel q v) :
    Nonempty ((embed.reduct (⟨Nat, 0, fnv, relv⟩ : Structure CSig)).Iso NatStd) := by
  refine ⟨{ to := id, inv := id, left := fun _ => rfl, right := fun _ => rfl, dflt := rfl,
            fn := ?_, rel := ?_ }⟩
  · intro g v
    show fnv (.base g) (fun i => argEnv (⟨Nat, 0, fnv, relv⟩ : Structure CSig) v i.val) = _
    rw [hfn]
    congr 1
    funext i
    show argEnv _ v i.val = v i
    unfold argEnv
    exact dite_eq_left i.isLt
  · intro q v
    show relv (.base q) (fun i => argEnv (⟨Nat, 0, fnv, relv⟩ : Structure CSig) v i.val) ↔ _
    rw [hrel]
    rw [show (fun i => argEnv (⟨Nat, 0, fnv, relv⟩ : Structure CSig) v i.val) = v from by
      funext i; unfold argEnv; exact dite_eq_left i.isLt]
    exact Iff.rfl

/-! ## Dünyalar -/

/-- Zarar, süre, ρ ve vergi değerleriyle ℕ üzerinde bir dünya. -/
def cWorld (d h r t : Nat) : Structure CSig where
  D := Nat
  dflt := 0
  fn := fun f v => match f, v with
    | .base g, v => NatStd.fn g v
    | .damage, _ => d
    | .horizon, _ => h
    | .rho, _ => r
    | .tax, _ => t
  rel := fun r v => match r, v with
    | .base q, v => NatStd.rel q v

theorem cWorld_adm (d h r t : Nat) :
    Nonempty ((embed.reduct (cWorld d h r t)).Iso NatStd) :=
  adm_nat _ _ (fun _ _ => rfl) (fun _ _ => Iff.rfl)

/-- Yalnızca ρ ve vergiyi değiştiren yeniden yorum. -/
def normsTo (W : Structure CSig) (r t : W.D) : (f : CFn) → (Fin (CSig.fnArity f) → W.D) → W.D :=
  fun f v => match f, v with
    | .rho, _ => r
    | .tax, _ => t
    | f, v => W.fn f v

/-! Değişkenler üzerinden genel lemmalar: somut sayılarla elaborator'da hesap yapılmaz. -/

theorem cWorld_facts (d h r t : Nat) (hf : 900000 ≤ d ∧ d ≤ 1100000 ∧ 150 ≤ h ∧ h ≤ 300) :
    ∀ ψ ∈ sccFacts, ∀ env, ψ.eval (cWorld d h r t) env := by
  intro ψ hψ env
  simp only [sccFacts, List.mem_cons, List.not_mem_nil, or_false] at hψ
  rcases hψ with rfl | rfl | rfl | rfl
  · exact (show 900000 ≤ d from hf.1)
  · exact (show d ≤ 1100000 from hf.2.1)
  · exact (show 150 ≤ h from hf.2.2.1)
  · exact (show h ≤ 300 from hf.2.2.2)

theorem cWorld_norms (d h r : Nat) :
    ∀ ψ ∈ [Formula.eq rhoT (cnum r), Formula.eq taxT (cscc dmg hor rhoT)], ∀ env,
      ψ.eval (cWorld d h r (sccOf d h r)) env := by
  intro ψ hψ env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
  rcases hψ with rfl | rfl
  · exact (show r = r from rfl)
  · exact (show sccOf d h r = sccOf d h r from rfl)

theorem cWorld_models (d h r : Nat) (hf : 900000 ≤ d ∧ d ≤ 1100000 ∧ 150 ≤ h ∧ h ≤ 300) :
    (Theory.withBackground (sccFacts ++ [Formula.eq rhoT (cnum r), Formula.eq taxT (cscc dmg hor rhoT)])
      embed NatStd).Models (cWorld d h r (sccOf d h r)) := by
  refine ⟨cWorld_adm _ _ _ _, fun ψ hψ env => ?_⟩
  rcases List.mem_append.1 hψ with h1 | h2
  · exact cWorld_facts d h r _ hf ψ h1 env
  · exact cWorld_norms d h r ψ h2 env

theorem alt_adm (d h r t r' t' : Nat) :
    Nonempty ((embed.reduct ((cWorld d h r t).reinterp (normsTo (cWorld d h r t) r' t')
      (cWorld d h r t).rel)).Iso NatStd) :=
  adm_nat _ _ (fun _ _ => rfl) (fun _ _ => Iff.rfl)

theorem alt_fails_atLeast (d h r t r' t' : Nat) (hlow : ¬ 120000000 ≤ t') :
    ¬ ((cWorld d h r t).reinterp (normsTo (cWorld d h r t) r' t') (cWorld d h r t).rel).Sat
      taxAtLeast120 :=
  fun hs => hlow (hs (fun _ => (0 : Nat)))

theorem alt_fails_below (d h r t r' t' : Nat) (hhigh : 75000000 ≤ t') :
    ¬ ((cWorld d h r t).reinterp (normsTo (cWorld d h r t) r' t') (cWorld d h r t).rel).Sat
      taxBelow75 :=
  fun hs => (hs (fun _ => (0 : Nat)) : ¬ 75000000 ≤ t') hhigh

theorem box_low : 900000 ≤ 900000 ∧ 900000 ≤ 1100000 ∧ 150 ≤ 150 ∧ 150 ≤ 300 := by decide

/-! ## Stern -/

theorem scc_stern_proof_checks :
    check (SternSCC.axioms ++ [bgStern].map embed.trF) taxAtLeast120 sternProof = true := by
  decide +kernel

theorem stern_entails : SternSCC.Entails taxAtLeast120 :=
  calculus_sound_bg SternSCC embed NatStd [bgStern] taxAtLeast120 sternProof (fun _ h => h)
    (fun ψ hψ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
      subst hψ; exact scc_background_stern)
    scc_stern_proof_checks

theorem scc_stern_verdict : Nonempty (PolicyVerdict SternSCC taxAtLeast120) :=
  ⟨{ entails := stern_entails
     world := cWorld 900000 150 10 (sccOf 900000 150 10)
     world_ok := cWorld_models 900000 150 10 box_low
     g := normsTo (cWorld 900000 150 10 (sccOf 900000 150 10)) (150 : Nat) (sccOf 900000 150 150)
     h := (cWorld 900000 150 10 (sccOf 900000 150 10)).rel
     alt_adm := alt_adm _ _ _ _ _ _
     fails := alt_fails_atLeast _ _ _ _ _ _ nordhaus_world_low }⟩

/-! ## Nordhaus -/

theorem scc_nordhaus_proof_checks :
    check (NordhausSCC.axioms ++ [bgNordhaus].map embed.trF) taxBelow75 nordhausProof = true := by
  decide +kernel

theorem nordhaus_entails : NordhausSCC.Entails taxBelow75 :=
  calculus_sound_bg NordhausSCC embed NatStd [bgNordhaus] taxBelow75 nordhausProof (fun _ h => h)
    (fun ψ hψ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
      subst hψ; exact scc_background_nordhaus)
    scc_nordhaus_proof_checks

theorem scc_nordhaus_verdict : Nonempty (PolicyVerdict NordhausSCC taxBelow75) :=
  ⟨{ entails := nordhaus_entails
     world := cWorld 900000 150 150 (sccOf 900000 150 150)
     world_ok := cWorld_models 900000 150 150 box_low
     g := normsTo (cWorld 900000 150 150 (sccOf 900000 150 150)) (10 : Nat) (sccOf 900000 150 10)
     h := (cWorld 900000 150 150 (sccOf 900000 150 150)).rel
     alt_adm := alt_adm _ _ _ _ _ _
     fails := alt_fails_below _ _ _ _ _ _ stern_world_high }⟩

theorem scc_roles_computed :
    sccFacts.all (·.descriptive) = true ∧ sternNorms.all (fun ψ => !ψ.descriptive) = true ∧
    nordhausNorms.all (fun ψ => !ψ.descriptive) = true ∧ taxAtLeast120.descriptive = false := by
  decide

end Proofs
