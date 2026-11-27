import Hakem
import Solution.Meta

/-! Untrusted proofs: soundness of the calculus. -/

namespace Proofs

variable {S : Signature}

theorem Term.beq_sound [DecidableEq S.Fn] (t : Term S) : ∀ u, t.beq u = true → t = u := by
  induction t with
  | var n =>
    intro u h
    cases u with
    | var m => simp only [Term.beq, decide_eq_true_eq] at h; rw [h]
    | dflt => simp [Term.beq] at h
    | app g b => simp [Term.beq] at h
  | dflt =>
    intro u h
    cases u with
    | var m => simp [Term.beq] at h
    | dflt => rfl
    | app g b => simp [Term.beq] at h
  | app f a ih =>
    intro u h
    cases u with
    | var m => simp [Term.beq] at h
    | dflt => simp [Term.beq] at h
    | app g b =>
      unfold Term.beq at h
      split at h
      · rename_i hfg
        subst hfg
        have hall := allFin_spec h
        show Term.app f a = Term.app f b
        congr 1
        funext i
        exact ih i _ (hall i)
      · simp at h

theorem Formula.beq_sound [DecidableEq S.Fn] [DecidableEq S.Rel] (φ : Formula S) :
    ∀ ψ, φ.beq ψ = true → φ = ψ := by
  induction φ with
  | falsum => intro ψ h; cases ψ <;> first | rfl | simp [Formula.beq] at h
  | eq t u =>
    intro ψ h
    cases ψ with
    | eq t' u' =>
      simp only [Formula.beq, Bool.and_eq_true] at h
      rw [Term.beq_sound t t' h.1, Term.beq_sound u u' h.2]
    | _ => simp [Formula.beq] at h
  | rel r a =>
    intro ψ h
    cases ψ with
    | rel s b =>
      unfold Formula.beq at h
      split at h
      · rename_i hrs
        subst hrs
        have hall := allFin_spec h
        show Formula.rel r a = Formula.rel r b
        congr 1
        funext i
        exact Term.beq_sound (a i) _ (hall i)
      · simp at h
    | _ => simp [Formula.beq] at h
  | imp φ ψ ihφ ihψ =>
    intro χ h
    cases χ with
    | imp φ' ψ' =>
      simp only [Formula.beq, Bool.and_eq_true] at h
      rw [ihφ φ' h.1, ihψ ψ' h.2]
    | _ => simp [Formula.beq] at h
  | and φ ψ ihφ ihψ =>
    intro χ h
    cases χ with
    | and φ' ψ' =>
      simp only [Formula.beq, Bool.and_eq_true] at h
      rw [ihφ φ' h.1, ihψ ψ' h.2]
    | _ => simp [Formula.beq] at h
  | or φ ψ ihφ ihψ =>
    intro χ h
    cases χ with
    | or φ' ψ' =>
      simp only [Formula.beq, Bool.and_eq_true] at h
      rw [ihφ φ' h.1, ihψ ψ' h.2]
    | _ => simp [Formula.beq] at h
  | all φ ih =>
    intro χ h
    cases χ with
    | all φ' => simp only [Formula.beq] at h; rw [ih φ' h]
    | _ => simp [Formula.beq] at h
  | ex φ ih =>
    intro χ h
    cases χ with
    | ex φ' => simp only [Formula.beq] at h; rw [ih φ' h]
    | _ => simp [Formula.beq] at h

theorem eval_shiftF (M : Structure S) (φ : Formula S) (d : M.D) (env : Nat → M.D) :
    φ.shift.eval M (cons d env) ↔ φ.eval M env := by
  unfold Formula.shift
  rw [Formula.eval_subst]
  exact Iff.rfl

theorem eval_inst (M : Structure S) (φ : Formula S) (t : Term S) (env : Nat → M.D) :
    (φ.subst (instSubst t)).eval M env ↔ φ.eval M (cons (t.eval M env) env) := by
  rw [Formula.eval_subst]
  rw [show (fun n => (instSubst t n).eval M env) = cons (t.eval M env) env from by
    funext n; cases n <;> rfl]

theorem hyps_shift (M : Structure S) (Γ : List (Formula S)) (d : M.D) (env : Nat → M.D)
    (hΓ : ∀ ψ ∈ Γ, ψ.eval M env) : ∀ ψ ∈ Γ.map Formula.shift, ψ.eval M (cons d env) := by
  intro ψ hψ
  obtain ⟨ψ₀, h₀, rfl⟩ := List.mem_map.1 hψ
  exact (eval_shiftF M ψ₀ d env).2 (hΓ ψ₀ h₀)

theorem hyps_cons (M : Structure S) {Γ : List (Formula S)} {φ : Formula S} {env : Nat → M.D}
    (hφ : φ.eval M env) (hΓ : ∀ ψ ∈ Γ, ψ.eval M env) : ∀ ψ ∈ φ :: Γ, ψ.eval M env := by
  intro ψ hψ
  rcases List.mem_cons.1 hψ with rfl | h
  · exact hφ
  · exact hΓ ψ h

theorem infer_sound [DecidableEq S.Fn] [DecidableEq S.Rel] (p : Proof S) :
    ∀ (Γ : List (Formula S)) (φ : Formula S), infer Γ p = some φ →
      ∀ (M : Structure S) (env : Nat → M.D), (∀ ψ ∈ Γ, ψ.eval M env) → φ.eval M env := by
  induction p with
  | hyp i =>
    intro Γ φ h M env hΓ
    exact hΓ φ (List.mem_of_getElem? h)
  | falsumE φ p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i heq
      exact (ih Γ _ heq M env hΓ).elim
    · simp at h
  | impI φ p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    cases hq : infer (φ :: Γ) p with
    | none => rw [hq] at h; simp at h
    | some ψ =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact fun hφ => ih _ _ hq M env (hyps_cons M hφ hΓ)
  | impE p q ihp ihq =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i φ ψ φ' hp hq
      split at h
      · rename_i hb
        simp only [Option.some.injEq] at h
        subst h
        have e := Formula.beq_sound φ φ' hb
        subst e
        exact (ihp Γ _ hp M env hΓ) (ihq Γ _ hq M env hΓ)
      · simp at h
    · simp at h
  | andI p q ihp ihq =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i φ ψ hp hq
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨ihp Γ _ hp M env hΓ, ihq Γ _ hq M env hΓ⟩
    · simp at h
  | andE1 p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i φ ψ hp
      simp only [Option.some.injEq] at h
      subst h
      exact (ih Γ _ hp M env hΓ).1
    · simp at h
  | andE2 p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i φ ψ hp
      simp only [Option.some.injEq] at h
      subst h
      exact (ih Γ _ hp M env hΓ).2
    · simp at h
  | orI1 ψ p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    cases hq : infer Γ p with
    | none => rw [hq] at h; simp at h
    | some φ =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact Or.inl (ih Γ _ hq M env hΓ)
  | orI2 φ p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    cases hq : infer Γ p with
    | none => rw [hq] at h; simp at h
    | some ψ =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact Or.inr (ih Γ _ hq M env hΓ)
  | orE p q r ihp ihq ihr =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i φ ψ hp
      split at h
      · rename_i χ₁ χ₂ hq hr
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          have e := Formula.beq_sound χ₁ χ₂ hb
          subst e
          rcases ihp Γ _ hp M env hΓ with hφ | hψ
          · exact ihq _ _ hq M env (hyps_cons M hφ hΓ)
          · exact ihr _ _ hr M env (hyps_cons M hψ hΓ)
        · simp at h
      · simp at h
    · simp at h
  | allI p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    cases hq : infer (Γ.map Formula.shift) p with
    | none => rw [hq] at h; simp at h
    | some φ =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact fun d => ih _ _ hq M (cons d env) (hyps_shift M Γ d env hΓ)
  | allE t p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i φ hp
      simp only [Option.some.injEq] at h
      subst h
      exact (eval_inst M φ t env).2 (ih Γ _ hp M env hΓ _)
    · simp at h
  | exI φ t p ih =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i χ₀ hp
      split at h
      · rename_i hb
        simp only [Option.some.injEq] at h
        subst h
        have e := Formula.beq_sound _ _ hb
        subst e
        exact ⟨t.eval M env, (eval_inst M φ t env).1 (ih Γ _ hp M env hΓ)⟩
      · simp at h
    · simp at h
  | exE χ p q ihp ihq =>
    intro Γ χ' h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i φ hp
      split at h
      · rename_i χ₁ hq
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          have e := Formula.beq_sound _ _ hb
          subst e
          obtain ⟨d, hd⟩ := ihp Γ _ hp M env hΓ
          exact (eval_shiftF M _ d env).1
            (ihq _ _ hq M (cons d env) (hyps_cons M hd (hyps_shift M Γ d env hΓ)))
        · simp at h
      · simp at h
    · simp at h
  | refl t =>
    intro Γ χ h M env hΓ
    simp only [infer, Option.some.injEq] at h
    subst h
    show t.eval M env = t.eval M env
    rfl
  | eqE φ p q ihp ihq =>
    intro Γ χ h M env hΓ
    simp only [infer] at h
    split at h
    · rename_i t u χ₀ hp hq
      split at h
      · rename_i hb
        simp only [Option.some.injEq] at h
        subst h
        have e := Formula.beq_sound _ _ hb
        subst e
        have htu : t.eval M env = u.eval M env := ihp Γ _ hp M env hΓ
        have hφ := (eval_inst M φ t env).1 (ihq Γ _ hq M env hΓ)
        rw [htu] at hφ
        exact (eval_inst M φ u env).2 hφ
      · simp at h
    · simp at h
  | em φ =>
    intro Γ χ h M env hΓ
    simp only [infer, Option.some.injEq] at h
    subst h
    exact Classical.em _

/-- Soundness of the calculus: a proof that passes the check shows what the theory entails. -/
theorem calculus_sound : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S), check T.axioms φ p = true → T.Entails φ := by
  intro S _ _ T φ p h M hM env
  unfold check at h
  split at h
  · rename_i ψ hp
    have e := Formula.beq_sound _ _ h
    subst e
    exact infer_sound p _ _ hp M env (fun χ hχ => hM.2 χ hχ env)
  · simp at h

end Proofs
