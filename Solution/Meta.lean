import Hakem

/-! Untrusted proofs: the general laws of the kernel. -/

namespace Proofs

variable {S S₁ S₂ S₃ : Signature}

/-! ## Helpers -/

theorem allFin_spec : ∀ {k : Nat} {p : Fin k → Bool}, allFin k p = true → ∀ i, p i = true
  | 0, _, _, i => i.elim0
  | k + 1, p, h, i => by
    simp only [allFin, Bool.and_eq_true] at h
    exact Fin.cases (motive := fun i => p i = true) h.1
      (fun j => allFin_spec (p := fun i => p i.succ) h.2 j) i

/-! ## Substitution -/

theorem Term.eval_subst (M : Structure S) (σ : Nat → Term S) (env : Nat → M.D) (t : Term S) :
    (t.subst σ).eval M env = t.eval M (fun n => (σ n).eval M env) := by
  induction t with
  | var n => rfl
  | dflt => rfl
  | app f a ih => exact congrArg (M.fn f) (funext ih)

theorem Term.eval_shift (M : Structure S) (t : Term S) (d : M.D) (env : Nat → M.D) :
    t.shift.eval M (cons d env) = t.eval M env := by
  unfold Term.shift
  rw [Term.eval_subst]
  rfl

theorem eval_liftSubst (M : Structure S) (σ : Nat → Term S) (d : M.D) (env : Nat → M.D) :
    (fun n => (liftSubst σ n).eval M (cons d env)) = cons d (fun n => (σ n).eval M env) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact Term.eval_shift M (σ n) d env

theorem Formula.eval_subst (M : Structure S) (φ : Formula S) :
    ∀ (σ : Nat → Term S) (env : Nat → M.D),
      (φ.subst σ).eval M env ↔ φ.eval M (fun n => (σ n).eval M env) := by
  induction φ with
  | falsum => intro σ env; exact Iff.rfl
  | eq t u =>
    intro σ env
    show (t.subst σ).eval M env = (u.subst σ).eval M env ↔ _
    rw [Term.eval_subst, Term.eval_subst]
    exact Iff.rfl
  | rel r a =>
    intro σ env
    show M.rel r (fun i => ((a i).subst σ).eval M env) ↔ M.rel r (fun i => (a i).eval M _)
    rw [show (fun i => ((a i).subst σ).eval M env) = (fun i => (a i).eval M _) from
      funext fun i => Term.eval_subst M σ env (a i)]
  | imp φ ψ ihφ ihψ =>
    intro σ env
    exact ⟨fun h x => (ihψ σ env).1 (h ((ihφ σ env).2 x)),
           fun h x => (ihψ σ env).2 (h ((ihφ σ env).1 x))⟩
  | and φ ψ ihφ ihψ =>
    intro σ env
    exact ⟨fun ⟨x, y⟩ => ⟨(ihφ σ env).1 x, (ihψ σ env).1 y⟩,
           fun ⟨x, y⟩ => ⟨(ihφ σ env).2 x, (ihψ σ env).2 y⟩⟩
  | or φ ψ ihφ ihψ =>
    intro σ env
    exact ⟨fun h => h.elim (fun x => Or.inl ((ihφ σ env).1 x)) (fun y => Or.inr ((ihψ σ env).1 y)),
           fun h => h.elim (fun x => Or.inl ((ihφ σ env).2 x)) (fun y => Or.inr ((ihψ σ env).2 y))⟩
  | all φ ih =>
    intro σ env
    show (∀ d, (φ.subst (liftSubst σ)).eval M (cons d env)) ↔ ∀ d, φ.eval M (cons d _)
    constructor
    · intro h d
      have := (ih (liftSubst σ) (cons d env)).1 (h d)
      rwa [eval_liftSubst] at this
    · intro h d
      apply (ih (liftSubst σ) (cons d env)).2
      rw [eval_liftSubst]
      exact h d
  | ex φ ih =>
    intro σ env
    show (∃ d, (φ.subst (liftSubst σ)).eval M (cons d env)) ↔ ∃ d, φ.eval M (cons d _)
    constructor
    · rintro ⟨d, hd⟩
      have := (ih (liftSubst σ) (cons d env)).1 hd
      rw [eval_liftSubst] at this
      exact ⟨d, this⟩
    · rintro ⟨d, hd⟩
      refine ⟨d, (ih (liftSubst σ) (cons d env)).2 ?_⟩
      rw [eval_liftSubst]
      exact hd

/-! ## Satisfaction condition: translation agrees with the reduct -/

theorem argSubst_eval (M : Structure S₂) {k : Nat} (a : Fin k → Term S₂) (v : Fin k → M.D)
    (env : Nat → M.D) (h : ∀ i, (a i).eval M env = v i) :
    (fun n => (argSubst a n).eval M env) = argEnv M v := by
  funext n
  unfold argSubst argEnv
  by_cases hn : n < k
  · rw [dite_eq_left hn, dite_eq_left hn]; exact h _
  · rw [dite_eq_right hn, dite_eq_right hn]; rfl

theorem trT_eval (σ : SigMorph S₁ S₂) (M : Structure S₂) (env : Nat → M.D) (t : Term S₁) :
    (σ.trT t).eval M env = t.eval (σ.reduct M) env := by
  induction t with
  | var n => rfl
  | dflt => rfl
  | app f a ih =>
    show ((σ.fnMap f).subst (argSubst fun i => σ.trT (a i))).eval M env =
      (σ.fnMap f).eval M (argEnv M fun i => (a i).eval (σ.reduct M) env)
    rw [Term.eval_subst, argSubst_eval M _ _ env ih]

/-- Satisfaction condition. -/
theorem trF_eval (σ : SigMorph S₁ S₂) (M : Structure S₂) (φ : Formula S₁) :
    ∀ env : Nat → M.D, (σ.trF φ).eval M env ↔ φ.eval (σ.reduct M) env := by
  induction φ with
  | falsum => intro env; exact Iff.rfl
  | eq t u =>
    intro env
    show (σ.trT t).eval M env = (σ.trT u).eval M env ↔ _
    rw [trT_eval, trT_eval]
    exact Iff.rfl
  | rel r a =>
    intro env
    show ((σ.relMap r).subst (argSubst fun i => σ.trT (a i))).eval M env ↔
      (σ.relMap r).eval M (argEnv M fun i => (a i).eval (σ.reduct M) env)
    rw [Formula.eval_subst, argSubst_eval M _ _ env (fun i => trT_eval σ M env (a i))]
  | imp φ ψ ihφ ihψ =>
    intro env
    exact ⟨fun h x => (ihψ env).1 (h ((ihφ env).2 x)), fun h x => (ihψ env).2 (h ((ihφ env).1 x))⟩
  | and φ ψ ihφ ihψ =>
    intro env
    exact ⟨fun ⟨x, y⟩ => ⟨(ihφ env).1 x, (ihψ env).1 y⟩, fun ⟨x, y⟩ => ⟨(ihφ env).2 x, (ihψ env).2 y⟩⟩
  | or φ ψ ihφ ihψ =>
    intro env
    exact ⟨fun h => h.elim (fun x => Or.inl ((ihφ env).1 x)) (fun y => Or.inr ((ihψ env).1 y)),
           fun h => h.elim (fun x => Or.inl ((ihφ env).2 x)) (fun y => Or.inr ((ihψ env).2 y))⟩
  | all φ ih =>
    intro env
    exact ⟨fun h d => (ih (cons d env)).1 (h d), fun h d => (ih (cons d env)).2 (h d)⟩
  | ex φ ih =>
    intro env
    exact ⟨fun ⟨d, hd⟩ => ⟨d, (ih (cons d env)).1 hd⟩, fun ⟨d, hd⟩ => ⟨d, (ih (cons d env)).2 hd⟩⟩

theorem satisfaction (σ : SigMorph S₁ S₂) (M : Structure S₂) (φ : Formula S₁) :
    M.Sat (σ.trF φ) ↔ (σ.reduct M).Sat φ :=
  ⟨fun h env => (trF_eval σ M φ env).1 (h env), fun h env => (trF_eval σ M φ env).2 (h env)⟩

/-! ## Transfer -/

theorem reduct_models {A : Theory S₁} {B : Theory S₂} (a : Analogy A B) (M : Structure S₂)
    (hM : B.Models M) : A.Models (a.σ.reduct M) :=
  ⟨a.adm M hM, fun ψ hψ => (satisfaction a.σ M ψ).1 (a.preserves ψ hψ M hM)⟩

theorem transfer {A : Theory S₁} {B : Theory S₂} (a : Analogy A B) {φ : Formula S₁}
    (h : A.Entails φ) : B.Entails (a.σ.trF φ) :=
  fun M hM => (satisfaction a.σ M φ).2 (h _ (reduct_models a M hM))

theorem source_consistent {A : Theory S₁} {B : Theory S₂} (a : Analogy A B) :
    ∃ M, A.Models M :=
  ⟨a.σ.reduct a.model, reduct_models a a.model a.model_ok⟩

/-! ## Composition -/

theorem reduct_comp (σ : SigMorph S₁ S₂) (τ : SigMorph S₂ S₃) (M : Structure S₃) :
    (σ.comp τ).reduct M = σ.reduct (τ.reduct M) := by
  unfold SigMorph.reduct SigMorph.comp
  congr 1
  · funext f v
    exact trT_eval τ M _ (σ.fnMap f)
  · funext r v
    exact propext (trF_eval τ M (σ.relMap r) _)

def compose {A : Theory S₁} {B : Theory S₂} {C : Theory S₃} (a : Analogy A B) (b : Analogy B C) :
    Analogy A C where
  σ := a.σ.comp b.σ
  adm := fun M hM => by
    rw [reduct_comp]
    exact a.adm _ (reduct_models b M hM)
  preserves := fun φ hφ M hM => by
    rw [satisfaction, reduct_comp, ← satisfaction, ← satisfaction]
    exact transfer b (a.preserves φ hφ) M hM
  model := b.model
  model_ok := b.model_ok

theorem compose_exists {A : Theory S₁} {B : Theory S₂} {C : Theory S₃}
    (a : Analogy A B) (b : Analogy B C) : ∃ c : Analogy A C, c.σ = a.σ.comp b.σ :=
  ⟨compose a b, rfl⟩

/-! ## Metaphor -/

theorem trT_congr {pf : S₁.Fn → Bool} {σ τ : SigMorph S₁ S₂}
    (hag : ∀ f, pf f = true → σ.fnMap f = τ.fnMap f) (t : Term S₁) :
    t.onlySyms pf = true → σ.trT t = τ.trT t := by
  induction t with
  | var n => intro _; rfl
  | dflt => intro _; rfl
  | app f a ih =>
    intro h
    simp only [Term.onlySyms, Bool.and_eq_true] at h
    have hall := allFin_spec h.2
    show (σ.fnMap f).subst (argSubst fun i => σ.trT (a i)) =
      (τ.fnMap f).subst (argSubst fun i => τ.trT (a i))
    rw [hag f h.1, show (fun i => σ.trT (a i)) = (fun i => τ.trT (a i)) from
      funext fun i => ih i (hall i)]

theorem trF_congr {pf : S₁.Fn → Bool} {pr : S₁.Rel → Bool} {σ τ : SigMorph S₁ S₂}
    (hag : σ.AgreeOn pf pr τ) (φ : Formula S₁) : φ.onlySyms pf pr = true → σ.trF φ = τ.trF φ := by
  induction φ with
  | falsum => intro _; rfl
  | eq t u =>
    intro h
    simp only [Formula.onlySyms, Bool.and_eq_true] at h
    show Formula.eq (σ.trT t) (σ.trT u) = Formula.eq (τ.trT t) (τ.trT u)
    rw [trT_congr hag.1 t h.1, trT_congr hag.1 u h.2]
  | rel r a =>
    intro h
    simp only [Formula.onlySyms, Bool.and_eq_true] at h
    have hall := allFin_spec h.2
    show (σ.relMap r).subst (argSubst fun i => σ.trT (a i)) =
      (τ.relMap r).subst (argSubst fun i => τ.trT (a i))
    rw [hag.2 r h.1, show (fun i => σ.trT (a i)) = (fun i => τ.trT (a i)) from
      funext fun i => trT_congr hag.1 (a i) (hall i)]
  | imp φ ψ ihφ ihψ =>
    intro h
    simp only [Formula.onlySyms, Bool.and_eq_true] at h
    show Formula.imp _ _ = Formula.imp _ _
    rw [ihφ h.1, ihψ h.2]
  | and φ ψ ihφ ihψ =>
    intro h
    simp only [Formula.onlySyms, Bool.and_eq_true] at h
    show Formula.and _ _ = Formula.and _ _
    rw [ihφ h.1, ihψ h.2]
  | or φ ψ ihφ ihψ =>
    intro h
    simp only [Formula.onlySyms, Bool.and_eq_true] at h
    show Formula.or _ _ = Formula.or _ _
    rw [ihφ h.1, ihψ h.2]
  | all φ ih =>
    intro h
    show Formula.all _ = Formula.all _
    rw [ih h]
  | ex φ ih =>
    intro h
    show Formula.ex _ = Formula.ex _
    rw [ih h]

theorem refutation_sound {A : Theory S₁} {B : Theory S₂} {pf : S₁.Fn → Bool} {pr : S₁.Rel → Bool}
    {gl : SigMorph S₁ S₂} (r : Refutation A B pf pr gl) (a : Analogy A B)
    (hag : a.σ.AgreeOn pf pr gl) : False := by
  have h := transfer a r.thm
  rw [trF_congr hag r.φ r.only] at h
  exact r.fails (h r.cex r.cex_ok)

/-! ## Hume's law -/

theorem Term.eval_reinterp (M : Structure S) (g h) (env : Nat → M.D) (t : Term S) :
    t.onlySyms (fun f => decide (S.fnRole f ≠ .normative)) = true →
      t.eval (M.reinterp g h) env = t.eval M env := by
  induction t with
  | var n => intro _; rfl
  | dflt => intro _; rfl
  | app f a ih =>
    intro hd
    simp only [Term.onlySyms, Bool.and_eq_true, decide_eq_true_eq] at hd
    have hall := allFin_spec hd.2
    show (if S.fnRole f = .normative then g f else M.fn f) (fun i => (a i).eval (M.reinterp g h) env) =
      M.fn f (fun i => (a i).eval M env)
    rw [ite_eq_right hd.1, show (fun i => (a i).eval (M.reinterp g h) env) = (fun i => (a i).eval M env)
      from funext fun i => ih i (hall i)]

theorem Formula.eval_reinterp (M : Structure S) (g h) (φ : Formula S) :
    φ.descriptive = true → ∀ env : Nat → M.D, (φ.eval (M.reinterp g h) env ↔ φ.eval M env) := by
  unfold Formula.descriptive
  induction φ with
  | falsum => intro _ env; exact Iff.rfl
  | eq t u =>
    intro hd env
    simp only [Formula.onlySyms, Bool.and_eq_true] at hd
    show t.eval (M.reinterp g h) env = u.eval (M.reinterp g h) env ↔ t.eval M env = u.eval M env
    rw [Term.eval_reinterp M g h env t hd.1, Term.eval_reinterp M g h env u hd.2]
    exact Iff.rfl
  | rel r a =>
    intro hd env
    simp only [Formula.onlySyms, Bool.and_eq_true, decide_eq_true_eq] at hd
    have hall := allFin_spec hd.2
    show (if S.relRole r = .normative then h r else M.rel r) (fun i => (a i).eval (M.reinterp g h) env) ↔
      M.rel r (fun i => (a i).eval M env)
    rw [ite_eq_right hd.1, show (fun i => (a i).eval (M.reinterp g h) env) = (fun i => (a i).eval M env)
      from funext fun i => Term.eval_reinterp M g h env (a i) (hall i)]
  | imp φ ψ ihφ ihψ =>
    intro hd env
    simp only [Formula.onlySyms, Bool.and_eq_true] at hd
    exact ⟨fun k x => (ihψ hd.2 env).1 (k ((ihφ hd.1 env).2 x)),
           fun k x => (ihψ hd.2 env).2 (k ((ihφ hd.1 env).1 x))⟩
  | and φ ψ ihφ ihψ =>
    intro hd env
    simp only [Formula.onlySyms, Bool.and_eq_true] at hd
    exact ⟨fun ⟨x, y⟩ => ⟨(ihφ hd.1 env).1 x, (ihψ hd.2 env).1 y⟩,
           fun ⟨x, y⟩ => ⟨(ihφ hd.1 env).2 x, (ihψ hd.2 env).2 y⟩⟩
  | or φ ψ ihφ ihψ =>
    intro hd env
    simp only [Formula.onlySyms, Bool.and_eq_true] at hd
    exact ⟨fun k => k.elim (fun x => Or.inl ((ihφ hd.1 env).1 x)) (fun y => Or.inr ((ihψ hd.2 env).1 y)),
           fun k => k.elim (fun x => Or.inl ((ihφ hd.1 env).2 x)) (fun y => Or.inr ((ihψ hd.2 env).2 y))⟩
  | all φ ih =>
    intro hd env
    exact ⟨fun k d => (ih hd (cons d env)).1 (k d), fun k d => (ih hd (cons d env)).2 (k d)⟩
  | ex φ ih =>
    intro hd env
    exact ⟨fun ⟨d, x⟩ => ⟨d, (ih hd (cons d env)).1 x⟩, fun ⟨d, x⟩ => ⟨d, (ih hd (cons d env)).2 x⟩⟩

/-- Hume's law: a theory whose premises are all descriptive has no policy verdict. -/
theorem hume_law {T : Theory S} {φ : Formula S} (hT : ∀ ψ ∈ T.axioms, ψ.descriptive = true) :
    ¬ Nonempty (PolicyVerdict T φ) := by
  rintro ⟨v⟩
  apply v.fails
  apply v.entails
  exact ⟨v.alt_adm, fun ψ hψ env =>
    (Formula.eval_reinterp v.world v.g v.h ψ (hT ψ hψ) env).2 (v.world_ok.2 ψ hψ env)⟩

/-- Same facts: the alternative world agrees with the actual world on every descriptive
symbol; the conclusion holds in the actual world and fails in the alternative. -/
theorem verdict_same_facts {T : Theory S} {φ : Formula S} (v : PolicyVerdict T φ) :
    (∀ f, S.fnRole f ≠ .normative → (v.world.reinterp v.g v.h).fn f = v.world.fn f) ∧
    (∀ r, S.relRole r ≠ .normative → (v.world.reinterp v.g v.h).rel r = v.world.rel r) ∧
    v.world.Sat φ ∧ ¬ (v.world.reinterp v.g v.h).Sat φ :=
  ⟨fun _ hf => ite_eq_right hf, fun _ hr => ite_eq_right hr, v.entails _ v.world_ok, v.fails⟩

end Proofs
