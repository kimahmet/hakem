import Hakem
import Solution.Calculus

/-! Güvenilmeyen ispatlar: sonlu model denetleyicisinin sağlamlığı. -/

namespace Proofs

variable {S : Signature}

theorem allFin_iff : ∀ {k : Nat} {p : Fin k → Bool}, allFin k p = true ↔ ∀ i, p i = true
  | 0, _ => ⟨fun _ i => i.elim0, fun _ => rfl⟩
  | k + 1, p => by
    constructor
    · exact allFin_spec
    · intro h
      simp only [allFin, Bool.and_eq_true]
      exact ⟨h 0, allFin_iff.2 (fun i => h i.succ)⟩

theorem anyFin_iff : ∀ {k : Nat} {p : Fin k → Bool}, anyFin k p = true ↔ ∃ i, p i = true
  | 0, _ => by simp [anyFin, allFin]
  | k + 1, p => by
    have e : anyFin (k + 1) p = (p 0 || anyFin k (fun i => p i.succ)) := by
      simp only [anyFin, allFin, Bool.not_and, Bool.not_not]
    rw [e, Bool.or_eq_true, anyFin_iff]
    constructor
    · rintro (h | ⟨i, h⟩)
      · exact ⟨0, h⟩
      · exact ⟨i.succ, h⟩
    · rintro ⟨i, h⟩
      revert h
      refine Fin.cases (motive := fun i => p i = true → _) (fun h => Or.inl h) (fun j h => Or.inr ⟨j, h⟩) i

theorem evalB_iff (M : FinStructure S) (φ : Formula S) :
    ∀ env, M.evalB env φ = true ↔ φ.eval M.toStructure env := by
  induction φ with
  | falsum => intro env; simp [FinStructure.evalB, Formula.eval]
  | eq t u => intro env; simp [FinStructure.evalB, Formula.eval]
  | rel r a => intro env; exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro env
    show (!(M.evalB env φ) || M.evalB env ψ) = true ↔ (φ.eval M.toStructure env → ψ.eval M.toStructure env)
    rw [← ihφ env, ← ihψ env]
    cases M.evalB env φ <;> cases M.evalB env ψ <;> simp
  | and φ ψ ihφ ihψ =>
    intro env
    show (M.evalB env φ && M.evalB env ψ) = true ↔ (φ.eval M.toStructure env ∧ ψ.eval M.toStructure env)
    rw [← ihφ env, ← ihψ env]
    cases M.evalB env φ <;> cases M.evalB env ψ <;> simp
  | or φ ψ ihφ ihψ =>
    intro env
    show (M.evalB env φ || M.evalB env ψ) = true ↔ (φ.eval M.toStructure env ∨ ψ.eval M.toStructure env)
    rw [← ihφ env, ← ihψ env]
    cases M.evalB env φ <;> cases M.evalB env ψ <;> simp
  | all φ ih =>
    intro env
    show allFin (M.n + 1) (fun d => M.evalB (cons d env) φ) = true ↔ ∀ d, φ.eval M.toStructure (cons d env)
    rw [allFin_iff]
    exact ⟨fun h d => (ih _).1 (h d), fun h d => (ih _).2 (h d)⟩
  | ex φ ih =>
    intro env
    show anyFin (M.n + 1) (fun d => M.evalB (cons d env) φ) = true ↔ ∃ d, φ.eval M.toStructure (cons d env)
    rw [anyFin_iff]
    exact ⟨fun ⟨d, h⟩ => ⟨d, (ih _).1 h⟩, fun ⟨d, h⟩ => ⟨d, (ih _).2 h⟩⟩

theorem Term.eval_agree (M : Structure S) (t : Term S) :
    ∀ (k : Nat) (env env' : Nat → M.D), t.varsBelow k = true →
      (∀ i, i < k → env i = env' i) → t.eval M env = t.eval M env' := by
  induction t with
  | var n =>
    intro k env env' h hag
    simp only [Term.varsBelow, decide_eq_true_eq] at h
    exact hag n h
  | dflt => intro _ _ _ _ _; rfl
  | app f a ih =>
    intro k env env' h hag
    have hall := allFin_spec h
    exact congrArg (M.fn f) (funext fun i => ih i k env env' (hall i) hag)

theorem Formula.eval_agree (M : Structure S) (φ : Formula S) :
    ∀ (k : Nat) (env env' : Nat → M.D), φ.varsBelow k = true →
      (∀ i, i < k → env i = env' i) → (φ.eval M env ↔ φ.eval M env') := by
  induction φ with
  | falsum => intro _ _ _ _ _; exact Iff.rfl
  | eq t u =>
    intro k env env' h hag
    simp only [Formula.varsBelow, Bool.and_eq_true] at h
    show t.eval M env = u.eval M env ↔ t.eval M env' = u.eval M env'
    rw [Term.eval_agree M t k env env' h.1 hag, Term.eval_agree M u k env env' h.2 hag]
  | rel r a =>
    intro k env env' h hag
    have hall := allFin_spec h
    show M.rel r _ ↔ M.rel r _
    rw [show (fun i => (a i).eval M env) = (fun i => (a i).eval M env') from
      funext fun i => Term.eval_agree M (a i) k env env' (hall i) hag]
  | imp φ ψ ihφ ihψ =>
    intro k env env' h hag
    simp only [Formula.varsBelow, Bool.and_eq_true] at h
    have a := ihφ k env env' h.1 hag
    have b := ihψ k env env' h.2 hag
    exact ⟨fun x y => b.1 (x (a.2 y)), fun x y => b.2 (x (a.1 y))⟩
  | and φ ψ ihφ ihψ =>
    intro k env env' h hag
    simp only [Formula.varsBelow, Bool.and_eq_true] at h
    have a := ihφ k env env' h.1 hag
    have b := ihψ k env env' h.2 hag
    exact ⟨fun ⟨x, y⟩ => ⟨a.1 x, b.1 y⟩, fun ⟨x, y⟩ => ⟨a.2 x, b.2 y⟩⟩
  | or φ ψ ihφ ihψ =>
    intro k env env' h hag
    simp only [Formula.varsBelow, Bool.and_eq_true] at h
    have a := ihφ k env env' h.1 hag
    have b := ihψ k env env' h.2 hag
    exact ⟨fun x => x.elim (fun y => Or.inl (a.1 y)) (fun y => Or.inr (b.1 y)),
           fun x => x.elim (fun y => Or.inl (a.2 y)) (fun y => Or.inr (b.2 y))⟩
  | all φ ih =>
    intro k env env' h hag
    have hag' : ∀ d, ∀ i, i < k + 1 → cons d env i = cons d env' i := by
      intro d i hi
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    exact ⟨fun x d => (ih (k + 1) _ _ h (hag' d)).1 (x d),
           fun x d => (ih (k + 1) _ _ h (hag' d)).2 (x d)⟩
  | ex φ ih =>
    intro k env env' h hag
    have hag' : ∀ d, ∀ i, i < k + 1 → cons d env i = cons d env' i := by
      intro d i hi
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    exact ⟨fun ⟨d, x⟩ => ⟨d, (ih (k + 1) _ _ h (hag' d)).1 x⟩,
           fun ⟨d, x⟩ => ⟨d, (ih (k + 1) _ _ h (hag' d)).2 x⟩⟩

theorem closed_sat_iff (M : Structure S) (φ : Formula S) (hc : φ.closed = true) (env : Nat → M.D) :
    M.Sat φ ↔ φ.eval M env :=
  ⟨fun h => h env, fun h env' =>
    (Formula.eval_agree M φ 0 env env' hc (fun _ hi => absurd hi (Nat.not_lt_zero _))).1 h⟩

/-- Sonlu yapıda, kapalı bir formül için hesap ile doğruluk örtüşür. -/
theorem finite_sat_iff : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    φ.closed = true → (M.toStructure.Sat φ ↔ M.evalB (fun _ => 0) φ = true) :=
  fun M φ hc => (closed_sat_iff M.toStructure φ hc (fun _ => 0)).trans (evalB_iff M φ _).symm

/-- Sonlu model denetimi sağlamdır. -/
theorem finite_models_sound : ∀ {S : Signature} (M : FinStructure S) (T : Theory S),
    T.admissible M.toStructure → M.checkTheory T = true → T.Models M.toStructure := by
  intro S M T hadm h
  refine ⟨hadm, fun ψ hψ => ?_⟩
  have := List.all_eq_true.1 h ψ hψ
  simp only [Bool.and_eq_true] at this
  exact (finite_sat_iff M ψ this.1).2 this.2

/-- Sonlu çürütme sağlamdır. -/
theorem finite_refutes_sound : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    M.refutes φ = true → ¬ M.toStructure.Sat φ := by
  intro S M φ h hs
  simp only [FinStructure.refutes, Bool.and_eq_true, Bool.not_eq_true'] at h
  have := (finite_sat_iff M φ h.1).1 hs
  rw [h.2] at this
  exact Bool.false_ne_true this

theorem reinterpB_toStructure (M : FinStructure S) (g h) :
    (M.reinterpB g h).toStructure = M.toStructure.reinterp g (fun r v => h r v = true) := by
  unfold FinStructure.reinterpB FinStructure.toStructure Structure.reinterp
  congr 1
  funext r v
  by_cases hr : S.relRole r = .normatif
  · simp [hr]
  · simp [hr]

/-- Veriden politika hükmü: kalkülüs ispatı, öncülleri sağlayan sonlu bir dünya ve
yalnızca normatif sembolleri değiştirilmiş, sonucu çürüten sonlu bir alternatif. -/
theorem verdict_of_data : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S) (W : FinStructure S) (g h),
    (∀ M : Structure S, T.admissible M) →
    check T.axioms φ p = true → W.checkTheory T = true → (W.reinterpB g h).refutes φ = true →
    Nonempty (PolicyVerdict T φ) := by
  intro S _ _ T φ p W g h hadm hp hW hr
  exact ⟨{ entails := calculus_sound T φ p hp
           world := W.toStructure
           world_ok := finite_models_sound W T (hadm _) hW
           g := g
           h := fun r v => h r v = true
           alt_adm := hadm _
           fails := by
             have := finite_refutes_sound _ φ hr
             rwa [reinterpB_toStructure] at this }⟩

/-- Veriden metafor sertifikası: kalkülüs ispatı ve sonlu karşı örnek. -/
theorem refutation_of_data : ∀ {S₁ S₂ : Signature} [DecidableEq S₁.Fn] [DecidableEq S₁.Rel]
    (A : Theory S₁) (B : Theory S₂) (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool)
    (gl : SigMorph S₁ S₂) (φ : Formula S₁) (p : Proof S₁) (C : FinStructure S₂),
    B.admissible C.toStructure →
    check A.axioms φ p = true → φ.onlySyms pf pr = true → C.checkTheory B = true →
    C.refutes (gl.trF φ) = true → Nonempty (Refutation A B pf pr gl) := by
  intro S₁ S₂ _ _ A B pf pr gl φ p C hadm hp ho hC hr
  exact ⟨{ φ := φ, thm := calculus_sound A φ p hp, only := ho, cex := C.toStructure,
           cex_ok := finite_models_sound C B hadm hC, fails := finite_refutes_sound C _ hr }⟩

end Proofs
