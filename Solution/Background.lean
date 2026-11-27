import Hakem
import Solution.Calculus

/-! Güvenilmeyen ispatlar: izomorfizmle değişmezlik ve arka plan. -/

namespace Proofs

variable {S : Signature}

theorem Iso.inj {M N : Structure S} (e : M.Iso N) {x y : M.D} (h : e.to x = e.to y) : x = y := by
  rw [← e.left x, ← e.left y, h]

theorem Term.eval_iso {M N : Structure S} (e : M.Iso N) (env : Nat → M.D) (t : Term S) :
    e.to (t.eval M env) = t.eval N (fun n => e.to (env n)) := by
  induction t with
  | var n => rfl
  | dflt => exact e.dflt
  | app f a ih =>
    show e.to (M.fn f _) = N.fn f _
    rw [e.fn]
    exact congrArg (N.fn f) (funext ih)

theorem cons_iso {M N : Structure S} (e : M.Iso N) (d : M.D) (env : Nat → M.D) :
    (fun n => e.to (cons d env n)) = cons (e.to d) (fun n => e.to (env n)) := by
  funext n; cases n <;> rfl

theorem Formula.eval_iso {M N : Structure S} (e : M.Iso N) (φ : Formula S) :
    ∀ env : Nat → M.D, φ.eval M env ↔ φ.eval N (fun n => e.to (env n)) := by
  induction φ with
  | falsum => intro _; exact Iff.rfl
  | eq t u =>
    intro env
    show t.eval M env = u.eval M env ↔ t.eval N _ = u.eval N _
    rw [← Term.eval_iso e env t, ← Term.eval_iso e env u]
    exact ⟨congrArg e.to, Iso.inj e⟩
  | rel r a =>
    intro env
    show M.rel r _ ↔ N.rel r _
    rw [e.rel]
    rw [show (fun i => e.to ((a i).eval M env)) = (fun i => (a i).eval N _) from
      funext fun i => Term.eval_iso e env (a i)]
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
    constructor
    · intro h d'
      have := (ih (cons (e.inv d') env)).1 (h _)
      rwa [cons_iso, e.right] at this
    · intro h d
      apply (ih (cons d env)).2
      rw [cons_iso]
      exact h _
  | ex φ ih =>
    intro env
    constructor
    · rintro ⟨d, hd⟩
      have := (ih (cons d env)).1 hd
      rw [cons_iso] at this
      exact ⟨_, this⟩
    · rintro ⟨d', hd'⟩
      refine ⟨e.inv d', (ih _).2 ?_⟩
      rw [cons_iso, e.right]
      exact hd'

/-- İzomorf yapılar aynı önermeleri doğrular. -/
theorem iso_sat : ∀ {S : Signature} {M N : Structure S}, M.Iso N → ∀ φ : Formula S,
    M.Sat φ ↔ N.Sat φ := by
  intro S M N e φ
  constructor
  · intro h env'
    have := (Formula.eval_iso e φ (fun n => e.inv (env' n))).1 (h _)
    simp only [e.right] at this
    exact this
  · intro h env
    exact (Formula.eval_iso e φ env).2 (h _)

/-- Arka plan sağlamlığı: standart yapıda doğru olan her önerme, kabul edilebilir her
modelde (çevirisiyle) doğrudur. -/
theorem background_sound : ∀ {S₀ S : Signature} (ι : SigMorph S₀ S) (B : Structure S₀)
    (M : Structure S), Nonempty ((ι.reduct M).Iso B) → ∀ ψ : Formula S₀, B.Sat ψ →
    M.Sat (ι.trF ψ) := by
  intro S₀ S ι B M ⟨e⟩ ψ hB
  exact (satisfaction ι M ψ).2 ((iso_sat e ψ).2 hB)

/-- Arka planlı kalkülüs: ispat, kuramın aksiyomlarına ek olarak standart yapıda doğru
önermeleri (çevirileriyle) hipotez olarak kullanabilir. -/
theorem calculus_sound_bg : ∀ {S₀ S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (ι : SigMorph S₀ S) (B : Structure S₀) (bg : List (Formula S₀))
    (φ : Formula S) (p : Proof S),
    (∀ M, T.admissible M → Nonempty ((ι.reduct M).Iso B)) → (∀ ψ ∈ bg, B.Sat ψ) →
    check (T.axioms ++ bg.map ι.trF) φ p = true → T.Entails φ := by
  intro S₀ S _ _ T ι B bg φ p hadm hbg h M hM env
  unfold check at h
  split at h
  · rename_i ψ hp
    have e := Formula.beq_sound _ _ h
    subst e
    refine infer_sound p _ _ hp M env (fun χ hχ => ?_)
    rcases List.mem_append.1 hχ with hax | hb
    · exact hM.2 χ hax env
    · obtain ⟨ψ₀, h₀, rfl⟩ := List.mem_map.1 hb
      exact background_sound ι B M (hadm M hM.1) ψ₀ (hbg ψ₀ h₀) env
  · simp at h


/-! ## Taşıma: her kabul edilebilir model, standart taşıyıcılı bir modele izomorftur -/

/-- `M`'yi standart taşıyıcıya taşı. -/
def transport {S₀ : Signature} {ι : SigMorph S₀ S} {B : Structure S₀} (M : Structure S)
    (e : (ι.reduct M).Iso B) : Structure S where
  D    := B.D
  dflt := B.dflt
  fn   := fun f v => e.to (M.fn f (fun i => e.inv (v i)))
  rel  := fun r v => M.rel r (fun i => e.inv (v i))

def transportIso {S₀ : Signature} {ι : SigMorph S₀ S} {B : Structure S₀} (M : Structure S)
    (e : (ι.reduct M).Iso B) : M.Iso (transport M e) where
  to    := e.to
  inv   := e.inv
  left  := e.left
  right := e.right
  dflt  := e.dflt
  fn    := fun f v =>
    congrArg e.to (congrArg (M.fn f) (funext fun i => (e.left (v i)).symm))
  rel   := fun r v =>
    iff_of_eq (congrArg (M.rel r) (funext fun i => (e.left (v i)).symm))

theorem inv_argEnv {S₀ : Signature} {ι : SigMorph S₀ S} {B : Structure S₀} (M : Structure S)
    (e : (ι.reduct M).Iso B) {k : Nat} (v : Fin k → B.D) :
    (fun n => e.inv (argEnv (transport M e) v n)) = argEnv M (fun i => e.inv (v i)) := by
  funext n
  unfold argEnv
  by_cases hn : n < k
  · simp only [hn, ↓reduceDIte]
  · simp only [hn, ↓reduceDIte]
    show e.inv B.dflt = M.dflt
    rw [← e.dflt]
    exact e.left _

theorem transport_std_fn {S₀ : Signature} {ι : SigMorph S₀ S} {B : Structure S₀} (M : Structure S)
    (e : (ι.reduct M).Iso B) (f : S₀.Fn) (v : Fin (S₀.fnArity f) → B.D) :
    (ι.reduct (transport M e)).fn f v = B.fn f v := by
  show (ι.fnMap f).eval (transport M e) (argEnv (transport M e) v) = B.fn f v
  have hr : (fun n => e.to (e.inv (argEnv (transport M e) v n))) = argEnv (transport M e) v :=
    funext fun n => e.right _
  have h1 := Term.eval_iso (transportIso M e) (fun n => e.inv (argEnv (transport M e) v n)) (ι.fnMap f)
  have h3 := e.fn f (fun i => e.inv (v i))
  exact ((congrArg (fun env => (ι.fnMap f).eval (transport M e) env) hr.symm).trans h1.symm).trans
    ((congrArg (fun env => e.to ((ι.fnMap f).eval M env)) (inv_argEnv M e v)).trans
      (h3.trans (congrArg (B.fn f) (funext fun i => e.right (v i)))))

theorem transport_std_rel {S₀ : Signature} {ι : SigMorph S₀ S} {B : Structure S₀} (M : Structure S)
    (e : (ι.reduct M).Iso B) (r : S₀.Rel) (v : Fin (S₀.relArity r) → B.D) :
    (ι.reduct (transport M e)).rel r v ↔ B.rel r v := by
  show (ι.relMap r).eval (transport M e) (argEnv (transport M e) v) ↔ B.rel r v
  have hr : (fun n => e.to (e.inv (argEnv (transport M e) v n))) = argEnv (transport M e) v :=
    funext fun n => e.right _
  have h1 := Formula.eval_iso (transportIso M e) (ι.relMap r)
    (fun n => e.inv (argEnv (transport M e) v n))
  have h3 := e.rel r (fun i => e.inv (v i))
  have h4 : (fun i => e.to (e.inv (v i))) = v := funext fun i => e.right (v i)
  exact ((iff_of_eq (congrArg (fun env => (ι.relMap r).eval (transport M e) env) hr.symm)).trans
    h1.symm).trans ((iff_of_eq (congrArg (fun env => (ι.relMap r).eval M env) (inv_argEnv M e v))).trans
      (h3.trans (iff_of_eq (congrArg (B.rel r) h4))))

/-- Standart taşıyıcıda akıl yürütme. Arka planlı bir kuramın gerektirdiğini göstermek
için, taşıyıcısı standart olan ve standart sembolleri standart yorumlanan modellere
bakmak yeterlidir. Böylece sıradan Lean matematiği (ör. `omega`) kullanılabilir. -/
theorem entails_of_std : ∀ {S₀ S : Signature} (T : Theory S) (ι : SigMorph S₀ S)
    (B : Structure S₀), (∀ M, T.admissible M → Nonempty ((ι.reduct M).Iso B)) →
    ∀ φ : Formula S,
    (∀ (fn : (f : S.Fn) → (Fin (S.fnArity f) → B.D) → B.D)
       (rel : (r : S.Rel) → (Fin (S.relArity r) → B.D) → Prop),
       (∀ f v, (ι.reduct (⟨B.D, B.dflt, fn, rel⟩ : Structure S)).fn f v = B.fn f v) →
       (∀ r v, (ι.reduct (⟨B.D, B.dflt, fn, rel⟩ : Structure S)).rel r v ↔ B.rel r v) →
       (∀ ψ ∈ T.axioms, (⟨B.D, B.dflt, fn, rel⟩ : Structure S).Sat ψ) →
       (⟨B.D, B.dflt, fn, rel⟩ : Structure S).Sat φ) →
    T.Entails φ := by
  intro S₀ S T ι B hadm φ h M hM
  obtain ⟨e⟩ := hadm M hM.1
  have hT := h (transport M e).fn (transport M e).rel (transport_std_fn M e) (transport_std_rel M e)
    (fun ψ hψ => (iso_sat (transportIso M e) ψ).1 (hM.2 ψ hψ))
  exact (iso_sat (transportIso M e) φ).2 hT

end Proofs
