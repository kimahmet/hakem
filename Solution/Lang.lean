import Hakem
import Solution.Calculus
import Solution.Finite

/-! Untrusted proofs: soundness of the Hakem language checker. -/

namespace Proofs

/-! ## Cut: earlier lemmas as hypotheses -/

theorem calculus_sound_extra {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (extra : List (Formula S)) (hex : ∀ ψ ∈ extra, T.Entails ψ)
    (φ : Formula S) (p : Proof S) (h : check (T.axioms ++ extra) φ p = true) : T.Entails φ := by
  intro M hM env
  unfold check at h
  split at h
  · rename_i ψ hp
    have e := Formula.beq_sound _ _ h
    subst e
    refine infer_sound p _ _ hp M env (fun χ hχ => ?_)
    rcases List.mem_append.1 hχ with hax | hl
    · exact hM.2 χ hax env
    · exact hex χ hl M hM env
  · simp at h

/-- A good theory: all its lemmas follow from its axioms. -/
def _root_.Thy.Good (t : Thy) : Prop := ∀ ψ ∈ t.lems, t.theory.Entails ψ

theorem checkIn_sound (t : Thy) (ht : t.Good) (φ : Formula (mkSig t.decls)) (p : RProof)
    (h : checkIn t φ p = true) : t.theory.Entails φ := by
  unfold checkIn at h
  split at h
  · rename_i p' _
    exact calculus_sound_extra t.theory t.lems ht φ p' h
  · simp at h

theorem checkModel_sound (t : Thy) (m : RModel) (h : checkModel t m = true) :
    ∃ M : FinStructure (mkSig t.decls), t.theory.Models M.toStructure := by
  unfold checkModel at h
  split at h
  · rename_i M _
    exact ⟨M, finite_models_sound M t.theory trivial h⟩
  · simp at h

/-! ## Anchors: a formula only uses the symbols it mentions -/

theorem Term.onlySyms_of_mentions {S : Signature} [DecidableEq S.Fn] (P : S.Fn → Bool) (t : Term S) :
    (∀ f, t.mentionsFn f = true → P f = true) → t.onlySyms P = true := by
  induction t with
  | var n => intro _; rfl
  | dflt => intro _; rfl
  | app g a ih =>
    intro H
    simp only [Term.onlySyms, Bool.and_eq_true]
    refine ⟨H g (by simp [Term.mentionsFn]), allFin_iff.2 (fun i => ih i (fun f hf => H f ?_))⟩
    simp only [Term.mentionsFn, Bool.or_eq_true]
    exact Or.inr (anyFin_iff.2 ⟨i, hf⟩)

theorem Formula.onlySyms_of_mentions {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (P : S.Fn → Bool) (Q : S.Rel → Bool) (φ : Formula S) :
    (∀ f, φ.mentionsFn f = true → P f = true) → (∀ r, φ.mentionsRel r = true → Q r = true) →
      φ.onlySyms P Q = true := by
  induction φ with
  | falsum => intro _ _; rfl
  | eq t u =>
    intro HP _
    simp only [Formula.onlySyms, Bool.and_eq_true]
    exact ⟨Term.onlySyms_of_mentions P t (fun f hf => HP f (by simp [Formula.mentionsFn, hf])),
           Term.onlySyms_of_mentions P u (fun f hf => HP f (by simp [Formula.mentionsFn, hf]))⟩
  | rel r a =>
    intro HP HQ
    simp only [Formula.onlySyms, Bool.and_eq_true]
    refine ⟨HQ r (by simp [Formula.mentionsRel]), allFin_iff.2 (fun i =>
      Term.onlySyms_of_mentions P (a i) (fun f hf => HP f ?_))⟩
    simp only [Formula.mentionsFn]
    exact anyFin_iff.2 ⟨i, hf⟩
  | imp φ ψ ihφ ihψ =>
    intro HP HQ
    simp only [Formula.onlySyms, Bool.and_eq_true]
    exact ⟨ihφ (fun f hf => HP f (by simp [Formula.mentionsFn, hf])) (fun r hr => HQ r (by simp [Formula.mentionsRel, hr])),
           ihψ (fun f hf => HP f (by simp [Formula.mentionsFn, hf])) (fun r hr => HQ r (by simp [Formula.mentionsRel, hr]))⟩
  | and φ ψ ihφ ihψ =>
    intro HP HQ
    simp only [Formula.onlySyms, Bool.and_eq_true]
    exact ⟨ihφ (fun f hf => HP f (by simp [Formula.mentionsFn, hf])) (fun r hr => HQ r (by simp [Formula.mentionsRel, hr])),
           ihψ (fun f hf => HP f (by simp [Formula.mentionsFn, hf])) (fun r hr => HQ r (by simp [Formula.mentionsRel, hr]))⟩
  | or φ ψ ihφ ihψ =>
    intro HP HQ
    simp only [Formula.onlySyms, Bool.and_eq_true]
    exact ⟨ihφ (fun f hf => HP f (by simp [Formula.mentionsFn, hf])) (fun r hr => HQ r (by simp [Formula.mentionsRel, hr])),
           ihψ (fun f hf => HP f (by simp [Formula.mentionsFn, hf])) (fun r hr => HQ r (by simp [Formula.mentionsRel, hr]))⟩
  | all φ ih =>
    intro HP HQ
    exact ih (fun f hf => HP f hf) (fun r hr => HQ r hr)
  | ex φ ih =>
    intro HP HQ
    exact ih (fun f hf => HP f hf) (fun r hr => HQ r hr)

/-! ## A single claim -/

theorem zip_cover {α β : Type} : ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
    ∀ x ∈ l1, ∃ y, (x, y) ∈ l1.zip l2
  | [], _, _, x, hx => absurd hx (List.not_mem_nil)
  | a :: as, [], h, _, _ => by simp at h
  | a :: as, b :: bs, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact ⟨b, by simp⟩
    · obtain ⟨y, hy⟩ := zip_cover as bs (by simpa using h) x hx'
      exact ⟨y, by simp [hy]⟩


theorem analogy_sound (n : String) (ta tb : Thy) (htb : tb.Good) (σ : SigMorph (mkSig ta.decls) (mkSig tb.decls))
    (md : RModel) (obs : List (String × RProof))
    (h : checkClaim (.analogy n ta tb σ md obs) = true) : ∃ a : Analogy ta.theory tb.theory, a.σ = σ := by
  simp only [checkClaim, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨_, hlen⟩, hall⟩, hmod⟩ := h
  obtain ⟨M, hM⟩ := checkModel_sound tb md hmod
  refine ⟨{ σ := σ, adm := fun _ _ => trivial, preserves := ?_, model := M.toStructure,
            model_ok := hM }, rfl⟩
  intro φ hφ
  obtain ⟨y, hy⟩ := zip_cover ta.axs obs hlen.symm φ hφ
  exact checkIn_sound tb htb _ _ (hall _ hy)

theorem refute_sound (n : String) (ta tb : Thy) (hta : ta.Good) (σ : SigMorph (mkSig ta.decls) (mkSig tb.decls))
    (φ : Formula (mkSig ta.decls)) (p : RProof) (md : RModel)
    (h : checkClaim (.refute n ta tb σ φ p md) = true) :
    Nonempty (Refutation ta.theory tb.theory (fun f => φ.mentionsFn f) (fun r => φ.mentionsRel r) σ) := by
  simp only [checkClaim, Bool.and_eq_true] at h
  obtain ⟨hp, hm⟩ := h
  split at hm
  · rename_i M _
    simp only [Bool.and_eq_true] at hm
    exact ⟨{ φ := φ, thm := checkIn_sound ta hta φ p hp,
             only := Formula.onlySyms_of_mentions _ _ φ (fun _ h => h) (fun _ h => h),
             cex := M.toStructure, cex_ok := finite_models_sound M tb.theory trivial hm.1,
             fails := finite_refutes_sound M _ hm.2 }⟩
  · simp at hm

theorem verdict_sound (n : String) (t : Thy) (ht : t.Good) (φ : Formula (mkSig t.decls)) (p : RProof)
    (w alt : RModel) (h : checkClaim (.verdict n t φ p w alt) = true) :
    Nonempty (PolicyVerdict t.theory φ) := by
  simp only [checkClaim, Bool.and_eq_true] at h
  obtain ⟨hp, hm⟩ := h
  split at hm
  · rename_i W _
    simp only [Bool.and_eq_true] at hm
    exact ⟨{ entails := checkIn_sound t ht φ p hp
             world := W.toStructure
             world_ok := finite_models_sound W t.theory trivial hm.1
             g := altFn t.decls W alt
             h := fun r v => altRel t.decls W alt r v = true
             alt_adm := trivial
             fails := by
               have := finite_refutes_sound _ φ hm.2
               rwa [reinterpB_toStructure] at this }⟩
  · simp at hm

/-! ## Documents -/

def _root_.Env.Good (env : Env) : Prop := ∀ t ∈ env.thys, t.Good

theorem findThy_mem : ∀ (n : String) (l : List Thy) (t : Thy), findThy n l = some t → t ∈ l
  | _, [], _, h => by simp [findThy] at h
  | n, x :: xs, t, h => by
    unfold findThy at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (findThy_mem n xs t h)

theorem step_sound (env : Env) (hg : env.Good) (e : REntry) (env' : Env) (cs : List Claim)
    (h : env.step e = some (env', cs)) (hc : ∀ c ∈ cs, checkClaim c = true) :
    env'.Good ∧ ∀ c ∈ cs, c.Holds := by
  cases e with
  | sig n fs rs =>
    simp only [Env.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hg, fun _ h => absurd h List.not_mem_nil⟩
  | morph n s1 s2 fs rs =>
    simp only [Env.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hg, fun _ h => absurd h List.not_mem_nil⟩
  | theory n s axs =>
    unfold Env.step at h
    simp only [bind, Option.bind, pure] at h
    (try dsimp only at h); split at h
    · contradiction
    · (try dsimp only at h); split at h
      · contradiction
      · (try dsimp only at h); simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨fun t ht => ?_, fun _ h => absurd h List.not_mem_nil⟩
        rcases List.mem_cons.1 ht with rfl | ht'
        · intro ψ hψ; exact absurd hψ List.not_mem_nil
        · exact hg t ht'
  | lemma n tn a p =>
    unfold Env.step at h
    simp only [bind, Option.bind, pure] at h
    (try dsimp only at h); split at h
    · contradiction
    · rename_i t htf
      (try dsimp only at h); split at h
      · contradiction
      · rename_i φ _
        (try dsimp only at h); simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ht := hg t (findThy_mem _ _ _ htf)
        have hφ : t.theory.Entails φ := checkIn_sound t ht φ p (hc _ (List.mem_singleton.2 rfl))
        refine ⟨fun t' ht' => ?_, fun c hcm => ?_⟩
        · rcases List.mem_cons.1 ht' with rfl | ht''
          · intro ψ hψ
            rcases List.mem_append.1 hψ with h1 | h2
            · exact ht ψ h1
            · simp only [List.mem_singleton] at h2; exact h2 ▸ hφ
          · exact hg t' (List.mem_filter.1 ht'').1
        · simp only [List.mem_singleton] at hcm; subst hcm; exact hφ
  | analogy n a b m md obs =>
    unfold Env.step at h
    simp only [bind, Option.bind, pure] at h
    (try dsimp only at h); split at h
    · contradiction
    · rename_i ta hta
      (try dsimp only at h); split at h
      · contradiction
      · rename_i tb htb
        (try dsimp only at h); split at h
        · contradiction
        · rename_i rm _
          (try dsimp only at h); split at h
          · (try dsimp only at h); split at h
            · contradiction
            · rename_i σ _
              (try dsimp only at h); simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨hg, fun c hcm => ?_⟩
              simp only [List.mem_singleton] at hcm; subst hcm
              exact analogy_sound n ta tb (hg tb (findThy_mem _ _ _ htb)) σ md obs
                (hc _ (List.mem_singleton.2 rfl))
          · contradiction
  | refute n a b m f p md =>
    unfold Env.step at h
    simp only [bind, Option.bind, pure] at h
    (try dsimp only at h); split at h
    · contradiction
    · rename_i ta hta
      (try dsimp only at h); split at h
      · contradiction
      · rename_i tb htb
        (try dsimp only at h); split at h
        · contradiction
        · rename_i rm _
          (try dsimp only at h); split at h
          · (try dsimp only at h); split at h
            · contradiction
            · rename_i σ _
              (try dsimp only at h); split at h
              · contradiction
              · rename_i φ _
                (try dsimp only at h); simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨hg, fun c hcm => ?_⟩
                simp only [List.mem_singleton] at hcm; subst hcm
                exact refute_sound n ta tb (hg ta (findThy_mem _ _ _ hta)) σ φ p md
                  (hc _ (List.mem_singleton.2 rfl))
          · contradiction
  | verdict n tn f p w alt =>
    unfold Env.step at h
    simp only [bind, Option.bind, pure] at h
    (try dsimp only at h); split at h
    · contradiction
    · rename_i t htf
      (try dsimp only at h); split at h
      · contradiction
      · rename_i φ _
        (try dsimp only at h); simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hg, fun c hcm => ?_⟩
        simp only [List.mem_singleton] at hcm; subst hcm
        exact verdict_sound n t (hg t (findThy_mem _ _ _ htf)) φ p w alt
          (hc _ (List.mem_singleton.2 rfl))

theorem elabEntries_sound : ∀ (es : List REntry) (env : Env) (cs : List Claim), env.Good →
    elabEntries env es = some cs → (∀ c ∈ cs, checkClaim c = true) → ∀ c ∈ cs, c.Holds
  | [], _, cs, _, h, _ => by
    simp only [elabEntries, Option.some.injEq] at h; subst h
    intro c hc; exact absurd hc List.not_mem_nil
  | e :: es, env, cs, hg, h, hc => by
    unfold elabEntries at h
    simp only [bind, Option.bind, pure] at h
    (try dsimp only at h); split at h
    · contradiction
    rename_i x hstep
    obtain ⟨env', cs1⟩ := x
    (try dsimp only at h); split at h
    · contradiction
    rename_i cs2 hrest
    (try dsimp only at h); simp only [Option.some.injEq] at h
    subst h
    have hc1 : ∀ c ∈ cs1, checkClaim c = true := fun c h => hc c (List.mem_append_left _ h)
    have hc2 : ∀ c ∈ cs2, checkClaim c = true := fun c h => hc c (List.mem_append_right _ h)
    obtain ⟨hg', h1⟩ := step_sound env hg e env' cs1 hstep hc1
    have h2 := elabEntries_sound es env' cs2 hg' hrest hc2
    intro c hcm
    rcases List.mem_append.1 hcm with h | h
    · exact h1 c h
    · exact h2 c h

/-- **Soundness of the language (tree)**: every claim of an accepted document tree holds. -/
theorem checkTree_sound : ∀ es : List SExp, checkTree es = true → Doc.HoldsTree es := by
  intro es h
  unfold checkTree at h
  split at h
  · rename_i cs hcs
    refine ⟨cs, hcs, ?_⟩
    unfold Doc.claimsTree at hcs
    simp only [Option.bind_eq_some_iff] at hcs
    obtain ⟨entries, _, hel⟩ := hcs
    exact elabEntries_sound entries ⟨[], [], []⟩ cs (fun _ h => absurd h List.not_mem_nil) hel
      (fun c hc => List.all_eq_true.1 h c hc)
  · simp at h

/-- **Soundness of the language (text)**: every claim of an accepted document holds. -/
theorem checkDoc_sound : ∀ s : String, checkDoc s = true → Doc.Holds s := by
  intro s h
  unfold checkDoc at h
  split at h
  · rename_i es hes
    exact ⟨es, hes, checkTree_sound es h⟩
  · simp at h

end Proofs
