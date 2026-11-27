import Hakem
import CorpusTrees

/-!
# Claims (trusted text)

There are no proofs here (`sorry`); proofs come from the untrusted side (`Solution`). The
judge checks that the theorems of the same name prove the same statement as terms, that the
meaning base is identical, that only permitted axioms are used, and that the independent
kernel accepts the export. READING lines are not checked.

## I. General laws
They hold for every vocabulary, theory, analogy and policy argument.

## II. Language
They hold for every document written in the Hakem language: the checker is sound.

## III. Corpus
Documents written in the language. Each is checked by kernel computation alone.
-/

/-! ## I. General laws -/

/-- READING: Satisfaction condition. The translation of a formula holds in a target world
if and only if the formula holds in that world read in the source language. -/
theorem satisfaction : ∀ {S₁ S₂ : Signature} (σ : SigMorph S₁ S₂) (M : Structure S₂)
    (φ : Formula S₁), M.Sat (σ.trF φ) ↔ (σ.reduct M).Sat φ := sorry

/-- READING: Transfer. The target theory entails the translation of every formula the
source theory entails. -/
theorem transfer : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} (a : Analogy A B)
    {φ : Formula S₁}, A.Entails φ → B.Entails (a.σ.trF φ) := sorry

/-- READING: If an analogy exists, the source theory has a model (transfer is not vacuous). -/
theorem source_consistent : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂},
    Analogy A B → ∃ M, A.Models M := sorry

/-- READING: Composition. Analogies chain; the glossary of the chain is the composition of glossaries. -/
theorem compose_exists : ∀ {S₁ S₂ S₃ : Signature} {A : Theory S₁} {B : Theory S₂}
    {C : Theory S₃} (a : Analogy A B) (b : Analogy B C),
    ∃ c : Analogy A C, c.σ = a.σ.comp b.σ := sorry

/-- READING: Metaphor. A counterexample excludes every analogy whose anchors agree with the
proposed glossary. -/
theorem refutation_sound : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂}
    {pf : S₁.Fn → Bool} {pr : S₁.Rel → Bool} {gl : SigMorph S₁ S₂},
    Refutation A B pf pr gl → ∀ a : Analogy A B, a.σ.AgreeOn pf pr gl → False := sorry

/-- READING: Hume's law. From a theory whose premises are all descriptive (contain no
normative symbol), no policy verdict can be built. -/
theorem hume_law : ∀ {S : Signature} {T : Theory S} {φ : Formula S},
    (∀ ψ ∈ T.axioms, ψ.descriptive = true) → ¬ Nonempty (PolicyVerdict T φ) := sorry

/-- READING: In every policy verdict the dispute is normative. The alternative world agrees
with the actual one on every descriptive symbol; the conclusion holds in one and fails in the other. -/
theorem verdict_same_facts : ∀ {S : Signature} {T : Theory S} {φ : Formula S}
    (v : PolicyVerdict T φ),
    (∀ f, S.fnRole f ≠ .normative → (v.world.reinterp v.g v.h).fn f = v.world.fn f) ∧
    (∀ r, S.relRole r ≠ .normative → (v.world.reinterp v.g v.h).rel r = v.world.rel r) ∧
    v.world.Sat φ ∧ ¬ (v.world.reinterp v.g v.h).Sat φ := sorry

/-! ## I-b. Certificates as data: calculus and finite models -/

/-- READING: Soundness of the calculus. A proof datum that passes the check shows that the
theory entails the formula. -/
theorem calculus_sound : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S), check T.axioms φ p = true → T.Entails φ := sorry

/-- READING: In a finite structure, computation agrees with truth for a closed formula. -/
theorem finite_sat_iff : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    φ.closed = true → (M.toStructure.Sat φ ↔ M.evalB (fun _ => 0) φ = true) := sorry

/-- READING: Finite model checking is sound. -/
theorem finite_models_sound : ∀ {S : Signature} (M : FinStructure S) (T : Theory S),
    T.admissible M.toStructure → M.checkTheory T = true → T.Models M.toStructure := sorry

/-- READING: Finite refutation is sound. -/
theorem finite_refutes_sound : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    M.refutes φ = true → ¬ M.toStructure.Sat φ := sorry

/-- READING: Metaphor certificate from data. A proof datum in the source and a finite
counterexample in the target suffice for a metaphor certificate. -/
theorem refutation_of_data : ∀ {S₁ S₂ : Signature} [DecidableEq S₁.Fn] [DecidableEq S₁.Rel]
    (A : Theory S₁) (B : Theory S₂) (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool)
    (gl : SigMorph S₁ S₂) (φ : Formula S₁) (p : Proof S₁) (C : FinStructure S₂),
    B.admissible C.toStructure →
    check A.axioms φ p = true → φ.onlySyms pf pr = true → C.checkTheory B = true →
    C.refutes (gl.trF φ) = true → Nonempty (Refutation A B pf pr gl) := sorry

/-- READING: Policy verdict from data. A proof datum, a finite world satisfying the premises,
and an alternative that changes only normative symbols and refutes the conclusion suffice. -/
theorem verdict_of_data : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S) (W : FinStructure S) (g h),
    (∀ M : Structure S, T.admissible M) →
    check T.axioms φ p = true → W.checkTheory T = true → (W.reinterpB g h).refutes φ = true →
    Nonempty (PolicyVerdict T φ) := sorry

/-- READING: Isomorphic structures satisfy the same formulas. -/
theorem iso_sat : ∀ {S : Signature} {M N : Structure S}, M.Iso N → ∀ φ : Formula S,
    M.Sat φ ↔ N.Sat φ := sorry

/-- READING: Background soundness. Every formula true in the standard structure holds
(translated) in every model whose standard part is isomorphic to it. -/
theorem background_sound : ∀ {S₀ S : Signature} (ι : SigMorph S₀ S) (B : Structure S₀)
    (M : Structure S), Nonempty ((ι.reduct M).Iso B) → ∀ ψ : Formula S₀, B.Sat ψ →
    M.Sat (ι.trF ψ) := sorry

/-- READING: Calculus with background. Besides the theory's axioms, a proof may use
(translations of) formulas true in the standard structure as hypotheses. -/
theorem calculus_sound_bg : ∀ {S₀ S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (ι : SigMorph S₀ S) (B : Structure S₀) (bg : List (Formula S₀))
    (φ : Formula S) (p : Proof S),
    (∀ M, T.admissible M → Nonempty ((ι.reduct M).Iso B)) → (∀ ψ ∈ bg, B.Sat ψ) →
    check (T.axioms ++ bg.map ι.trF) φ p = true → T.Entails φ := sorry

/-- READING: Reasoning on the standard carrier. To show what a theory with background
entails, it suffices to consider models on the standard carrier whose standard symbols
are interpreted standardly. -/
theorem entails_of_std : ∀ {S₀ S : Signature} (T : Theory S) (ι : SigMorph S₀ S)
    (B : Structure S₀), (∀ M, T.admissible M → Nonempty ((ι.reduct M).Iso B)) →
    ∀ φ : Formula S,
    (∀ (fn : (f : S.Fn) → (Fin (S.fnArity f) → B.D) → B.D)
       (rel : (r : S.Rel) → (Fin (S.relArity r) → B.D) → Prop),
       (∀ f v, (ι.reduct (⟨B.D, B.dflt, fn, rel⟩ : Structure S)).fn f v = B.fn f v) →
       (∀ r v, (ι.reduct (⟨B.D, B.dflt, fn, rel⟩ : Structure S)).rel r v ↔ B.rel r v) →
       (∀ ψ ∈ T.axioms, (⟨B.D, B.dflt, fn, rel⟩ : Structure S).Sat ψ) →
       (⟨B.D, B.dflt, fn, rel⟩ : Structure S).Sat φ) →
    T.Entails φ := sorry

/-! ## II. Language -/

/-- READING: Soundness of the language (tree). Every claim of an accepted document tree
holds. -/
theorem checkTree_sound : ∀ es : List SExp, checkTree es = true → Doc.HoldsTree es := sorry

/-- READING: Soundness of the language (text). Every claim of an accepted document text
holds. -/
theorem checkDoc_sound : ∀ s : String, checkDoc s = true → Doc.Holds s := sorry

/-! ## III. Corpus -/

/-- READING: every claim of the document `corpus/conservation.hkm` holds. -/
theorem conservation_holds : Doc.HoldsTree conservation_tree := sorry

/-- READING: every claim of the document `corpus/policy.hkm` holds. -/
theorem policy_holds : Doc.HoldsTree policy_tree := sorry
