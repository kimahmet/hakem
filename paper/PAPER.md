# Hakem: A Kernel-Checked Writing System for Machine Reasoning

### Automating the oversight of autonomous AI learning across disciplines

**kimahmet** (vision, direction) — implementation developed with the assistance of Claude (Anthropic)

*Draft, November 2026. Every technical claim marked ✓ below refers to a named Lean
theorem that receives formal acceptance in [`KARAR.md`](../KARAR.md). Read §6 for
exactly what that acceptance means.*

---

## Abstract

AI resembles the abacus more than it resembles writing. The abacus gave humanity a
shared capacity to compute and a shared way to check computations. Writing did
something different: it gave a shared, durable record, a way to send results to
people one never meets, and therefore cumulative progress. Mathematics has already
lived through the transition this paper is concerned with. Once proofs exceeded what
humans could check, the field adopted proof assistants such as Lean. Libraries such as
Mathlib then became a shared, machine-checked record that people and programs extend
together.

We present **Hakem** (Turkish: *referee*), an attempt to build the corresponding
"writing" for AI, beyond mathematics. Hakem is a small language in which models write
the following:

* theories with typed vocabularies, where each symbol is definitional, empirical or
  normative;
* glossaries between disciplines;
* claims: lemmas, analogies, metaphor refutations and policy verdicts;
* certificates: natural-deduction proofs and finite counter-models.

A checker accepts or rejects each document. Its soundness is proved once, in the
Lean 4 kernel, for every possible document. Accepted lemmas can be reused by later
proofs, which gives a first progress loop. A machine-readable verdict and a ledger
turn acceptance into a verifiable reward signal. This automates a part of the
oversight of autonomous learning that does not need a human in the loop.

The kernel encodes three principles. (1) A result proven in one discipline may be
carried to another only along a structure-preserving map. (2) A map that breaks
structure is a metaphor, and can be refuted by a concrete counter-model. (3) No policy
conclusion ("ought") follows from premises that contain no normative symbol (Hume's
law). These are general theorems, not conventions.

## 1. Vision

### 1.1 The abacus and writing

The abacus is shared computational capacity plus a shared verification mechanism.
Anyone can recompute and see whether the beads agree. Today's AI systems are abacus-like
in this sense: enormous shared capacity, and verification that is local and ad hoc.

What writing added is not more computation. It added three things:

* **a record**: results outlive the computation that produced them;
* **communication**: results move between parties who never meet;
* **accumulation**: new results are built on recorded ones.

The project's thesis is that AI needs the same layer: a common written form in which
models record what they have established, send it to other models, and build on it,
with a referee that anyone can re-run.

### 1.2 Mathematics as the precedent

Mathematics already crossed the threshold where computation exceeds human checking.
The response was not to trust the computation. It was to write results in a formal
language, check them with a small trusted kernel, and accumulate them in a shared
library. The loop of conjecture, machine-checked proof, library, and new conjecture is
what Hakem imitates. It extends the loop to claims that cross disciplines: physics,
accounting, economics, policy.

### 1.3 Design principles

* **De Bruijn criterion.** Anyone, human or AI, may propose. The proposer is an
  untrusted prover. Judgment belongs to a small, auditable kernel.
* **Independent refereeing.** The trusted part should be small enough for other
  organisations to re-implement. Hakem reuses Lean's kernel, which already has several
  independent implementations, and keeps its own trusted vocabulary small.
* **Chaos is located, not removed.** Measurement and value choices are outside the
  kernel's jurisdiction. They must appear explicitly, as symbol roles, and results are
  conditional on them.
* **The word "proven" belongs to the judge.** Only the judge may write *formal
  acceptance*, and only for a specific formal statement. Natural-language readings are
  shown separately and marked unchecked.

## 2. Oversight in autonomous learning

Systems that improve themselves need a signal that tells good outputs from bad ones.
When that signal comes from a learned model, it can be gamed. When it comes from a
checker whose soundness is a theorem, the only remaining question is whether the
*statement* means what we intend. Hakem's contribution is to make such a checker
available for a class of claims wider than pure mathematics:

* **Analogies.** "This result from discipline A holds in discipline B, under this
  glossary."
* **Metaphors.** "This glossary does not preserve structure; here is a world of B that
  breaks it."
* **Policy verdicts.** "Under these explicitly normative premises, this policy follows,
  and the facts alone do not decide it."

The resulting loop is:

```
 proposer models ──▶ inbox/*.hkm ──▶ hakem json ──▶ accepted? ──▶ corpus/ (content hash)
        ▲                                │                             │
        └──────── reward 0/1, reasons ◀──┴──────── ledger.jsonl ◀──────┘
                                                  later documents reuse lemmas
```

`tools/loop.py` implements this loop without a human in it. Each verdict is appended to
`ledger.jsonl` with a SHA-256 content hash and a 0/1 reward. Accepted documents enter
the corpus. `tools/corpus.py` turns them into kernel certificates.

## 3. The logic

Disciplines are data. A **signature** lists function and relation symbols with arities
and **roles** (`tanim` definitional, `ampirik` empirical, `normatif` normative).
Formulas are first-order with equality, using de Bruijn indices. A **structure** gives a
carrier and interpretations. A **theory** is a list of axioms, optionally with a class of
admissible structures.

**Analogy as signature morphism.** A glossary σ sends each source symbol to a target term
or formula, for example "energy ↦ deposits − loans". A target world M is read in the
source language by the *reduct* σ(M).

* **Satisfaction condition** ✓ `satisfaction`:
  `M ⊨ σ(φ)  ⇔  σ(M) ⊨ φ`.
* **Analogy certificate** `Analogy A B`: for every axiom of A, B entails its translation.
  B also has a model, so the transfer is not vacuous.
* **Transfer** ✓ `transfer`: `A ⊨ φ ⇒ B ⊨ σ(φ)`.
* **Composition** ✓ `compose_exists`: analogies compose, and the glossary of the chain
  is the composition of glossaries.
* **Non-vacuity** ✓ `source_consistent`: if an analogy exists, the source theory has a
  model.

**Metaphor certificate.** A metaphor is certified by a source theorem φ together with a
target model in which σ(φ) fails.

* ✓ `refutation_sound`: such a certificate excludes **every** analogy that agrees with σ
  on the symbols anchored by the certificate.

**Fact and value.** `reinterp` changes the interpretations of normative symbols only. A
**policy verdict** for φ in T consists of three parts: T ⊨ φ; a world satisfying all of
T; and an alternative, differing from that world only in normative symbols, where φ
fails.

* ✓ `hume_law`: if every axiom of T is descriptive (contains no normative symbol), no
  policy verdict exists.
* ✓ `verdict_same_facts`: in every verdict the two worlds agree on all descriptive
  symbols; the conclusion is true in one and false in the other. The dispute is
  normative.

The normative status of a formula is *computed* from its symbols (`Formula.descriptive`).
It is never declared.

## 4. Certificates are data

**Proof calculus.** `Proof` is a term language for natural deduction (∧ ∨ → ∀ ∃ =,
excluded middle). `infer` computes what a proof proves.

* ✓ `calculus_sound`: `check T.axioms φ p = true ⇒ T ⊨ φ`.

**Finite models.** `FinStructure` has carrier `Fin (n+1)` and computable interpretations.

* ✓ `finite_sat_iff`, ✓ `finite_models_sound`, ✓ `finite_refutes_sound`: on finite
  structures, computation agrees with truth for closed formulas.
* ✓ `refutation_of_data`, ✓ `verdict_of_data`: metaphor certificates and policy
  verdicts are built entirely from data.

**Standard mathematics.** In a theory with background, admissible models are those whose
standard part is isomorphic to a fixed structure, such as ℕ or ℤ.

* ✓ `iso_sat`, ✓ `background_sound`, ✓ `calculus_sound_bg`, ✓ `entails_of_std`:
  reasoning about numbers can be done directly on the standard carrier.

Once these are accepted, a certificate is checked by kernel computation alone
(`decide +kernel`). No tactic, parser or compiler is involved.

## 5. The language

A Hakem document is a list of S-expressions, specified in [`DIL.md`](../DIL.md):

```lisp
(hakem 1)
(sig phys (fn E 1 ampirik) (rel Exch 2 tanim))
(theory Physics phys (ax cons (all (all (imp (Exch v0 v1) (= (E v0) (E v1)))))))
(sig bank (fn Dep 1 ampirik) (fn Net 1 ampirik) (rel Tr 2 tanim) (rel Cr 2 tanim))
(theory Banking bank (ax trNet …) (ax crNet …) (ax crMoney …) …)
(lemma stepNet Banking (all (all (imp (or (Tr v0 v1) (Cr v0 v1)) (= (Net v0) (Net v1))))) PROOF)
(morph net phys bank (fn E (Net p0)) (rel Exch (or (Tr p0 p1) (Cr p0 p1))))
(analogy physicsToBanking Physics Banking net (model 2 …) (oblig cons (ax stepNet)))
(refute depositsMetaphor Physics Banking dep (all …) (ax cons) (model 2 …))
```

**Meaning.** `Doc.HoldsTree` says that every claim of the document holds, in the sense
of `Claim.Holds`.

* ✓ `checkTree_sound`, ✓ `checkDoc_sound`: every document the checker accepts means
  what it says. This is the fundamental theorem of the language, proved once for all
  documents.

**Trust chain.** The chain is text → tree → claims → verdict. Only the first step, a
reader of about 40 lines, runs outside the kernel. Anyone can re-implement it and
compare trees. A finding motivated this split: kernel reduction of `String.toList`
costs about 0.1 s per character, while checking a document's tree costs about 2 s per
document.

**Corpus** (✓ `korunum_holds`, ✓ `politika_holds`). Two conformance documents:
* energy conservation transfers to banking under the glossary "energy ↦ net position";
* the glossary "energy ↦ deposits" is refuted, because credit creates money;
* a policy verdict whose normative premise is computed as normative.

Three bad documents are rejected: a wrong proof, a normative symbol mislabelled as
empirical, and a "counterexample" that is not a model.

## 6. What formal acceptance means

The judge (`tools/Judge.lean`, `tools/hakem.sh`) accepts a claim only when all of the
following hold:

1. Lean's kernel accepts it, and the export is re-checked by an independent kernel,
   nanoda, written in Rust.
2. The statement in the trusted `Challenge.lean` and the proof in the untrusted
   `Solution` are identical *as terms*.
3. Every definition the statement depends on (its *meaning base*) is identical on both
   sides.
4. The proof uses only `propext`, `Quot.sound` and `Classical.choice`.

The current state is **21 / 21 claims accepted**. 61,454 declarations were re-checked
by nanoda.

Acceptance does **not** establish:

* that a reading describes its statement correctly;
* that a model is faithful to the real discipline;
* that measured values or value choices are right;
* that the local run resists adversarial input. That requires
  `lake comparator --paranoid` on Linux, with a sandbox and several kernels. This runs in
  CI on every push. In its first run (27 November 2026) all six kernels accepted: Lean
  paranoid, lean4lean, nanoda, con-leche, con-ron, and Lean's default kernel.

## 7. Adversarial validation

A self-test feeds attack-shaped submissions to the judge. Each must be rejected for the
expected reason:

* a new axiom;
* `sorry`;
* the same name with a different statement;
* a hollowed-out redefinition of trusted data under the same names;
* `native_decide`, which trusts the compiler;
* the three bad documents above.

Validation found and fixed two real defects in the judge:

* The axiom collector silently returned nothing, because `ConstantInfo.value?` omits
  theorem bodies. A `sorry` proof would have passed.
* The meaning base counted only `Hakem`/`Challenge` modules, so a hollowed-out corpus
  tree was accepted.

We report these because they are the failure mode a referee must anticipate.

## 8. Related work

* **Lean 4 and its kernel**, the independent kernels nanoda and lean4lean, and the Lean
  FRO's comparator for judging untrusted proofs. Hakem builds on and reuses all of
  these.
* **Mathlib** as a shared, cumulative, machine-checked record: the precedent for the
  progress loop.
* **Metamath and the de Bruijn criterion**: a small checker that independent parties can
  re-implement.
* **Institution theory** (Goguen and Burstall): the satisfaction condition and theory
  morphisms.
* **Categorical approaches to interdisciplinary modelling** (Spivak's ologs,
  AlgebraicJulia): Hakem's analogies are model morphisms, and a categorical formulation
  is the natural long-term direction.
* **Training provers against formal checkers**: the use of verifiable rewards that this
  work generalises beyond mathematics.

## 9. Limitations and future work

* **Faithfulness.** Whether a theory faithfully represents a discipline cannot be
  checked by Lean. We propose plural, independent human review pinned to definition
  fingerprints.
* **Cross-document imports.** Version 1 reuses lemmas only within a document. Next:
  imports by content hash, so that the corpus becomes a library.
* **Backgrounds in the language.** The kernel supports ℕ/ℤ backgrounds; the language
  does not yet. ℝ and analysis need Mathlib as a background.
* **Proof search.** The language carries proofs; it does not find them. A search tool
  needs no trust, because its output is checked.
* **Independent implementations.** A second reader and checker, written by another party
  against `DIL.md` and the conformance corpus.
* **Adversarial deployment.** Comparator already runs in CI; next, signed verdicts and
  reproducible builds so that third parties can verify a verdict offline.

## 10. Conclusion

Hakem is a small step toward a common written form for machine reasoning. Models can use
it to record, communicate and build on interdisciplinary results. A referee whose
soundness is a theorem judges every document, and the referee stays small enough to
rebuild.

---

*Repository: https://github.com/kimahmet/hakem — Apache-2.0. Please cite via
`CITATION.cff` and retain `NOTICE`.*
