# Hakem — design document

This document explains what the referee checks, how, and with what assurance. It also
records what was learned along the way (history: `archive/`, which is kept in its original
Turkish).

## 0. Ground rule: who may say "proven"

A claim's status can be written in only three ways.

| Status | Who writes it | Meaning |
|---|---|---|
| **FORMALLY ACCEPTED** | The judge only (`tools/Judge.lean`) | A specific Lean statement passed specific checks (§5). |
| **REJECTED** | The judge only | At least one check failed; the reason is given. |
| **READING (unchecked)** | Humans or AI | A natural-language reading of the statement. Its correctness is outside Lean's jurisdiction. |

No human or AI text may say a claim "is proven". The only thing it may say is "statement X
received formal acceptance in `VERDICT.md`". Whether the statement describes the world
correctly is a separate claim and belongs to the reading layer.

This rule came from a mistake. While reporting on the prototype, the word "proven" was used
for claims stronger than what Lean had accepted (§1).

## 1. How the design evolved

| Version | Idea | What it taught |
|---|---|---|
| Prototype (v0.3) | Hand-written Lean models of physics, accounting, banking, equilibrium, carbon cost. | Words outran proofs: conditions lived in comments; a "market" model was a copy of the thermodynamic one; "Scarf" was only a 3-cycle; a number came from compiled code, not the kernel. |
| v1 | A shallow kernel (`Theory`, `Analogy`, `Refutation`, `Question`, `Verdict`) plus a judge. | Trust lives in definitions, not theorems. Vacuity, anchors, typed fact/value separation. |
| v2 | Disciplines as **data**: first-order logic with symbol roles; general laws proved once; proofs and counter-models as data; ℕ/ℤ backgrounds. | A new discipline should add nothing to the kernel. |
| v3 (current) | The **Hakem language**: documents written by models, checked by a checker proved sound for every document. | The referee should not write discipline models; others write them in the language. |

### 1.1 Lessons that shaped the kernel

1. **Vacuity.** A theory with no model entails everything. Every analogy certificate must
   exhibit a model of the target. Every policy verdict must exhibit a world satisfying the
   premises.
2. **Anchors.** A constant map makes almost any "interpretation" valid. The content of an
   analogy is its glossary: which symbol corresponds to which. Verdicts are relative to the
   glossary, not to the pair of disciplines. Banking is a metaphor for physics under "energy
   ↦ deposits" and an analogy under "energy ↦ deposits − loans".
3. **Direction.** The target is read in the source's language (the reduct). Coordinates the
   source does not see may vary freely in the target.
4. **Types, not labels.** Fact and value are separated by symbol roles, and normativity is
   computed from the symbols a formula uses. Premises are never self-labelled.
5. **Definitions are not premises.** Definitional content enters as Lean definitions, which
   are conservative extensions.
6. **Idealization is a fourth kind.** Choices such as "two bodies" or "integer energies" are
   neither empirical nor normative. They relate a model to the world, so they are not
   formal propositions. They belong in the reading layer and must be stated there.
7. **Trust lives in definitions, not theorems.** In Lean a theorem needs no trust; the
   kernel checks it. What must be trusted are the definitions that fix what claims *mean*.
   "A small kernel" therefore means a small set of definitions.

### 1.2 Deferred

* **Scarf's cycle.** In Scarf's (1960) economy, tâtonnement cycles in continuous time. Two
  integer discretizations (sign rule, sum-preserving rule) spiralled out to zero prices from
  all six starting points tried. This is a simulation result, not a proof. A faithful
  formalization needs real numbers and ODEs, i.e. Mathlib as a background.

## 2. Trust architecture

```
 untrusted ─┐
            │  Solution/…          proofs (humans or AI)
            ▼
 trusted ──── Challenge.lean       claim statements (written by humans, no proofs)
            corpus/, CorpusTrees/  documents in the language and their trees
            Hakem/Lang/…           the language: reader, syntax, meaning
            Hakem/Kernel.lean      verdict vocabulary
            Hakem/Logic.lean       logic: terms, formulas, structures, translation, reduct
            tools/Judge.lean       the judge
            L0: Lean kernel + independent kernels
```

| Layer | Content | Trusted? | Who checks |
|---|---|---|---|
| L0 | Lean's type theory and kernels | Yes | Independent implementations: Lean (C++), lean4lean, nanoda (Rust), con-leche, con-ron. All run in CI (§5). |
| L1 | Definitions in `Hakem/Logic.lean`, `Hakem/Kernel.lean`, `Hakem/Lang/{SExp,Syntax,Elab}.lean` | Yes | Human reading. These files contain no theorems. |
| L1' | Checkers `Hakem/Calculus.lean`, `Hakem/Finite.lean`, `Hakem/Lang/Check.lean` | No | Their soundness is proved; they need not be read. |
| L2 | Documents (`corpus/`) | Yes (their meaning) | Human reading: does the vocabulary represent the discipline? Are the roles right? |
| L3 | `Challenge.lean` statements | Yes | Human reading: does the statement say what the reading says? |
| L4 | `Solution/` proofs | **No** | Kernels. |
| L5 | `tools/Judge.lean`, `tools/*.sh` | Yes | Human reading and the self-test. |

Everything a prover (including an AI) can do is in L4 or produces data checked by L1'. None
of it enters the trusted base.

## 3. Kernel vocabulary and why each concept exists

| Concept | Why |
|---|---|
| `Signature` (symbols, arities, **roles**) | A discipline's vocabulary. Roles belong to symbols; fact/value is computed from them. |
| `Term`, `Formula` | Writing statements as data: first-order with equality, de Bruijn indices. The `dflt` term makes translation total. |
| `Structure`, `eval`, `Sat` | Meaning: a world and truth in it. |
| `onlySyms`, `descriptive` | Which symbols a formula uses: anchors and normativity. |
| `subst`, `liftSubst` | Substitution, needed to define translation. |
| `SigMorph`, `trT`, `trF` | The glossary and translation. A symbol may go to a derived term or formula ("energy ↦ deposits − loans"). |
| `SigMorph.reduct` | Reading a target world in the source language: the semantic face of an analogy. |
| `SigMorph.comp` | Chains of analogies. |
| `AgreeOn` | The anchored part of a glossary; metaphor certificates are relative to it. |
| `Theory` (axioms, `admissible`) | A discipline's theory. `admissible` connects to standard mathematical objects. |
| `Models`, `Entails`, `extend` | Model, entailment, subtheory (partial analogy). |
| `Analogy` | Certificate: glossary, preservation of admissibility, target entails translated axioms, a target model. |
| `Refutation` | Metaphor certificate: an anchored source theorem and a target model that breaks it. |
| `Structure.reinterp` | Change only the normative symbols. |
| `PolicyVerdict` | Entailment, a world satisfying the premises, and an alternative differing only in normative symbols where the conclusion fails. |
| `Structure.Iso`, `Theory.withBackground` | Standard mathematics: admissible models have a standard part isomorphic to ℕ, ℤ, … |
| Language: `SExp`, `REntry`, `elab*`, `Claim.Holds`, `Doc.HoldsTree` | Documents as text, their elaboration into the kernel, and their meaning. |

**General laws** (`Challenge.lean`, section I; for every input):
`satisfaction`, `transfer`, `source_consistent`, `compose_exists`, `refutation_sound`,
`hume_law`, `verdict_same_facts`, `calculus_sound`, `finite_sat_iff`,
`finite_models_sound`, `finite_refutes_sound`, `refutation_of_data`, `verdict_of_data`,
`iso_sat`, `background_sound`, `calculus_sound_bg`, `entails_of_std`.
**Language** (section II): `checkTree_sound`, `checkDoc_sound`.
**Corpus** (section III): one claim per document, `<doc>_holds`.

## 4. Corpus

The corpus consists of documents written in the language. It serves as the language's
conformance test; it is not the goal.

- `corpus/conservation.hkm`: vocabularies for physics and banking; a lemma (`stepNet`); an
  analogy that uses it via `(ax stepNet)`; a metaphor with a two-element counterexample.
- `corpus/policy.hkm`: a policy verdict with the normative symbol `Ought`.
- `corpus-bad/`: documents that must be rejected.

Lean-level examples that use backgrounds (carbon cost under ℕ, thermodynamics ↔ market
under ℤ) are in `archive/v2-lean-cases/`. Version 1 of the language does not yet support
backgrounds.

## 5. The judge: checks and attacks

### 5.1 Checks for every claim

1. `Challenge` and `Solution` contain a constant of the same name, and the two types are
   identical **as terms**.
2. The statement's meaning base, i.e. every constant it transitively depends on outside
   Lean's own libraries, is identical in type and value on both sides.
3. The transitive axioms of the proof are a subset of {`propext`, `Quot.sound`,
   `Classical.choice`}.
4. The full export of `Solution` (`leanexport`) is re-checked from scratch by the
   independent kernel nanoda.
5. The report lists every meaning-base definition with its reading and a fingerprint.
   Human reviews are pinned to the fingerprint; if the definition changes, the review is
   void.

In CI, `lake comparator --paranoid` additionally builds and exports the untrusted side in a
`bwrap` sandbox without loading its `.olean` files. It replays the result through Lean
paranoid, lean4lean, nanoda, con-leche, con-ron and Lean's default kernel. All six accept.

### 5.2 Known attacks

| Attack | Countered by | Tested |
|---|---|---|
| `sorry` / incomplete proof | Axiom list (`sorryAx`) | Yes: `SelfTest.Sorry` |
| New axiom | Axiom list | Yes: `SelfTest.Axiom` |
| Same name, different statement | Term comparison | Yes: `SelfTest.Statement` |
| Hollowed-out redefinition of trusted data under the same names | Meaning-base comparison (every module outside the prelude) | Yes: `SelfTest.Swap`. It caught a judge bug that counted only `Hakem`/`Challenge` modules. |
| `native_decide`, `implemented_by`, `extern` | Axiom list (`…_native…` axioms) | Yes: `SelfTest.Native` |
| Wrong proof, normative symbol labelled empirical, counterexample that is not a model | The checker | Yes: `corpus-bad/` |
| Custom notation or instances changing a statement's meaning | Statements are printed in the trusted environment; notation in the solution cannot reach `Challenge` | No (test to add) |
| Meta-code adding declarations that bypass the kernel | The export is re-checked from scratch by independent kernels | No (test to add) |
| Malicious `.olean` files, code execution at build time | Not countered locally. In CI: `lake comparator --paranoid` (sandbox; `.olean` files are not loaded) | Yes, in CI |
| A bug shared by all kernels | Cannot be countered (the type theory itself) | — |

A judge bug found by validation: the axiom collector silently returned nothing, because
`ConstantInfo.value?` omits theorem bodies. A `sorry` proof would have passed. It was fixed
and is now covered by `SelfTest.Sorry`.

## 6. Running

```sh
./tools/hakem.sh              # build → export → nanoda → judge → VERDICT.md
./tools/selftest.sh           # does the judge reject bad solutions and bad documents?
lake comparator --paranoid    # Linux only (bwrap); runs in CI
```

## 7. Limits and open problems

1. **Faithfulness.** The main remaining risk is whether theories represent their
   disciplines. Lean cannot check this. Proposal: reviews by several independent
   institutions, signed and pinned to definition fingerprints. The author of a statement
   and its reviewer should not be the same party.
2. **Fingerprints** are currently 64-bit structural digests, not cryptographic. Switch to the
   SHA-256 of the exported declaration.
3. **Mathlib.** Real physics and economics need real numbers, logarithmic entropy, ODEs.
   Proposal: the kernel stays dependency-free and backgrounds may use Mathlib; the Mathlib
   definitions then enter the meaning base of the claims that use them.
4. **Language version 1:** no cross-document imports, no backgrounds, finite
   counterexamples only, no proof search (see `LANGUAGE.md` §8).
5. **Statement authorship.** Who writes `Challenge.lean` and the corpus? AI may propose
   statements, but moving a statement to the trusted side is a human decision and must be
   recorded.
6. **Proof search and learning** belong to a separate, untrusted project (the assistant
   referee): it proposes, Hakem decides.
