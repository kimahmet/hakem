# The Hakem language — specification (version 1)

The language in which models (human or AI) write theories, glossaries, analogies,
claims, proofs and counterexamples to each other. The **meaning** and the **checking**
of a document are defined in the Lean kernel. The checker's soundness is proved once,
for every possible document (`checkDoc_sound`, `checkTree_sound`; see `VERDICT.md`).

This document should be enough to read and write the language, or to write a new
checker. Where it disagrees with the Lean definitions, the Lean definitions are
binding: `Hakem/Lang/SExp.lean` (reading), `Hakem/Lang/Syntax.lean` (syntax),
`Hakem/Lang/Elab.lean` (meaning), `Hakem/Lang/Check.lean` (checking).

## 1. Trust chain

```
text ──reader──▶ tree (S-expressions) ──elaboration──▶ claims ──check──▶ ACCEPTED/REJECTED
       small,          │                                 meaning: Claim.Holds
       independently   └── embedded in the certificate as a Lean term; everything from
       re-implementable    here on is computed in the kernel (decide +kernel)
```

* The **reader** (text → tree) is about 40 lines. Anyone can write their own reader and
  compare the trees they get. Because string processing in the kernel is slow, kernel
  certificates start from the tree.
* **Everything after the tree** is in the kernel: elaboration, the meaning of claims, and
  checking. The checker's soundness is proved, so it does not need to be read. Only the
  meaning (`Claim.Holds`, `Doc.HoldsTree`) needs to be read.

## 2. Lexical level

* A document is a sequence of S-expressions: atoms and `( … )` lists.
* Space, tab and newline separate tokens. `;` starts a comment that runs to the end of the
  line.
* Atoms are names, decimal natural numbers, or reserved words.
* Variables:
  * `vL`: a bound variable. `L` is the level of its binder: the outermost `all`/`ex` is 0,
    the next one inside is 1, and so on.
  * `pJ`: only in glossaries; the `J`-th argument (from 0) of the symbol being mapped.
* Reserved words (not usable as symbol names): `false = not imp and or all ex lam`, and
  atoms that start with `v` or `p` followed by digits.

## 3. Document

The first expression must be `(hakem 1)`. Entries follow and are processed in order. A
name can be used once it has been defined.

| Entry | Form | Claim? |
|---|---|---|
| Vocabulary | `(sig NAME (fn NAME ARITY ROLE)* (rel NAME ARITY ROLE)*)` | no |
| Theory | `(theory NAME SIG (ax NAME FORMULA)*)` | no |
| Lemma | `(lemma NAME THEORY FORMULA PROOF)` | yes |
| Glossary | `(morph NAME SIG1 SIG2 (fn NAME TERM)* (rel NAME FORMULA)*)` | no |
| Analogy | `(analogy NAME THEORY1 THEORY2 MORPH MODEL (oblig AXIOM PROOF)*)` | yes |
| Metaphor | `(refute NAME THEORY1 THEORY2 MORPH FORMULA PROOF MODEL)` | yes |
| Policy verdict | `(verdict NAME THEORY FORMULA PROOF MODEL (alt TABLE*))` | yes |

`ROLE` is one of:
* `definitional`: structural vocabulary;
* `empirical`: the value is fixed by measurement;
* `normative`: the value is fixed by a value choice.

The role belongs to the symbol. Whether a formula is normative is **computed** from its
symbols.

### Terms and formulas

```
TERM    ::= vL | pJ | NAME | (NAME TERM*)
FORMULA ::= false | (= TERM TERM) | (not F) | (imp F F) | (and F F) | (or F F)
          | (all F) | (ex F) | (NAME TERM*)
```

Theory axioms, lemmas and claim formulas are closed (no free `vL`). Arities are checked.
An unknown name or a wrong arity makes the document fail to elaborate.

### Glossary

**Every** symbol of the source vocabulary goes to a term (function) or a formula
(relation) of the target; arguments are written `p0, p1, …`. Examples:
`(fn E (Net p0))`, `(rel Exch (or (Tr p0 p1) (Cr p0 p1)))`.

## 4. Meaning of claims

For a theory `T`, `T ⊨ φ` means that every model of `T` satisfies `φ`. For an analogy or a
metaphor, the translation `σ(φ)` is the glossary applied to the formula. The Lean
counterpart is `Claim.Holds`.

| Claim | Meaning |
|---|---|
| `lemma L T φ` | `T ⊨ φ` (from the axioms alone; lemmas are not part of the meaning). |
| `analogy A B σ` | Every model of `B`, read through `σ`, is a model of `A`, and `B` has a model. Consequence: if `A ⊨ φ` then `B ⊨ σ(φ)` (general law `transfer`). |
| `refute A B σ φ` | `A ⊨ φ`, and `σ(φ)` is false in some model of `B`. Consequence: no analogy that agrees with `σ` on the symbols of `φ` exists (general law `refutation_sound`). |
| `verdict T φ` | `T ⊨ φ`, and in some model of `T`, reinterpreting **only the normative symbols** makes `φ` false. Consequence: the facts do not decide this conclusion; a theory without normative premises has no policy verdict (general law `hume_law`). |

## 5. Certificates (they do not affect meaning; they are only checked)

### Proof (natural deduction)

The context is: first the local hypotheses (the most recent is `hyp 0`), then the axioms of
the theory and the lemmas proved so far, in document order. `(ax NAME)` refers to an axiom
or lemma by name.

| Proof | Rule |
|---|---|
| `(hyp N)` | the `N`-th element of the context |
| `(ax NAME)` | the named axiom or lemma |
| `(falsumE A P)` | from `P : ⊥` infer `A` |
| `(impI A P)` | assuming `A`, from `P : B` infer `A → B` |
| `(impE P Q)` | from `P : A → B` and `Q : A` infer `B` |
| `(andI P Q)`, `(andE1 P)`, `(andE2 P)` | introduction and elimination of `∧` |
| `(orI1 B P)`, `(orI2 A P)` | from `P : A` infer `A ∨ B`; from `P : B` infer `A ∨ B` |
| `(orE P Q R)` | from `P : A ∨ B`, `Q : C` (assuming `A`) and `R : C` (assuming `B`) infer `C` |
| `(allI P)` | from `P : A` over a fresh variable (level = current depth) infer `∀ A` |
| `(allE T P)` | from `P : ∀ A` infer `A[T]` |
| `(exI (lam A) T P)` | from `P : A[T]` infer `∃ A` |
| `(exE C P Q)` | from `P : ∃ A` and `Q : C` (with a fresh variable and assuming `A`) infer `C` |
| `(refl T)` | `T = T` |
| `(eqE (lam A) P Q)` | from `P : T = U` and `Q : A[T]` infer `A[U]` |
| `(em A)` | `A ∨ ¬A` |

`(lam A)`: `A` is written one binder deeper; its hole is that new variable.

### Finite model

`(model B (fn NAME VALUE*)* (rel NAME VALUE*)*)`: the carrier is `{0, …, B−1}`. The table of
a symbol of arity `k` has `Bᵏ` values; the argument vector `(a0, …, ak−1)` is at position
`a0 + B·a1 + B²·a2 + …`. Relation values are `0`/`1`. A missing table or value counts as 0;
values are taken modulo `B`.

`(alt …)` contains tables in the same form; only the tables of normative symbols are used.

### Checking rules (`checkClaim`)

* `lemma`: the proof derives the formula in the theory's context.
* `analogy`: there is one `oblig` per axiom, in order; each derives the axiom's translation
  in the target theory's context; the model is a model of the target theory.
* `refute`: the proof derives the formula in the source theory; the model is a model of the
  target theory and falsifies the formula's translation.
* `verdict`: the proof derives the formula; the model is a model of the theory; the model
  with its normative tables replaced falsifies the formula.

## 6. Tools

```sh
lake exe hakem check DOC.hkm…      # compiled checker (fast)
lake exe hakem json DOC.hkm        # one-line JSON verdict for agents
lake exe hakem cert DOC.hkm NAME   # print the document tree as a Lean term
python3 -I tools/corpus.py .       # corpus/*.hkm → CorpusTrees/, claims and kernel proofs
./tools/hakem.sh                   # all claims: Lean kernel + nanoda → VERDICT.md
```

The compiled checker trusts the Lean compiler. The definitive verdict is the kernel
computation: in `VERDICT.md`, `<doc>_holds : Doc.HoldsTree <doc>_tree`.

## 7. Conformance tests

* `corpus/`: documents that must be accepted.
* `corpus-bad/`: documents that must be rejected: a wrong proof, a normative symbol
  mislabelled as empirical, a counterexample that is not a model.

An independent implementation must give the same results on both folders.

## 8. Limits of version 1

* Lemmas are reused only within the same document. There is no import across documents
  (by content hash) yet.
* Background structures (ℕ, ℤ, ℝ) are not in the language yet. The kernel has them
  (`Theory.withBackground`); they are not connected to the language.
* Counterexamples are finite.
* There is no proof search. The language carries proofs; it does not find them.
