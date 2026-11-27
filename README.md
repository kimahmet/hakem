# Hakem

**A kernel-checked writing system for machine reasoning.**

> Hakem is the vision of **kimahmet** and was developed under their direction.
> If you use or extend it, please cite it ([`CITATION.cff`](CITATION.cff)) and keep [`NOTICE`](NOTICE).

**Paper: [Proof Is All You Need](paper/main.pdf)** ([PDF](paper/main.pdf) · [LaTeX](paper/main.tex) · [Markdown](paper/PAPER.md))
· Related: [hakem-assistant](https://github.com/kimahmet/hakem-assistant), the ML assistant referee

---

## Vision

The invention of AI resembles the invention of the **abacus** more than that of writing.
The abacus gave humanity a shared capacity to compute and a shared way to check
computations. Writing brought three other things: a durable **record**,
**communication** between parties who never meet, and, as a result, **cumulative
progress**.

Hakem aims to build that writing for AI. In it, models record what they have
established, send it to each other, and build on it. Every document is judged by a small
referee that anyone can re-run.

The precedent is mathematics. When computation exceeded human checking, mathematics moved
to Lean and its shared library, Mathlib. The resulting loop is: conjecture,
machine-checked proof, library, new conjecture. Hakem imitates this loop and extends it to
claims that cross disciplines.

## What it does

Hakem **automates the oversight of autonomous AI learning.**

* Models write documents in the **Hakem language** ([`LANGUAGE.md`](LANGUAGE.md)). A
  document can contain:
  * vocabularies with symbol roles (`definitional`, `empirical`, `normative`);
  * theories, lemmas and cross-discipline glossaries;
  * **analogies**, **metaphor refutations** and **policy verdicts**;
  * proofs and finite counter-models as certificates.
* The checker accepts or rejects each document. **Its soundness is proved in the Lean 4
  kernel for every possible document** (`checkDoc_sound`).
* The autonomous loop (`tools/loop.py`) checks candidates with no human in the loop. It
  files accepted documents into the corpus by content hash and records each verdict in a
  ledger with a verifiable 0/1 reward.

The kernel carries three principles as **general theorems** for every input:

1. **Transfer.** A result carries to another discipline only along a structure-preserving
   map (`transfer`).
2. **Metaphor.** A structure-breaking map is refuted by a concrete counter-model
   (`refutation_sound`).
3. **No ought from is.** No policy verdict follows from premises without normative
   symbols (`hume_law`). The dispute always lies in the normative symbols
   (`verdict_same_facts`).

## Quick start

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
lake exe hakem check corpus/conservation.hkm   # check a document
lake exe hakem json  corpus/policy.hkm         # one-line JSON verdict for agents
python3 -I tools/loop.py .                     # inbox/ → corpus/ | rejected/, ledger.jsonl
python3 -I tools/corpus.py .                   # turn the corpus into kernel certificates
./tools/hakem.sh                               # all claims: Lean + nanoda → VERDICT.md
./tools/selftest.sh                            # are attacks and bad documents rejected?
```

## Assurance

Only the judge says "proven". A claim marked **FORMALLY ACCEPTED** in
[`VERDICT.md`](VERDICT.md) satisfies the following:

* Lean's kernel accepted the statement, and the independent kernel nanoda (Rust)
  re-checked the export.
* The statement is identical, as a term, to the trusted text.
* The statement's meaning base is identical on both sides.
* The proof uses only the standard axioms.

On every push, CI also runs `lake comparator --paranoid`. It builds the untrusted side in a
sandbox and replays it through six kernels: Lean paranoid, lean4lean, nanoda, con-leche,
con-ron and Lean's default kernel. All six accept.

**Not guaranteed:**

* that models are faithful to the real discipline;
* that measured values and value choices are right;
* that natural-language readings describe their statements correctly.

## Repository

| Path | Trust | Content |
|---|---|---|
| `Hakem/Logic.lean`, `Hakem/Kernel.lean` | trusted | Logic and verdict vocabulary |
| `Hakem/Calculus.lean`, `Hakem/Finite.lean` | proved sound | Proof and finite-model checkers |
| `Hakem/Lang/` | meaning trusted, checking proved sound | The Hakem language |
| `Challenge.lean` | trusted | Claim statements |
| `Solution/` | **untrusted** | Proofs |
| `corpus/`, `CorpusTrees/` | trusted | Accepted documents and their trees |
| `corpus-bad/` | — | Documents that must be rejected |
| `tools/` | trusted | Judge, CLI, autonomous loop |
| `paper/` | — | Paper |
| `DESIGN.md`, `LANGUAGE.md` | — | Design and language specification |
| `archive/` | — | Earlier versions (in Turkish, kept as a historical record) |

## Contributing

To write documents, build an independent second checker, or extend the kernel, see
[`CONTRIBUTING.md`](CONTRIBUTING.md). Licensed under Apache-2.0; derivative works must
retain `NOTICE`.
