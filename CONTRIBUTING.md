# Contributing

Hakem is the vision of kimahmet (see `NOTICE`). Contributions are licensed under
Apache-2.0. Derivative works must retain `NOTICE` and should cite the project via
`CITATION.cff`.

## 1. Writing documents (the easiest contribution)

1. Read `LANGUAGE.md` and look at the examples in `corpus/`.
2. Put your document in `inbox/` and run `python3 -I tools/loop.py .`, or check it directly
   with `lake exe hakem check DOC.hkm`.
3. Accepted documents enter `corpus/`. Run `python3 -I tools/corpus.py .` and
   `./tools/hakem.sh` to turn them into kernel certificates (`<name>_holds`).
4. Open a pull request. Reviewers look at the **reading**: does the vocabulary represent the
   discipline, and are the roles right? Checking is done by the machine.

## 2. An independent second implementation

Hakem's assurance rests on independent parties being able to re-implement the reader and
the checker. An implementation written against `LANGUAGE.md` must accept the documents in
`corpus/` and reject those in `corpus-bad/`.

## 3. Kernel and tools

* Trusted definitions: `Hakem/Logic.lean`, `Hakem/Kernel.lean`,
  `Hakem/Lang/{SExp,Syntax,Elab}.lean`. Every new concept added here must be justified in
  `DESIGN.md`.
* Claims live in `Challenge.lean` (with `sorry`); proofs live in `Solution/`.
  `Solution.lean` is generated: `python3 -I tools/gen_solution.py .`.
* After every change, `./tools/hakem.sh` and `./tools/selftest.sh` must pass.
* If you find a new form of attack, add a test under `SelfTest/` or `corpus-bad/`.

## 4. The word "proven"

Only the judge says a claim is proven (`VERDICT.md`). In documents, papers and pull
requests, say "received formal acceptance in `VERDICT.md`" and name the statement that
was accepted.
