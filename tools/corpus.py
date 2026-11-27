"""Corpus: from the documents corpus/*.hkm, generate
  * CorpusTrees/<Name>.lean — the document tree (`hakem cert` output),
  * CorpusTrees.lean        — the root,
  * Challenge.lean §III     — for each document, `<name>_holds : Doc.HoldsTree <name>_tree`,
  * Solution/Corpus.lean    — its proof by kernel computation.
Usage: python3 -I tools/corpus.py <project-root>"""
import pathlib, re, subprocess, sys
root = pathlib.Path(sys.argv[1])
docs = sorted((root / "corpus").glob("*.hkm"))
(root / "CorpusTrees").mkdir(exist_ok=True)
names = []
def ident(stem):
    """Lean identifier from a file name: non-alphanumerics become `_`, must start with a letter."""
    x = re.sub(r"[^A-Za-z0-9]", "_", stem)
    return x if x[:1].isalpha() else "d_" + x

for d in docs:
    n = ident(d.stem)
    out = subprocess.run([str(root / ".lake/build/bin/hakem"), "cert", str(d.relative_to(root)), n],
                         cwd=root, capture_output=True, text=True, check=True).stdout
    (root / "CorpusTrees" / f"{n.capitalize()}.lean").write_text(out)
    names.append(n)
(root / "CorpusTrees.lean").write_text("".join(f"import CorpusTrees.{n.capitalize()}\n" for n in names))
ch = (root / "Challenge.lean").read_text()
marker = "/-! ## III. Corpus -/\n"
ch = ch[: ch.index(marker) + len(marker)]
for n in names:
    ch += (f"\n/-- READING: every claim of the document `corpus/{n}.hkm` holds. -/\n"
           f"theorem {n}_holds : Doc.HoldsTree {n}_tree := sorry\n")
(root / "Challenge.lean").write_text(ch)
sol = "import Hakem\nimport CorpusTrees\nimport Solution.Lang\n\n/-! Untrusted proofs: the corpus (kernel computation only). -/\n\nnamespace Proofs\n"
for n in names:
    sol += (f"\nset_option maxRecDepth 100000 in\n"
            f"theorem {n}_holds : Doc.HoldsTree {n}_tree :=\n  checkTree_sound _ (by decide +kernel)\n")
sol += "\nend Proofs\n"
(root / "Solution" / "Corpus.lean").write_text(sol)
print(" ".join(names))
