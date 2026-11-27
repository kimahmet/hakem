"""Külliyat: corpus/*.hkm belgelerinden
  * Corpus/<Ad>.lean   — belge ağacı (`hakem cert` çıktısı),
  * Corpus.lean        — kök,
  * Challenge.lean §III — her belge için `<ad>_holds : Doc.HoldsTree <ad>_tree`,
  * Solution/Corpus.lean — çekirdek hesabıyla ispat.
Kullanım: python3 -I tools/corpus.py <proje-kökü>"""
import pathlib, re, subprocess, sys
root = pathlib.Path(sys.argv[1])
docs = sorted((root / "corpus").glob("*.hkm"))
(root / "Corpus").mkdir(exist_ok=True)
names = []
def ident(stem):
    """Dosya adından Lean tanımlayıcısı: harf/rakam dışı `_`, başta harf."""
    x = re.sub(r"[^A-Za-z0-9]", "_", stem)
    return x if x[:1].isalpha() else "d_" + x

for d in docs:
    n = ident(d.stem)
    out = subprocess.run([str(root / ".lake/build/bin/hakem"), "cert", str(d.relative_to(root)), n],
                         cwd=root, capture_output=True, text=True, check=True).stdout
    (root / "Corpus" / f"{n.capitalize()}.lean").write_text(out)
    names.append(n)
(root / "Corpus.lean").write_text("".join(f"import Corpus.{n.capitalize()}\n" for n in names))
ch = (root / "Challenge.lean").read_text()
marker = "/-! ## III. Külliyat -/\n"
ch = ch[: ch.index(marker) + len(marker)]
for n in names:
    ch += (f"\n/-- OKUMA: `corpus/{n}.hkm` belgesinin bütün iddiaları doğrudur. -/\n"
           f"theorem {n}_holds : Doc.HoldsTree {n}_tree := sorry\n")
(root / "Challenge.lean").write_text(ch)
sol = "import Hakem\nimport Corpus\nimport Solution.Lang\n\n/-! Güvenilmeyen ispatlar: külliyat (yalnızca çekirdek hesabı). -/\n\nnamespace Proofs\n"
for n in names:
    sol += (f"\nset_option maxRecDepth 100000 in\n"
            f"theorem {n}_holds : Doc.HoldsTree {n}_tree :=\n  checkTree_sound _ (by decide +kernel)\n")
sol += "\nend Proofs\n"
(root / "Solution" / "Corpus.lean").write_text(sol)
print(" ".join(names))
