"""Challenge.lean'den Solution.lean üretir: her `:= sorry`, aynı adlı Proofs teoremine bağlanır.
İfade metni kopyalanır; eşitliği yine de hakem (judge) terim düzeyinde denetler."""
import re, sys, pathlib
root = pathlib.Path(sys.argv[1])
src = (root / "Challenge.lean").read_text()
out, name = [], None
for line in src.splitlines():
    m = re.match(r"theorem (\S+)", line)
    if m: name = m.group(1)
    if line.startswith("import Hakem"):
        mods = sorted(f.stem for f in (root / "Solution").glob("*.lean"))
        line = "import Hakem\n" + "\n".join(f"import Solution.{m}" for m in mods)
    if line.rstrip().endswith(":= sorry"):
        line = line.replace(":= sorry", f":= Proofs.{name}")
    out.append(line)
(root / "Solution.lean").write_text("-- OTOMATİK ÜRETİLDİ: tools/gen_solution.py. Elle düzenleme.\n" + "\n".join(out) + "\n")
