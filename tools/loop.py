"""Hakem özerk döngüsü: denetimin otomatikleşmesi.

Bir ya da birçok model, aday belgeleri `inbox/` klasörüne yazar. Döngü:
  1. her adayı `hakem json` ile denetler (insan araya girmez),
  2. kabul edilenleri içerik özetiyle (SHA-256) `corpus/` klasörüne taşır,
  3. reddedilenleri gerekçesiyle `rejected/` klasörüne taşır,
  4. her kararı `ledger.jsonl` defterine ekler (ödül sinyali ve ortak kayıt).
Kabul edilen belgeler sonra `tools/corpus.py` ile çekirdek sertifikalarına çevrilir.

Defter, üreten modellerin öğrenmesi için doğrulanabilir ödül sağlar:
`accepted` = 1, aksi 0; iddia düzeyindeki ayrıntı da kayıtlıdır.

Kullanım: python3 -I tools/loop.py <proje-kökü>
"""
import hashlib, json, pathlib, shutil, subprocess, sys, time

root = pathlib.Path(sys.argv[1]).resolve()
inbox, corpus, rejected = root / "inbox", root / "corpus", root / "rejected"
for d in (inbox, corpus, rejected):
    d.mkdir(exist_ok=True)
hakem = root / ".lake" / "build" / "bin" / "hakem"
ledger = root / "ledger.jsonl"

for cand in sorted(inbox.glob("*.hkm")):
    data = cand.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    r = subprocess.run([str(hakem), "json", str(cand)], capture_output=True, text=True)
    try:
        verdict = json.loads(r.stdout.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        verdict = {"status": "error", "claims": [], "stderr": r.stderr[-500:]}
    ok = verdict.get("status") == "accepted"
    target = (corpus if ok else rejected) / f"{cand.stem}-{digest[:12]}.hkm"
    shutil.move(str(cand), target)
    entry = {"time": int(time.time()), "file": target.name, "sha256": digest,
             "reward": 1 if ok else 0, "verdict": verdict}
    with ledger.open("a") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")
    print(f"{'KABUL' if ok else 'RET  '} {target.name}")
