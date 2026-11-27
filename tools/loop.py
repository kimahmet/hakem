"""Hakem autonomous loop: automating oversight.

One or many models write candidate documents to `inbox/`. The loop
  1. checks every candidate with `hakem json` (no human in the loop),
  2. moves accepted ones into `corpus/` under their content hash (SHA-256),
  3. moves rejected ones into `rejected/`,
  4. appends every verdict to `ledger.jsonl` (reward signal and shared record).
Accepted documents are later turned into kernel certificates by `tools/corpus.py`.

The ledger gives proposer models a verifiable reward to learn from:
`accepted` = 1, otherwise 0; claim-level detail is recorded too.

Usage: python3 -I tools/loop.py <project-root>
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
    print(f"{'ACCEPTED' if ok else 'REJECTED'} {target.name}")
