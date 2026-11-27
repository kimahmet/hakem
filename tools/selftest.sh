#!/bin/sh
# Judge self-test: every bad solution must be REJECTED for the expected reason, and every
# bad document must be rejected by the checker.
# Note: the nanoda step is simulated here (exit code 0, statement printed), so that only the
# judge's own checks are tested. nanoda itself runs in tools/hakem.sh.
set -eu
cd "$(dirname "$0")/.."
OUT=.lake/hakem/selftest
mkdir -p "$OUT"
lake build SelfTest Challenge Solution hakem >/dev/null 2>&1 || true
fail=0
judge() { # module claim
  printf 'theorem %s : X :=\n  _\n' "$2" > "$OUT/nanoda.txt"
  printf '{"challenge_module":"Challenge","solution_module":"%s","theorem_names":["%s"]}\n' "$1" "$2" > "$OUT/cfg.json"
  lake env lean --run tools/Judge.lean "$OUT/cfg.json" "$OUT/nanoda.txt" 0 > "$OUT/$1.$2.md"
}
reject() { # module claim expected-reason
  if judge "$1" "$2"; then
    echo "FAIL: $1/$2 was accepted"; fail=1
  elif grep -q "$3" "$OUT/$1.$2.md"; then
    echo "ok: $1/$2 → REJECTED ($3)"
  else
    echo "FAIL: $1/$2 rejected without the expected reason: $3"; grep "STATUS" "$OUT/$1.$2.md"; fail=1
  fi
}
accept() { # module claim
  if judge "$1" "$2"; then echo "ok: $1/$2 → FORMALLY ACCEPTED"
  else echo "FAIL: $1/$2 rejected"; grep "STATUS" "$OUT/$1.$2.md"; fail=1; fi
}
reject SelfTest.Axiom     hume_law           "unpermitted axiom: cheat"
reject SelfTest.Sorry     transfer           "unpermitted axiom: sorryAx"
reject SelfTest.Statement hume_law           "STATEMENT DIFFERS"
reject SelfTest.Swap      conservation_holds "meaning base differs"
reject SelfTest.Native    conservation_holds "unpermitted axiom"
# Positive control: the real solution must be accepted under the same conditions.
accept Solution hume_law
accept Solution checkTree_sound
accept Solution conservation_holds
# Bad documents: the checker must reject every one.
for f in corpus-bad/*.hkm; do
  if .lake/build/bin/hakem check "$f" > "$OUT/$(basename "$f").txt" 2>&1; then
    echo "FAIL: bad document accepted: $f"; fail=1
  else
    echo "ok: $f → REJECTED ($(grep -m1 -E 'REJECTED|UNELABORATED|UNREADABLE' "$OUT/$(basename "$f").txt" | sed 's/^[^:]*: //'))"
  fi
done
exit $fail
