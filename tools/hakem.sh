#!/bin/sh
# Hakem: local checking pipeline. Output: VERDICT.md
# 1) Lean kernel (lake build)  2) independent kernel nanoda  3) judge (tools/Judge.lean)
set -eu
cd "$(dirname "$0")/.."
OUT=.lake/hakem
mkdir -p "$OUT"
# No stale verdict: if the pipeline fails, VERDICT.md must not exist.
rm -f VERDICT.md
lake build Hakem Challenge Solution
lake env leanexport Solution > "$OUT/solution.ndjson"
BIN="$(dirname "$(lake env which lean)")"
NAMES=$(python3 -I -c 'import json,sys; print(json.dumps(json.load(open(sys.argv[1]))["theorem_names"]))' comparator.json)
cat > "$OUT/nanoda.json" <<JSON
{"export_file_path": "$PWD/$OUT/solution.ndjson", "use_stdin": false,
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
 "unpermitted_axiom_hard_error": false, "nat_extension": true, "string_extension": true,
 "pp_declars": $NAMES, "pp_to_stdout": true,
 "pp_options": {"all": false, "explicit": false, "universes": false, "notation": false,
                "proofs": false, "indent": 2, "width": 100},
 "print_success_message": true}
JSON
set +e
"$BIN/nanoda_bin" "$OUT/nanoda.json" > "$OUT/nanoda.txt" 2>&1
CODE=$?
set -e
tail -1 "$OUT/nanoda.txt"
# Write to a temporary file first, so a judge error cannot leave a partial VERDICT.md.
lake env lean --run tools/Judge.lean comparator.json "$OUT/nanoda.txt" "$CODE" > "$OUT/VERDICT.md" || { cat "$OUT/VERDICT.md" | head -20; exit 1; }
mv "$OUT/VERDICT.md" VERDICT.md
