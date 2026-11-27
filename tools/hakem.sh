#!/bin/sh
# Hakem: yerel denetim hattı. Çıktı: KARAR.md
# 1) Lean çekirdeği (lake build)  2) bağımsız çekirdek nanoda  3) yargıç (tools/Judge.lean)
set -eu
cd "$(dirname "$0")/.."
OUT=.lake/hakem
mkdir -p "$OUT"
# Eski karar kalmasın: hat başarısız olursa KARAR.md hiç olmamalı.
rm -f KARAR.md
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
# Önce geçici dosyaya yaz: yargıç hata verirse eski KARAR.md bozulmaz.
lake env lean --run tools/Judge.lean comparator.json "$OUT/nanoda.txt" "$CODE" > "$OUT/KARAR.md" || { cat "$OUT/KARAR.md" | head -20; exit 1; }
mv "$OUT/KARAR.md" KARAR.md
