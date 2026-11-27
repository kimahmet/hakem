#!/bin/sh
# Yargıcın öz-sınaması: her kötü çözüm, beklenen gerekçeyle RET almalı.
# Not: nanoda adımı burada taklit edilir (çıkış kodu 0, ifade basılmış). Böylece
# yalnızca yargıcın kendi denetimleri sınanır. nanoda'nın kendisi hakem.sh'de çalışır.
set -eu
cd "$(dirname "$0")/.."
OUT=.lake/hakem/selftest
mkdir -p "$OUT"
lake build SelfTest Challenge Solution hakem >/dev/null 2>&1 || true
fail=0
judge() { # modül iddia
  printf 'theorem %s : X :=\n  _\n' "$2" > "$OUT/nanoda.txt"
  printf '{"challenge_module":"Challenge","solution_module":"%s","theorem_names":["%s"]}\n' "$1" "$2" > "$OUT/cfg.json"
  lake env lean --run tools/Judge.lean "$OUT/cfg.json" "$OUT/nanoda.txt" 0 > "$OUT/$1.$2.md"
}
reject() { # modül iddia beklenen-gerekçe
  if judge "$1" "$2"; then
    echo "BAŞARISIZ: $1/$2 kabul edildi"; fail=1
  elif grep -q "$3" "$OUT/$1.$2.md"; then
    echo "geçti: $1/$2 → RET ($3)"
  else
    echo "BAŞARISIZ: $1/$2 RET aldı ama beklenen gerekçe yok: $3"; grep "DURUM" "$OUT/$1.$2.md"; fail=1
  fi
}
accept() { # modül iddia
  if judge "$1" "$2"; then echo "geçti: $1/$2 → BİÇİMSEL KABUL"
  else echo "BAŞARISIZ: $1/$2 reddedildi"; grep "DURUM" "$OUT/$1.$2.md"; fail=1; fi
}
reject SelfTest.Axiom     hume_law          "izinsiz aksiyom: cheat"
reject SelfTest.Sorry     transfer          "izinsiz aksiyom: sorryAx"
reject SelfTest.Statement hume_law          "İFADE FARKLI"
reject SelfTest.Swap      korunum_holds     "anlam tabanı farklı"
reject SelfTest.Native    korunum_holds     "izinsiz aksiyom"
# Pozitif kontrol: gerçek çözüm aynı koşullarda kabul almalı.
accept Solution hume_law
accept Solution checkTree_sound
accept Solution korunum_holds
# Kötü belgeler: araç her birini reddetmeli.
for f in corpus-bad/*.hkm; do
  if .lake/build/bin/hakem check "$f" > "$OUT/$(basename "$f").txt" 2>&1; then
    echo "BAŞARISIZ: kötü belge kabul edildi: $f"; fail=1
  else
    echo "geçti: $f → RET ($(grep -m1 -E 'RET|ÇEVRİLEMEDİ|OKUNAMADI' "$OUT/$(basename "$f").txt" | sed 's/^[^:]*: //'))"
  fi
done
exit $fail
