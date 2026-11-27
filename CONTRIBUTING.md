# Katkı / Contributing

Hakem, kimahmet'in vizyonudur (bkz. `NOTICE`). Katkılar Apache-2.0 altındadır. Türev
çalışmalar `NOTICE` dosyasını korumalı ve `CITATION.cff` ile atıf yapmalıdır.

## 1. Belge yazmak (en kolay katkı)

1. `DIL.md`'yi okuyun ve `corpus/` altındaki örneklere bakın.
2. Belgenizi `inbox/` klasörüne koyun ve `python3 -I tools/loop.py .` çalıştırın. Ya da
   doğrudan `lake exe hakem check BELGE.hkm` ile denetleyin.
3. Kabul edilen belgeler `corpus/` klasörüne girer. `python3 -I tools/corpus.py .` ve
   `./tools/hakem.sh` ile belge çekirdek sertifikası olur (`<ad>_holds`).
4. Pull request açın. İnceleyenler belgenin **okumasına** bakar: sözlük disiplini doğru
   temsil ediyor mu, roller doğru mu? Denetimi ise makine yapar.

## 2. Bağımsız ikinci uygulama

Hakem'in güvencesi, bağımsız kurumların okuyucuyu ve denetleyiciyi yeniden
yazabilmesine dayanır. `DIL.md`'ye göre yazılmış bir uygulama, `corpus/` belgelerini
kabul etmeli ve `corpus-bad/` belgelerini reddetmelidir.

## 3. Çekirdek ve araçlar

* Güvenilen tanımlar: `Hakem/Logic.lean`, `Hakem/Kernel.lean`,
  `Hakem/Lang/{SExp,Syntax,Elab}.lean`. Buraya giren her yeni kavram
  `TASARIM.md`'de gerekçelendirilmelidir.
* İddialar `Challenge.lean`'de (`sorry` ile), ispatlar `Solution/`'dadır.
  `Solution.lean` otomatik üretilir: `python3 -I tools/gen_solution.py .`.
* Her değişiklikten sonra `./tools/hakem.sh` ve `./tools/selftest.sh` geçmelidir.
* Yeni bir saldırı biçimi bulursanız `SelfTest/` ya da `corpus-bad/` altına bir sınama
  ekleyin.

## 4. "Kanıtlı" sözcüğü

Bir iddianın kanıtlı olduğunu yalnızca yargıç söyler (`KARAR.md`). Belgelerde,
makalelerde ve PR açıklamalarında "`KARAR.md`'de biçimsel kabul aldı" deyin ve hangi
ifadenin kabul aldığını belirtin.

---

**English (short).** Contributions are under Apache-2.0; keep `NOTICE` and cite via
`CITATION.cff`. The easiest contribution is a document in the Hakem language: put it in
`inbox/` and run `tools/loop.py`. Independent re-implementations must accept `corpus/`
and reject `corpus-bad/`. Every new trusted concept must be justified in `TASARIM.md`.
Only the judge says "proven".
