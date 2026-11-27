# Hakem dili — belirtim (sürüm 1)

Modellerin (insan ya da yapay zekâ) kuram, sözlük, analoji, iddia, ispat ve karşı
örnekleri birbirine yazdığı dil. Bir belgenin **anlamı** ve **denetimi** Lean
çekirdeğinde tanımlıdır. Denetleyicinin sağlamlığı her olası belge için bir kez
ispatlanmıştır (`checkDoc_sound`, `checkTree_sound`; `KARAR.md`).

Bu belge, dili bağımsız olarak okuyup yazmak ya da yeni bir denetleyici yazmak için
yeterli olmalıdır. Uyuşmazlık durumunda bağlayıcı olan Lean tanımlarıdır:
`Hakem/Lang/SExp.lean` (okuma), `Hakem/Lang/Syntax.lean` (sözdizimi),
`Hakem/Lang/Elab.lean` (anlam), `Hakem/Lang/Check.lean` (denetim).

## 1. Güven zinciri

```
metin ──okuyucu──▶ ağaç (S-ifadesi) ──çeviri──▶ iddialar ──denetim──▶ KABUL/RET
        küçük,          │                         anlam: Claim.Holds
        bağımsız        └── sertifikaya Lean terimi olarak gömülür; buradan sonrası
        yazılabilir         çekirdekte hesaplanır (decide +kernel)
```

* **Okuyucu** (metin → ağaç) ~40 satırdır. Herkes kendi okuyucusunu yazıp aynı ağacı
  elde ettiğini karşılaştırabilir. Çekirdekte dizge işleme yavaş olduğundan, çekirdek
  sertifikaları ağaçtan başlar.
* **Ağaçtan sonrası** çekirdektedir: çeviri, iddiaların anlamı ve denetim. Denetimin
  sağlamlığı ispatlıdır; denetleyiciyi okumaya gerek yoktur. Okunması gereken yalnızca
  anlamdır (`Claim.Holds`, `Doc.HoldsTree`).

## 2. Sözcük düzeyi

* Belge, S-ifadelerinin dizisidir: atomlar ve `( … )` listeleri.
* Boşluk, sekme ve satır sonu ayırıcıdır. `;` satır sonuna kadar yorumdur.
* Atomlar: adlar, ondalık doğal sayılar, ayrılmış sözcükler.
* Değişkenler:
  * `vL`: bağlı değişken. `L`, bağlayıcının düzeyidir: en dıştaki `all`/`ex` 0, içindeki 1, …
  * `pJ`: yalnızca sözlük eşlemesinde; eşlenen sembolün `J`. argümanı (0'dan).
* Ayrılmış sözcükler (sembol adı olamaz): `false = not imp and or all ex lam`,
  ve `v`/`p` ile başlayıp rakamla devam eden atomlar.

## 3. Belge

İlk ifade `(hakem 1)` olmalıdır. Sonra girdiler gelir; sırayla işlenir. Bir ad,
tanımlandıktan sonra kullanılabilir.

| Girdi | Biçim | İddia mı |
|---|---|---|
| Sözlük | `(sig AD (fn AD İKİLİK ROL)* (rel AD İKİLİK ROL)*)` | hayır |
| Kuram | `(theory AD SÖZLÜK (ax AD FORMÜL)*)` | hayır |
| Lemma | `(lemma AD KURAM FORMÜL İSPAT)` | evet |
| Eşleme | `(morph AD SÖZLÜK1 SÖZLÜK2 (fn AD TERİM)* (rel AD FORMÜL)*)` | hayır |
| Analoji | `(analogy AD KURAM1 KURAM2 EŞLEME MODEL (oblig AKSİYOM İSPAT)*)` | evet |
| Metafor | `(refute AD KURAM1 KURAM2 EŞLEME FORMÜL İSPAT MODEL)` | evet |
| Politika hükmü | `(verdict AD KURAM FORMÜL İSPAT MODEL (alt TABLO*))` | evet |

`ROL`: `tanim` (yapısal sözcük), `ampirik` (değeri ölçümle belirlenir), `normatif`
(değeri değer seçimiyle belirlenir). Rol sembole aittir. Bir önermenin normatif olup
olmadığı, içindeki sembollerden **hesaplanır**.

### Terim ve formül

```
TERİM  ::= vL | pJ | AD | (AD TERİM*)
FORMÜL ::= false | (= TERİM TERİM) | (not F) | (imp F F) | (and F F) | (or F F)
         | (all F) | (ex F) | (AD TERİM*)
```

Kuram aksiyomları, lemma ve iddia formülleri kapalıdır (serbest `vL` yok). İkilikler
denetlenir. Bilinmeyen ad ya da yanlış ikilik belgeyi çevrilemez kılar.

### Eşleme

Kaynak sözlüğün **her** sembolü hedefte bir terime (fonksiyon) ya da formüle (bağıntı)
gider; argümanlar `p0, p1, …` ile anılır. Örnek: `(fn E (Net p0))`,
`(rel Exch (or (Tr p0 p1) (Cr p0 p1)))`.

## 4. İddiaların anlamı

`T` bir kuramsa, `T ⊨ φ`: `T`'nin her modeli `φ`'yi doğrular. Bir analoji ya da metafor
için "çeviri" `σ(φ)`, eşlemenin formüle uygulanmasıdır. Lean karşılığı `Claim.Holds`.

| İddia | Anlam |
|---|---|
| `lemma L T φ` | `T ⊨ φ` (yalnızca aksiyomlardan; lemmalar anlamın parçası değildir) |
| `analogy A B σ` | `B`'nin her modeli `σ` ile okunduğunda `A`'nın modelidir, ve `B`'nin bir modeli vardır. Sonuç: `A ⊨ φ` ise `B ⊨ σ(φ)` (genel yasa `transfer`). |
| `refute A B σ φ` | `A ⊨ φ` ve `B`'nin bir modelinde `σ(φ)` yanlıştır. Sonuç: `φ`'nin sembollerinde `σ` ile aynı olan hiçbir analoji yoktur (genel yasa `refutation_sound`). |
| `verdict T φ` | `T ⊨ φ`, ve `T`'nin bir modelinde **yalnızca normatif sembollerin** yorumu değiştirilince `φ` yanlış olur. Sonuç: olgular bu sonucu belirlemez; normatif öncülsüz kuramdan hiçbir politika hükmü yoktur (genel yasa `hume_law`). |

## 5. Sertifikalar (anlamı etkilemez, yalnızca denetlenir)

### İspat (doğal çıkarım)

Bağlam: önce yerel hipotezler (en yenisi `hyp 0`), sonra kuramın aksiyomları ve o ana
kadar ispatlanmış lemmaları, belgedeki sırayla. `(ax AD)` bir aksiyoma ya da lemmaya
adıyla başvurur.

| İspat | Kural |
|---|---|
| `(hyp N)` | bağlamın `N`. öğesi |
| `(ax AD)` | adlı aksiyom/lemma |
| `(falsumE A P)` | `P : ⊥` ⇒ `A` |
| `(impI A P)` | `A` varsayılıp `P : B` ⇒ `A → B` |
| `(impE P Q)` | `P : A → B`, `Q : A` ⇒ `B` |
| `(andI P Q)`, `(andE1 P)`, `(andE2 P)` | ∧ giriş/çıkış |
| `(orI1 B P)`, `(orI2 A P)` | `P : A` ⇒ `A ∨ B`; `P : B` ⇒ `A ∨ B` |
| `(orE P Q R)` | `P : A ∨ B`, `Q : C` (A varsayımıyla), `R : C` (B varsayımıyla) ⇒ `C` |
| `(allI P)` | yeni değişken (düzeyi = derinlik) üzerinde `P : A` ⇒ `∀ A` |
| `(allE T P)` | `P : ∀ A` ⇒ `A[T]` |
| `(exI (lam A) T P)` | `P : A[T]` ⇒ `∃ A` |
| `(exE C P Q)` | `P : ∃ A`, `Q : C` (yeni değişken ve `A` varsayımıyla) ⇒ `C` |
| `(refl T)` | `T = T` |
| `(eqE (lam A) P Q)` | `P : T = U`, `Q : A[T]` ⇒ `A[U]` |
| `(em A)` | `A ∨ ¬A` |

`(lam A)`: `A`, bir değişken daha açılmış derinlikte yazılır; deliği o değişkendir.

### Sonlu model

`(model B (fn AD DEĞER*)* (rel AD DEĞER*)*)`: taşıyıcı `{0, …, B−1}`. Bir `k` ikilikli
sembolün tablosu `Bᵏ` değer içerir; `(a0, …, ak−1)` argümanının konumu
`a0 + B·a1 + B²·a2 + …`. Bağıntı değerleri `0`/`1`. Eksik tablo ya da değer 0 sayılır;
değerler `B` modülünde alınır.

`(alt …)` aynı biçimde tablolar içerir; yalnızca normatif sembollerin tabloları kullanılır.

### Denetim kuralları (`checkClaim`)

* `lemma`: ispat, kuramın bağlamında formülü çıkarır.
* `analogy`: aksiyomların her biri için sırayla bir `oblig` vardır; her biri, hedef
  kuramın bağlamında aksiyomun çevirisini çıkarır; model hedef kuramın modelidir.
* `refute`: ispat kaynak kuramda formülü çıkarır; model hedef kuramın modelidir ve
  formülün çevirisini yanlışlar.
* `verdict`: ispat formülü çıkarır; model kuramın modelidir; normatif tabloları
  değiştirilmiş model formülü yanlışlar.

## 6. Araçlar

```sh
lake exe hakem check BELGE.hkm…     # derlenmiş denetleyici (hızlı)
lake exe hakem cert BELGE.hkm AD     # belge ağacını Lean terimi olarak basar
python3 -I tools/corpus.py .         # corpus/*.hkm → Kulliyat/, iddialar ve çekirdek ispatları
./tools/hakem.sh                     # bütün iddialar: Lean çekirdeği + nanoda → KARAR.md
```

Derlenmiş denetleyici Lean derleyicisine güvenir. Kesin hüküm çekirdek hesabıdır:
`KARAR.md`'de `<belge>_holds : Doc.HoldsTree <belge>_tree`.

## 7. Uyum sınamaları

* `corpus/` — kabul edilmesi gereken belgeler.
* `corpus-bad/` — reddedilmesi gereken belgeler: yanlış ispat, yanlış etiketlenmiş
  normatif sembol, model olmayan karşı örnek.

Bağımsız bir uygulama bu iki klasörde aynı sonuçları vermelidir.

## 8. Sürüm 1'in sınırları

* Lemmalar yalnızca aynı belgede yeniden kullanılır. Belgeler arası içe aktarma
  (içerik özetiyle) yok.
* Arka plan yapıları (ℕ, ℤ, ℝ) dilde yok. Çekirdekte var (`Theory.withBackground`),
  dile bağlanmadı.
* Karşı örnekler sonludur.
* İspat araması yok; dil ispatları taşır, bulmaz.
