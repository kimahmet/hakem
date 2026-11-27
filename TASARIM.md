# Hakem — tasarım belgesi (v3)

Bu belge hakemin neyi, nasıl ve hangi güvenle denetlediğini anlatır. Prototipten
(arşiv: `archive/prototip-0.3/`) öğrenilenleri de kayda geçirir.

## 0. Temel kural: "kanıtlı" sözcüğünü kim söyleyebilir

Hakemde bir iddianın durumu yalnızca üç biçimde yazılabilir.

| Durum | Kim yazar | Anlamı |
|---|---|---|
| **BİÇİMSEL KABUL** | Yalnızca yargıç (`tools/Judge.lean`) | Belirli bir Lean ifadesi, belirli denetimlerden geçti (§5). |
| **RET** | Yalnızca yargıç | Denetimlerden en az biri geçmedi; gerekçe yazılır. |
| **OKUMA (denetlenmedi)** | İnsan ya da yapay zekâ | İfadenin doğal dildeki okuması. Doğruluğu Lean'in hüküm alanı dışındadır. |

Hiçbir insan ya da yapay zekâ metni, bir iddia için "kanıtlandı" diyemez.
Söyleyebileceği tek şey "`KARAR.md`'de şu ifade biçimsel kabul aldı"dır. İfadenin
dünyayı doğru anlattığı ise ayrı bir iddiadır ve okuma katmanına aittir.

Bu kural prototipteki bir hatadan çıktı. Prototipi raporlarken "kanıtlı" sözcüğünü,
Lean'in kabul ettiği ifadeden daha güçlü iddialar için kullandım (§1).

## 0.5 v2: disiplinler veri, yasalar bir kez

v1 çekirdeği her disiplin için elle yazılmış Lean tipleri istiyordu (`Theory`'nin
`Str` alanı, `Question`'ın `E`/`N` tipleri). Bu, her yeni disiplinin hakemin dışında
yeniden yazılması demekti ve ölçeklenmez. v2'de:

* Bir disiplin **veridir**: bir sözlük (`Signature`) ve birinci mertebe aksiyomlar
  (`Formula` listesi). İnsan ya da yapay zekâ yazabilir.
* Bir analoji **veridir**: kaynak sözlüğün her sembolünün hedefte hangi terime ya da
  formüle gittiği (`SigMorph`). Bu eşleme sözlüğün (çapaların) kendisidir.
* Öncül türü **hesaplanır**: her sembolün rolü (`tanim`/`ampirik`/`normatif`)
  sözlükte bir kez yazılır; bir önermenin normatif olup olmadığı içindeki
  sembollerden hesaplanır (`Formula.descriptive`).
* Genel yasalar **bir kez** ve her olası girdi için çekirdekte ispatlanır:
  tatmin koşulu, aktarım, bileşim, metafor sağlamlığı, Hume yasası.
* **Sertifikalar da veridir.** İspatlar doğal çıkarım terimleri (`Proof`), karşı
  örnekler ve tanık dünyalar sonlu yapılardır (`FinStructure`). Denetleyicilerin
  (`check`, `evalB`) sağlamlığı bir kez ispatlanır. Sonra bir sertifika yalnızca çekirdek
  hesabıyla (`decide +kernel`) denetlenir; taktik, ayrıştırıcı ve derleyici devreye girmez.
* **Standart matematik.** Arka planlı kuramlarda (`Theory.withBackground`) kabul
  edilebilir modeller, standart kısmı belirli bir yapıya (ℕ, ℤ; ileride ℝ) izomorf
  olanlardır. Standart yapıdaki gerçekler kalkülüste hipotez olarak kullanılabilir
  (`calculus_sound_bg`), ya da akıl yürütme doğrudan standart taşıyıcıda yapılabilir
  (`entails_of_std`).

Yeni bir disiplin, analoji ya da politika argümanı eklemek çekirdeğe hiçbir şey
eklemez. Yalnızca veri ve o verinin ispat yükümlülükleri eklenir.

## 0.6 v3: dil

v2'de disiplinler Lean tanımı olarak yazılıyordu; her yeni disiplin Lean bilen biri
tarafından hakemin içine yazılmalıydı. v3'te disiplinler, analojiler, iddialar ve
sertifikalar **Hakem dilinde** yazılır (`DIL.md`). Hakem bu dili okur, anlamını
çekirdekte sabitler ve denetler. Denetleyicinin sağlamlığı (`checkTree_sound`,
`checkDoc_sound`) her olası belge için bir kez ispatlıdır. Bir belgeyi kabul etmek için
hakeme hiçbir şey eklenmez; belge ağacı çekirdekte hesaplanır.

Lean'de elle yazılmış disiplin örnekleri `archive/v2-lean-cases/` altındadır. Hakem
disiplin modeli yazmaz; modelleri dilde başkaları yazar.

İlerleme döngüsü: bir belgede ispatlanmış lemmalar sonraki ispatlarda `(ax AD)` ile
kullanılır (Mathlib'deki gibi). Belgeler arası içe aktarma sürüm 1'de yoktur.

## 1. Prototipten öğrenilenler

### 1.1 Söylenen ile Lean'in kabul ettiği arasındaki fark

| Prototip raporunda söylenen | Lean'in gerçekte kabul ettiği | Fark |
|---|---|---|
| "Analoji, mal korunuyorsa, marjinal değer azalıyorsa ve fiyat aradaysa geçerli" | Piyasa modelinin adım tanımı, termodinamik modelin harfi harfine kopyasıydı. Piyasa modelinde ne fayda ne fiyat vardı. | Koşullar yalnızca yorumdaydı; hiçbiri biçimsel hipotez değildi. **En büyük aşırı iddia.** |
| "Scarf döngüsünde hiçbir ölçü analojiyi kurtaramaz" | Üç durumlu bir döngüde kesin artan ölçü yoktur. | Scarf ekonomisi biçimselleştirilmemişti; bağ yalnızca addaydı. |
| "İkinci yasa kanıtlı" | İki tamsayılı oyuncak modelde, `min e1 e2` ölçüsü her tanımlı adımda artar. | `min`'in entropiyle sıralama-eşdeğerliği yalnızca yorumdaydı. |
| "Politika sonucu bir normatif öncüle dayanır ve öncül gereklidir" | Normatif öncüllerin *hepsi birlikte* atılınca sonuç düşer. | "Her biri gerekli" değil. Tanık dünya ampirik koordinatları da değiştirebiliyordu (kutu tipçe ayrılmamıştı). |
| "Hesap: 181,36 $" | `#eval` sonucuydu: derlenmiş kod, çekirdek değil. | Çekirdekte yalnızca "≥ 150 $" sınırı denetlenmişti. |
| "Çekirdek bağımsız uygulanabilir" | Yalnızca `lake build` ve `#print axioms` çalıştırılmıştı. | Lean belgelerine göre bu yalnızca dürüst hatalara karşı korur. Bağımsız çekirdek çalıştırılmamıştı. |
| Etiketler (`tanim`/`ampirik`/`normatif`) | Her öncül kendi etiketini kendisi beyan ediyordu. | `tanim` etiketli bir öncül (`scc = …`) aslında öncül kılığında bir tanımdı. |

### 1.2 Yapısal dersler

1. **Boşluk (vacuity).** Prototipte çelişkili öncüllü bir argüman da "geçerli"
   sayılıyordu. Hiç modeli olmayan bir kurama yapılan aktarım da "geçerli"ydi.
   v1'de her analoji sertifikası hedef kuramın bir modelini, her politika hükmü de
   değer seçimlerinin tutarlılığını göstermek zorundadır.
2. **Çapa.** Sabit bir eşleme (her şeyi tek bir modele gönderen) neredeyse her
   yorumu "geçerli" kılar. Analojinin içeriği, neyin neye karşılık geldiğini
   söyleyen çapalardadır. Hüküm disiplin çiftine değil, çapaya bağlıdır. Örnek:
   bankacılık, "enerji = mevduat" çapasıyla metafordur, "enerji = mevduat − kredi"
   çapasıyla analojidir (`analogy_physics_banking_net`).
3. **Yön.** Hedef kuram, kaynağın diliyle okunur (`red : B.Str → A.Str`). Kaynağın
   görmediği koordinatlar hedefte serbest kalabilir.
4. **Etiket değil, tip.** Olgu ile değer ayrımı, öncül başına etiketle değil,
   koordinat tipleriyle yapılmalıdır. Olgu kısıtı (`E → Prop`) değer koordinatını
   tipçe göremez.
5. **Tanım öncül değildir.** Tanımlar Lean `def`'idir (muhafazakâr genişleme).
   Bu yüzden "tanım" türü öncül listesinden çıktı.
6. **Dördüncü tür: idealleştirme.** "İki cisim", "tamsayı enerji", "aynı tercihler"
   gibi seçimler ne ampiriktir ne normatif; modelleme seçimidir. Bunlar biçimsel
   önerme değildir (model ile dünya arasındaki ilişkiyi anlatırlar). Bu yüzden her
   model tanımının docstring'inde zorunlu `İDEALLEŞTİRME` alanı olarak tutulur ve
   rapora girer.
7. **Güven tanımlarda, teoremlerde değil.** Lean'de bir teoremin güvene ihtiyacı
   yoktur; çekirdek onu denetler. Güvenilmesi gereken, iddiaların *anlamını*
   sabitleyen tanımlardır. Bu yüzden "küçük çekirdek" hedefi, küçük bir **tanım
   sözlüğü** hedefidir. Çekirdek teoremleri ne kadar uzun olursa olsun güven
   tabanını büyütmez.

### 1.3 Biçimselleştirilemeyen ve ertelenen

- **Scarf döngüsü.** Scarf (1960) ekonomisinde (Leontief tercihleri, üç mal)
  tâtonnement sürekli zamanda kapalı yörüngede döner. Tamsayı ayrıklaştırmalarını
  denedim: işaret kuralı ve toplamı koruyan kural. Altı başlangıç noktasının
  hepsinde fiyatlar dışa sarmallanıp sıfıra ulaştı; döngü oluşmadı. Bu bir
  simülasyon sonucudur (`python`), ispat değildir. Sadık bir biçimselleştirme gerçek
  sayılar ve ODE gerektirir, yani Mathlib (§7).

## 2. Güven mimarisi

```
 güvenilmeyen ─┐
               │  Solution/…      ispatlar (insan ya da yapay zekâ)
               ▼
 güvenilen ──── Challenge.lean    iddia metinleri (insanlar yazar, ispatsız)
               Hakem/Cases/…      disiplin verisi: sözlükler, aksiyomlar, analojiler
               Hakem/Kernel.lean  hüküm sözlüğü: kuram, analoji, metafor, politika hükmü
               Hakem/Logic.lean   dil: terim, formül, yapı, çeviri, indirgeme
               tools/Judge.lean   yargıç
               L0: Lean çekirdeği + bağımsız çekirdekler
```

| Katman | İçerik | Güven gerekir mi | Kim denetler |
|---|---|---|---|
| L0 | Lean'in tip kuramı ve çekirdekleri | Evet | Beş bağımsız uygulama: Lean C++, lean4lean, nanoda (Rust), con-leche, con-ron. con-leche'nin `False` kabul etmediği makine-denetimli olarak ispatlıdır (Lean belgelerine göre). |
| L1 | `Hakem/Logic.lean`, `Hakem/Kernel.lean` tanımları | Evet | İnsan okuması. Bu dosyalarda teorem yok. `Hakem/Calculus.lean` ve `Hakem/Finite.lean` denetleyicileri yalnızca sağlamlık iddialarının anlam tabanına girer; bir denetleyicinin sağlam olduğu ispatlıysa onu okumak gerekmez. |
| L2 | `Hakem/Cases/*` (ve gelecekte her disiplin verisi) | Evet | İnsan okuması: OKUMA ve İDEALLEŞTİRME. Asıl risk buradadır (§7). |
| L3 | `Challenge.lean` ifadeleri | Evet | İnsan okuması: ifade, okumanın söylediğini mi söylüyor? |
| L4 | `Solution/*` ispatları | **Hayır** | Çekirdekler. |
| L5 | `tools/Judge.lean`, `tools/*.sh` | Evet | İnsan okuması ve öz-sınama (`tools/selftest.sh`). |

Bir ispatçının (yapay zekâ dahil) yapabileceği her şey L4'tedir. L4'ün hiçbir
parçası güven tabanına girmez.

## 3. Çekirdek sözlük ve her kavramın gerekçesi

| Kavram | Neden var |
|---|---|
| `Signature` (semboller, ikilikler, **roller**) | Bir disiplinin sözlüğü. Rol sembole aittir; olgu/değer ayrımı buradan hesaplanır. |
| `Term`, `Formula` | Disiplin önermelerini veri olarak yazmak. Birinci mertebe, eşitlikli, de Bruijn değişkenli. `dflt` terimi ikilik dışı argümanları tam tanımlı kılar (çeviri her zaman tanımlıdır). |
| `Structure`, `eval`, `Sat` | Anlam: bir dünya ve önermenin o dünyada doğruluğu. |
| `Formula.onlySyms`, `descriptive` | Bir önermenin hangi sembolleri kullandığını hesaplamak: çapa denetimi ve öncül türü. |
| `subst`, `liftSubst` | Çevirinin tanımı için ikame. |
| `SigMorph`, `trT`, `trF` | Analoji sözlüğü ve önermelerin çevirisi. Sembol terime/formüle gidebilir: "enerji ↦ mevduat − kredi" gibi türetilmiş karşılıklar mümkündür. |
| `SigMorph.reduct` | Hedef dünyayı kaynağın diliyle okumak. Analojinin anlamsal yüzü. |
| `SigMorph.comp` | Analoji zincirleri. |
| `AgreeOn` | Bir sözlüğün çapalı kısmı; metafor sertifikası buna göre tanımlanır. |
| `Theory` (aksiyomlar, `admissible`) | Disiplin kuramı. `admissible`, standart matematik nesnelerine bağlanmak içindir; bir Lean yüklemidir ve anlam tabanına girer. |
| `Models`, `Entails`, `extend` | Model, gerektirme, alt kuram (kısmi analoji). |
| `Analogy` | Sertifika: sözlük, kabul edilebilirliğin korunması, aksiyom çevirilerinin hedefte gerektirilmesi, hedefin bir modeli. |
| `Refutation` | Metafor sertifikası: kaynağın çapalı bir teoremi ve onu çiğneyen hedef modeli. |
| `Structure.reinterp` | Yalnızca normatif sembollerin yorumunu değiştirmek. |
| `PolicyVerdict` | Politika hükmü: gerektirme, öncülleri sağlayan bir dünya ve o dünyada yalnızca normatif sembolleri değiştirince sonucun çöktüğü bir alternatif. |

**Genel yasalar** (`Challenge.lean`, bölüm I; her girdi için):

1. `satisfaction`: `M ⊨ σ(φ) ↔ reduct σ M ⊨ φ`.
2. `transfer`: `A ⊨ φ → B ⊨ σ(φ)` her analoji için.
3. `source_consistent`: analoji varsa kaynağın modeli vardır.
4. `compose_exists`: analojiler bileşir; sözlük `σ ∘ τ`.
5. `refutation_sound`: karşı örnek, çapaları aynı her analojiyi dışlar.
6. `hume_law`: bütün aksiyomları betimsel olan kuramdan hiçbir politika hükmü yoktur.
7. `verdict_same_facts`: her politika hükmünde alternatif dünya betimsel sembollerde
   asıl dünyayla aynıdır; tartışma normatiftir.
8. `calculus_sound`: denetimden geçen ispat verisi gerektirmeyi gösterir.
9. `finite_sat_iff`, `finite_models_sound`, `finite_refutes_sound`: sonlu yapıda hesap
   ile doğruluk örtüşür.
10. `refutation_of_data`, `verdict_of_data`: metafor sertifikası ve politika hükmü
    tamamen veriden kurulur.
11. `iso_sat`, `background_sound`, `calculus_sound_bg`, `entails_of_std`: standart
    matematik nesneleri üzerine akıl yürütme.

Bu yasalar kabul aldıktan sonra, yeni bir veri girişi için kalan tek iş kendi ispat
yükümlülükleridir: bir analoji için aksiyom çevirilerinin hedefte gerektiği, bir metafor
için karşı örneğin model olduğu, bir politika hükmü için gerektirme ve alternatif dünya.

## 4. Külliyat

Külliyat, dilde yazılmış belgelerdir; dilin uyum sınamasıdır, amaç değildir.

- `corpus/korunum.hkm`: fizik ve bankacılık sözlükleri; bir lemma (`stepNet`), onu
  `(ax stepNet)` ile kullanan bir analoji, iki elemanlı karşı örnekli bir metafor.
- `corpus/politika.hkm`: normatif `Ought` sembolüyle bir politika hükmü.
- `corpus-bad/`: reddedilmesi gereken belgeler.

Arka planlı (ℕ, ℤ) örnekler (karbonun sosyal maliyeti, termodinamik ↔ piyasa) Lean
düzeyinde `archive/v2-lean-cases/` altındadır; dil sürüm 1 arka plan yapılarını
desteklemez.

## 5. Yargıç: denetimler ve saldırılar

### 5.1 Her iddia için denetimler

1. `Challenge` ve `Solution`'da aynı adlı sabit vardır ve türleri **terim olarak** aynıdır.
2. İfadenin anlam tabanı (geçişli olarak dayandığı `Hakem.*`/`Challenge` tanımları)
   iki ortamda tür ve değer olarak aynıdır.
3. İspatın geçişli aksiyomları ⊆ {`propext`, `Quot.sound`, `Classical.choice`}.
4. `Solution`'ın tam dökümü (`leanexport`) bağımsız çekirdek nanoda'da hatasız
   yeniden denetlenir. İfade, nanoda'nın kendi yazıcısıyla gösterimsiz basılır.
5. Rapor her anlam tabanı tanımını, okumasını ve parmak izini listeler. İnsan
   incelemeleri parmak izine bağlanır: tanım değişirse inceleme geçersiz olur.

### 5.2 Bilinen saldırılar

| Saldırı | Karşılayan denetim | Sınanıyor mu |
|---|---|---|
| `sorry` / eksik ispat | Aksiyom listesi (`sorryAx`) | Evet: `SelfTest.Sorry` (aktarım yasası) |
| Yeni aksiyom | Aksiyom listesi | Evet: `SelfTest.Axiom` (Hume yasası) |
| Aynı ad, başka ifade | Terim karşılaştırması | Evet: `SelfTest.Statement` |
| Güvenilen veriyi (ör. bir belge ağacını) içe aktarmayıp aynı adlı, boşaltılmış bir sürüm tanımlamak | Anlam tabanı karşılaştırması (önsöz dışındaki her modül) | Evet: `SelfTest.Swap`. Bu sınama, yargıcın yalnızca `Hakem`/`Challenge` modüllerini saydığı bir hatayı yakaladı. |
| Yanlış ispat, yanlış etiketlenmiş normatif sembol, model olmayan karşı örnek (belge düzeyinde) | Denetleyici | Evet: `corpus-bad/` |
| `native_decide`, `implemented_by`, `extern` | Aksiyom listesi (`…_native…` aksiyomları) | Evet: `SelfTest.Native` |
| Özel gösterim/örnek ile ifadenin anlamını değiştirmek | İfade güvenilen ortamda basılır; çözümün gösterimi `Challenge`'a sızamaz | Hayır (sınama eklenmeli) |
| Çekirdeği atlayan meta-kod (denetlenmemiş bildirim eklemek) | Dökümün bağımsız çekirdekte baştan yeniden denetimi | Hayır (sınama eklenmeli) |
| Kötü niyetli `.olean` dosyaları, derleme sırasında kod çalıştırma | **Yerelde karşılanmıyor.** Linux'ta `lake comparator --paranoid` (bwrap sandbox, `.olean` yüklemez) | CI iş akışı yazıldı, çalıştırılmadı |
| Tüm çekirdeklerde ortak bir hata | Karşılanamaz (tip kuramının kendisi) | — |

Yerel yargıç `.olean` dosyalarını belleğe yükler. Bu yüzden saldırgan girdiye karşı
tek başına yeterli değildir. Saldırgan girdi için tek kabul yolu
`.github/workflows/hakem.yml` (Linux, sandbox, beş çekirdek) olmalıdır.

## 6. Çalıştırma

```sh
./tools/hakem.sh       # derle → döküm → nanoda → yargıç → KARAR.md
./tools/selftest.sh    # yargıç kötü çözümleri reddediyor mu
lake comparator --paranoid   # yalnızca Linux (bwrap); CI'da
```

## 7. Sınırlar ve açık sorunlar

0. **İspat araması.** Kalkülüs ispatları denetler, bulmaz. İspat verisi şimdilik elle
   ya da bir ispatçı (insan, yapay zekâ) tarafından yazılır. Bir arama aracı güven
   gerektirmez: çıktısı yine denetlenir.
0. **İfade gücü.** Birinci mertebe mantık. ℝ, analiz ve diferansiyel denklemler için
   arka plan yapısı olarak Mathlib nesneleri gerekir (ör. Scarf döngüsü). Çekirdek
   bağımlılıksız kalır; Mathlib tanımları ilgili iddiaların anlam tabanına girer.
0. **Seçkin öğe.** `dflt` terimi ve izomorfizmanın onu koruması teknik bir araçtır;
   arka plan yapısının seçkin öğesi (ℕ ve ℤ'de 0) bu yüzden sabittir.

1. **Sadakat (faithfulness).** Asıl kalan risk, anlam tabanındaki tanımların gerçek
   disiplini temsil edip etmediğidir. Lean bunu denetleyemez. Öneri: her tanım için
   birden çok bağımsız kurumun incelemesi, parmak izine bağlı ve imzalı olsun
   (`INCELEMELER/`, henüz yok). İfadeyi yazan ile inceleyen aynı taraf olmamalı.
2. **Parmak izi** şimdilik 64-bit yapısal özettir, kriptografik değildir. Dökümdeki
   bildirimin SHA-256 özetine geçilmeli.
3. **Mathlib.** Gerçek fizik ve ekonomi (gerçek sayılar, logaritmik entropi, ODE)
   Mathlib gerektirir. Öneri: çekirdek bağımlılıksız kalsın, modeller Mathlib
   kullanabilsin. Bu durumda Mathlib tanımları ilgili iddiaların anlam tabanına girer
   ve yargıç bunları listeler.
4. **Ters yön.** "Dağılım eşitse denge" henüz ispatlanmadı; yalnızca "denge ⇒ eşit"
   ispatlandı.
5. **Değer koordinatlarının seçimi.** Bir değer koordinatını `E`'ye koymak (yanlış
   tipleme) hâlâ mümkündür. Ama artık tek bir yerde (`Question`) ve okunabilir
   biçimde yapılır.
6. **İfade yazarlığı.** `Challenge.lean`'i kim yazar? Yapay zekâ ifade önerebilir,
   ama ifadeyi güvenilen tarafa almak bir insan kararıdır ve kayda geçmelidir.
7. **CI iş akışı** yazıldı ama çalıştırılmadı (uzak depo yok).
