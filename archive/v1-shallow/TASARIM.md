# Hakem — tasarım belgesi (v1)

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
               Hakem/Models/…     anlam tabanı: disiplin modelleri (OKUMA + İDEALLEŞTİRME)
               Hakem/Kernel.lean  hüküm sözlüğü: 11 tanım
               tools/Judge.lean   yargıç
               L0: Lean çekirdeği + bağımsız çekirdekler
```

| Katman | İçerik | Güven gerekir mi | Kim denetler |
|---|---|---|---|
| L0 | Lean'in tip kuramı ve çekirdekleri | Evet | Beş bağımsız uygulama: Lean C++, lean4lean, nanoda (Rust), con-leche, con-ron. con-leche'nin `False` kabul etmediği makine-denetimli olarak ispatlıdır (Lean belgelerine göre). |
| L1 | `Hakem/Kernel.lean` tanımları | Evet | İnsan okuması. 11 tanım (dosya, belgeleme ve teoremlerle birlikte 146 satır). |
| L2 | `Hakem/Models/*` tanımları | Evet | İnsan okuması: OKUMA ve İDEALLEŞTİRME. Asıl risk buradadır (§7). |
| L3 | `Challenge.lean` ifadeleri | Evet | İnsan okuması: ifade, okumanın söylediğini mi söylüyor? |
| L4 | `Solution/*` ispatları | **Hayır** | Çekirdekler. |
| L5 | `tools/Judge.lean`, `tools/*.sh` | Evet | İnsan okuması ve öz-sınama (`tools/selftest.sh`). |

Bir ispatçının (yapay zekâ dahil) yapabileceği her şey L4'tedir. L4'ün hiçbir
parçası güven tabanına girmez.

## 3. Çekirdek sözlük ve her kavramın gerekçesi

| Kavram | Neden var | Olmasaydı |
|---|---|---|
| `Theory` (Str, Ax) | Bir disiplini, bahsettiği yapılar ve aksiyomlarla verir. | Tek bir sabit modele bağlı kalınırdı (prototipteki `Model`); farklı disiplin türleri ifade edilemezdi. |
| `Theory.Thm` | "Disiplinde kanıtlanmış sonuç" ifadesinin tanımı. | Aktarılan şeyin ne olduğu tanımsız kalırdı. |
| `Theory.extend` | Kısmi analoji: alt kurama tam analoji. | Kısmi analoji için ayrı bir mekanizma gerekirdi. |
| `Interp` (red, ax) | Analojinin kendisi: hedef modelleri kaynak modellerine gider. | — |
| `Interp.id`, `Interp.comp` | Analojiler zincirlenebilir (fizik → muhasebe → …). Kategori yapısı (uzun vadeli yön). | Çok adımlı aktarım her seferinde yeniden ispatlanırdı. |
| `Interp.Anchors` | Neyin neye karşılık geldiğinin açık beyanı. | Sabit eşlemeler her analojiyi boş yere geçerli kılardı (§1.2-2). |
| `Analogy` | Sertifika biçimi: yorum, çapa ve hedefin bir modeli. | Modeli olmayan hedefe aktarım boş yere doğru olurdu. |
| `Refutation` | Metafor sertifikası: kaynakta teorem olan çapalı iddia ve onu çiğneyen hedef modeli. | Ret yalnızca "analoji bulunamadı" olurdu; okunabilir bir karşı örnek olmazdı. |
| `Question` (E, N, facts) | Olgu ile değerin tipçe ayrılması. | Etiket dürüstlüğüne güvenilirdi (§1.2-4). |
| `Verdict` | Politika hükmü: geçerlilik, değer tutarlılığı ve olguların hükmü açık bırakması. | "Olandan olması gereken" türetilebilirdi. |

Çekirdek teoremleri (`transfer`, `transfer_anchored`, `Refutation.no_interp`,
`Refutation.no_analogy`, `Verdict.dispute_is_normative`, `Verdict.not_from_facts`)
güven gerektirmez. Bu teoremler sözlüğün beklenen şekilde davrandığını gösterir.

**"Olandan olması gereken çıkmaz" kuralının biçimsel karşılığı:** Bir `Verdict Q norms C`
kurmak için, olgulara uyan bir `e` ve sonucu bozan bir değer seçimi `n` göstermek
gerekir. Çekirdek bundan, *aynı olgu durumunda* yalnızca değer seçimini değiştirerek
sonucun döndüğünü çıkarır (`dispute_is_normative`). Olgularca belirlenen bir sonuç
için `Verdict` kurulamaz (`not_from_facts`).

## 4. Örnek iddialar ve ne söyledikleri

Bütün iddialar `Challenge.lean`'de, durumları `KARAR.md`'dedir. Özet:

- **Korunum.** Fizik → muhasebe analojisi. Fizik → bankacılık(virman) analojisi.
  Fizik → bankacılık(kredi dahil) "enerji = mevduat" çapasıyla metafor, "enerji =
  net pozisyon" çapasıyla analoji.
- **Denge.** Termodinamik, Clausius ölçütüyle tanımlanır (süreç ⇔ toplam entropi
  artar). Piyasa, gönüllülükle tanımlanır (yan ödemeyle kimse kötüleşmez, biri
  iyileşir). İki tanımın örtüştüğü güvenilmeyen tarafta ispatlanır
  (`voluntary_iff_process`). Çapa: (dengede mi, fark).
  - **Koşul.** Kesin azalan marjinal fayda (termodinamikteki pozitif ısı sığasının
    karşılığı). Bu koşulla analoji kurulur ve "dengede dağılım eşittir" aktarılır.
  - **Metafor.** Koşul olmadan karşı örnek vardır: sabit marjinal fayda, `(0, 10)`
    dağılımı.
- **Karbonun sosyal maliyeti.** Ampirik kutu: zarar 0,9–1,1 $/t/yıl, süre 150–300
  yıl (örnek değerler). Pigou ölçütü altında ρ = %0,1 seçilirse kutunun tamamında
  vergi ≥ 120 $. ρ = %1,5 seçilirse < 75 $. Köşe değerleri yalnızca çekirdekte
  hesaplanır (`decide +kernel`). Kutunun içi monotonluk ispatlarıyla kapsanır.

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
| `sorry` / eksik ispat | Aksiyom listesi (`sorryAx`) | Evet: `SelfTest.Sorry` |
| Yeni aksiyom | Aksiyom listesi | Evet: `SelfTest.Axiom` |
| Aynı ad, başka ifade | Terim karşılaştırması | Evet: `SelfTest.Statement` |
| Modeli içe aktarmayıp aynı adlı boş bir model tanımlamak | Anlam tabanı karşılaştırması | Evet: `SelfTest.Swap` |
| `native_decide`, `implemented_by`, `extern` | Aksiyom listesi (`Lean.ofReduceBool` vb.) | Dolaylı (aksiyom denetimi) |
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
