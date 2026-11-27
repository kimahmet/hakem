# Hakem: Makine Akıl Yürütmesi İçin Çekirdekte Denetlenen Bir Yazı

### Yapay zekânın özerk öğrenmesindeki denetimin disiplinler arası otomatikleşmesi

**kimahmet** (vizyon, yönlendirme) — uygulama Claude (Anthropic) yardımıyla geliştirilmiştir

*Taslak, Kasım 2026. Aşağıda ✓ ile işaretli her teknik iddia, [`KARAR.md`](../KARAR.md)
dosyasında biçimsel kabul almış adlı bir Lean teoremine karşılık gelir. Bu kabulün tam
olarak ne anlama geldiği §6'da yazılıdır.*

---

## Özet

Yapay zekânın icadı yazının icadından çok abaküsün icadına benzer. Abaküs insanlığa
ortak bir hesap kapasitesi ve hesabı doğrulamanın ortak bir yolunu verdi. Yazının
yaptığı başkaydı: ortak ve kalıcı bir kayıt, hiç tanışmayan insanlara sonuç iletmenin
bir yolu ve bunların sonucunda birikimli ilerleme. Matematik bu makalenin ilgilendiği
geçişi zaten yaşadı. İspatlar insanların denetleyebileceği sınırı aşınca alan Lean
gibi ispat yardımcılarına geçti. Mathlib gibi kütüphaneler de insanların ve
programların birlikte genişlettiği, makinece denetlenen ortak bir kayda dönüştü.

**Hakem**, bunun matematik dışındaki karşılığını, yani yapay zekâ için "yazıyı" kurma
denemesidir. Hakem küçük bir dildir. Modeller bu dilde şunları yazar:

* tipli sözlüklü kuramlar: her sembol tanımsal, ampirik ya da normatiftir;
* disiplinler arası sözlükler;
* iddialar: lemmalar, analojiler, metafor çürütmeleri, politika hükümleri;
* sertifikalar: doğal çıkarım ispatları ve sonlu karşı modeller.

Bir denetleyici her belgeyi kabul ya da reddeder. Denetleyicinin sağlamlığı, her olası
belge için bir kez, Lean 4 çekirdeğinde ispatlanmıştır. Kabul edilmiş lemmalar sonraki
ispatlarda yeniden kullanılabilir; bu, ilk ilerleme döngüsüdür. Makinece okunur bir
karar ve bir defter, kabulü doğrulanabilir bir ödül sinyaline çevirir. Böylece özerk
öğrenmenin denetiminin insan gerektirmeyen kısmı otomatikleşir.

Çekirdek üç ilkeyi kodlar. (1) Bir disiplinde kanıtlanmış bir sonuç başka bir
disipline ancak yapıyı koruyan bir eşleme boyunca taşınabilir. (2) Yapıyı bozan bir
eşleme metafordur ve somut bir karşı modelle çürütülebilir. (3) Normatif sembol
içermeyen öncüllerden hiçbir politika ("olması gereken") sonucu çıkmaz (Hume yasası).
Bunlar uzlaşı değil, genel teoremlerdir.

## 1. Vizyon

### 1.1 Abaküs ve yazı

Abaküs, ortak hesap kapasitesi ile ortak bir doğrulama mekanizmasının birleşimidir.
Herkes yeniden hesaplayıp boncukların tutup tutmadığını görebilir. Bugünün yapay
zekâ sistemleri bu anlamda abaküse benzer: kapasiteleri muazzam ve ortaktır, ama
doğrulama yereldir ve duruma göre yapılır.

Yazının eklediği şey daha fazla hesap değildi. Yazı üç şey ekledi:

* **kayıt**: sonuçlar, onları üreten hesaptan uzun yaşar;
* **iletişim**: sonuçlar hiç tanışmayan taraflar arasında dolaşır;
* **birikim**: yeni sonuçlar kayıtlı olanların üzerine kurulur.

Projenin tezi şudur: yapay zekâ aynı katmana muhtaçtır. Modellerin vardıkları sonuçları
kaydettiği, başka modellere ilettiği ve üzerine kurduğu ortak bir yazılı biçim
gereklidir; bu biçimin hakemini de herkes yeniden çalıştırabilmelidir.

### 1.2 Öncül olarak matematik

Matematik, hesabın insan denetimini aştığı eşiği çoktan geçti. Verilen yanıt hesaba
güvenmek olmadı. Sonuçlar biçimsel bir dilde yazıldı, küçük ve güvenilen bir çekirdekle
denetlendi ve ortak bir kütüphanede biriktirildi. Hakem'in taklit ettiği döngü budur:
san, makinece denetlenmiş ispat, kütüphane, yeni san. Hakem bu döngüyü disiplinleri
aşan iddialara genişletir: fizik, muhasebe, ekonomi, politika.

### 1.3 Tasarım ilkeleri

* **De Bruijn kriteri.** İnsan ya da yapay zekâ, herkes önerebilir. Öneren
  güvenilmeyen ispatçıdır. Hüküm küçük ve denetlenebilir bir çekirdeğindir.
* **Bağımsız hakemlik.** Güvenilen kısım, başka kurumların yeniden yazabileceği kadar
  küçük olmalıdır. Hakem, birden çok bağımsız uygulaması olan Lean çekirdeğini kullanır
  ve kendi güvenilen sözlüğünü küçük tutar.
* **Kaos ortadan kaldırılmaz, yeri belirlenir.** Ölçüm ve değer seçimleri çekirdeğin
  hüküm alanı dışındadır. Ama sembol rolü olarak açıkça görünmeleri zorunludur;
  sonuçlar bunlara bağlı, koşulludur.
* **"Kanıtlı" sözcüğü yargıcındır.** Yalnızca yargıç *biçimsel kabul* yazabilir; o da
  yalnızca belirli bir biçimsel ifade için. Doğal dildeki okumalar ayrıca gösterilir ve
  "denetlenmedi" diye işaretlenir.

## 2. Özerk öğrenmede denetim

Kendini geliştiren sistemlerin iyi çıktıyı kötüden ayıran bir sinyale ihtiyacı vardır.
Bu sinyal öğrenilmiş bir modelden geliyorsa oyuna getirilebilir. Sağlamlığı bir teorem
olan bir denetleyiciden geliyorsa, geriye tek bir soru kalır: *ifade*, kastettiğimiz
şeyi mi söylüyor? Hakem'in katkısı, böyle bir denetleyiciyi saf matematikten daha
geniş bir iddia sınıfı için kullanılabilir kılmaktır:

* **Analojiler.** "A disiplinindeki bu sonuç, bu sözlükle B disiplininde de geçerlidir."
* **Metaforlar.** "Bu sözlük yapıyı korumaz; işte B'nin onu bozan bir dünyası."
* **Politika hükümleri.** "Açıkça normatif olan bu öncüller altında bu politika
  çıkar; olgular tek başına bunu belirlemez."

Ortaya çıkan döngü şudur:

```
 öneren modeller ──▶ inbox/*.hkm ──▶ hakem json ──▶ kabul? ──▶ corpus/ (içerik özeti)
        ▲                                 │                          │
        └────── ödül 0/1, gerekçeler ◀────┴────── ledger.jsonl ◀─────┘
                                             sonraki belgeler lemmaları kullanır
```

`tools/loop.py` bu döngüyü içinde insan olmadan çalıştırır. Her karar, SHA-256 içerik
özeti ve 0/1 ödülle `ledger.jsonl` defterine eklenir. Kabul edilen belgeler külliyata
girer. `tools/corpus.py` onları çekirdek sertifikalarına çevirir.

## 3. Mantık

Disiplinler veridir. Bir **sözlük**, fonksiyon ve bağıntı sembollerini ikilikleri ve
**rolleriyle** (`tanim`, `ampirik`, `normatif`) listeler. Formüller eşitlikli birinci
mertebedir ve de Bruijn indisleri kullanır. Bir **yapı**, bir taşıyıcı ve yorumlardan
oluşur. Bir **kuram** aksiyomların listesidir; isteğe bağlı olarak kabul edilebilir
yapılar sınıfı da içerir.

**Sözlük eşlemesi olarak analoji.** Bir sözlük σ, kaynağın her sembolünü hedefte bir
terime ya da formüle gönderir; örneğin "enerji ↦ mevduat − kredi". Bir hedef dünya M,
*indirgeme* σ(M) ile kaynağın diliyle okunur.

* **Tatmin koşulu** ✓ `satisfaction`: `M ⊨ σ(φ) ⇔ σ(M) ⊨ φ`.
* **Analoji sertifikası** `Analogy A B`: A'nın her aksiyomunun çevirisini B gerektirir.
  B'nin bir modeli de vardır; böylece aktarım boş değildir.
* **Aktarım** ✓ `transfer`: `A ⊨ φ ⇒ B ⊨ σ(φ)`.
* **Bileşim** ✓ `compose_exists`: analojiler zincirlenir; zincirin sözlüğü, sözlüklerin
  bileşimidir.
* **Boş olmama** ✓ `source_consistent`: bir analoji varsa kaynak kuramın da modeli vardır.

**Metafor sertifikası.** Bir metafor, kaynaktan bir φ teoremi ve σ(φ)'nin çöktüğü bir
hedef modeliyle belgelenir.

* ✓ `refutation_sound`: böyle bir sertifika, sertifikanın çapaladığı sembollerde σ ile
  aynı olan **her** analojiyi dışlar.

**Olgu ve değer.** `reinterp` yalnızca normatif sembollerin yorumunu değiştirir. T'de φ
için bir **politika hükmü** üç parçadan oluşur: T ⊨ φ; T'nin tamamını sağlayan bir
dünya; ve o dünyadan yalnızca normatif sembollerde ayrılan, φ'nin çöktüğü bir
alternatif.

* ✓ `hume_law`: T'nin bütün aksiyomları betimselse (hiçbirinde normatif sembol yoksa),
  hiçbir politika hükmü yoktur.
* ✓ `verdict_same_facts`: her hükümde iki dünya bütün betimsel sembollerde aynıdır;
  sonuç birinde doğru, ötekinde yanlıştır. Tartışma normatiftir.

Bir formülün normatif olup olmadığı sembollerinden *hesaplanır*
(`Formula.descriptive`). Hiçbir zaman beyan edilmez.

## 4. Sertifikalar veridir

**İspat kalkülüsü.** `Proof`, doğal çıkarım için bir terim dilidir (∧ ∨ → ∀ ∃ = ve
dışlanan orta). `infer` bir ispatın neyi ispatladığını hesaplar.

* ✓ `calculus_sound`: `check T.axioms φ p = true ⇒ T ⊨ φ`.

**Sonlu modeller.** `FinStructure`'ın taşıyıcısı `Fin (n+1)`'dir, yorumları
hesaplanabilirdir.

* ✓ `finite_sat_iff`, ✓ `finite_models_sound`, ✓ `finite_refutes_sound`: sonlu
  yapılarda, kapalı formüller için hesap ile doğruluk örtüşür.
* ✓ `refutation_of_data`, ✓ `verdict_of_data`: metafor sertifikaları ve politika
  hükümleri tamamen veriden kurulur.

**Standart matematik.** Arka planlı bir kuramda kabul edilebilir modeller, standart
kısmı ℕ ya da ℤ gibi sabit bir yapıya izomorf olanlardır.

* ✓ `iso_sat`, ✓ `background_sound`, ✓ `calculus_sound_bg`, ✓ `entails_of_std`:
  sayılarla akıl yürütme doğrudan standart taşıyıcı üzerinde yapılabilir.

Bunlar kabul aldıktan sonra bir sertifika yalnızca çekirdek hesabıyla
(`decide +kernel`) denetlenir. Taktik, ayrıştırıcı ya da derleyici devreye girmez.

## 5. Dil

Bir Hakem belgesi, S-ifadelerinin bir listesidir. Belirtimi
[`DIL.md`](../DIL.md) dosyasındadır:

```lisp
(hakem 1)
(sig phys (fn E 1 ampirik) (rel Exch 2 tanim))
(theory Physics phys (ax cons (all (all (imp (Exch v0 v1) (= (E v0) (E v1)))))))
(sig bank (fn Dep 1 ampirik) (fn Net 1 ampirik) (rel Tr 2 tanim) (rel Cr 2 tanim))
(theory Banking bank (ax trNet …) (ax crNet …) (ax crMoney …) …)
(lemma stepNet Banking (all (all (imp (or (Tr v0 v1) (Cr v0 v1)) (= (Net v0) (Net v1))))) İSPAT)
(morph net phys bank (fn E (Net p0)) (rel Exch (or (Tr p0 p1) (Cr p0 p1))))
(analogy physicsToBanking Physics Banking net (model 2 …) (oblig cons (ax stepNet)))
(refute depositsMetaphor Physics Banking dep (all …) (ax cons) (model 2 …))
```

**Anlam.** `Doc.HoldsTree`, belgenin bütün iddialarının `Claim.Holds` anlamında doğru
olduğunu söyler.

* ✓ `checkTree_sound`, ✓ `checkDoc_sound`: denetleyicinin kabul ettiği her belge
  söylediğini söyler. Bu, dilin temel teoremidir ve bütün belgeler için bir kez
  ispatlanmıştır.

**Güven zinciri.** Zincir metin → ağaç → iddialar → karardır. Çekirdeğin dışında
çalışan tek adım ilkidir: yaklaşık 40 satırlık bir okuyucu. Herkes bu okuyucuyu yeniden
yazıp ağaçları karşılaştırabilir. Bu ayrımı bir bulgu doğurdu: çekirdekte
`String.toList` indirgemesi karakter başına yaklaşık 0,1 saniye sürerken, bir belge
ağacının denetimi belge başına yaklaşık 2 saniye sürer.

**Külliyat** (✓ `korunum_holds`, ✓ `politika_holds`). İki uyum belgesi:
* enerji korunumu "enerji ↦ net pozisyon" sözlüğüyle bankacılığa taşınır;
* "enerji ↦ mevduat" sözlüğü çürütülür, çünkü kredi para yaratır;
* normatif öncülünün normatif olduğu hesaplanan bir politika hükmü.

Üç kötü belge reddedilir: yanlış ispat, ampirik diye yanlış etiketlenmiş bir normatif
sembol ve model olmayan bir "karşı örnek".

## 6. Biçimsel kabulün anlamı

Yargıç (`tools/Judge.lean`, `tools/hakem.sh`) bir iddiayı ancak şunların hepsi
sağlanınca kabul eder:

1. Lean'in çekirdeği iddiayı kabul eder ve döküm, Rust ile yazılmış bağımsız bir
   çekirdek olan nanoda'da yeniden denetlenir.
2. Güvenilen `Challenge.lean`'deki ifade ile güvenilmeyen `Solution`'daki ispatın
   ifadesi *terim olarak* aynıdır.
3. İfadenin dayandığı her tanım (*anlam tabanı*) iki tarafta aynıdır.
4. İspat yalnızca `propext`, `Quot.sound` ve `Classical.choice` aksiyomlarını kullanır.

Şu anki durum: **21 / 21 iddia kabul**. nanoda 61.454 bildirimi yeniden denetledi.

Kabul şunları **göstermez**:

* bir okumanın ifadesini doğru anlattığını;
* bir modelin gerçek disipline sadık olduğunu;
* ölçülmüş değerlerin ya da değer seçimlerinin doğru olduğunu;
* yerel çalıştırmanın saldırgan girdiye dayanıklı olduğunu. Bunun için Linux'ta
  sandbox ve birden çok çekirdekle `lake comparator --paranoid` gerekir. Bu denetim CI'da
  her gönderimde çalışır. İlk çalıştırmada (27 Kasım 2026) altı çekirdeğin hepsi kabul etti:
  Lean paranoid, lean4lean, nanoda, con-leche, con-ron ve Lean'in varsayılan çekirdeği.

## 7. Saldırgan sınama

Bir öz-sınama, yargıca saldırı biçimli girdiler verir. Her biri beklenen gerekçeyle
reddedilmelidir:

* yeni bir aksiyom;
* `sorry`;
* aynı ad, başka bir ifade;
* güvenilen verinin aynı adlarla boşaltılmış yeniden tanımı;
* derleyiciye güvenen `native_decide`;
* yukarıdaki üç kötü belge.

Sınama, yargıçta iki gerçek kusur buldu; ikisi de düzeltildi:

* Aksiyom toplayıcı sessizce boş dönüyordu, çünkü `ConstantInfo.value?` teorem
  gövdelerini içermiyor. `sorry` içeren bir ispat geçebilirdi.
* Anlam tabanı yalnızca `Hakem`/`Challenge` modüllerini sayıyordu; bu yüzden
  boşaltılmış bir külliyat ağacı kabul edildi.

Bunları raporluyoruz, çünkü bir hakemin önceden düşünmesi gereken başarısızlık biçimi
tam da budur.

## 8. İlgili çalışmalar

* **Lean 4 ve çekirdeği**, bağımsız çekirdekler nanoda ve lean4lean, ve Lean FRO'nun
  güvenilmeyen ispatları yargılamak için geliştirdiği comparator. Hakem bunların hepsini
  kullanır ve üzerine kurulur.
* **Mathlib**: ortak, birikimli, makinece denetlenen kaydın; yani ilerleme döngüsünün
  öncülü.
* **Metamath ve de Bruijn kriteri**: bağımsız tarafların yeniden yazabileceği küçük bir
  denetleyici.
* **Kurum kuramı** (Goguen ve Burstall): tatmin koşulu ve kuram morfizmleri.
* **Disiplinler arası modellemeye kategorik yaklaşımlar** (Spivak'ın ologları,
  AlgebraicJulia): Hakem'in analojileri model morfizmleridir; kategorik bir
  formülasyon doğal uzun vadeli yöndür.
* **İspatçıları biçimsel denetleyicilere karşı eğitmek**: bu çalışmanın matematik
  dışına genişlettiği, doğrulanabilir ödül kullanımı.

## 9. Sınırlar ve gelecek çalışmalar

* **Sadakat.** Bir kuramın bir disiplini sadakatle temsil edip etmediği Lean ile
  denetlenemez. Tanım parmak izlerine bağlı, çoğul ve bağımsız insan incelemesi
  öneriyoruz.
* **Belgeler arası içe aktarma.** Sürüm 1, lemmaları yalnızca aynı belge içinde yeniden
  kullanır. Sıradaki adım içerik özetiyle içe aktarmadır; böylece külliyat bir
  kütüphaneye dönüşür.
* **Dilde arka plan yapıları.** Çekirdek ℕ/ℤ arka planlarını destekliyor, dil henüz
  desteklemiyor. ℝ ve analiz için Mathlib arka plan olarak gerekiyor.
* **İspat araması.** Dil ispatları taşır, bulmaz. Bir arama aracı güven gerektirmez,
  çünkü çıktısı denetlenir.
* **Bağımsız uygulamalar.** Başka bir tarafın `DIL.md`'ye ve uyum külliyatına karşı
  yazdığı ikinci bir okuyucu ve denetleyici.
* **Saldırgan ortamda kullanım.** comparator CI'da zaten çalışıyor. Sıradaki adım: imzalı
  kararlar ve yeniden üretilebilir derlemeler; böylece üçüncü taraflar bir kararı çevrimdışı
  doğrulayabilir.

## 10. Sonuç

Hakem, makine akıl yürütmesi için ortak bir yazılı biçime doğru küçük bir adımdır.
Modeller onu disiplinler arası sonuçları kaydetmek, iletmek ve üzerine kurmak için
kullanabilir. Her belgeyi, sağlamlığı bir teorem olan bir hakem yargılar; hakem de
yeniden kurulabilecek kadar küçük kalır.

---

*Depo: https://github.com/kimahmet/hakem — Apache-2.0. Lütfen `CITATION.cff` ile atıf
yapın ve `NOTICE` dosyasını koruyun.*
