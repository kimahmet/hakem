# Hakem

**Makine akıl yürütmesi için çekirdekte denetlenen bir yazı.**
**A kernel-checked writing system for machine reasoning.**

> Hakem, **kimahmet**'in vizyonudur ve onun yönlendirmesiyle geliştirilmiştir.
> Hakem is the vision of **kimahmet** and was developed under their direction.
> Kullanırken ya da geliştirirken lütfen atıf yapın / Please cite: [`CITATION.cff`](CITATION.cff) · [`NOTICE`](NOTICE)

**Makale / Paper: [Proof Is All You Need](paper/main.pdf)** ([PDF](paper/main.pdf) · [LaTeX](paper/main.tex) · [EN](paper/PAPER.md) · [TR](paper/MAKALE.md))

[Türkçe](#türkçe) · [English](#english)

---

## Türkçe

### Vizyon

Yapay zekânın icadı yazının icadından çok **abaküsün** icadına benzer. Abaküs insanlığa
ortak bir hesap kapasitesi ve hesabı doğrulamanın ortak bir yolunu verdi. Yazı başka
üç şey getirdi: kalıcı bir **kayıt**, tanışmayan taraflar arasında **iletişim** ve
bunların sonucunda **birikimli ilerleme**.

Hakem, yapay zekâ için o yazıyı kurmayı amaçlıyor. Modeller bu yazıda vardıkları
sonuçları kaydeder, birbirine iletir ve üzerine kurar. Her belgeyi, herkesin yeniden
çalıştırabildiği küçük bir hakem yargılar.

Bunun öncülü matematiktir. Hesap insan denetimini aşınca matematik Lean'e ve ortak
kütüphanesi Mathlib'e geçti. Ortaya çıkan döngü şöyledir: san, makinece denetlenmiş
ispat, kütüphane, yeni san. Hakem bu döngüyü taklit eder ve disiplinleri aşan
iddialara genişletir.

### Ne yapar

Hakem, **yapay zekânın özerk öğrenmesindeki denetimi otomatikleştirir.**

* Modeller **Hakem dilinde** belge yazar ([`DIL.md`](DIL.md)). Bir belge şunları
  içerebilir: rollü sözlükler (`tanim`, `ampirik`, `normatif`), kuramlar, lemmalar,
  disiplinler arası sözlükler, **analojiler**, **metafor çürütmeleri** ve **politika
  hükümleri**; bunların yanında ispatlar ve sonlu karşı modeller.
* Denetleyici her belgeyi kabul ya da reddeder. **Sağlamlığı her olası belge için Lean
  4 çekirdeğinde ispatlıdır** (`checkDoc_sound`).
* Özerk döngü (`tools/loop.py`) adayları insansız denetler. Kabul edilenleri içerik
  özetiyle külliyata alır. Her kararı doğrulanabilir bir ödülle (0/1) deftere yazar.

Çekirdek üç ilkeyi her girdi için **genel teorem** olarak taşır:

1. **Aktarım.** Bir sonuç başka bir disipline yalnızca yapıyı koruyan bir eşleme
   boyunca taşınır (`transfer`).
2. **Metafor.** Yapıyı bozan eşleme somut bir karşı modelle reddedilir
   (`refutation_sound`).
3. **Olandan olması gereken çıkmaz.** Normatif sembol içermeyen öncüllerden politika
   hükmü çıkmaz (`hume_law`). Tartışma her zaman normatif semboldedir
   (`verdict_same_facts`).

### Hızlı başlangıç

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
lake exe hakem check corpus/korunum.hkm     # belgeyi denetle
lake exe hakem json  corpus/politika.hkm    # ajanlar için JSON karar
python3 -I tools/loop.py .                  # inbox/ → corpus/ | rejected/, ledger.jsonl
python3 -I tools/corpus.py .                # külliyatı çekirdek sertifikalarına çevir
./tools/hakem.sh                            # bütün iddialar: Lean + nanoda → KARAR.md
./tools/selftest.sh                         # saldırılar ve kötü belgeler reddediliyor mu
```

### Güvence

"Kanıtlı" sözcüğünü yalnızca yargıç söyler. [`KARAR.md`](KARAR.md)'de **BİÇİMSEL
KABUL** alan bir iddia için şunlar sağlanmıştır:

* Lean çekirdeği ifadeyi kabul etti ve bağımsız çekirdek nanoda (Rust) dökümü yeniden
  denetledi.
* İfade, güvenilen metinle terim olarak aynı.
* İfadenin anlam tabanı iki tarafta aynı.
* İspat yalnızca standart aksiyomlara dayanıyor.

**Garanti edilmeyenler:**

* Modellerin gerçek disipline sadakati.
* Ölçülmüş değerler ve değer seçimleri.
* Doğal dildeki okumaların ifadeyi doğru anlatması.
* Yerel çalıştırmada saldırgan girdiye karşı tam güvence. Bunun için Linux'ta
  `lake comparator --paranoid` gerekir. Bu denetim CI'da her gönderimde çalışır ve altı çekirdeğin hepsi kabul ediyor.

### Depo

| Yol | Güven | İçerik |
|---|---|---|
| `Hakem/Logic.lean`, `Hakem/Kernel.lean` | güvenilen | Mantık ve hüküm sözlüğü |
| `Hakem/Calculus.lean`, `Hakem/Finite.lean` | sağlamlığı ispatlı | İspat ve sonlu model denetleyicileri |
| `Hakem/Lang/` | anlam güvenilen, denetim ispatlı | Hakem dili |
| `Challenge.lean` | güvenilen | İddia metinleri |
| `Solution/` | **güvenilmeyen** | İspatlar |
| `corpus/`, `Kulliyat/` | güvenilen | Kabul edilmiş belgeler ve ağaçları |
| `corpus-bad/` | — | Reddedilmesi gereken belgeler |
| `tools/` | güvenilen | Yargıç, CLI, özerk döngü |
| `paper/` | — | Makale (TR/EN) |
| `TASARIM.md`, `DIL.md` | — | Tasarım ve dil belirtimi |
| `archive/` | — | Önceki sürümler |

### Katkı

Belge yazmak, ikinci bir bağımsız denetleyici yazmak ya da çekirdeği geliştirmek için
bkz. [`CONTRIBUTING.md`](CONTRIBUTING.md). Lisans Apache-2.0'dır; türev çalışmalar
`NOTICE` dosyasını korumalıdır.

---

## English

### Vision

The invention of AI resembles the invention of the **abacus** more than that of writing.
The abacus gave humanity a shared capacity to compute and a shared way to check
computations. Writing brought three other things: a durable **record**,
**communication** between parties who never meet, and, as a result, **cumulative
progress**.

Hakem aims to build that writing for AI. In it, models record what they have
established, send it to each other, and build on it. Every document is judged by a small
referee that anyone can re-run.

The precedent is mathematics. When computation exceeded human checking, mathematics
moved to Lean and its shared library, Mathlib. The resulting loop is: conjecture,
machine-checked proof, library, new conjecture. Hakem imitates this loop and extends it
to claims that cross disciplines.

### What it does

Hakem **automates the oversight of autonomous AI learning.**

* Models write documents in the **Hakem language** ([`DIL.md`](DIL.md), in Turkish). A
  document can contain: vocabularies with symbol roles (definitional, empirical,
  normative), theories, lemmas, cross-discipline glossaries, **analogies**, **metaphor
  refutations** and **policy verdicts**, together with proofs and finite counter-models.
* The checker accepts or rejects each document. **Its soundness is proved in the Lean 4
  kernel for every possible document** (`checkDoc_sound`).
* The autonomous loop (`tools/loop.py`) checks candidates with no human in the loop. It
  files accepted documents into the corpus by content hash and records each verdict in a
  ledger with a verifiable 0/1 reward.

The kernel carries three principles as **general theorems** for every input:

1. **Transfer.** A result carries to another discipline only along a
   structure-preserving map (`transfer`).
2. **Metaphor.** A structure-breaking map is refuted by a concrete counter-model
   (`refutation_sound`).
3. **No ought from is.** No policy verdict follows from premises without normative
   symbols (`hume_law`). The dispute always lies in the normative symbols
   (`verdict_same_facts`).

### Quick start

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
lake exe hakem check corpus/korunum.hkm     # check a document
lake exe hakem json  corpus/politika.hkm    # JSON verdict for agents
python3 -I tools/loop.py .                  # inbox/ → corpus/ | rejected/, ledger.jsonl
python3 -I tools/corpus.py .                # turn the corpus into kernel certificates
./tools/hakem.sh                            # all claims: Lean + nanoda → KARAR.md
./tools/selftest.sh                         # are attacks and bad documents rejected?
```

### Assurance

Only the judge says "proven". A claim with **BİÇİMSEL KABUL** (formal acceptance) in
[`KARAR.md`](KARAR.md) satisfies the following:

* Lean's kernel accepted the statement, and the independent kernel nanoda (Rust)
  re-checked the export.
* The statement is identical, as a term, to the trusted text.
* The statement's meaning base is identical on both sides.
* The proof uses only the standard axioms.

**Not guaranteed:**

* Faithfulness of models to the real discipline.
* Measured values and value choices.
* That natural-language readings describe their statements correctly.
* Full protection against adversarial input in local runs. That requires
  `lake comparator --paranoid` on Linux. This runs in CI on every push, and all six kernels accept.

### Contributing

To write documents, build an independent second checker, or extend the kernel, see
[`CONTRIBUTING.md`](CONTRIBUTING.md). Licensed under Apache-2.0; derivative works must
retain `NOTICE`.
