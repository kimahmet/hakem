# Analoji Denetçisi / Analogy Checker

[Türkçe](#türkçe) · [English](#english)

---

## Türkçe

### Vizyon

Disiplinler arası modeller için (bir matematik ispatı, bir fizik modeli, yeni bir
ekonomik düzen) bağımsız bir formel hakem. Benchmark değil, Lean gibi bir hakem.

Temel ilke: bir disiplinde kanıtlanmış bir sonuç başka bir disipline ancak
**yapıyı koruyan bir eşleme** (analoji) boyunca taşınabilir. Yapıyı korumayan
eşleme metafordur ve çekirdek onu reddeder.

Tasarım ilkeleri:

- **De Bruijn kriteri.** Analojiyi insan ya da yapay zekâ önerebilir. Öneren
  güvenilmeyen ispatçıdır. Hüküm küçük ve denetlenebilir bir çekirdeğindir.
- **Bağımsız hakemlik.** Çekirdek, farklı kuruluşların bağımsız olarak yeniden
  yazabileceği kadar küçüktür: `AnalojiDenetcisi/Kernel.lean`, yaklaşık 120 satır,
  bağımlılık yok.
- **Kaos ortadan kaldırılmaz, yeri belirlenir.** Ölçüm değerleri ve değer
  seçimleri çekirdeğin hüküm alanında değildir. Ama her argümanda açıkça
  etiketlenmeleri zorunludur. Sonuçlar koşulludur: "bu değer seçilirse sonuç şudur".

### Çekirdek

**I. Analoji**

| Kavram | Anlamı |
|---|---|
| `Model` | Durumlar, adımlar (dinamik), tamsayı bir ölçü. |
| `Model.Preserves M R` | Her adım ölçü üzerinde `R` ilişkisini sağlar. Korunum `(· = ·)`, ikinci yasa `(· < ·)`. |
| `Analogy A B` | `map : B.State → A.State`; adımları adımlara, ölçüyü ölçüye götürür. |
| `Analogy.transfer` | `A.Preserves R → B.Preserves R`. Tek aktarım teoremi. |
| `Model.restrict M P` | Yalnızca `P` adımlarını tutan alt model. Kısmi analoji, alt modele tam analojidir. |
| `Model.Equilibrium` | Hiçbir adımın mümkün olmadığı durum. |
| `Analogy.equilibrium_transfer` | `A`'daki görüntü dengedeyse `B` durumu dengededir. |

**II. Öncül türleri**

| Kavram | Anlamı |
|---|---|
| `Kind` | `tanim`, `ampirik` veya `normatif`. |
| `Premise W` | Adı, türü ve hangi olası dünyalarda (`W`) doğru olduğu. |
| `Argument W C` | Etiketli öncüller ve öncüllerden `C`'ye geçerli çıkarım. |
| `PolicyArgument W C` | Ek alan `hume`: tüm olgulara (tanım + ampirik) uyan ama `C`'yi sağlamayan bir dünya. |
| `PolicyArgument.not_facts_only` | Normatif öncülsüz bir politika argümanı kurulamaz. |

"Olandan olması gereken çıkmaz" kuralı tek bir alanla uygulanır. Bir politika
argümanı, normatif öncüller atıldığında sonucun düştüğünü bir tanık dünya ile
göstermek zorundadır. Bu tek alan iki şeyi birden kanıtlar: normatif öncül
vardır ve normatif öncül işe yarar, süs değildir. Tanık dünya, tartışmanın
nerede yattığını gösterir.

### Çekirdek neyi garanti eder

- Kabul edilen bir analoji boyunca taşınan her sonuç hedef modelde gerçekten
  geçerlidir.
- Yapıyı bozan bir eşleme (ör. kredi ile para yaratımına korunum taşımak) kabul
  edilmez. Reddin kendisi de ispatlanabilir (`¬ Nonempty (Analogy A B)`).
- Her politika sonucu en az bir açık normatif öncüle dayanır, ve bu öncül
  sonuç için gereklidir.
- Sayısal denetimler `decide +kernel` ile yalnızca Lean çekirdeğinde yapılır.
  Derleyiciye güvenilmez, `native_decide` kullanılmaz.

### Çekirdek neyi garanti etmez

- **Ölçüm sınırı.** Bir modelin dünyayı doğru betimlediğini garanti etmez.
  `ampirik` öncüllerin değerleri ölçümden gelir. Çekirdek yalnızca bunların
  görünür olmasını sağlar.
- **Değer seçimleri.** Hangi ρ'nun, hangi adalet ilkesinin doğru olduğuna hüküm
  vermez. Her seçim için koşullu sonucu verir.
- **Etiket dürüstlüğü.** Bir normatif öncülü `ampirik` diye etiketlemek
  mümkündür. Yine de `hume` tanığı, sonucu taşıyan öncülün hangisi olduğunu açığa
  çıkarır. Etiketin denetimi insan incelemesine kalır.
- **Model seçimi.** Hangi durum uzayının, hangi ölçünün seçileceği modelcinin
  işidir. Çekirdek yalnızca seçilen yapının korunup korunmadığını denetler.

### Örnekler (`AnalojiDenetcisi/Examples/`)

- **Physics, Accounting.** Enerji korunumu muhasebe virmanlarına taşınır.
- **Banking.** Fizikten tüm bankacılığa analoji reddedilir, çünkü kredi para
  yaratır. Virman alt modeline analoji geçerlidir. Sonuç: "virmanlar altında
  korunum" taşınır, "tüm adımlar altında korunum" taşınmaz.
- **Equilibrium.** Termodinamik denge (ikinci yasa) ile piyasa dengesi.
  - Analoji geçerlidir: mal korunuyorsa, marjinal değer azalıyorsa ve fiyat iki
    değerleme arasındaysa. Bu durumda refahın kesin artışı ve denge taşınır.
  - Metafor kalır: artan getiri durumunda (bu refah ölçüsüyle) ve Scarf tipi
    fiyat döngüsünde. Scarf döngüsünde hiçbir ölçü seçimi analojiyi kurtaramaz.
- **CarbonCost.** Karbonun sosyal maliyeti. Olgular aynıdır. ρ = %0,1 (Stern)
  seçilirse vergi ≥ 150 $/t (hesap: 181,36 $), ρ = %1,5 (Nordhaus) seçilirse
  vergi < 70 $/t (hesap: 64,22 $). `dispute_is_rho` teoremi, tartışmanın ρ'da
  yattığını gösterir. Zarar ve ufuk değerleri örnektir, tahmin değildir.

### Kurulum

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
```

### Yön

Yapıyı koruyan eşlemelerin doğal dili kategori teorisidir (Spivak'ın ologları,
AlgebraicJulia). `Analogy` bir model morfizmidir. Çekirdek şimdilik sade Lean 4
ile ve bağımlılıksız tutulmaktadır. Çekirdeğe giren her yeni kavram gerekçe ister.

---

## English

### Vision

An independent formal referee for interdisciplinary models: a mathematical
proof, a physical model, a new economic order. Not a benchmark, but a referee
in the way Lean is one.

Core principle: a result proven in one discipline may be carried to another
only along a **structure-preserving map** (an analogy). A map that does not
preserve structure is a metaphor, and the kernel rejects it.

Design principles:

- **De Bruijn criterion.** Humans or AI may propose analogies. The proposer is
  an untrusted prover. Judgment belongs to a small, auditable kernel.
- **Independent refereeing.** The kernel is small enough for other
  organizations to reimplement on their own: `AnalojiDenetcisi/Kernel.lean`,
  about 120 lines, no dependencies.
- **Chaos is not removed, it is located.** Measured values and value judgments
  are outside the kernel's jurisdiction. But every argument must label them
  explicitly. Results are conditional: "if this value is chosen, the result is this".

### Kernel

**I. Analogy**

| Concept | Meaning |
|---|---|
| `Model` | States, steps (dynamics), an integer measure. |
| `Model.Preserves M R` | Every step satisfies `R` on the measure. Conservation is `(· = ·)`, the second law is `(· < ·)`. |
| `Analogy A B` | `map : B.State → A.State`; it sends steps to steps and the measure to the measure. |
| `Analogy.transfer` | `A.Preserves R → B.Preserves R`. The single transfer theorem. |
| `Model.restrict M P` | Submodel that keeps only the `P` steps. A partial analogy is a full analogy to a submodel. |
| `Model.Equilibrium` | A state from which no step is possible. |
| `Analogy.equilibrium_transfer` | If the image of a `B` state is an equilibrium in `A`, the `B` state is an equilibrium. |

**II. Premise kinds**

| Concept | Meaning |
|---|---|
| `Kind` | `tanim` (definition), `ampirik` (empirical) or `normatif` (normative). |
| `Premise W` | Name, kind, and in which possible worlds (`W`) it holds. |
| `Argument W C` | Labelled premises and a valid inference from them to `C`. |
| `PolicyArgument W C` | Extra field `hume`: a world that satisfies all facts (definitions + empirical) but not `C`. |
| `PolicyArgument.not_facts_only` | A policy argument without a normative premise cannot be built. |

The rule "no ought from an is" is enforced by a single field. A policy argument
must exhibit a witness world showing that the conclusion fails once the
normative premises are dropped. This one field proves two things: a normative
premise exists, and it does real work rather than being decorative. The witness
world shows where the disagreement lies.

### What the kernel guarantees

- Every result carried along an accepted analogy really holds in the target model.
- A structure-breaking map is not accepted. An example is transferring
  conservation to money creation by credit. The rejection itself can be proven
  (`¬ Nonempty (Analogy A B)`).
- Every policy conclusion rests on at least one explicit normative premise, and
  that premise is necessary for the conclusion.
- Numerical checks run with `decide +kernel`, in the Lean kernel only. The
  compiler is not trusted, and `native_decide` is not used.

### What the kernel does not guarantee

- **The measurement boundary.** It does not guarantee that a model describes
  the world correctly. The values of `ampirik` premises come from measurement.
  The kernel only makes them visible.
- **Value choices.** It does not rule on which ρ or which principle of justice
  is right. It gives the conditional result for each choice.
- **Honest labelling.** A normative premise can be mislabelled as `ampirik`.
  Even so, the `hume` witness exposes which premise carries the conclusion.
  Checking the labels is left to human review.
- **Model choice.** Choosing the state space and the measure is the modeller's
  job. The kernel only checks whether the chosen structure is preserved.

### Examples (`AnalojiDenetcisi/Examples/`)

- **Physics, Accounting.** Energy conservation transfers to accounting transfers.
- **Banking.** The analogy from physics to all of banking is rejected, because
  credit creates money. The analogy to the transfers-only submodel holds. Result:
  "conservation under transfers" carries over, "conservation under all steps" does not.
- **Equilibrium.** Thermodynamic equilibrium (the second law) and market equilibrium.
  - The analogy holds when the good is conserved, marginal value diminishes, and
    the price lies between the two valuations. Then strict welfare increase and
    equilibrium carry over.
  - It remains a metaphor under increasing returns (for this welfare measure)
    and under a Scarf-type price cycle. In the Scarf cycle, no choice of measure
    can rescue the analogy.
- **CarbonCost.** The social cost of carbon. The facts are the same in both
  arguments. With ρ = 0.1% (Stern) the tax is ≥ $150/t (computed: $181.36).
  With ρ = 1.5% (Nordhaus) the tax is < $70/t (computed: $64.22). The theorem
  `dispute_is_rho` shows that the disagreement lies in ρ. The damage and
  horizon values are illustrative, not estimates.

### Build

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
```

### Direction

The natural language of structure-preserving maps is category theory (Spivak's
ologs, AlgebraicJulia). An `Analogy` is a model morphism. For now, the kernel
stays in plain Lean 4 with no dependencies. Every new kernel concept must be justified.
