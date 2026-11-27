/-!
# Hakem — çekirdek sözlük (v1)

Bu dosya hakemin **hüküm sözlüğüdür**. Dosyada iki tür içerik vardır.

* **Tanımlar** (`structure`, `def`). İddiaların ne *anlama* geldiğini bunlar
  sabitler. Güvenilen ve insanlarca okunması gereken tek kısım budur.
* **Teoremler.** Bunlar güven gerektirmez. Lean çekirdeği ve bağımsız çekirdekler
  (nanoda, lean4lean, con-leche, con-ron) tarafından yeniden denetlenirler.

Bağımlılık yok. Tasarım gerekçeleri `TASARIM.md` dosyasında.

## A. Kuram, yorum, aktarım
Bir disiplin bir **kuram** olarak verilir: bahsettiği yapılar (`Str`) ve bu
yapıların uyduğu aksiyomlar (`Ax`). Analoji, hedef kuramın her modelini kaynak
kuramın diliyle okuyan bir **yorumdur** (`Interp`). Hedef modelleri kaynak
aksiyomlarına gider. Neyin neye karşılık geldiği **çapalarla** (`Anchors`) açıkça
yazılır. Çapasız bir yorum boş olabilir: örneğin her şeyi tek bir modele eşleyen
sabit bir eşleme. Hüküm her zaman bir çapa listesine görelidir.

## B. Olgu ve değer
Bir politika sorusunda dünyalar iki koordinat tipine ayrılır: ampirik (`E`) ve
normatif (`N`). Olgular yalnızca `E` üzerine kısıt koyabilir; bunu tip sistemi
zorlar. Tanımlar öncül değildir; Lean tanımı olarak girerler ve elenebilirler.
Bir politika hükmü (`Verdict`), olgular sabit tutulup yalnızca normatif koordinat
değiştiğinde sonucun döndüğünü göstermek zorundadır.
-/

universe u v w

/-! ## A. Kuram, yorum, aktarım -/

/-- Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir. -/
structure Theory where
  Str : Type u
  Ax  : Str → Prop

namespace Theory

/-- `φ` kuramın teoremidir: her modelde doğrudur. -/
def Thm (T : Theory.{u}) (φ : T.Str → Prop) : Prop :=
  ∀ s, T.Ax s → φ s

/-- Alt kuram: ek aksiyom `P`. Kısmi analoji, alt kurama kurulan tam analojidir. -/
abbrev extend (T : Theory.{u}) (P : T.Str → Prop) : Theory.{u} where
  Str := T.Str
  Ax  := fun s => T.Ax s ∧ P s

end Theory

/-- Yorum: `B`'nin her yapısı `A`'nın diliyle okunur ve `B` modelleri `A` modellerine gider. -/
structure Interp (A : Theory.{u}) (B : Theory.{v}) where
  red : B.Str → A.Str
  ax  : ∀ s, B.Ax s → A.Ax (red s)

namespace Interp

variable {A : Theory.{u}} {B : Theory.{v}} {C : Theory.{w}}

def id (A : Theory.{u}) : Interp A A := ⟨fun s => s, fun _ h => h⟩

def comp (i : Interp A B) (j : Interp B C) : Interp A C :=
  ⟨fun s => i.red (j.red s), fun s h => i.ax _ (j.ax s h)⟩

/-- Aktarım: `A`'nın her teoremi, yorum boyunca `B`'nin teoremidir. -/
theorem transfer (i : Interp A B) {φ : A.Str → Prop} (h : A.Thm φ) :
    B.Thm (fun s => φ (i.red s)) :=
  fun s hs => h _ (i.ax s hs)

/-- Çapa: `B` modellerinde, yorum altında `A`'nın `oa` gözlenebiliri `B`'nin `ob`
gözlenebilirine eşittir. Örnek: "fizikteki enerji = muhasebedeki bakiye". -/
def Anchors {α : Sort w} (i : Interp A B) (oa : A.Str → α) (ob : B.Str → α) : Prop :=
  ∀ s, B.Ax s → oa (i.red s) = ob s

/-- Çapalı aktarım: `A`'da `oa` üzerine kanıtlanan iddia, `B`'de `ob` üzerine geçerlidir.
Sonuç `B`'nin kendi sözcükleriyle ifade edilir. -/
theorem transfer_anchored {α : Sort w} (i : Interp A B) {oa : A.Str → α} {ob : B.Str → α}
    (hc : i.Anchors oa ob) {ψ : α → Prop} (h : A.Thm (fun s => ψ (oa s))) :
    B.Thm (fun s => ψ (ob s)) :=
  fun s hs => by
    show ψ (ob s)
    rw [← hc s hs]
    exact h _ (i.ax s hs)

end Interp

/-- Analoji sertifikası: çapalı yorum ve `B`'nin bir modeli. Model şarttır:
modeli olmayan bir kurama yapılan aktarım boş yere doğrudur. -/
structure Analogy {α : Sort w} (A : Theory.{u}) (B : Theory.{v})
    (oa : A.Str → α) (ob : B.Str → α) extends Interp A B where
  anchors  : toInterp.Anchors oa ob
  model    : B.Str
  model_ax : B.Ax model

/-- Metafor sertifikası: `A`'da teorem olan çapalı bir iddia ve bu iddiayı çiğneyen
bir `B` modeli (karşı örnek). Okunabilir biçimi: "`A` şunu kanıtlar; `B`'nin şu
modelinde bu çöker; öyleyse bu çapa ile analoji kurulamaz". -/
structure Refutation {α : Sort w} (A : Theory.{u}) (B : Theory.{v})
    (oa : A.Str → α) (ob : B.Str → α) where
  claim  : α → Prop
  thm    : A.Thm (fun s => claim (oa s))
  cex    : B.Str
  cex_ax : B.Ax cex
  fails  : ¬ claim (ob cex)

/-- Karşı örnek, verilen çapalarla **her** yorumu dışlar. -/
theorem Refutation.no_interp {α : Sort w} {A : Theory.{u}} {B : Theory.{v}}
    {oa : A.Str → α} {ob : B.Str → α} (r : Refutation A B oa ob) (i : Interp A B) :
    ¬ i.Anchors oa ob :=
  fun hc => r.fails (i.transfer_anchored hc r.thm r.cex r.cex_ax)

theorem Refutation.no_analogy {α : Sort w} {A : Theory.{u}} {B : Theory.{v}}
    {oa : A.Str → α} {ob : B.Str → α} (r : Refutation A B oa ob) :
    ¬ Nonempty (Analogy A B oa ob) :=
  fun ⟨a⟩ => r.no_interp a.toInterp a.anchors

/-! ## B. Olgu ve değer -/

/-- Politika sorusu. `E`: ölçülen koordinatlar. `N`: seçilen (değer) koordinatlar.
`facts` yalnızca `E`'ye bakabilir; olgular değer seçimini tipçe göremez. -/
structure Question where
  E     : Type u
  N     : Type v
  facts : E → Prop

/-- Politika hükmü: "`norms` değer seçimleri yapılırsa, ölçüm aralığındaki her olgu için `C`".
* `norms_sat`: değer seçimleri tutarlıdır (yoksa hüküm boş yere doğru olurdu).
* `open_by_facts`: olgulara uyan bir dünyada başka bir değer seçimi `C`'yi bozar.
  "Olandan olması gereken çıkmaz" kuralı budur. -/
structure Verdict (Q : Question.{u, v}) (norms : Q.N → Prop) (C : Q.E → Q.N → Prop) where
  valid         : ∀ e, Q.facts e → ∀ n, norms n → C e n
  norms_sat     : ∃ n, norms n
  open_by_facts : ∃ e, Q.facts e ∧ ∃ n, ¬ C e n

/-- Tartışma normatiftir: aynı olgu durumunda yalnızca değer seçimi değişince sonuç döner. -/
theorem Verdict.dispute_is_normative {Q : Question.{u, v}} {norms : Q.N → Prop}
    {C : Q.E → Q.N → Prop} (vd : Verdict Q norms C) :
    ∃ e, Q.facts e ∧ ∃ n n', norms n ∧ C e n ∧ ¬ C e n' :=
  let ⟨e, he, n', hn'⟩ := vd.open_by_facts
  let ⟨n, hn⟩ := vd.norms_sat
  ⟨e, he, n, n', hn, vd.valid e he n hn, hn'⟩

/-- Olgularca belirlenen bir sonuç için politika hükmü kurulamaz. -/
theorem Verdict.not_from_facts {Q : Question.{u, v}} {norms : Q.N → Prop}
    {C : Q.E → Q.N → Prop} (vd : Verdict Q norms C) : ¬ ∀ e, Q.facts e → ∀ n, C e n :=
  fun h => let ⟨e, he, n, hn⟩ := vd.open_by_facts; hn (h e he n)
