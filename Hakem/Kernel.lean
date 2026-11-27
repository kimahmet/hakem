import Hakem.Logic

/-!
# Hakem — çekirdek sözlük (v2)

Hükümlerin anlamı burada sabitlenir: kuram, analoji, metafor sertifikası, politika
hükmü. Hepsi `Hakem.Logic` dilindeki **veri** üzerine tanımlıdır. Disiplin
sayısına, büyüklüğüne ya da türüne bağlı değildir.

Bu sözlüğün davrandığını gösteren genel yasalar (aktarım, bileşim, metafor,
Hume yasası) `Challenge.lean`'de iddia olarak yazılıdır. Her olası girdi için bir
kez çekirdekte ispatlanırlar.
-/

variable {S S₁ S₂ : Signature}

/-- Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
`admissible`, standart matematik nesnelerine bağlanmak içindir (ör. "taşıyıcı ℕ'dir").
Bu bir Lean yüklemidir ve anlam tabanına girer. -/
structure Theory (S : Signature) where
  axioms     : List (Formula S)
  admissible : Structure S → Prop := fun _ => True

namespace Theory

/-- `M`, kuramın bir modelidir. -/
def Models (T : Theory S) (M : Structure S) : Prop :=
  T.admissible M ∧ ∀ φ ∈ T.axioms, M.Sat φ

/-- Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular. -/
def Entails (T : Theory S) (φ : Formula S) : Prop :=
  ∀ M, T.Models M → M.Sat φ

/-- Alt kuram: ek aksiyomlar. Kısmi analoji, alt kurama kurulan analojidir. -/
def extend (T : Theory S) (extra : List (Formula S)) : Theory S where
  axioms     := T.axioms ++ extra
  admissible := T.admissible

end Theory

/-- Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
söyler. Hedefin her modeli, `σ` ile okunduğunda kaynağın bir modelidir: kaynak
aksiyomlarının çevirileri hedefte gerekir. Hedefin en az bir modeli gösterilir;
yoksa aktarım boş yere doğru olurdu. -/
structure Analogy (A : Theory S₁) (B : Theory S₂) where
  σ         : SigMorph S₁ S₂
  adm       : ∀ M, B.Models M → A.admissible (σ.reduct M)
  preserves : ∀ φ ∈ A.axioms, B.Entails (σ.trF φ)
  model     : Structure S₂
  model_ok  : B.Models model

/-- Metafor sertifikası. `glossary`, önerilen sözlüktür. `pf`/`pr` sözlüğün bağlayıcı
kısmını (çapaları) seçer. Kaynak, yalnızca çapalı sembollerle yazılmış bir `φ`
gerektirir. Hedefin bir modelinde `φ`'nin sözlükteki çevirisi çöker. Bu durumda,
çapaları bu sözlükle aynı olan hiçbir analoji yoktur. -/
structure Refutation (A : Theory S₁) (B : Theory S₂)
    (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool) (glossary : SigMorph S₁ S₂) where
  φ      : Formula S₁
  thm    : A.Entails φ
  only   : φ.onlySyms pf pr = true
  cex    : Structure S₂
  cex_ok : B.Models cex
  fails  : ¬ cex.Sat (glossary.trF φ)

/-- Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve
ampirik) semboller olduğu gibi kalır. -/
def Structure.reinterp (M : Structure S)
    (g : (f : S.Fn) → (Fin (S.fnArity f) → M.D) → M.D)
    (h : (r : S.Rel) → (Fin (S.relArity r) → M.D) → Prop) : Structure S where
  D    := M.D
  dflt := M.dflt
  fn   := fun f => if S.fnRole f = .normatif then g f else M.fn f
  rel  := fun r => if S.relRole r = .normatif then h r else M.rel r

/-- Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
o dünyada **yalnızca normatif sembollerin** yeniden yorumlanmasıyla `φ`'nin çöktüğü
bir alternatif gösterilir. Olgular sabitken sonucu değer seçimi belirler. -/
structure PolicyVerdict (T : Theory S) (φ : Formula S) where
  entails  : T.Entails φ
  world    : Structure S
  world_ok : T.Models world
  g        : (f : S.Fn) → (Fin (S.fnArity f) → world.D) → world.D
  h        : (r : S.Rel) → (Fin (S.relArity r) → world.D) → Prop
  alt_adm  : T.admissible (world.reinterp g h)
  fails    : ¬ (world.reinterp g h).Sat φ

/-! ## Arka plan: standart matematik nesneleri -/

/-- İki yapı arasında izomorfizma: ters çevrilebilir, bütün yorumları koruyan eşleme. -/
structure Structure.Iso (M N : Structure S) where
  to    : M.D → N.D
  inv   : N.D → M.D
  left  : ∀ x, inv (to x) = x
  right : ∀ y, to (inv y) = y
  dflt  : to M.dflt = N.dflt
  fn    : ∀ f v, to (M.fn f v) = N.fn f (fun i => to (v i))
  rel   : ∀ r v, M.rel r v ↔ N.rel r (fun i => to (v i))

/-- Arka planlı kuram. `ι` standart sözlüğü (ör. ℕ'nin sayıları, sırası, fonksiyonları)
disiplin sözlüğüne gömer. Kabul edilebilir yapılar, standart kısmı `B`'ye izomorf
olanlardır. Böylece "sayı" gerçekten sayıdır. -/
def Theory.withBackground {S₀ : Signature} (axioms : List (Formula S)) (ι : SigMorph S₀ S)
    (B : Structure S₀) : Theory S where
  axioms     := axioms
  admissible := fun M => Nonempty ((ι.reduct M).Iso B)
