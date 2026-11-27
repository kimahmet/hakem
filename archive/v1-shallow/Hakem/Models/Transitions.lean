import Hakem.Kernel

/-!
# Geçiş kuramları

Dinamik bir disiplini kurama çevirmenin bir yolu. Yapılar `(önce, sonra)`
çiftleridir. Aksiyom: bu çift izinli bir adımdır. "Her adımda X" türü yasalar
bu kuramın teoremleridir.
-/

/-- OKUMA: `step` ile izin verilen tek adımlık değişimlerin kuramı.
Bir model, izinli bir `(önce, sonra)` çiftidir. -/
abbrev transitions (σ : Type) (step : σ → σ → Prop) : Theory where
  Str := σ × σ
  Ax  := fun p => step p.1 p.2

/-- OKUMA: bir ölçünün adımdan önceki ve sonraki değeri. Çapa olarak kullanılır. -/
def beforeAfter {σ : Type} (m : σ → Int) : σ × σ → Int × Int :=
  fun p => (m p.1, m p.2)

/-- OKUMA: önce ve sonra değerleri eşit. Korunum budur. -/
def Unchanged : Int × Int → Prop :=
  fun x => x.1 = x.2
