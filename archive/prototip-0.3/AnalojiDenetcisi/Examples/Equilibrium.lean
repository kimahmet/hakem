import AnalojiDenetcisi.Kernel

/-!
# Termodinamik denge ↔ piyasa dengesi

Yapı türü: ikinci yasa / Lyapunov, yani `Preserves (· < ·)`. Her gerçek adım
ölçüyü kesin artırır. Sonuçları: döngü yoktur ve denge durağan durumdur.

- **Kaynak (termodinamik):** iki cisim arasında ısı akışı. Isı sıcaktan soğuğa
  akar ve aşma yoktur. Eşit ısı sığasında, sabit toplam enerjide entropi
  `min e1 e2` ile aynı sıralamayı verir. Bu yüzden ölçü olarak `min` kullanılır
  (sıralı, ordinal entropi).
- **Geçerli olduğu koşullar (değişim piyasası):** Aşağıdaki üç koşul birlikte
  sağlanırsa analoji kurulur ve ikinci yasa ile denge piyasaya taşınır.
  1. Mal korunur (üretim yok).
  2. Marjinal değer azalır, yani `v_i = K - q_i`. Bu yüzden gönüllü ticaret
     malı çok tutandan az tutana akıtır.
  3. Fiyat iki değerleme arasındadır (aşma yok).
- **Metafor kalan durum 1 (artan getiri):** Marjinal değer artınca ticaret
  büyük tutucuya akar. Bu durumda refah ölçüsü düşebilir ve analoji reddedilir.
- **Metafor kalan durum 2 (Scarf döngüsü):** Fiyat ayarlaması (tâtonnement)
  kapalı bir yörüngede döner. Hiçbir ölçü seçimiyle analoji kurulamaz.
  Burada Scarf (1960) örneğinin yalnızca döngü yapısı alınmıştır.
-/

/-! ## Kaynak: termodinamik -/

structure Bodies where
  e1 : Int
  e2 : Int

/-- Isı akışı: `a > 0` birim sıcaktan soğuğa, aşmadan. -/
def heatFlow (p q : Bodies) : Prop :=
  ∃ a : Int, 0 < a ∧
    ((2 * a ≤ p.e1 - p.e2 ∧ q.e1 = p.e1 - a ∧ q.e2 = p.e2 + a) ∨
     (2 * a ≤ p.e2 - p.e1 ∧ q.e1 = p.e1 + a ∧ q.e2 = p.e2 - a))

abbrev Thermo : Model where
  State   := Bodies
  Step    := heatFlow
  measure := fun p => min p.e1 p.e2

/-- İkinci yasa: her ısı akışı (ordinal) entropiyi kesin artırır. -/
theorem thermo_second_law : Thermo.Preserves (· < ·) := by
  rintro p q ⟨a, ha, ⟨hh, h1, h2⟩ | ⟨hh, h1, h2⟩⟩ <;>
    show min p.e1 p.e2 < min q.e1 q.e2 <;> omega

/-- Termodinamik denge: sıcaklık farkı en fazla bir birim (ayrık model). -/
theorem thermo_equilibrium_iff (p : Bodies) :
    Thermo.Equilibrium p ↔ (p.e1 - p.e2 ≤ 1 ∧ p.e2 - p.e1 ≤ 1) := by
  constructor
  · intro h
    constructor
    · by_cases hc : p.e1 - p.e2 ≤ 1
      · exact hc
      · exact (h ⟨p.e1 - 1, p.e2 + 1⟩ ⟨1, by decide, Or.inl ⟨by omega, rfl, rfl⟩⟩).elim
    · by_cases hc : p.e2 - p.e1 ≤ 1
      · exact hc
      · exact (h ⟨p.e1 + 1, p.e2 - 1⟩ ⟨1, by decide, Or.inr ⟨by omega, rfl, rfl⟩⟩).elim
  · rintro ⟨h1, h2⟩ t ⟨a, ha, ⟨hh, -, -⟩ | ⟨hh, -, -⟩⟩ <;> omega

/-! ## Geçerli analoji: azalan marjinal değerli değişim piyasası -/

/-- İki tüccarın bir maldaki elde tutuşu. Marjinal değer `K - q_i`. -/
structure Holdings where
  q1 : Int
  q2 : Int

/-- Gönüllü ticaret: mal düşük marjinal değerliden (çok tutan) yükseğe (az tutan)
akar. Fiyat iki değerleme arasında olduğu için aşma yoktur. -/
def voluntaryTrade (p q : Holdings) : Prop :=
  ∃ a : Int, 0 < a ∧
    ((2 * a ≤ p.q1 - p.q2 ∧ q.q1 = p.q1 - a ∧ q.q2 = p.q2 + a) ∨
     (2 * a ≤ p.q2 - p.q1 ∧ q.q1 = p.q1 + a ∧ q.q2 = p.q2 - a))

/-- Ölçü: ordinal refah. Simetrik içbükey faydada toplam fayda, sabit toplam
altında `min q1 q2` ile aynı sıralamayı verir. -/
abbrev Market : Model where
  State   := Holdings
  Step    := voluntaryTrade
  measure := fun p => min p.q1 p.q2

def thermoToMarket : Analogy Thermo Market where
  map := fun h => ⟨h.q1, h.q2⟩
  step_pres := by
    rintro p q ⟨a, ha, h⟩
    exact ⟨a, ha, h⟩
  measure_pres := fun _ => rfl

/-- Taşınan sonuç: her gönüllü ticaret refahı kesin artırır. -/
theorem market_second_law : Market.Preserves (· < ·) :=
  thermoToMarket.transfer thermo_second_law

/-- Taşınan sonuç: eşit dağılım bir piyasa dengesidir. -/
theorem market_equilibrium_example : Market.Equilibrium ⟨5, 5⟩ :=
  thermoToMarket.equilibrium_transfer ((thermo_equilibrium_iff ⟨5, 5⟩).2 ⟨by decide, by decide⟩)

/-! ## Metafor 1: artan marjinal değer (artan getiri) -/

/-- Marjinal değer elde tutuşla artınca ticaret malı büyük tutucuya akıtır. -/
def increasingReturnsTrade (p q : Holdings) : Prop :=
  ∃ a : Int, 0 < a ∧
    ((p.q1 ≤ p.q2 ∧ q.q1 = p.q1 - a ∧ q.q2 = p.q2 + a) ∨
     (p.q2 ≤ p.q1 ∧ q.q1 = p.q1 + a ∧ q.q2 = p.q2 - a))

abbrev IncreasingReturns : Model where
  State   := Holdings
  Step    := increasingReturnsTrade
  measure := fun p => min p.q1 p.q2

/-- Aynı refah ölçüsüyle analoji yok: `⟨1,2⟩ → ⟨0,3⟩` adımında refah düşer. -/
theorem no_analogy_thermo_increasingReturns :
    ¬ Nonempty (Analogy Thermo IncreasingReturns) := fun ⟨h⟩ =>
  have : min (1 : Int) 2 < min 0 3 :=
    h.transfer thermo_second_law ⟨1, 2⟩ ⟨0, 3⟩ ⟨1, by decide, Or.inl ⟨by decide, rfl, rfl⟩⟩
  by omega

/-! ## Metafor 2: Scarf döngüsü — hiçbir ölçüyle kurtarılamaz -/

/-- Üç fiyat durumu arasında kapalı yörünge: 0 → 1 → 2 → 0. -/
abbrev scarfStep (s t : Fin 3) : Prop := (s.val + 1) % 3 = t.val

abbrev ScarfCycle (m : Fin 3 → Int) : Model where
  State   := Fin 3
  Step    := scarfStep
  measure := m

/-- Hangi refah/potansiyel ölçüsü seçilirse seçilsin termodinamik analoji kurulamaz. -/
theorem no_analogy_thermo_scarf (m : Fin 3 → Int) :
    ¬ Nonempty (Analogy Thermo (ScarfCycle m)) := fun ⟨h⟩ =>
  have hp := h.transfer thermo_second_law
  have h01 : m 0 < m 1 := hp 0 1 (by decide : scarfStep 0 1)
  have h12 : m 1 < m 2 := hp 1 2 (by decide : scarfStep 1 2)
  have h20 : m 2 < m 0 := hp 2 0 (by decide : scarfStep 2 0)
  by omega
