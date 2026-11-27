import Hakem.Kernel

/-!
# Denge: termodinamik ve değişim piyasası

İki disiplin ayrı sözcüklerle tanımlanır. Termodinamikte süreç, Clausius
biçiminde entropiyle tanımlanır. Piyasada ticaret, gönüllülükle (yan ödeme ile
iki tarafın da razı olması) tanımlanır. Analojinin kurulabilmesi için ikisinin
aynı şey olduğu ispatlanmalıdır. Bu ispat iddia dosyasında değil, ispatlardadır.
-/

/-- OKUMA: korunan bir niceliğin iki parça arasındaki dağılımı. -/
structure Split where
  x1 : Int
  x2 : Int

/-- OKUMA: iki parça arasındaki fark (`x1 - x2`). -/
def Split.gap (p : Split) : Int := p.x1 - p.x2

/-- OKUMA: bu dağılımda iki parça da negatif değil. -/
def Split.Feasible (p : Split) : Prop := 0 ≤ p.x1 ∧ 0 ≤ p.x2

/-- OKUMA: `f` kesin içbükeydir. Ardışık artışlar kesin azalır.
Ayrık sürümdür. -/
def StrictlyConcave (f : Int → Int) : Prop :=
  ∀ x, f (x + 2) - f (x + 1) < f (x + 1) - f x

/-! ## Termodinamik -/

/-- OKUMA: iki cisimli sistem. İki cismin entropi fonksiyonu `S` aynıdır, `state`
enerji dağılımıdır.
İDEALLEŞTİRME: iki cisim, aynı madde; tamsayı enerji; entropi tamsayı değerli;
iş ve hacim yok, yalnızca ısı. -/
structure ThermoSys where
  S     : Int → Int
  state : Split

/-- OKUMA: Clausius ölçütü. `p`'den `q`'ya bir süreç mümkündür ancak ve ancak
enerji korunur, enerjiler negatif olmaz ve toplam entropi kesin artar. -/
def heatProcess (S : Int → Int) (p q : Split) : Prop :=
  q.x1 + q.x2 = p.x1 + p.x2 ∧ q.Feasible ∧ S p.x1 + S p.x2 < S q.x1 + S q.x2

/-- OKUMA: termodinamik denge. Hiçbir süreç mümkün değil. -/
def ThermoSys.Equilibrium (t : ThermoSys) : Prop :=
  ∀ q, ¬ heatProcess t.S t.state q

/-- OKUMA: termodinamik kuramı. Aksiyomlar: entropi kesin içbükeydir, yani ısı
sığası pozitiftir (termodinamik kararlılık); enerjiler negatif değildir. -/
abbrev Thermo : Theory where
  Str := ThermoSys
  Ax  := fun t => StrictlyConcave t.S ∧ t.state.Feasible

/-! ## Değişim piyasası -/

/-- OKUMA: iki tüccar. Mal için fayda fonksiyonları `u` aynıdır, `alloc` malın
dağılımıdır. Para yan ödeme olarak aktarılabilir; fayda parada doğrusaldır
(yarı-doğrusal fayda).
İDEALLEŞTİRME: tek mal; iki tüccar; aynı tercihler; tamsayı miktar ve para;
üretim yok. -/
structure Exchange where
  u     : Int → Int
  alloc : Split

/-- OKUMA: gönüllü ticaret. Mal korunur ve miktarlar negatif olmaz. Bir `t`
yan ödemesi vardır: 1. tüccar `t` alır, 2. tüccar `t` öder. Bu ödemeyle iki
tarafın hiçbiri kötüleşmez ve en az biri kesin iyileşir. -/
def voluntaryTrade (u : Int → Int) (p q : Split) : Prop :=
  q.x1 + q.x2 = p.x1 + p.x2 ∧ q.Feasible ∧
  ∃ t : Int, 0 ≤ u q.x1 - u p.x1 + t ∧ 0 ≤ u q.x2 - u p.x2 - t ∧
    (0 < u q.x1 - u p.x1 + t ∨ 0 < u q.x2 - u p.x2 - t)

/-- OKUMA: piyasa dengesi. Gönüllü ticaret kalmamıştır (Pareto-etkinlik). -/
def Exchange.Equilibrium (m : Exchange) : Prop :=
  ∀ q, ¬ voluntaryTrade m.u m.alloc q

/-- OKUMA: azalan marjinal fayda. -/
def DiminishingMarginalUtility (u : Int → Int) : Prop :=
  ∀ x, u (x + 2) - u (x + 1) < u (x + 1) - u x

/-- OKUMA: değişim piyasası kuramı. Tercihlere kısıt yoktur; yalnızca mevcut dağılım
negatif olmayan miktarlardan oluşur. -/
abbrev Market : Theory where
  Str := Exchange
  Ax  := fun m => m.alloc.Feasible

/-- OKUMA: azalan marjinal faydalı piyasalar (alt kuram). -/
abbrev MarketDMU : Theory := Market.extend (fun m => DiminishingMarginalUtility m.u)

/-! ## Çapalar -/

/-- OKUMA: termodinamik gözlenebilirler. Sistem dengede mi; enerji farkı. -/
def thermoObs (t : ThermoSys) : Prop × Int := (t.Equilibrium, t.state.gap)

/-- OKUMA: piyasa gözlenebilirleri. Piyasa dengede mi; miktar farkı. -/
def marketObs (m : Exchange) : Prop × Int := (m.Equilibrium, m.alloc.gap)

/-- OKUMA: "dengedeyse dağılım eşittir (en çok bir birim fark)". -/
def EquilibriumIsEven (x : Prop × Int) : Prop := x.1 → -1 ≤ x.2 ∧ x.2 ≤ 1
