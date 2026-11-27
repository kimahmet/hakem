import Hakem.Models.Transitions

/-!
# Korunum: fizik, muhasebe, bankacılık

Her tanımın docstring'inde iki bölüm var: OKUMA, tanımın neyi temsil ettiğini;
İDEALLEŞTİRME, gerçek disiplinden neyin atıldığını söyler. Bunlar Lean tarafından
denetlenmez. İnsan incelemesine açıktır ve hakem raporunda olduğu gibi gösterilir.
-/

/-! ## Fizik -/

/-- OKUMA: iki cisim ve enerjileri.
İDEALLEŞTİRME: yalnızca iki cisim var; enerji tamsayı; dış dünya yok (yalıtık sistem). -/
structure Bodies where
  e1 : Int
  e2 : Int

/-- OKUMA: enerji alışverişi. Bir cisim `a` kadar verir, öteki `a` kadar alır.
`a` her işaretten olabilir. -/
def energyExchange (p q : Bodies) : Prop :=
  ∃ a : Int, q.e1 = p.e1 - a ∧ q.e2 = p.e2 + a

/-- OKUMA: toplam enerji. -/
def totalEnergy (p : Bodies) : Int := p.e1 + p.e2

/-- OKUMA: yalıtık iki cisimli sistemde enerji alışverişlerinin kuramı. -/
abbrev Physics : Theory := transitions Bodies energyExchange

/-! ## Muhasebe -/

/-- OKUMA: iki hesaplı defter (kasa, banka).
İDEALLEŞTİRME: iki hesap; tamsayı tutarlar; yalnızca hesaplar arası virman. -/
structure Ledger where
  kasa  : Int
  banka : Int

/-- OKUMA: kasa ile banka arasında virman. -/
def ledgerTransfer (p q : Ledger) : Prop :=
  ∃ a : Int, q.kasa = p.kasa - a ∧ q.banka = p.banka + a

/-- OKUMA: toplam bakiye. -/
def balance (p : Ledger) : Int := p.kasa + p.banka

/-- OKUMA: iki hesaplı defterde virmanların kuramı. -/
abbrev Accounting : Theory := transitions Ledger ledgerTransfer

/-! ## Bankacılık -/

/-- OKUMA: bir bankanın iki mevduat hesabı ve kredi defteri.
İDEALLEŞTİRME: tek banka; iki mevduat; kredi geri ödemesi, faiz ve nakit çekimi yok. -/
structure Bank where
  mevduat1 : Int
  mevduat2 : Int
  kredi    : Int

/-- OKUMA: mevduat hesapları arasında virman. Kredi değişmez. -/
def bankTransfer (p q : Bank) : Prop :=
  ∃ a : Int, q.mevduat1 = p.mevduat1 - a ∧ q.mevduat2 = p.mevduat2 + a ∧ q.kredi = p.kredi

/-- OKUMA: kredi açma. Banka `a > 0` kredi verir ve bunu borçlunun hesabına mevduat
olarak yazar. Para yaratımı budur. -/
def bankLoan (p q : Bank) : Prop :=
  ∃ a : Int, 0 < a ∧ q.mevduat1 = p.mevduat1 + a ∧ q.mevduat2 = p.mevduat2 ∧
    q.kredi = p.kredi + a

/-- OKUMA: bankanın izinli adımları: virman ya da kredi açma. -/
def bankStep (p q : Bank) : Prop := bankTransfer p q ∨ bankLoan p q

/-- OKUMA: toplam mevduat (geniş para). -/
def deposits (p : Bank) : Int := p.mevduat1 + p.mevduat2

/-- OKUMA: net pozisyon. Mevduat eksi kredi; bilançonun iki yakası. -/
def netPosition (p : Bank) : Int := p.mevduat1 + p.mevduat2 - p.kredi

/-- OKUMA: bankacılık kuramı (virman ve kredi). -/
abbrev Banking : Theory := transitions Bank bankStep

/-- OKUMA: adım bir virmandır. Kısmi analojide alt kuramı seçer. -/
def isTransfer (p : Bank × Bank) : Prop := bankTransfer p.1 p.2
