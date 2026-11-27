import Hakem.Finite

/-!
# Sınama durumu: korunum (veri olarak)

İki disiplin sözlük ve aksiyom olarak yazılır. Üç sözlük önerisi sınanır.
İDEALLEŞTİRME: durumlar soyut; adım bir bağıntı; ölçü tek argümanlı bir fonksiyon.
-/

inductive PhysFn  | E      deriving DecidableEq
inductive PhysRel | Exch   deriving DecidableEq

/-- OKUMA: fizik sözlüğü. `E x`: x durumunun enerjisi (ampirik). `Exch x y`: x'ten y'ye
bir alışveriş adımı (tanım). -/
abbrev PhysSig : Signature where
  Fn := PhysFn
  Rel := PhysRel
  fnArity := fun _ => 1
  relArity := fun _ => 2
  fnRole := fun _ => .ampirik
  relRole := fun _ => .tanim

/-- OKUMA: korunum yasası. ∀x ∀y, Exch(x,y) → E(x) = E(y). -/
def conservationLaw : Formula PhysSig :=
  .all (.all (.imp (.rel .Exch (vec2 (.var 1) (.var 0)))
    (.eq (.app .E (vec1 (.var 1))) (.app .E (vec1 (.var 0))))))

/-- OKUMA: yalıtık sistem fiziği (tek aksiyom: korunum). -/
def Physics : Theory PhysSig where
  axioms := [conservationLaw]

inductive BankFn  | Dep | Net  deriving DecidableEq
inductive BankRel | Tr | Cr    deriving DecidableEq

/-- OKUMA: bankacılık sözlüğü. `Dep x`: toplam mevduat; `Net x`: mevduat eksi kredi
(ampirik). `Tr x y`: virman; `Cr x y`: kredi açma (tanım). -/
abbrev BankSig : Signature where
  Fn := BankFn
  Rel := BankRel
  fnArity := fun _ => 1
  relArity := fun _ => 2
  fnRole := fun _ => .ampirik
  relRole := fun _ => .tanim

/-- OKUMA: ∀x ∀y, R(x,y) → F(x) = F(y). -/
def bankPreserves (R : BankRel) (F : BankFn) : Formula BankSig :=
  .all (.all (.imp (.rel R (vec2 (.var 1) (.var 0)))
    (.eq (.app F (vec1 (.var 1))) (.app F (vec1 (.var 0))))))

/-- OKUMA: ∀x ∀y, Cr(x,y) → ¬ Dep(x) = Dep(y). Kredi mevduatı değiştirir. -/
def creditCreatesMoney : Formula BankSig :=
  .all (.all (.imp (.rel .Cr (vec2 (.var 1) (.var 0)))
    (.not (.eq (.app .Dep (vec1 (.var 1))) (.app .Dep (vec1 (.var 0)))))))

/-- OKUMA: bankacılık kuramı. Virman mevduatı ve net pozisyonu korur; kredi net pozisyonu
korur, mevduatı değiştirir. -/
def Banking : Theory BankSig where
  axioms := [bankPreserves .Tr .Dep, bankPreserves .Tr .Net, bankPreserves .Cr .Net,
             creditCreatesMoney]

/-- OKUMA: adım = virman ya da kredi. -/
def anyStep : Formula BankSig :=
  .or (.rel .Tr (vec2 (.var 0) (.var 1))) (.rel .Cr (vec2 (.var 0) (.var 1)))

/-- OKUMA: sözlük "enerji = mevduat, alışveriş = her banka adımı". -/
def glossaryDeposits : SigMorph PhysSig BankSig where
  fnMap := fun _ => .app .Dep (vec1 (.var 0))
  relMap := fun _ => anyStep

/-- OKUMA: sözlük "enerji = net pozisyon, alışveriş = her banka adımı". -/
def glossaryNet : SigMorph PhysSig BankSig where
  fnMap := fun _ => .app .Net (vec1 (.var 0))
  relMap := fun _ => anyStep

/-- OKUMA: sözlük "enerji = mevduat, alışveriş = yalnızca virman" (kısmi analoji). -/
def glossaryTransfers : SigMorph PhysSig BankSig where
  fnMap := fun _ => .app .Dep (vec1 (.var 0))
  relMap := fun _ => .rel .Tr (vec2 (.var 0) (.var 1))

/-! ## İspat verisi -/

/-- OKUMA: "her adım = virman ya da kredi" (iki değişkenli, x = 1, y = 0). -/
def netStep : Formula BankSig :=
  .or (.rel .Tr (vec2 (.var 1) (.var 0))) (.rel .Cr (vec2 (.var 1) (.var 0)))

/-- OKUMA: bankacılık aksiyomlarından "her adım net pozisyonu korur" çevirisinin
doğal çıkarım ispatı. Veridir; Lean taktiği içermez. -/
def netProof : Proof BankSig :=
  .allI (.allI (.impI netStep
    (.orE (.hyp 0)
      (.impE (.allE (.var 0) (.allE (.var 1) (.hyp 3))) (.hyp 0))
      (.impE (.allE (.var 0) (.allE (.var 1) (.hyp 4))) (.hyp 0)))))

/-- OKUMA: iki durumlu bir banka (veri). Mevduat = durum numarası, net = 0, virman =
aynı durum, kredi = 0'dan 1'e geçiş. -/
def bankFin : FinStructure BankSig where
  n := 1
  fn := fun f v => match f with
    | .Dep => v 0
    | .Net => 0
  rel := fun r v => match r with
    | .Tr => decide (v 0 = v 1)
    | .Cr => decide (v 0 = 0 ∧ v 1 = 1)

/-- OKUMA: fizikte korunum yasasının ispatı: aksiyomun kendisi. -/
def conservationProof : Proof PhysSig := .hyp 0
