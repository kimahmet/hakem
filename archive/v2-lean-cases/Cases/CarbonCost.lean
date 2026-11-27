import Hakem.Finite

/-!
# Sınama durumu: karbonun sosyal maliyeti (arka planlı, veri olarak)

Arka plan: standart ℕ (sayılar, `≤`, SCC fonksiyonu). Ampirik semboller: zarar, süre.
Normatif semboller: ρ (saf zaman tercihi), vergi (olması gereken vergi). Öncüllerin
türü sembollerden hesaplanır.
İDEALLEŞTİRME: zarar yıllık sabit; iskonto yalnızca ρ (Ramsey'in `η·g` terimi yok);
yuvarlama her dönemde aşağı; tutarlar µ$/tCO₂; değerler ÖRNEKtir, ampirik tahmin değildir.
-/

/-- OKUMA: iskontolu toplam `v + v/(1+ρ) + …`, `n` dönem, ρ baz puan. -/
def discountedSum (rho : Nat) : Nat → Nat → Nat
  | 0,     _ => 0
  | n + 1, v => v + discountedSum rho n (v * 10000 / (10000 + rho))

/-- OKUMA: karbonun sosyal maliyeti (zarar, süre, ρ). -/
def sccOf (damage horizon rho : Nat) : Nat := discountedSum rho horizon damage

/-! ## Arka plan sözlüğü ve standart yapı -/

inductive NatFn  | num (n : Nat) | scc  deriving DecidableEq
inductive NatRel | le                  deriving DecidableEq

/-- OKUMA: sayı sözlüğü: her doğal sayı için bir sabit, SCC fonksiyonu, `≤`. -/
abbrev NatSig : Signature where
  Fn := NatFn
  Rel := NatRel
  fnArity := fun | .num _ => 0 | .scc => 3
  relArity := fun _ => 2
  fnRole := fun _ => .tanim
  relRole := fun _ => .tanim

/-- OKUMA: standart ℕ. -/
def NatStd : Structure NatSig where
  D := Nat
  dflt := 0
  fn := fun f v => match f, v with
    | .num n, _ => n
    | .scc,   v => sccOf (v 0) (v 1) (v 2)
  rel := fun _ v => v 0 ≤ v 1

/-! ## Disiplin sözlüğü -/

inductive CFn  | base (f : NatFn) | damage | horizon | rho | tax  deriving DecidableEq
inductive CRel | base (r : NatRel)                                deriving DecidableEq

/-- OKUMA: SCC sözlüğü. `damage`, `horizon`: ampirik. `rho`, `tax`: normatif. -/
abbrev CSig : Signature where
  Fn := CFn
  Rel := CRel
  fnArity := fun | .base f => NatSig.fnArity f | _ => 0
  relArity := fun | .base r => NatSig.relArity r
  fnRole := fun
    | .base _ => .tanim
    | .damage => .ampirik
    | .horizon => .ampirik
    | .rho => .normatif
    | .tax => .normatif
  relRole := fun _ => .tanim

/-- OKUMA: sayı sözlüğünün SCC sözlüğüne gömülmesi. -/
def embed : SigMorph NatSig CSig where
  fnMap := fun f => .app (.base f) (fun i => .var i.val)
  relMap := fun r => .rel (.base r) (fun i => .var i.val)

def cnum (n : Nat) : Term CSig := .app (.base (.num n)) vec0
def dmg : Term CSig := .app .damage vec0
def hor : Term CSig := .app .horizon vec0
def rhoT : Term CSig := .app .rho vec0
def taxT : Term CSig := .app .tax vec0
def cscc (a b c : Term CSig) : Term CSig := .app (.base .scc) (vec3 a b c)
def cle (a b : Term CSig) : Formula CSig := .rel (.base .le) (vec2 a b)

/-- OKUMA: ölçüm aralığı (ÖRNEK): zarar 0,9–1,1 $/t/yıl; süre 150–300 yıl. -/
def sccFacts : List (Formula CSig) :=
  [cle (cnum 900000) dmg, cle dmg (cnum 1100000), cle (cnum 150) hor, cle hor (cnum 300)]

/-- OKUMA: Stern türü değer seçimleri: ρ = %0,1; vergi = SCC (Pigou). -/
def sternNorms : List (Formula CSig) := [.eq rhoT (cnum 10), .eq taxT (cscc dmg hor rhoT)]

/-- OKUMA: Nordhaus türü değer seçimleri: ρ = %1,5; vergi = SCC (Pigou). -/
def nordhausNorms : List (Formula CSig) := [.eq rhoT (cnum 150), .eq taxT (cscc dmg hor rhoT)]

/-- OKUMA: Stern kuramı: olgular ve Stern seçimleri, ℕ arka planıyla. -/
def SternSCC : Theory CSig := Theory.withBackground (sccFacts ++ sternNorms) embed NatStd

/-- OKUMA: Nordhaus kuramı: aynı olgular ve Nordhaus seçimleri, ℕ arka planıyla. -/
def NordhausSCC : Theory CSig := Theory.withBackground (sccFacts ++ nordhausNorms) embed NatStd

/-- OKUMA: vergi en az 120 $/tCO₂ olmalı. -/
def taxAtLeast120 : Formula CSig := cle (cnum 120000000) taxT

/-- OKUMA: vergi 75 $/tCO₂'nin altında olmalı. -/
def taxBelow75 : Formula CSig := .not (cle (cnum 75000000) taxT)

/-! ## Arka plan gerçekleri (ℕ'de doğruluğu ayrıca ispatlanır) -/

def nnum (n : Nat) : Term NatSig := .app (.num n) vec0
def nscc (a b c : Term NatSig) : Term NatSig := .app .scc (vec3 a b c)
def nle (a b : Term NatSig) : Formula NatSig := .rel .le (vec2 a b)

/-- OKUMA: ∀ d h, ölçüm aralığındaysa SCC(d, h, %0,1) ≥ 120 $. -/
def bgStern : Formula NatSig :=
  .all (.all (.imp (nle (nnum 900000) (.var 1)) (.imp (nle (.var 1) (nnum 1100000))
    (.imp (nle (nnum 150) (.var 0)) (.imp (nle (.var 0) (nnum 300))
      (nle (nnum 120000000) (nscc (.var 1) (.var 0) (nnum 10))))))))

/-- OKUMA: ∀ d h, ölçüm aralığındaysa SCC(d, h, %1,5) < 75 $. -/
def bgNordhaus : Formula NatSig :=
  .all (.all (.imp (nle (nnum 900000) (.var 1)) (.imp (nle (.var 1) (nnum 1100000))
    (.imp (nle (nnum 150) (.var 0)) (.imp (nle (.var 0) (nnum 300))
      (.not (nle (nnum 75000000) (nscc (.var 1) (.var 0) (nnum 150)))))))))

/-! ## İspat verisi

Bağlam: 0–3 olgular, 4 ρ seçimi, 5 Pigou, 6 arka plan gerçeği. -/

/-- OKUMA: arka plan gerçeğini olgulara uygula, sonra ρ ve vergi eşitlikleriyle yeniden yaz. -/
def sternProof : Proof CSig :=
  let inst := Proof.allE hor (.allE dmg (.hyp 6))
  let p10 := Proof.impE (.impE (.impE (.impE inst (.hyp 0)) (.hyp 1)) (.hyp 2)) (.hyp 3)
  let symRho := Proof.eqE (.eq (.var 0) rhoT) (.hyp 4) (.refl rhoT)
  let pRho := Proof.eqE (cle (cnum 120000000) (cscc dmg hor (.var 0))) symRho p10
  let symTax := Proof.eqE (.eq (.var 0) taxT) (.hyp 5) (.refl taxT)
  .eqE (cle (cnum 120000000) (.var 0)) symTax pRho

/-- OKUMA: aynı iskelet, Nordhaus seçimleriyle ve "< 75 $" sonucuyla. -/
def nordhausProof : Proof CSig :=
  let inst := Proof.allE hor (.allE dmg (.hyp 6))
  let p150 := Proof.impE (.impE (.impE (.impE inst (.hyp 0)) (.hyp 1)) (.hyp 2)) (.hyp 3)
  let symRho := Proof.eqE (.eq (.var 0) rhoT) (.hyp 4) (.refl rhoT)
  let pRho := Proof.eqE (.not (cle (cnum 75000000) (cscc dmg hor (.var 0)))) symRho p150
  let symTax := Proof.eqE (.eq (.var 0) taxT) (.hyp 5) (.refl taxT)
  .eqE (.not (cle (cnum 75000000) (.var 0))) symTax pRho
