import Hakem.Finite

/-!
# Sınama durumu: termodinamik denge ↔ piyasa dengesi (ℤ arka planı, veri olarak)

Termodinamik: iki cisim, aynı entropi fonksiyonu `S`, enerjiler `e1`, `e2`.
Aksiyom: `S` kesin içbükey (pozitif ısı sığası); enerjiler negatif değil.
Denge: hiçbir enerji yeniden dağılımı (toplam korunur, negatif olmaz) toplam entropiyi
kesin artırmaz (Clausius).

Piyasa: iki tüccar, aynı fayda fonksiyonu `u`, miktarlar `q1`, `q2`.
Denge: hiçbir gönüllü ticaret (yan ödeme `t` ile kimse kötüleşmez, biri iyileşir) yoktur.
İki denge tanımı farklı sözcüklerle yazılmıştır.

İDEALLEŞTİRME: iki parça; aynı fonksiyon; tamsayı nicelikler; tek mal; yarı-doğrusal fayda.
-/

/-! ## Arka plan: ℤ -/

inductive IntFn  | num (z : Int) | add | sub  deriving DecidableEq
inductive IntRel | lt | le                    deriving DecidableEq

/-- OKUMA: tamsayı sözlüğü: sabitler, toplama, çıkarma, `<`, `≤`. -/
abbrev IntSig : Signature where
  Fn := IntFn
  Rel := IntRel
  fnArity := fun | .num _ => 0 | .add => 2 | .sub => 2
  relArity := fun _ => 2
  fnRole := fun _ => .tanim
  relRole := fun _ => .tanim

/-- OKUMA: standart ℤ. -/
def IntStd : Structure IntSig where
  D := Int
  dflt := 0
  fn := fun f v => match f, v with
    | .num z, _ => z
    | .add, v => v 0 + v 1
    | .sub, v => v 0 - v 1
  rel := fun r v => match r with
    | .lt => v 0 < v 1
    | .le => v 0 ≤ v 1

/-! ## Termodinamik sözlüğü -/

inductive ThFn  | base (f : IntFn) | S | e1 | e2  deriving DecidableEq
inductive ThRel | base (r : IntRel)              deriving DecidableEq

/-- OKUMA: termodinamik sözlüğü. `S`: entropi fonksiyonu; `e1`, `e2`: enerjiler (ampirik). -/
abbrev ThSig : Signature where
  Fn := ThFn
  Rel := ThRel
  fnArity := fun | .base f => IntSig.fnArity f | .S => 1 | _ => 0
  relArity := fun | .base r => IntSig.relArity r
  fnRole := fun | .base _ => .tanim | _ => .ampirik
  relRole := fun _ => .tanim

def thEmbed : SigMorph IntSig ThSig where
  fnMap := fun f => .app (.base f) (fun i => .var i.val)
  relMap := fun r => .rel (.base r) (fun i => .var i.val)

def tnum (z : Int) : Term ThSig := .app (.base (.num z)) vec0
def tadd (a b : Term ThSig) : Term ThSig := .app (.base .add) (vec2 a b)
def tsub (a b : Term ThSig) : Term ThSig := .app (.base .sub) (vec2 a b)
def tS (a : Term ThSig) : Term ThSig := .app .S (vec1 a)
def te1 : Term ThSig := .app .e1 vec0
def te2 : Term ThSig := .app .e2 vec0
def tlt (a b : Term ThSig) : Formula ThSig := .rel (.base .lt) (vec2 a b)
def tle (a b : Term ThSig) : Formula ThSig := .rel (.base .le) (vec2 a b)

/-- OKUMA: ∀x, S(x+2) − S(x+1) < S(x+1) − S(x). Kesin içbükeylik (pozitif ısı sığası). -/
def thConcave : Formula ThSig :=
  .all (tlt (tsub (tS (tadd (.var 0) (tnum 2))) (tS (tadd (.var 0) (tnum 1))))
            (tsub (tS (tadd (.var 0) (tnum 1))) (tS (.var 0))))

/-- OKUMA: termodinamik kuramı: içbükeylik, negatif olmayan enerjiler, ℤ arka planı. -/
def Thermo : Theory ThSig :=
  Theory.withBackground [thConcave, tle (tnum 0) te1, tle (tnum 0) te2] thEmbed IntStd

/-- OKUMA: termodinamik denge (Clausius). ∀ y1 y2, y1 + y2 = e1 + e2 ∧ 0 ≤ y1 ∧ 0 ≤ y2 →
¬ (S e1 + S e2 < S y1 + S y2). -/
def thEquilibrium : Formula ThSig :=
  .all (.all (.imp
    (.and (.eq (tadd (.var 1) (.var 0)) (tadd te1 te2)) (.and (tle (tnum 0) (.var 1)) (tle (tnum 0) (.var 0))))
    (.not (tlt (tadd (tS te1) (tS te2)) (tadd (tS (.var 1)) (tS (.var 0)))))))

/-- OKUMA: enerji eşit dağılmış (en çok bir birim fark). -/
def thEven : Formula ThSig := .and (tle (tnum (-1)) (tsub te1 te2)) (tle (tsub te1 te2) (tnum 1))

/-- OKUMA: termodinamik yasa: dengede enerji eşit dağılır. -/
def thermoLaw : Formula ThSig := .imp thEquilibrium thEven

/-! ## Piyasa sözlüğü -/

inductive MkFn  | base (f : IntFn) | u | q1 | q2  deriving DecidableEq
inductive MkRel | base (r : IntRel)              deriving DecidableEq

/-- OKUMA: piyasa sözlüğü. `u`: fayda fonksiyonu; `q1`, `q2`: miktarlar (ampirik). -/
abbrev MkSig : Signature where
  Fn := MkFn
  Rel := MkRel
  fnArity := fun | .base f => IntSig.fnArity f | .u => 1 | _ => 0
  relArity := fun | .base r => IntSig.relArity r
  fnRole := fun | .base _ => .tanim | _ => .ampirik
  relRole := fun _ => .tanim

def mkEmbed : SigMorph IntSig MkSig where
  fnMap := fun f => .app (.base f) (fun i => .var i.val)
  relMap := fun r => .rel (.base r) (fun i => .var i.val)

def mnum (z : Int) : Term MkSig := .app (.base (.num z)) vec0
def madd (a b : Term MkSig) : Term MkSig := .app (.base .add) (vec2 a b)
def msub (a b : Term MkSig) : Term MkSig := .app (.base .sub) (vec2 a b)
def mu (a : Term MkSig) : Term MkSig := .app .u (vec1 a)
def mq1 : Term MkSig := .app .q1 vec0
def mq2 : Term MkSig := .app .q2 vec0
def mlt (a b : Term MkSig) : Formula MkSig := .rel (.base .lt) (vec2 a b)
def mle (a b : Term MkSig) : Formula MkSig := .rel (.base .le) (vec2 a b)

/-- OKUMA: ∀x, u(x+2) − u(x+1) < u(x+1) − u(x). Kesin azalan marjinal fayda. -/
def mkDMU : Formula MkSig :=
  .all (mlt (msub (mu (madd (.var 0) (mnum 2))) (mu (madd (.var 0) (mnum 1))))
            (msub (mu (madd (.var 0) (mnum 1))) (mu (.var 0))))

/-- OKUMA: kısıtsız piyasa: negatif olmayan miktarlar, ℤ arka planı. -/
def Market : Theory MkSig :=
  Theory.withBackground [mle (mnum 0) mq1, mle (mnum 0) mq2] mkEmbed IntStd

/-- OKUMA: azalan marjinal faydalı piyasa. -/
def MarketDMU : Theory MkSig :=
  Theory.withBackground [mle (mnum 0) mq1, mle (mnum 0) mq2, mkDMU] mkEmbed IntStd

/-- OKUMA: piyasa dengesi (gönüllülük). ∀ y1 y2, y1 + y2 = q1 + q2 ∧ 0 ≤ y1 ∧ 0 ≤ y2 →
¬ ∃ t, 0 ≤ u y1 − u q1 + t ∧ 0 ≤ u y2 − u q2 − t ∧ (0 < u y1 − u q1 + t ∨ 0 < u y2 − u q2 − t). -/
def mkEquilibrium : Formula MkSig :=
  .all (.all (.imp
    (.and (.eq (madd (.var 1) (.var 0)) (madd mq1 mq2)) (.and (mle (mnum 0) (.var 1)) (mle (mnum 0) (.var 0))))
    (.not (.ex (.and (mle (mnum 0) (madd (msub (mu (.var 2)) (mu mq1)) (.var 0)))
      (.and (mle (mnum 0) (msub (msub (mu (.var 1)) (mu mq2)) (.var 0)))
        (.or (mlt (mnum 0) (madd (msub (mu (.var 2)) (mu mq1)) (.var 0)))
             (mlt (mnum 0) (msub (msub (mu (.var 1)) (mu mq2)) (.var 0))))))))))

/-- OKUMA: mal eşit dağılmış (en çok bir birim fark). -/
def mkEven : Formula MkSig := .and (mle (mnum (-1)) (msub mq1 mq2)) (mle (msub mq1 mq2) (mnum 1))

/-- OKUMA: piyasa yasası: dengede mal eşit dağılır. -/
def marketLaw : Formula MkSig := .imp mkEquilibrium mkEven

/-! ## Sözlük -/

/-- OKUMA: sözlük: sayılar ↦ sayılar, entropi ↦ fayda, enerjiler ↦ miktarlar. -/
def thermoToMarket : SigMorph ThSig MkSig where
  fnMap := fun
    | .base f => .app (.base f) (fun i => .var i.val)
    | .S => .app .u (vec1 (.var 0))
    | .e1 => mq1
    | .e2 => mq2
  relMap := fun
    | .base r => .rel (.base r) (fun i => .var i.val)
