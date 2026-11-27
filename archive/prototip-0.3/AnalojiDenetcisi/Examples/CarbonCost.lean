import AnalojiDenetcisi.Kernel

/-!
# Karbonun sosyal maliyeti (SCC): tartışma ρ'da yatıyor

Olgular aynı tutulur: tanım ve ampirik öncüller. Yalnızca normatif öncül, yani
saf zaman tercihi ρ, değişir. Bu durumda politika sonucu tersine döner.
Çekirdek bu sonucu "eğer ρ seçilirse vergi şudur" biçiminde koşullu olarak üretir.

ρ değerleri literatürdendir: Stern (2006) ρ = %0,1; Nordhaus (DICE) ρ = %1,5.
Zarar ve ufuk değerleri **örnek** değerlerdir, ampirik tahmin değildir.
Modeli basit tutmak için Ramsey kuralının `η·g` terimi (o da kısmen normatif)
ve büyüyen zararlar dışarıda bırakılmıştır. Hepsi µ$/tCO₂ cinsindendir.
-/

/-- Olası dünya: parametre atamaları. -/
structure World where
  damage  : Nat  -- marjinal zarar, µ$/tCO₂/yıl
  horizon : Nat  -- etki süresi, yıl
  rho     : Nat  -- saf zaman tercihi, baz puan (10 = %0,1)
  scc     : Nat  -- karbonun sosyal maliyeti, µ$/tCO₂
  tax     : Nat  -- önerilen karbon vergisi, µ$/tCO₂

/-- İskontolu toplam: `v + v/(1+ρ) + v/(1+ρ)² + …`, `n` dönem. -/
-- irreducible: elaborator değeri hesaplamaya çalışmasın; sayısal denetimi `decide +kernel` yapar.
@[irreducible] def discountedSum (rho : Nat) : Nat → Nat → Nat
  | 0,     _ => 0
  | n + 1, v => v + discountedSum rho n (v * 10000 / (10000 + rho))

def sccOf (damage horizon rho : Nat) : Nat := discountedSum rho horizon damage

/-! ## Etiketli öncüller -/

def defSCC : Premise World :=
  ⟨"SCC = marjinal zararın iskontolu toplamı", .tanim,
   fun w => w.scc = sccOf w.damage w.horizon w.rho⟩

def damageObs : Premise World :=
  ⟨"marjinal zarar 1 $/tCO₂/yıl (örnek değer)", .ampirik, fun w => w.damage = 1000000⟩

def horizonObs : Premise World :=
  ⟨"etki süresi 200 yıl (örnek değer)", .ampirik, fun w => w.horizon = 200⟩

def rhoChoice (r : Nat) : Premise World :=
  ⟨"saf zaman tercihi ρ (baz puan)", .normatif, fun w => w.rho = r⟩

def pigou : Premise World :=
  ⟨"vergi marjinal sosyal maliyete eşit olmalı (Pigou)", .normatif, fun w => w.tax = w.scc⟩

/-- Ortak olgular. İki argüman yalnızca `rhoChoice` öncülünde ayrılır. -/
def facts : List (Premise World) := [defSCC, damageObs, horizonObs]

/-! ## Olgulara uyan iki dünya -/

def sternWorld : World :=
  ⟨1000000, 200, 10, sccOf 1000000 200 10, sccOf 1000000 200 10⟩

def nordhausWorld : World :=
  ⟨1000000, 200, 150, sccOf 1000000 200 150, sccOf 1000000 200 150⟩

/-! ## İki politika argümanı -/

/-- ρ = %0,1 ise vergi en az 150 $/tCO₂ olmalı. -/
def sternArgument : PolicyArgument World (fun w => 150000000 ≤ w.tax) where
  premises := [defSCC, damageObs, horizonObs, rhoChoice 10, pigou]
  valid := by
    rintro w ⟨h1, h2, h3, h4, h5, -⟩
    show 150000000 ≤ w.tax
    rw [h5, h1, h2, h3, h4]
    decide +kernel
  -- Tanık: aynı olgular, ρ = %1,5. Sonuç düşer.
  hume := ⟨nordhausWorld, ⟨Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl, trivial⟩,
           by decide +kernel⟩

/-- ρ = %1,5 ise vergi 70 $/tCO₂'nin altında olmalı. -/
def nordhausArgument : PolicyArgument World (fun w => w.tax < 70000000) where
  premises := [defSCC, damageObs, horizonObs, rhoChoice 150, pigou]
  valid := by
    rintro w ⟨h1, h2, h3, h4, h5, -⟩
    show w.tax < 70000000
    rw [h5, h1, h2, h3, h4]
    decide +kernel
  -- Tanık: aynı olgular, ρ = %0,1. Sonuç düşer.
  hume := ⟨sternWorld, ⟨Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl, trivial⟩,
           by decide +kernel⟩

/-- İki argüman aynı olguları paylaşır; fark yalnızca normatif öncüllerdedir. -/
theorem same_facts :
    sternArgument.premises.take 3 = facts ∧ nordhausArgument.premises.take 3 = facts :=
  ⟨rfl, rfl⟩

/-- Olgular tek başına hiçbir vergi eşiğini belirlemez: her iki dünya da olgulara uyar,
ama biri 150 $ üstünde, diğeri 70 $ altında vergi verir. -/
theorem dispute_is_rho :
    Premise.allHold facts sternWorld ∧ Premise.allHold facts nordhausWorld ∧
    150000000 ≤ sternWorld.tax ∧ nordhausWorld.tax < 70000000 :=
  ⟨⟨rfl, rfl, rfl, trivial⟩, ⟨rfl, rfl, rfl, trivial⟩, by decide +kernel, by decide +kernel⟩
