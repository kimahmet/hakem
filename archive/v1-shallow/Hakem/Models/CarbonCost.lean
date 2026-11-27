import Hakem.Kernel

/-!
# Karbonun sosyal maliyeti (SCC)

Ampirik koordinatlar (`Facts`) ile normatif koordinatlar (`Values`) ayrı
tiplerdir. Olgu kısıtı (`measured`) tip gereği değer seçimini göremez.
Tanımlar (`scc`, `recommendedTax`) öncül değildir; Lean tanımıdır.
-/

/-- OKUMA: ampirik koordinatlar.
`damage`: bir ton CO₂'nin yıllık marjinal zararı (µ$/tCO₂/yıl).
`horizon`: zararın süreceği yıl sayısı.
İDEALLEŞTİRME: zarar yıllık sabit; büyüme, belirsizlik dağılımı ve eşik etkileri yok. -/
structure Facts where
  damage  : Nat
  horizon : Nat

/-- OKUMA: politika ölçütü. `pigou`: vergi marjinal sosyal maliyete eşit olmalı.
`laissezFaire`: vergi olmamalı. -/
inductive Criterion where
  | pigou
  | laissezFaire

/-- OKUMA: normatif koordinatlar.
`rho`: saf zaman tercihi, baz puan (10 = %0,1).
`criterion`: politika ölçütü.
İDEALLEŞTİRME: Ramsey kuralının `η·g` terimi (eşitsizlik karşıtlığı × büyüme) yok;
iskonto oranı yalnızca ρ. -/
structure Values where
  rho       : Nat
  criterion : Criterion

/-- OKUMA: iskontolu toplam `v + v/(1+ρ) + v/(1+ρ)² + …`, `n` dönem.
Her dönemde aşağı yuvarlanır. -/
def discountedSum (rho : Nat) : Nat → Nat → Nat
  | 0,     _ => 0
  | n + 1, v => v + discountedSum rho n (v * 10000 / (10000 + rho))

/-- OKUMA: karbonun sosyal maliyeti, µ$/tCO₂. -/
def scc (e : Facts) (rho : Nat) : Nat := discountedSum rho e.horizon e.damage

/-- OKUMA: ölçütün önerdiği vergi, µ$/tCO₂. -/
def recommendedTax (e : Facts) (n : Values) : Nat :=
  match n.criterion with
  | .pigou        => scc e n.rho
  | .laissezFaire => 0

/-- OKUMA: ölçüm aralığı (ÖRNEK değerler, ampirik tahmin değil).
Zarar 0,9–1,1 $/tCO₂/yıl; süre 150–300 yıl. -/
def measured (e : Facts) : Prop :=
  900000 ≤ e.damage ∧ e.damage ≤ 1100000 ∧ 150 ≤ e.horizon ∧ e.horizon ≤ 300

/-- OKUMA: SCC politika sorusu. -/
abbrev SCCQuestion : Question where
  E     := Facts
  N     := Values
  facts := measured

/-- OKUMA: Stern (2006) türü seçim. Pigou ölçütü, ρ = %0,1. -/
def sternNorms (n : Values) : Prop := n.criterion = .pigou ∧ n.rho = 10

/-- OKUMA: Nordhaus (DICE) türü seçim. Pigou ölçütü, ρ = %1,5. -/
def nordhausNorms (n : Values) : Prop := n.criterion = .pigou ∧ n.rho = 150

/-- OKUMA: önerilen vergi en az `x` µ$/tCO₂. -/
def TaxAtLeast (x : Nat) (e : Facts) (n : Values) : Prop := x ≤ recommendedTax e n

/-- OKUMA: önerilen vergi `x` µ$/tCO₂'den az. -/
def TaxBelow (x : Nat) (e : Facts) (n : Values) : Prop := recommendedTax e n < x
