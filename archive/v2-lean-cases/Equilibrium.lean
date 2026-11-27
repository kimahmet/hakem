import Hakem
import Solution.Background

/-! Güvenilmeyen ispatlar: termodinamik ↔ piyasa (ℤ arka planı). -/

namespace Proofs

/-! ## ℤ'de içbükeylik -/

theorem concave_far {f : Int → Int} (h : ∀ x, f (x + 2) - f (x + 1) < f (x + 1) - f x) (x : Int) :
    ∀ k : Nat, f (x + k + 2) - f (x + k + 1) < f (x + 1) - f x := by
  intro k
  induction k with
  | zero =>
    rw [show x + ((0 : Nat) : Int) + 2 = x + 2 by omega,
        show x + ((0 : Nat) : Int) + 1 = x + 1 by omega]
    exact h x
  | succ k ih =>
    have hk := h (x + k + 1)
    rw [show x + ((k + 1 : Nat) : Int) + 2 = x + k + 3 by omega,
        show x + ((k + 1 : Nat) : Int) + 1 = x + k + 2 by omega]
    rw [show x + (k : Int) + 1 + 2 = x + k + 3 by omega,
        show x + (k : Int) + 1 + 1 = x + k + 2 by omega] at hk
    omega

theorem concave_step {f : Int → Int} (h : ∀ x, f (x + 2) - f (x + 1) < f (x + 1) - f x)
    {lo hi : Int} (hd : lo + 2 ≤ hi) : f lo + f hi < f (lo + 1) + f (hi - 1) := by
  have := concave_far h lo (hi - lo - 2).toNat
  have hk : (((hi - lo - 2).toNat : Nat) : Int) = hi - lo - 2 := Int.toNat_of_nonneg (by omega)
  rw [show lo + (((hi - lo - 2).toNat : Nat) : Int) + 2 = hi by omega,
      show lo + (((hi - lo - 2).toNat : Nat) : Int) + 1 = hi - 1 by omega] at this
  omega

/-! ## Standart yapılar -/

def thStd (s : Int → Int) (a b : Int) : Structure ThSig where
  D := Int
  dflt := 0
  fn := fun f v => match f, v with
    | .base g, v => IntStd.fn g v
    | .S, v => s (v 0)
    | .e1, _ => a
    | .e2, _ => b
  rel := fun r v => match r, v with
    | .base q, v => IntStd.rel q v

def mkStd (u : Int → Int) (a b : Int) : Structure MkSig where
  D := Int
  dflt := 0
  fn := fun f v => match f, v with
    | .base g, v => IntStd.fn g v
    | .u, v => u (v 0)
    | .q1, _ => a
    | .q2, _ => b
  rel := fun r v => match r, v with
    | .base q, v => IntStd.rel q v

theorem argEnv_val {S : Signature} (M : Structure S) {k : Nat} (v : Fin k → M.D) :
    (fun i : Fin k => argEnv M v i.val) = v := by
  funext i; unfold argEnv; exact dite_eq_left i.isLt

theorem fin1_eq (v : Fin 1 → Int) : v = fun _ => v 0 := by
  funext i; exact congrArg v (Fin.ext (by have := i.isLt; omega))

theorem fin0_eq (v w : Fin 0 → Int) : v = w := funext fun i => i.elim0

/-- Standart tabanlı her termodinamik yapı bir `thStd`'dir. -/
theorem th_std_eq (fn : (f : ThFn) → (Fin (ThSig.fnArity f) → IntStd.D) → IntStd.D)
    (rel : (r : ThRel) → (Fin (ThSig.relArity r) → IntStd.D) → Prop)
    (hfn : ∀ f v, (thEmbed.reduct (⟨IntStd.D, IntStd.dflt, fn, rel⟩ : Structure ThSig)).fn f v = IntStd.fn f v)
    (hrel : ∀ r v, (thEmbed.reduct (⟨IntStd.D, IntStd.dflt, fn, rel⟩ : Structure ThSig)).rel r v ↔ IntStd.rel r v) :
    (⟨IntStd.D, IntStd.dflt, fn, rel⟩ : Structure ThSig) =
      thStd (fun x => fn .S (fun _ => x)) (fn .e1 (fun i => i.elim0)) (fn .e2 (fun i => i.elim0)) := by
  have hb : ∀ g v, fn (.base g) v = IntStd.fn g v := fun g v => by
    have := hfn g v
    rw [← this]
    show fn (.base g) v = fn (.base g) (fun i => argEnv _ v i.val)
    rw [argEnv_val]
  have hr : ∀ q v, rel (.base q) v ↔ IntStd.rel q v := fun q v => by
    have := hrel q v
    rw [← this]
    show rel (.base q) v ↔ rel (.base q) (fun i => argEnv _ v i.val)
    rw [argEnv_val]
  unfold thStd
  congr 1
  · funext f v
    cases f with
    | base g => exact hb g v
    | S => exact congrArg (fn .S) (fin1_eq v)
    | e1 => exact congrArg (fn .e1) (fin0_eq _ _)
    | e2 => exact congrArg (fn .e2) (fin0_eq _ _)
  · funext r v
    cases r with
    | base q => exact propext (hr q v)

theorem mk_std_eq (fn : (f : MkFn) → (Fin (MkSig.fnArity f) → IntStd.D) → IntStd.D)
    (rel : (r : MkRel) → (Fin (MkSig.relArity r) → IntStd.D) → Prop)
    (hfn : ∀ f v, (mkEmbed.reduct (⟨IntStd.D, IntStd.dflt, fn, rel⟩ : Structure MkSig)).fn f v = IntStd.fn f v)
    (hrel : ∀ r v, (mkEmbed.reduct (⟨IntStd.D, IntStd.dflt, fn, rel⟩ : Structure MkSig)).rel r v ↔ IntStd.rel r v) :
    (⟨IntStd.D, IntStd.dflt, fn, rel⟩ : Structure MkSig) =
      mkStd (fun x => fn .u (fun _ => x)) (fn .q1 (fun i => i.elim0)) (fn .q2 (fun i => i.elim0)) := by
  have hb : ∀ g v, fn (.base g) v = IntStd.fn g v := fun g v => by
    have := hfn g v
    rw [← this]
    show fn (.base g) v = fn (.base g) (fun i => argEnv _ v i.val)
    rw [argEnv_val]
  have hr : ∀ q v, rel (.base q) v ↔ IntStd.rel q v := fun q v => by
    have := hrel q v
    rw [← this]
    show rel (.base q) v ↔ rel (.base q) (fun i => argEnv _ v i.val)
    rw [argEnv_val]
  unfold mkStd
  congr 1
  · funext f v
    cases f with
    | base g => exact hb g v
    | u => exact congrArg (fn .u) (fin1_eq v)
    | q1 => exact congrArg (fn .q1) (fin0_eq _ _)
    | q2 => exact congrArg (fn .q2) (fin0_eq _ _)
  · funext r v
    cases r with
    | base q => exact propext (hr q v)

theorem mk_adm (u : Int → Int) (a b : Int) : Nonempty ((mkEmbed.reduct (mkStd u a b)).Iso IntStd) := by
  refine ⟨{ to := id, inv := id, left := fun _ => rfl, right := fun _ => rfl, dflt := rfl,
            fn := ?_, rel := ?_ }⟩
  · intro g v
    exact congrArg (IntStd.fn g) (argEnv_val (mkStd u a b) v)
  · intro q v
    exact iff_of_eq (congrArg (IntStd.rel q) (argEnv_val (mkStd u a b) v))

/-! ## Okumalar: formüllerin standart yapılardaki anlamı -/

theorem th_concave_iff (s : Int → Int) (a b : Int) :
    (thStd s a b).Sat thConcave ↔ ∀ x, s (x + 2) - s (x + 1) < s (x + 1) - s x :=
  ⟨fun h x => h (fun _ => (0 : Int)) x, fun h _ x => h x⟩

theorem th_law_iff (s : Int → Int) (a b : Int) :
    (thStd s a b).Sat thermoLaw ↔
      ((∀ y1 y2 : Int, (y1 + y2 = a + b ∧ 0 ≤ y1 ∧ 0 ≤ y2) → ¬ (s a + s b < s y1 + s y2)) →
        (-1 ≤ a - b ∧ a - b ≤ 1)) :=
  ⟨fun h => h (fun _ => (0 : Int)), fun h _ => h⟩

theorem mk_law_iff (u : Int → Int) (a b : Int) :
    (mkStd u a b).Sat marketLaw ↔
      ((∀ y1 y2 : Int, (y1 + y2 = a + b ∧ 0 ≤ y1 ∧ 0 ≤ y2) →
          ¬ ∃ t : Int, 0 ≤ u y1 - u a + t ∧ 0 ≤ u y2 - u b - t ∧
            (0 < u y1 - u a + t ∨ 0 < u y2 - u b - t)) →
        (-1 ≤ a - b ∧ a - b ≤ 1)) :=
  ⟨fun h => h (fun _ => (0 : Int)), fun h _ => h⟩

/-! ## Termodinamik yasası -/

theorem th_std_law (s : Int → Int) (a b : Int) (hc : ∀ x, s (x + 2) - s (x + 1) < s (x + 1) - s x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : (thStd s a b).Sat thermoLaw := by
  rw [th_law_iff]
  intro heq
  constructor
  · by_cases h : -1 ≤ a - b
    · exact h
    · exfalso
      exact heq (a + 1) (b - 1) ⟨by omega, by omega, by omega⟩ (concave_step hc (by omega))
  · by_cases h : a - b ≤ 1
    · exact h
    · exfalso
      have := concave_step hc (lo := b) (hi := a) (by omega)
      exact heq (a - 1) (b + 1) ⟨by omega, by omega, by omega⟩ (by omega)

theorem thermo_equilibrium_even : Thermo.Entails thermoLaw := by
  refine entails_of_std Thermo thEmbed IntStd (fun _ h => h) thermoLaw ?_
  intro fn rel hfn hrel hax
  rw [th_std_eq fn rel hfn hrel] at hax ⊢
  have h0 := hax thConcave (by simp [Thermo, Theory.withBackground])
  have h1 : (0 : Int) ≤ fn .e1 (fun i => i.elim0) :=
    hax (tle (tnum 0) te1) (by simp [Thermo, Theory.withBackground]) (fun _ => (0 : Int))
  have h2 : (0 : Int) ≤ fn .e2 (fun i => i.elim0) :=
    hax (tle (tnum 0) te2) (by simp [Thermo, Theory.withBackground]) (fun _ => (0 : Int))
  exact th_std_law _ _ _ ((th_concave_iff _ _ _).1 h0) h1 h2

/-! ## Analoji -/

theorem comp_embed : thEmbed.comp thermoToMarket = mkEmbed := by
  unfold SigMorph.comp
  congr 1
  · funext f
    show (Term.app (S := MkSig) (MkFn.base f) fun i =>
        (Term.var (S := MkSig) i.val).subst (argSubst fun j => Term.var (S := MkSig) j.val)) =
      Term.app (S := MkSig) (MkFn.base f) (fun i => Term.var i.val)
    congr 1
    funext i
    show argSubst (fun j : Fin (IntSig.fnArity f) => (Term.var j.val : Term MkSig)) i.val = Term.var i.val
    unfold argSubst
    exact dite_eq_left i.isLt
  · funext r
    show (Formula.rel (S := MkSig) (MkRel.base r) fun i =>
        (Term.var (S := MkSig) i.val).subst (argSubst fun j => Term.var (S := MkSig) j.val)) =
      Formula.rel (S := MkSig) (MkRel.base r) (fun i => Term.var i.val)
    congr 1
    funext i
    show argSubst (fun j : Fin (IntSig.relArity r) => (Term.var j.val : Term MkSig)) i.val = Term.var i.val
    unfold argSubst
    exact dite_eq_left i.isLt

theorem reduct_mkStd (u : Int → Int) (a b : Int) : thermoToMarket.reduct (mkStd u a b) = thStd u a b := by
  unfold SigMorph.reduct thStd
  congr 1
  · funext f v
    cases f with
    | base g => exact congrArg (IntStd.fn g) (argEnv_val (mkStd u a b) v)
    | S => rfl
    | e1 => rfl
    | e2 => rfl
  · funext r v
    cases r with
    | base q => exact congrArg (IntStd.rel q) (argEnv_val (mkStd u a b) v)

theorem law_of_reduct (u : Int → Int) (a b : Int)
    (h : (thermoToMarket.reduct (mkStd u a b)).Sat thermoLaw) : (thStd u a b).Sat thermoLaw :=
  reduct_mkStd u a b ▸ h

theorem negSq_concave : ∀ x : Int, -((x + 2) * (x + 2)) - -((x + 1) * (x + 1)) < -((x + 1) * (x + 1)) - -(x * x) := by
  intro x
  simp only [Int.add_mul, Int.mul_add]
  omega

def thermoMarketDMU : Analogy Thermo MarketDMU where
  σ := thermoToMarket
  adm := fun M hM => by
    show Nonempty ((thEmbed.reduct (thermoToMarket.reduct M)).Iso IntStd)
    rw [← reduct_comp, comp_embed]
    exact hM.1
  preserves := by
    intro φ hφ
    simp only [Thermo, Theory.withBackground, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact calculus_sound MarketDMU _ (.hyp 2) (by decide +kernel)
    · exact calculus_sound MarketDMU _ (.hyp 0) (by decide +kernel)
    · exact calculus_sound MarketDMU _ (.hyp 1) (by decide +kernel)
  model := mkStd (fun x => -(x * x)) 0 0
  model_ok := by
    refine ⟨mk_adm _ _ _, fun ψ hψ env => ?_⟩
    simp only [MarketDMU, Theory.withBackground, List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl | rfl
    · exact (show (0 : Int) ≤ 0 by decide)
    · exact (show (0 : Int) ≤ 0 by decide)
    · exact negSq_concave

theorem analogy_thermo_marketDMU : ∃ a : Analogy Thermo MarketDMU, a.σ = thermoToMarket :=
  ⟨thermoMarketDMU, rfl⟩

/-- Piyasada gönüllü ticaret yoksa toplam fayda artırılamaz (yan ödeme `t = u a − u y1`). -/
theorem voluntary_of_surplus (u : Int → Int) (a b y1 y2 : Int) (h : u a + u b < u y1 + u y2) :
    ∃ t : Int, 0 ≤ u y1 - u a + t ∧ 0 ≤ u y2 - u b - t ∧ (0 < u y1 - u a + t ∨ 0 < u y2 - u b - t) :=
  ⟨u a - u y1, by omega, by omega, Or.inr (by omega)⟩

/-- Aktarılan yasa ve gönüllülük–Clausius köprüsüyle piyasa yasası. -/
theorem market_equilibrium_even : MarketDMU.Entails marketLaw := by
  have htr := transfer thermoMarketDMU thermo_equilibrium_even
  refine entails_of_std MarketDMU mkEmbed IntStd (fun _ h => h) marketLaw ?_
  intro fn rel hfn hrel hax
  have hM : MarketDMU.Models (⟨IntStd.D, IntStd.dflt, fn, rel⟩ : Structure MkSig) := by
    refine ⟨?_, hax⟩
    rw [mk_std_eq fn rel hfn hrel]
    exact mk_adm _ _ _
  have ht := htr _ hM
  rw [mk_std_eq fn rel hfn hrel] at ht ⊢
  have h2 := (th_law_iff _ _ _).1 (law_of_reduct _ _ _ ((satisfaction thermoToMarket _ thermoLaw).1 ht))
  exact (mk_law_iff _ _ _).2 (fun hvol =>
    h2 (fun y1 y2 hy hs => hvol y1 y2 hy
      (voluntary_of_surplus (fun x => fn .u (fun _ => x)) _ _ y1 y2 hs)))

/-! ## Metafor: kısıtsız piyasa -/

def thermoMarketRefutation :
    Refutation Thermo Market (fun _ => true) (fun _ => true) thermoToMarket where
  φ := thermoLaw
  thm := thermo_equilibrium_even
  only := by decide
  cex := mkStd (fun x => x) 0 10
  cex_ok := by
    refine ⟨mk_adm _ _ _, fun ψ hψ env => ?_⟩
    simp only [Market, Theory.withBackground, List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl
    · exact (show (0 : Int) ≤ 0 by decide)
    · exact (show (0 : Int) ≤ 10 by decide)
  fails := by
    intro hs
    have h := (th_law_iff _ _ _).1 (law_of_reduct _ _ _ ((satisfaction thermoToMarket _ thermoLaw).1 hs))
    have := h (fun y1 y2 hy hs => by omega)
    omega

theorem metaphor_thermo_market :
    Nonempty (Refutation Thermo Market (fun _ => true) (fun _ => true) thermoToMarket) :=
  ⟨thermoMarketRefutation⟩

end Proofs
