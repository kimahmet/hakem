import Hakem
import Solution.Meta

/-! Güvenilmeyen ispatlar: sınama durumları. -/

namespace Proofs

theorem eval_vec2 {S : Signature} (M : Structure S) (env : Nat → M.D) (a b : Term S) :
    (fun i => (vec2 a b i).eval M env) = vec2 (a.eval M env) (b.eval M env) := by
  funext i
  unfold vec2
  split <;> rfl

/-! ## Korunum -/

theorem eval_conservationLaw (N : Structure PhysSig) (env : Nat → N.D) :
    conservationLaw.eval N env ↔
      ∀ x y, N.rel .Exch (vec2 x y) → N.fn .E (vec1 x) = N.fn .E (vec1 y) := by
  show (∀ x y, N.rel .Exch (fun i => (vec2 (Term.var 1) (Term.var 0) i).eval N (cons y (cons x env))) →
      N.fn .E (vec1 x) = N.fn .E (vec1 y)) ↔ _
  simp only [eval_vec2]
  exact Iff.rfl

theorem eval_bankPreserves (M : Structure BankSig) (env : Nat → M.D) (R : BankRel) (F : BankFn) :
    (bankPreserves R F).eval M env ↔
      ∀ x y, M.rel R (vec2 x y) → M.fn F (vec1 x) = M.fn F (vec1 y) := by
  show (∀ x y, M.rel R (fun i => (vec2 (Term.var 1) (Term.var 0) i).eval M (cons y (cons x env))) →
      M.fn F (vec1 x) = M.fn F (vec1 y)) ↔ _
  simp only [eval_vec2]
  exact Iff.rfl

theorem eval_creditCreatesMoney (M : Structure BankSig) (env : Nat → M.D) :
    creditCreatesMoney.eval M env ↔
      ∀ x y, M.rel .Cr (vec2 x y) → ¬ M.fn .Dep (vec1 x) = M.fn .Dep (vec1 y) := by
  show (∀ x y, M.rel .Cr (fun i => (vec2 (Term.var 1) (Term.var 0) i).eval M (cons y (cons x env))) →
      ¬ M.fn .Dep (vec1 x) = M.fn .Dep (vec1 y)) ↔ _
  simp only [eval_vec2]
  exact Iff.rfl

theorem eval_anyStep (M : Structure BankSig) (x y : M.D) :
    anyStep.eval M (argEnv M (vec2 x y)) ↔ (M.rel .Tr (vec2 x y) ∨ M.rel .Cr (vec2 x y)) := by
  show (M.rel .Tr (fun i => (vec2 (Term.var 0) (Term.var 1) i).eval M (argEnv M (vec2 x y))) ∨
        M.rel .Cr (fun i => (vec2 (Term.var 0) (Term.var 1) i).eval M (argEnv M (vec2 x y)))) ↔ _
  simp only [eval_vec2]
  exact Iff.rfl

/-- Banka kuramının modelleri, aksiyomların Lean okumasıyla. -/
theorem banking_models (M : Structure BankSig) :
    Banking.Models M ↔
      (∀ x y, M.rel .Tr (vec2 x y) → M.fn .Dep (vec1 x) = M.fn .Dep (vec1 y)) ∧
      (∀ x y, M.rel .Tr (vec2 x y) → M.fn .Net (vec1 x) = M.fn .Net (vec1 y)) ∧
      (∀ x y, M.rel .Cr (vec2 x y) → M.fn .Net (vec1 x) = M.fn .Net (vec1 y)) ∧
      (∀ x y, M.rel .Cr (vec2 x y) → ¬ M.fn .Dep (vec1 x) = M.fn .Dep (vec1 y)) := by
  constructor
  · rintro ⟨-, h⟩
    have e : M.D := M.dflt
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (eval_bankPreserves M (fun _ => e) _ _).1 (h _ (by simp [Banking]) _)
    · exact (eval_bankPreserves M (fun _ => e) _ _).1 (h _ (by simp [Banking]) _)
    · exact (eval_bankPreserves M (fun _ => e) _ _).1 (h _ (by simp [Banking]) _)
    · exact (eval_creditCreatesMoney M (fun _ => e)).1 (h _ (by simp [Banking]) _)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨trivial, ?_⟩
    intro ψ hψ env
    simp only [Banking, List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl | rfl | rfl
    · exact (eval_bankPreserves M env _ _).2 h1
    · exact (eval_bankPreserves M env _ _).2 h2
    · exact (eval_bankPreserves M env _ _).2 h3
    · exact (eval_creditCreatesMoney M env).2 h4

/-- Bir banka modeli: taşıyıcı ℕ, mevduat = durum, net = 0, virman = eşitlik,
kredi = bir artış. -/
abbrev bankModel : Structure BankSig where
  D := Nat
  dflt := 0
  fn := fun f v => match f with
    | .Dep => v 0
    | .Net => 0
  rel := fun r v => match r with
    | .Tr => v 0 = v 1
    | .Cr => v 1 = v 0 + 1

theorem bankModel_ok : Banking.Models bankModel := by
  rw [banking_models]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h; exact h
  · intro _ _ _; rfl
  · intro _ _ _; rfl
  · intro (x : Nat) (y : Nat) (h : y = x + 1) (h' : x = y); omega

/-- Fizik yasasının çevirisinin, okuma sözlüğüyle anlamı. -/
theorem physics_entails_conservation : Physics.Entails conservationLaw :=
  fun M hM => hM.2 _ (by simp [Physics])

def analogyNet : Analogy Physics Banking where
  σ := glossaryNet
  adm := fun _ _ => trivial
  preserves := by
    intro φ hφ M hM
    simp only [Physics, List.mem_cons, List.not_mem_nil, or_false] at hφ
    subst hφ
    rw [satisfaction]
    intro env
    rw [eval_conservationLaw]
    intro x y hxy
    have hs := (eval_anyStep M x y).1 hxy
    obtain ⟨-, h2, h3, -⟩ := (banking_models M).1 hM
    exact hs.elim (h2 x y) (h3 x y)
  model := bankModel
  model_ok := bankModel_ok

def analogyTransfers : Analogy Physics Banking where
  σ := glossaryTransfers
  adm := fun _ _ => trivial
  preserves := by
    intro φ hφ M hM
    simp only [Physics, List.mem_cons, List.not_mem_nil, or_false] at hφ
    subst hφ
    rw [satisfaction]
    intro env
    rw [eval_conservationLaw]
    intro x y hxy
    have hs : M.rel .Tr (vec2 x y) := by
      have := hxy
      simp only [SigMorph.reduct, glossaryTransfers, Formula.eval, eval_vec2] at this
      exact this
    exact ((banking_models M).1 hM).1 x y hs
  model := bankModel
  model_ok := bankModel_ok

def refutationDeposits :
    Refutation Physics Banking (fun _ => true) (fun _ => true) glossaryDeposits where
  φ := conservationLaw
  thm := physics_entails_conservation
  only := by decide
  cex := bankModel
  cex_ok := bankModel_ok
  fails := by
    intro h
    have := (eval_conservationLaw (glossaryDeposits.reduct bankModel) (fun _ => (0 : Nat))).1 ((satisfaction _ _ _).1 h (fun _ => (0 : Nat))) (0 : Nat) (1 : Nat)
      ((eval_anyStep bankModel (0 : Nat) (1 : Nat)).2 (Or.inr rfl))
    exact (by decide : ¬ (0 : Nat) = 1) this

theorem analogy_physics_banking_net :
    ∃ a : Analogy Physics Banking, a.σ = glossaryNet := ⟨analogyNet, rfl⟩

theorem analogy_physics_banking_transfers :
    ∃ a : Analogy Physics Banking, a.σ = glossaryTransfers := ⟨analogyTransfers, rfl⟩

theorem banking_net_conserved : Banking.Entails (glossaryNet.trF conservationLaw) :=
  transfer analogyNet physics_entails_conservation

theorem metaphor_physics_banking_deposits_semantic :
    Nonempty (Refutation Physics Banking (fun _ => true) (fun _ => true) glossaryDeposits) :=
  ⟨refutationDeposits⟩

theorem no_analogy_with_deposits_glossary :
    ¬ ∃ a : Analogy Physics Banking, a.σ = glossaryDeposits := by
  rintro ⟨a, ha⟩
  exact refutation_sound refutationDeposits a ⟨fun f _ => by rw [ha], fun r _ => by rw [ha]⟩

/-! ## Olgu ve değer -/

def verdictPrevent : PolicyVerdict WithNorm preventAct where
  entails := by
    rintro M ⟨-, hax⟩ env
    have hf := hax harmFact (by simp [WithNorm]) env
    have hn := hax harmNorm (by simp [WithNorm]) env
    exact hn _ hf
  world := { D := Unit, dflt := (), fn := fun _ _ => (), rel := fun _ _ => True }
  world_ok := by
    refine ⟨trivial, ?_⟩
    intro ψ hψ env
    simp only [WithNorm, List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl
    · exact trivial
    · exact fun _ _ => trivial
  g := fun _ _ => ()
  h := fun _ _ => False
  alt_adm := trivial
  fails := fun hs => hs (fun _ => ())

theorem policy_verdict_prevent_semantic : Nonempty (PolicyVerdict WithNorm preventAct) := ⟨verdictPrevent⟩

theorem facts_alone_no_verdict : ¬ Nonempty (PolicyVerdict FactsOnly preventAct) :=
  hume_law (fun ψ hψ => by
    simp only [FactsOnly, List.mem_cons, List.not_mem_nil, or_false] at hψ
    subst hψ
    rfl)

theorem roles_are_computed :
    harmFact.descriptive = true ∧ harmNorm.descriptive = false ∧ preventAct.descriptive = false := by
  decide

end Proofs
