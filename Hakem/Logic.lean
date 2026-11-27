/-!
# Hakem — logic

The language in which disciplines, analogies and arguments are written as **data**:
first-order logic with equality and de Bruijn variables.

* A discipline's vocabulary is a `Signature`. Every symbol has a **role**:
  `definitional`, `empirical` or `normative`. The role belongs to the symbol, not to the
  premise. Whether a formula is normative is computed from its symbols
  (`Formula.descriptive`); it is never declared.
* An analogy is a **symbol map** from one vocabulary to another (`SigMorph`). Each
  symbol goes to a term or formula of the target language. The map is the glossary
  (the anchors) itself.
* Meaning: `Structure` (carrier and interpretations) and `Formula.eval`.

This file contains only definitions. All theorems live in separate proof files and
require no trust.
-/

/-! ## Syntax -/

/-- Symbol role. `definitional`: structural vocabulary. `empirical`: value fixed by measurement.
`normative`: value fixed by a value choice. -/
inductive Role where
  | definitional
  | empirical
  | normative
  deriving DecidableEq, Repr

/-- Vocabulary: function and relation symbols, their arities and roles. -/
structure Signature where
  Fn       : Type
  Rel      : Type
  fnArity  : Fn → Nat
  relArity : Rel → Nat
  fnRole   : Fn → Role
  relRole  : Rel → Role

variable {S S₁ S₂ S₃ : Signature}

/-- Term. `var n`: de Bruijn variable. `dflt`: the distinguished element of every structure. -/
inductive Term (S : Signature) where
  | var  : Nat → Term S
  | dflt : Term S
  | app  : (f : S.Fn) → (Fin (S.fnArity f) → Term S) → Term S

/-- Formula. `all`/`ex` bind variable 0. -/
inductive Formula (S : Signature) where
  | falsum : Formula S
  | eq     : Term S → Term S → Formula S
  | rel    : (r : S.Rel) → (Fin (S.relArity r) → Term S) → Formula S
  | imp    : Formula S → Formula S → Formula S
  | and    : Formula S → Formula S → Formula S
  | or     : Formula S → Formula S → Formula S
  | all    : Formula S → Formula S
  | ex     : Formula S → Formula S

/-- `¬ φ`. -/
abbrev Formula.not (φ : Formula S) : Formula S := .imp φ .falsum

/-- `&&` over a finite family. -/
def allFin : (k : Nat) → (Fin k → Bool) → Bool
  | 0,     _ => true
  | k + 1, p => p 0 && allFin k (fun i => p i.succ)

/-- Every function symbol of the term satisfies `pf`. -/
def Term.onlySyms (pf : S.Fn → Bool) : Term S → Bool
  | .var _   => true
  | .dflt    => true
  | .app f a => pf f && allFin _ (fun i => (a i).onlySyms pf)

/-- Every symbol of the formula satisfies `pf`/`pr`. -/
def Formula.onlySyms (pf : S.Fn → Bool) (pr : S.Rel → Bool) : Formula S → Bool
  | .falsum  => true
  | .eq t u  => t.onlySyms pf && u.onlySyms pf
  | .rel r a => pr r && allFin _ (fun i => (a i).onlySyms pf)
  | .imp φ ψ => φ.onlySyms pf pr && ψ.onlySyms pf pr
  | .and φ ψ => φ.onlySyms pf pr && ψ.onlySyms pf pr
  | .or φ ψ  => φ.onlySyms pf pr && ψ.onlySyms pf pr
  | .all φ   => φ.onlySyms pf pr
  | .ex φ    => φ.onlySyms pf pr

/-- Descriptive formula: contains no normative symbol. -/
def Formula.descriptive (φ : Formula S) : Bool :=
  φ.onlySyms (fun f => decide (S.fnRole f ≠ .normative)) (fun r => decide (S.relRole r ≠ .normative))

/-- Paralel ikame. -/
def Term.subst (σ : Nat → Term S) : Term S → Term S
  | .var n   => σ n
  | .dflt    => .dflt
  | .app f a => .app f (fun i => (a i).subst σ)

/-- Increments every free variable. -/
def Term.shift (t : Term S) : Term S := t.subst (fun n => .var (n + 1))

/-- Substitution moved under a binder. -/
def liftSubst (σ : Nat → Term S) : Nat → Term S
  | 0     => .var 0
  | n + 1 => (σ n).shift

def Formula.subst : (Nat → Term S) → Formula S → Formula S
  | _, .falsum  => .falsum
  | σ, .eq t u  => .eq (t.subst σ) (u.subst σ)
  | σ, .rel r a => .rel r (fun i => (a i).subst σ)
  | σ, .imp φ ψ => .imp (φ.subst σ) (ψ.subst σ)
  | σ, .and φ ψ => .and (φ.subst σ) (ψ.subst σ)
  | σ, .or φ ψ  => .or (φ.subst σ) (ψ.subst σ)
  | σ, .all φ   => .all (φ.subst (liftSubst σ))
  | σ, .ex φ    => .ex (φ.subst (liftSubst σ))

/-! ## Anlam -/

/-- Structure: carrier, distinguished element, symbol interpretations. -/
structure Structure (S : Signature) where
  D    : Type
  dflt : D
  fn   : (f : S.Fn) → (Fin (S.fnArity f) → D) → D
  rel  : (r : S.Rel) → (Fin (S.relArity r) → D) → Prop

/-- Extend an environment with an element (variable 0). -/
def cons {α : Type} (d : α) (env : Nat → α) : Nat → α
  | 0     => d
  | n + 1 => env n

def Term.eval (M : Structure S) (env : Nat → M.D) : Term S → M.D
  | .var n   => env n
  | .dflt    => M.dflt
  | .app f a => M.fn f (fun i => (a i).eval M env)

def Formula.eval (M : Structure S) : (Nat → M.D) → Formula S → Prop
  | _,   .falsum  => False
  | env, .eq t u  => t.eval M env = u.eval M env
  | env, .rel r a => M.rel r (fun i => (a i).eval M env)
  | env, .imp φ ψ => φ.eval M env → ψ.eval M env
  | env, .and φ ψ => φ.eval M env ∧ ψ.eval M env
  | env, .or φ ψ  => φ.eval M env ∨ ψ.eval M env
  | env, .all φ   => ∀ d, φ.eval M (cons d env)
  | env, .ex φ    => ∃ d, φ.eval M (cons d env)

/-- The structure satisfies the formula in every environment (free variables universal). -/
def Structure.Sat (M : Structure S) (φ : Formula S) : Prop :=
  ∀ env, φ.eval M env

/-! ## Glossaries (the syntax of analogy) -/

/-- Symbol map. `fnMap f`: a term of the target language; `var i` is the `i`-th argument of `f`.
`relMap r`: a formula of the target language, likewise. -/
structure SigMorph (S₁ S₂ : Signature) where
  fnMap  : (f : S₁.Fn) → Term S₂
  relMap : (r : S₁.Rel) → Formula S₂

/-- Turn an argument vector into a substitution; variables beyond the arity become `dflt`. -/
def argSubst {k : Nat} (a : Fin k → Term S) : Nat → Term S :=
  fun n => if h : n < k then a ⟨n, h⟩ else .dflt

def SigMorph.trT (σ : SigMorph S₁ S₂) : Term S₁ → Term S₂
  | .var n   => .var n
  | .dflt    => .dflt
  | .app f a => (σ.fnMap f).subst (argSubst (fun i => σ.trT (a i)))

/-- Translation of a formula into the target language. -/
def SigMorph.trF (σ : SigMorph S₁ S₂) : Formula S₁ → Formula S₂
  | .falsum  => .falsum
  | .eq t u  => .eq (σ.trT t) (σ.trT u)
  | .rel r a => (σ.relMap r).subst (argSubst (fun i => σ.trT (a i)))
  | .imp φ ψ => .imp (σ.trF φ) (σ.trF ψ)
  | .and φ ψ => .and (σ.trF φ) (σ.trF ψ)
  | .or φ ψ  => .or (σ.trF φ) (σ.trF ψ)
  | .all φ   => .all (σ.trF φ)
  | .ex φ    => .ex (σ.trF φ)

/-- Composition of glossaries: first `σ`, then `τ`. -/
def SigMorph.comp (σ : SigMorph S₁ S₂) (τ : SigMorph S₂ S₃) : SigMorph S₁ S₃ where
  fnMap  := fun f => τ.trT (σ.fnMap f)
  relMap := fun r => τ.trF (σ.relMap r)

/-- Turn an argument vector into an environment; variables beyond the arity become the distinguished element. -/
def argEnv (M : Structure S) {k : Nat} (v : Fin k → M.D) : Nat → M.D :=
  fun n => if h : n < k then v ⟨n, h⟩ else M.dflt

/-- Reduct: reading a target world in the source language. The carrier stays the same; a
source symbol is interpreted as what the glossary points to in the target. -/
def SigMorph.reduct (σ : SigMorph S₁ S₂) (M : Structure S₂) : Structure S₁ where
  D    := M.D
  dflt := M.dflt
  fn   := fun f v => (σ.fnMap f).eval M (argEnv M v)
  rel  := fun r v => (σ.relMap r).eval M (argEnv M v)

/-- Two glossaries agree on the symbols selected by `pf`/`pr`. -/
def SigMorph.AgreeOn (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool) (σ τ : SigMorph S₁ S₂) : Prop :=
  (∀ f, pf f = true → σ.fnMap f = τ.fnMap f) ∧ (∀ r, pr r = true → σ.relMap r = τ.relMap r)

/-! ## Helpers for writing data -/

/-- One argument. -/
def vec1 {α : Type} (a : α) : Fin 1 → α := fun _ => a

/-- Two arguments: 0th and 1st. -/
def vec2 {α : Type} (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b

/-- Zero arguments. -/
def vec0 {α : Type} : Fin 0 → α := fun i => i.elim0

/-- Three arguments: 0th, 1st, 2nd. -/
def vec3 {α : Type} (a b c : α) : Fin 3 → α :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else c
