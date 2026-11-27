import Hakem.Calculus

/-!
# Hakem — finite models

Counterexamples and witness worlds are data too. `FinStructure` is a structure with
carrier `Fin (n+1)` and computable interpretations. `evalB` **computes** a formula in it.
For closed formulas computation agrees with meaning (`finite_sat_iff`, `Challenge.lean`).
So the claims "this structure is a model of this theory" and "this formula is false in
this structure" are checked by kernel computation (`decide +kernel`).
-/

variable {S : Signature}

/-- `||` over a finite family. -/
def anyFin (k : Nat) (p : Fin k → Bool) : Bool := !allFin k (fun i => !p i)

/-- Every variable of the term is `< k`. -/
def Term.varsBelow (k : Nat) : Term S → Bool
  | .var n   => decide (n < k)
  | .dflt    => true
  | .app _ a => allFin _ (fun i => (a i).varsBelow k)

/-- Every free variable of the formula is `< k`. -/
def Formula.varsBelow : Nat → Formula S → Bool
  | _, .falsum  => true
  | k, .eq t u  => t.varsBelow k && u.varsBelow k
  | k, .rel _ a => allFin _ (fun i => (a i).varsBelow k)
  | k, .imp φ ψ => φ.varsBelow k && ψ.varsBelow k
  | k, .and φ ψ => φ.varsBelow k && ψ.varsBelow k
  | k, .or φ ψ  => φ.varsBelow k && ψ.varsBelow k
  | k, .all φ   => φ.varsBelow (k + 1)
  | k, .ex φ    => φ.varsBelow (k + 1)

/-- Closed formula (sentence). -/
def Formula.closed (φ : Formula S) : Bool := φ.varsBelow 0

/-- Finite structure: carrier `Fin (n+1)`, functions, and `Bool`-valued relations. -/
structure FinStructure (S : Signature) where
  n   : Nat
  fn  : (f : S.Fn) → (Fin (S.fnArity f) → Fin (n + 1)) → Fin (n + 1)
  rel : (r : S.Rel) → (Fin (S.relArity r) → Fin (n + 1)) → Bool

/-- The semantic counterpart of a finite structure. The distinguished element is 0. -/
abbrev FinStructure.toStructure (M : FinStructure S) : Structure S where
  D    := Fin (M.n + 1)
  dflt := 0
  fn   := M.fn
  rel  := fun r v => M.rel r v = true

/-- Computing a formula in a finite structure. -/
def FinStructure.evalB (M : FinStructure S) : (Nat → Fin (M.n + 1)) → Formula S → Bool
  | _,   .falsum  => false
  | env, .eq t u  => decide (t.eval M.toStructure env = u.eval M.toStructure env)
  | env, .rel r a => M.rel r (fun i => (a i).eval M.toStructure env)
  | env, .imp φ ψ => !(M.evalB env φ) || M.evalB env ψ
  | env, .and φ ψ => M.evalB env φ && M.evalB env ψ
  | env, .or φ ψ  => M.evalB env φ || M.evalB env ψ
  | env, .all φ   => allFin (M.n + 1) (fun d => M.evalB (cons d env) φ)
  | env, .ex φ    => anyFin (M.n + 1) (fun d => M.evalB (cons d env) φ)

/-- The finite structure satisfies every axiom of the theory (as closed formulas). -/
def FinStructure.checkTheory (M : FinStructure S) (T : Theory S) : Bool :=
  T.axioms.all (fun ψ => ψ.closed && M.evalB (fun _ => 0) ψ)

/-- A closed formula is false in the finite structure. -/
def FinStructure.refutes (M : FinStructure S) (φ : Formula S) : Bool :=
  φ.closed && !(M.evalB (fun _ => 0) φ)

/-- The finite alternative obtained by changing the normative symbols of a witness world.
`g`/`h` are used only on normative symbols. -/
def FinStructure.reinterpB (M : FinStructure S)
    (g : (f : S.Fn) → (Fin (S.fnArity f) → Fin (M.n + 1)) → Fin (M.n + 1))
    (h : (r : S.Rel) → (Fin (S.relArity r) → Fin (M.n + 1)) → Bool) : FinStructure S where
  n   := M.n
  fn  := fun f => if S.fnRole f = .normative then g f else M.fn f
  rel := fun r => if S.relRole r = .normative then h r else M.rel r
