import Hakem.Lang.SExp
import Hakem.Logic

/-!
# Hakem language — syntax

A document is a sequence of entries. Names are strings; variables are:
* `vL`: bound variable, `L` the binder level (0, 1, … from the outside in),
* `pJ`: in a glossary, the `J`-th argument of the symbol being mapped.

```
(hakem 1)
(sig NAME (fn NAME ARITY ROLE)* (rel NAME ARITY ROLE)*)  ; ROLE: definitional | empirical | normative
(theory NAME SIG (ax NAME FORMULA)*)
(lemma NAME THEORY FORMULA PROOF)
(morph NAME SIG1 SIG2 (fn NAME TERM)* (rel NAME FORMULA)*)
(analogy NAME THEORY1 THEORY2 MORPH MODEL (oblig AXIOM-NAME PROOF)*)
(refute NAME THEORY1 THEORY2 MORPH FORMULA PROOF MODEL)
(verdict NAME THEORY FORMULA PROOF MODEL (alt (fn NAME VALUE*)* (rel NAME VALUE*)*))
```

Formula: `false`, `(= T U)`, `(not A)`, `(imp A B)`, `(and A B)`, `(or A B)`, `(all A)`,
`(ex A)`, `(R T*)`. Term: `vL`, `pJ`, `c`, `(f T*)`.
Proof: `(hyp N)`, `(ax NAME)`, `(falsumE A P)`, `(impI A P)`, `(impE P Q)`, `(andI P Q)`,
`(andE1 P)`, `(andE2 P)`, `(orI1 B P)`, `(orI2 A P)`, `(orE P Q R)`, `(allI P)`,
`(allE T P)`, `(exI (lam A) T P)`, `(exE C P Q)`, `(refl T)`, `(eqE (lam A) P Q)`, `(em A)`.
Model: `(model SIZE (fn NAME VALUE*)* (rel NAME VALUE*)*)`; table order:
the argument vector `(a0, a1, …)` is at position `a0 + B·a1 + B²·a2 + …`.
-/

inductive RTerm where
  | bvar : Nat → RTerm
  | pvar : Nat → RTerm
  | app  : String → List RTerm → RTerm
  deriving Repr, Inhabited

inductive RForm where
  | fals : RForm
  | eq   : RTerm → RTerm → RForm
  | rel  : String → List RTerm → RForm
  | not  : RForm → RForm
  | imp  : RForm → RForm → RForm
  | and  : RForm → RForm → RForm
  | or   : RForm → RForm → RForm
  | all  : RForm → RForm
  | ex   : RForm → RForm
  deriving Repr, Inhabited

inductive RProof where
  | hyp     : Nat → RProof
  | ax      : String → RProof
  | falsumE : RForm → RProof → RProof
  | impI    : RForm → RProof → RProof
  | impE    : RProof → RProof → RProof
  | andI    : RProof → RProof → RProof
  | andE1   : RProof → RProof
  | andE2   : RProof → RProof
  | orI1    : RForm → RProof → RProof
  | orI2    : RForm → RProof → RProof
  | orE     : RProof → RProof → RProof → RProof
  | allI    : RProof → RProof
  | allE    : RTerm → RProof → RProof
  | exI     : RForm → RTerm → RProof → RProof
  | exE     : RForm → RProof → RProof → RProof
  | refl    : RTerm → RProof
  | eqE     : RForm → RProof → RProof → RProof
  | em      : RForm → RProof
  deriving Repr, Inhabited

/-- Finite model: size and symbol tables. -/
structure RModel where
  size : Nat
  fns  : List (String × List Nat)
  rels : List (String × List Nat)
  deriving Repr, Inhabited

/-- A symbol declaration in a vocabulary. -/
structure SymDecl where
  name  : String
  arity : Nat
  role  : Role
  deriving Repr

inductive REntry where
  | sig     : String → List SymDecl → List SymDecl → REntry
  | theory  : String → String → List (String × RForm) → REntry
  | lemma   : String → String → RForm → RProof → REntry
  | morph   : String → String → String → List (String × RTerm) → List (String × RForm) → REntry
  | analogy : String → String → String → String → RModel → List (String × RProof) → REntry
  | refute  : String → String → String → String → RForm → RProof → RModel → REntry
  | verdict : String → String → RForm → RProof → RModel → RModel → REntry
  deriving Repr, Inhabited

/-! ## From tree to syntax -/

def atomStr : SExp → Option String
  | .atom s => some s
  | _ => none

/-- Decimal digits (non-empty). Computable in the kernel. -/
def digitsVal : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    if '0' ≤ c ∧ c ≤ '9' then digitsVal cs (acc * 10 + (c.toNat - '0'.toNat)) else none

def natOf (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | cs => digitsVal cs 0

def atomNat (x : SExp) : Option Nat := (atomStr x).bind natOf

def parseRole : String → Option Role
  | "definitional" => some .definitional
  | "empirical" => some .empirical
  | "normative" => some .normative
  | _ => none

def varOf (s : String) : Option RTerm :=
  match s.toList with
  | 'v' :: rest => (natOf (String.ofList rest)).map RTerm.bvar
  | 'p' :: rest => (natOf (String.ofList rest)).map RTerm.pvar
  | _ => none

mutual
def decodeTerm : SExp → Option RTerm
  | .atom s => some ((varOf s).getD (.app s []))
  | .list (.atom f :: args) => (decodeTerms args).map (RTerm.app f)
  | _ => none

def decodeTerms : List SExp → Option (List RTerm)
  | [] => some []
  | x :: xs => do
    let t ← decodeTerm x
    let ts ← decodeTerms xs
    pure (t :: ts)
end

def decodeForm : SExp → Option RForm
  | .atom "false" => some .fals
  | .list [.atom "=", a, b] => do pure (.eq (← decodeTerm a) (← decodeTerm b))
  | .list [.atom "not", a] => do pure (.not (← decodeForm a))
  | .list [.atom "imp", a, b] => do pure (.imp (← decodeForm a) (← decodeForm b))
  | .list [.atom "and", a, b] => do pure (.and (← decodeForm a) (← decodeForm b))
  | .list [.atom "or", a, b] => do pure (.or (← decodeForm a) (← decodeForm b))
  | .list [.atom "all", a] => do pure (.all (← decodeForm a))
  | .list [.atom "ex", a] => do pure (.ex (← decodeForm a))
  | .list (.atom r :: args) => (decodeTerms args).map (RForm.rel r)
  | _ => none

/-- `(lam A)`: a formula body that opens one binder. -/
def decodeLam : SExp → Option RForm
  | .list [.atom "lam", a] => decodeForm a
  | _ => none

def decodeProof : SExp → Option RProof
  | .list [.atom "hyp", n] => (atomNat n).map RProof.hyp
  | .list [.atom "ax", n] => (atomStr n).map RProof.ax
  | .list [.atom "falsumE", a, p] => do pure (.falsumE (← decodeForm a) (← decodeProof p))
  | .list [.atom "impI", a, p] => do pure (.impI (← decodeForm a) (← decodeProof p))
  | .list [.atom "impE", p, q] => do pure (.impE (← decodeProof p) (← decodeProof q))
  | .list [.atom "andI", p, q] => do pure (.andI (← decodeProof p) (← decodeProof q))
  | .list [.atom "andE1", p] => do pure (.andE1 (← decodeProof p))
  | .list [.atom "andE2", p] => do pure (.andE2 (← decodeProof p))
  | .list [.atom "orI1", b, p] => do pure (.orI1 (← decodeForm b) (← decodeProof p))
  | .list [.atom "orI2", a, p] => do pure (.orI2 (← decodeForm a) (← decodeProof p))
  | .list [.atom "orE", p, q, r] => do pure (.orE (← decodeProof p) (← decodeProof q) (← decodeProof r))
  | .list [.atom "allI", p] => do pure (.allI (← decodeProof p))
  | .list [.atom "allE", t, p] => do pure (.allE (← decodeTerm t) (← decodeProof p))
  | .list [.atom "exI", a, t, p] => do pure (.exI (← decodeLam a) (← decodeTerm t) (← decodeProof p))
  | .list [.atom "exE", c, p, q] => do pure (.exE (← decodeForm c) (← decodeProof p) (← decodeProof q))
  | .list [.atom "refl", t] => do pure (.refl (← decodeTerm t))
  | .list [.atom "eqE", a, p, q] => do pure (.eqE (← decodeLam a) (← decodeProof p) (← decodeProof q))
  | .list [.atom "em", a] => do pure (.em (← decodeForm a))
  | _ => none

def decodeNats : List SExp → Option (List Nat) := List.mapM atomNat

/-- Split `(fn NAME VALUE*)` and `(rel NAME VALUE*)` tables. -/
def decodeTables : List SExp → Option (List (String × List Nat) × List (String × List Nat))
  | [] => some ([], [])
  | .list (.atom "fn" :: .atom n :: vs) :: rest => do
    let (fs, rs) ← decodeTables rest
    pure ((n, ← decodeNats vs) :: fs, rs)
  | .list (.atom "rel" :: .atom n :: vs) :: rest => do
    let (fs, rs) ← decodeTables rest
    pure (fs, (n, ← decodeNats vs) :: rs)
  | _ => none

def decodeModel : SExp → Option RModel
  | .list (.atom "model" :: n :: ts) => do
    let (fs, rs) ← decodeTables ts
    pure ⟨← atomNat n, fs, rs⟩
  | _ => none

def decodeAlt : SExp → Option RModel
  | .list (.atom "alt" :: ts) => do
    let (fs, rs) ← decodeTables ts
    pure ⟨0, fs, rs⟩
  | _ => none

def decodeSyms : List SExp → Option (List SymDecl × List SymDecl)
  | [] => some ([], [])
  | .list [.atom "fn", .atom n, k, .atom r] :: rest => do
    let (fs, rs) ← decodeSyms rest
    pure (⟨n, ← atomNat k, ← parseRole r⟩ :: fs, rs)
  | .list [.atom "rel", .atom n, k, .atom r] :: rest => do
    let (fs, rs) ← decodeSyms rest
    pure (fs, ⟨n, ← atomNat k, ← parseRole r⟩ :: rs)
  | _ => none

def decodeAxioms : List SExp → Option (List (String × RForm))
  | [] => some []
  | .list [.atom "ax", .atom n, a] :: rest => do pure ((n, ← decodeForm a) :: (← decodeAxioms rest))
  | _ => none

def decodeMaps : List SExp → Option (List (String × RTerm) × List (String × RForm))
  | [] => some ([], [])
  | .list [.atom "fn", .atom n, t] :: rest => do
    let (fs, rs) ← decodeMaps rest
    pure ((n, ← decodeTerm t) :: fs, rs)
  | .list [.atom "rel", .atom n, a] :: rest => do
    let (fs, rs) ← decodeMaps rest
    pure (fs, (n, ← decodeForm a) :: rs)
  | _ => none

def decodeObligs : List SExp → Option (List (String × RProof))
  | [] => some []
  | .list [.atom "oblig", .atom n, p] :: rest => do pure ((n, ← decodeProof p) :: (← decodeObligs rest))
  | _ => none

def decodeEntry : SExp → Option REntry
  | .list (.atom "sig" :: .atom n :: syms) => do
    let (fs, rs) ← decodeSyms syms
    pure (.sig n fs rs)
  | .list (.atom "theory" :: .atom n :: .atom s :: axs) => do pure (.theory n s (← decodeAxioms axs))
  | .list [.atom "lemma", .atom n, .atom t, a, p] => do pure (.lemma n t (← decodeForm a) (← decodeProof p))
  | .list (.atom "morph" :: .atom n :: .atom s1 :: .atom s2 :: ms) => do
    let (fs, rs) ← decodeMaps ms
    pure (.morph n s1 s2 fs rs)
  | .list (.atom "analogy" :: .atom n :: .atom a :: .atom b :: .atom m :: md :: obs) => do
    pure (.analogy n a b m (← decodeModel md) (← decodeObligs obs))
  | .list [.atom "refute", .atom n, .atom a, .atom b, .atom m, f, p, md] => do
    pure (.refute n a b m (← decodeForm f) (← decodeProof p) (← decodeModel md))
  | .list [.atom "verdict", .atom n, .atom t, f, p, w, alt] => do
    pure (.verdict n t (← decodeForm f) (← decodeProof p) (← decodeModel w) (← decodeAlt alt))
  | _ => none

/-- Document: the `(hakem 1)` header and entries. -/
def decodeDoc : List SExp → Option (List REntry)
  | .list [.atom "hakem", .atom "1"] :: rest => rest.mapM decodeEntry
  | _ => none
