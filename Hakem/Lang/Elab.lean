import Hakem.Lang.Syntax
import Hakem.Finite

/-!
# Hakem language — meaning

The **meaning** of a document is fixed here: vocabulary declarations become kernel
signatures, names become symbols, formulas become kernel formulas, and every entry
becomes a kernel proposition (`Claim.Holds`). `Doc.Holds s`: every claim of text `s` holds.

Proofs and models (certificates) do not affect meaning; they are only checked
(`Hakem.Lang.Check`).
-/

/-- Declarations of a vocabulary: function and relation symbols. -/
abbrev Decls := List SymDecl × List SymDecl

/-- Kernel signature from declarations: symbols are named by position. -/
abbrev mkSig (d : Decls) : Signature where
  Fn := Fin d.1.length
  Rel := Fin d.2.length
  fnArity := fun i => (d.1.get i).arity
  relArity := fun i => (d.2.get i).arity
  fnRole := fun i => (d.1.get i).role
  relRole := fun i => (d.2.get i).role

/-- Position of the first declaration named `n`. -/
def findName (n : String) : List SymDecl → Option Nat
  | [] => none
  | s :: ss => if s.name = n then some 0 else (findName n ss).map (· + 1)

def lookupFn (d : Decls) (n : String) : Option (Fin d.1.length) :=
  (findName n d.1).bind fun i => if h : i < d.1.length then some ⟨i, h⟩ else none

def lookupRel (d : Decls) (n : String) : Option (Fin d.2.length) :=
  (findName n d.2).bind fun i => if h : i < d.2.length then some ⟨i, h⟩ else none

/-- Value of the first entry named `n`. -/
def assoc {α : Type} (n : String) : List (String × α) → Option α
  | [] => none
  | (k, v) :: rest => if k = n then some v else assoc n rest

/-! ## Elaborating terms and formulas
`depth`: number of enclosing binders. `vL` ↦ `var (depth − 1 − L)`.
`np`: number of parameters in a glossary entry. `pJ` ↦ `var (J + depth)`. -/

mutual
def elabTerm (d : Decls) (depth np : Nat) : RTerm → Option (Term (mkSig d))
  | .bvar l => if l < depth then some (.var (depth - 1 - l)) else none
  | .pvar j => if j < np then some (.var (j + depth)) else none
  | .app f args => do
    let i ← lookupFn d f
    let ts ← elabTerms d depth np args
    if h : ts.length = (d.1.get i).arity then
      some (.app i (fun k => ts.get ⟨k.val, by rw [h]; exact k.isLt⟩))
    else none

def elabTerms (d : Decls) (depth np : Nat) : List RTerm → Option (List (Term (mkSig d)))
  | [] => some []
  | t :: ts => do
    let t' ← elabTerm d depth np t
    let ts' ← elabTerms d depth np ts
    pure (t' :: ts')
end

def elabForm (d : Decls) : Nat → Nat → RForm → Option (Formula (mkSig d))
  | _,  _,  .fals => some .falsum
  | dp, np, .eq t u => do pure (.eq (← elabTerm d dp np t) (← elabTerm d dp np u))
  | dp, np, .rel r args => do
    let i ← lookupRel d r
    let ts ← elabTerms d dp np args
    if h : ts.length = (d.2.get i).arity then
      some (.rel i (fun k => ts.get ⟨k.val, by rw [h]; exact k.isLt⟩))
    else none
  | dp, np, .not a => do pure (Formula.not (← elabForm d dp np a))
  | dp, np, .imp a b => do pure (.imp (← elabForm d dp np a) (← elabForm d dp np b))
  | dp, np, .and a b => do pure (.and (← elabForm d dp np a) (← elabForm d dp np b))
  | dp, np, .or a b => do pure (.or (← elabForm d dp np a) (← elabForm d dp np b))
  | dp, np, .all a => do pure (.all (← elabForm d (dp + 1) np a))
  | dp, np, .ex a => do pure (.ex (← elabForm d (dp + 1) np a))

/-! ## Theories and glossaries -/

/-- A theory defined in the document. `lems`: lemmas proved earlier in the document. -/
structure Thy where
  name     : String
  sig      : String
  decls    : Decls
  axNames  : List String
  axs      : List (Formula (mkSig decls))
  lemNames : List String
  lems     : List (Formula (mkSig decls))

/-- Kernel counterpart of the theory: axioms only (lemmas are not part of the meaning). -/
def Thy.theory (t : Thy) : Theory (mkSig t.decls) := { axioms := t.axs }

structure RMorph where
  s1   : String
  s2   : String
  fns  : List (String × RTerm)
  rels : List (String × RForm)

/-- Glossary: a target term/formula for every source symbol (parameters `pJ`). -/
def elabMorph (d1 d2 : Decls) (m : RMorph) : Option (SigMorph (mkSig d1) (mkSig d2)) := do
  let ts ← d1.1.mapM (fun sd => (assoc sd.name m.fns).bind (elabTerm d2 0 sd.arity))
  let fs ← d1.2.mapM (fun sd => (assoc sd.name m.rels).bind (elabForm d2 0 sd.arity))
  if h1 : ts.length = d1.1.length then
    if h2 : fs.length = d1.2.length then
      some ⟨fun i => ts.get ⟨i.val, by rw [h1]; exact i.isLt⟩,
            fun r => fs.get ⟨r.val, by rw [h2]; exact r.isLt⟩⟩
    else none
  else none

/-! ## Symbol occurrence (the anchors of a metaphor certificate) -/

def Term.mentionsFn {S : Signature} [DecidableEq S.Fn] (f : S.Fn) : Term S → Bool
  | .var _   => false
  | .dflt    => false
  | .app g a => decide (g = f) || anyFin _ (fun i => (a i).mentionsFn f)

def Formula.mentionsFn {S : Signature} [DecidableEq S.Fn] (f : S.Fn) : Formula S → Bool
  | .falsum  => false
  | .eq t u  => t.mentionsFn f || u.mentionsFn f
  | .rel _ a => anyFin _ (fun i => (a i).mentionsFn f)
  | .imp φ ψ => φ.mentionsFn f || ψ.mentionsFn f
  | .and φ ψ => φ.mentionsFn f || ψ.mentionsFn f
  | .or φ ψ  => φ.mentionsFn f || ψ.mentionsFn f
  | .all φ   => φ.mentionsFn f
  | .ex φ    => φ.mentionsFn f

def Formula.mentionsRel {S : Signature} [DecidableEq S.Rel] (r : S.Rel) : Formula S → Bool
  | .falsum  => false
  | .eq _ _  => false
  | .rel q _ => decide (q = r)
  | .imp φ ψ => φ.mentionsRel r || ψ.mentionsRel r
  | .and φ ψ => φ.mentionsRel r || ψ.mentionsRel r
  | .or φ ψ  => φ.mentionsRel r || ψ.mentionsRel r
  | .all φ   => φ.mentionsRel r
  | .ex φ    => φ.mentionsRel r

/-! ## Claims and their meaning -/

inductive Claim where
  | lemma   : String → (t : Thy) → Formula (mkSig t.decls) → RProof → Claim
  | analogy : String → (ta tb : Thy) → SigMorph (mkSig ta.decls) (mkSig tb.decls) →
      RModel → List (String × RProof) → Claim
  | refute  : String → (ta tb : Thy) → SigMorph (mkSig ta.decls) (mkSig tb.decls) →
      Formula (mkSig ta.decls) → RProof → RModel → Claim
  | verdict : String → (t : Thy) → Formula (mkSig t.decls) → RProof → RModel → RModel → Claim

/-- The meaning of a claim. Certificates (proofs, models) are not part of it. -/
def Claim.Holds : Claim → Prop
  | .lemma _ t φ _ => t.theory.Entails φ
  | .analogy _ ta tb σ _ _ => ∃ a : Analogy ta.theory tb.theory, a.σ = σ
  | .refute _ ta tb σ φ _ _ =>
    Nonempty (Refutation ta.theory tb.theory (fun f => φ.mentionsFn f) (fun r => φ.mentionsRel r) σ)
  | .verdict _ t φ _ _ _ => Nonempty (PolicyVerdict t.theory φ)

def Claim.name : Claim → String
  | .lemma n .. | .analogy n .. | .refute n .. | .verdict n .. => n

structure Env where
  sigs   : List (String × Decls)
  thys   : List Thy
  morphs : List (String × RMorph)

def findThy (n : String) : List Thy → Option Thy
  | [] => none
  | t :: ts => if t.name = n then some t else findThy n ts

def Env.step (env : Env) : REntry → Option (Env × List Claim)
  | .sig n fs rs => some ({ env with sigs := (n, (fs, rs)) :: env.sigs }, [])
  | .theory n s axs => do
    let d ← assoc s env.sigs
    let fs ← axs.mapM (fun a => elabForm d 0 0 a.2)
    pure ({ env with thys := ⟨n, s, d, axs.map (·.1), fs, [], []⟩ :: env.thys }, [])
  | .lemma n tn a p => do
    let t ← findThy tn env.thys
    let φ ← elabForm t.decls 0 0 a
    let t' : Thy := { t with lemNames := t.lemNames ++ [n], lems := t.lems ++ [φ] }
    pure ({ env with thys := t' :: env.thys.filter (fun x => x.name != tn) }, [.lemma n t φ p])
  | .morph n s1 s2 fs rs => some ({ env with morphs := (n, ⟨s1, s2, fs, rs⟩) :: env.morphs }, [])
  | .analogy n a b m md obs => do
    let ta ← findThy a env.thys
    let tb ← findThy b env.thys
    let rm ← assoc m env.morphs
    if rm.s1 = ta.sig ∧ rm.s2 = tb.sig then
      let σ ← elabMorph ta.decls tb.decls rm
      pure (env, [.analogy n ta tb σ md obs])
    else none
  | .refute n a b m f p md => do
    let ta ← findThy a env.thys
    let tb ← findThy b env.thys
    let rm ← assoc m env.morphs
    if rm.s1 = ta.sig ∧ rm.s2 = tb.sig then
      let σ ← elabMorph ta.decls tb.decls rm
      let φ ← elabForm ta.decls 0 0 f
      pure (env, [.refute n ta tb σ φ p md])
    else none
  | .verdict n tn f p w alt => do
    let t ← findThy tn env.thys
    let φ ← elabForm t.decls 0 0 f
    pure (env, [.verdict n t φ p w alt])

def elabEntries : Env → List REntry → Option (List Claim)
  | _, [] => some []
  | env, e :: es => do
    let (env', cs) ← env.step e
    let cs' ← elabEntries env' es
    pure (cs ++ cs')

/-- The claims of a tree. -/
def Doc.claimsTree (es : List SExp) : Option (List Claim) :=
  (decodeDoc es).bind (elabEntries ⟨[], [], []⟩)

/-- **Meaning of a document tree**: it elaborates and all its claims hold. -/
def Doc.HoldsTree (es : List SExp) : Prop :=
  ∃ cs, Doc.claimsTree es = some cs ∧ ∀ c ∈ cs, c.Holds

/-- **Meaning of a document text**: it reads into a tree that holds. -/
def Doc.Holds (s : String) : Prop :=
  ∃ es, readSExps s = some es ∧ Doc.HoldsTree es
