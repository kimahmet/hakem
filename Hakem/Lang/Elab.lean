import Hakem.Lang.Syntax
import Hakem.Finite

/-!
# Hakem dili — anlam

Bir belgenin **anlamı** burada sabitlenir: sözlük bildirimleri çekirdek imzalarına,
adlar sembollere, formüller çekirdek formüllerine çevrilir; her girdi bir çekirdek
önermesine (`Claim.Holds`) gider. `Doc.Holds s`: `s` metninin bütün iddiaları doğrudur.

İspatlar ve modeller (sertifikalar) anlamı etkilemez; yalnızca denetlenir
(`Hakem.Lang.Check`).
-/

/-- Bir sözlüğün bildirimleri: fonksiyon ve bağıntı sembolleri. -/
abbrev Decls := List SymDecl × List SymDecl

/-- Bildirimlerden çekirdek imzası: semboller konumlarıyla adlandırılır. -/
abbrev mkSig (d : Decls) : Signature where
  Fn := Fin d.1.length
  Rel := Fin d.2.length
  fnArity := fun i => (d.1.get i).arity
  relArity := fun i => (d.2.get i).arity
  fnRole := fun i => (d.1.get i).role
  relRole := fun i => (d.2.get i).role

/-- Adı `n` olan ilk bildirimin konumu. -/
def findName (n : String) : List SymDecl → Option Nat
  | [] => none
  | s :: ss => if s.name = n then some 0 else (findName n ss).map (· + 1)

def lookupFn (d : Decls) (n : String) : Option (Fin d.1.length) :=
  (findName n d.1).bind fun i => if h : i < d.1.length then some ⟨i, h⟩ else none

def lookupRel (d : Decls) (n : String) : Option (Fin d.2.length) :=
  (findName n d.2).bind fun i => if h : i < d.2.length then some ⟨i, h⟩ else none

/-- Adı `n` olan ilk kaydın değeri. -/
def assoc {α : Type} (n : String) : List (String × α) → Option α
  | [] => none
  | (k, v) :: rest => if k = n then some v else assoc n rest

/-! ## Terim ve formül çevirisi
`depth`: içinde bulunulan bağlayıcı sayısı. `vL` ↦ `var (depth − 1 − L)`.
`np`: eşlemede parametre sayısı. `pJ` ↦ `var (J + depth)`. -/

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

/-! ## Kuramlar ve eşlemeler -/

/-- Belgede tanımlanmış bir kuram. `lems`: belgede daha önce ispatlanmış lemmalar. -/
structure Thy where
  name     : String
  sig      : String
  decls    : Decls
  axNames  : List String
  axs      : List (Formula (mkSig decls))
  lemNames : List String
  lems     : List (Formula (mkSig decls))

/-- Kuramın çekirdek karşılığı: yalnızca aksiyomlar (lemmalar anlamın parçası değildir). -/
def Thy.theory (t : Thy) : Theory (mkSig t.decls) := { axioms := t.axs }

structure RMorph where
  s1   : String
  s2   : String
  fns  : List (String × RTerm)
  rels : List (String × RForm)

/-- Eşleme: kaynak sözlüğün her sembolü için hedefte bir terim/formül (parametreler `pJ`). -/
def elabMorph (d1 d2 : Decls) (m : RMorph) : Option (SigMorph (mkSig d1) (mkSig d2)) := do
  let ts ← d1.1.mapM (fun sd => (assoc sd.name m.fns).bind (elabTerm d2 0 sd.arity))
  let fs ← d1.2.mapM (fun sd => (assoc sd.name m.rels).bind (elabForm d2 0 sd.arity))
  if h1 : ts.length = d1.1.length then
    if h2 : fs.length = d1.2.length then
      some ⟨fun i => ts.get ⟨i.val, by rw [h1]; exact i.isLt⟩,
            fun r => fs.get ⟨r.val, by rw [h2]; exact r.isLt⟩⟩
    else none
  else none

/-! ## Sembol geçişi (metafor sertifikasının çapaları) -/

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

/-! ## İddialar ve anlamları -/

inductive Claim where
  | lemma   : String → (t : Thy) → Formula (mkSig t.decls) → RProof → Claim
  | analogy : String → (ta tb : Thy) → SigMorph (mkSig ta.decls) (mkSig tb.decls) →
      RModel → List (String × RProof) → Claim
  | refute  : String → (ta tb : Thy) → SigMorph (mkSig ta.decls) (mkSig tb.decls) →
      Formula (mkSig ta.decls) → RProof → RModel → Claim
  | verdict : String → (t : Thy) → Formula (mkSig t.decls) → RProof → RModel → RModel → Claim

/-- Bir iddianın anlamı. Sertifikalar (ispat, model) bu anlama girmez. -/
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

/-- Ağacın iddiaları. -/
def Doc.claimsTree (es : List SExp) : Option (List Claim) :=
  (decodeDoc es).bind (elabEntries ⟨[], [], []⟩)

/-- **Belge ağacının anlamı**: çevrilir ve bütün iddiaları doğrudur. -/
def Doc.HoldsTree (es : List SExp) : Prop :=
  ∃ cs, Doc.claimsTree es = some cs ∧ ∀ c ∈ cs, c.Holds

/-- **Belge metninin anlamı**: okunur ve ağacı doğrudur. -/
def Doc.Holds (s : String) : Prop :=
  ∃ es, readSExps s = some es ∧ Doc.HoldsTree es
