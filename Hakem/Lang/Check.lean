import Hakem.Lang.Elab

/-!
# Hakem dili — denetleyici

`checkDoc s = true` ise `Doc.Holds s` (sağlamlık: `checkDoc_sound`, `Challenge.lean`).
Denetleyici güven gerektirmez: sağlamlığı bir kez ispatlanır. Derlenmiş kodla hızlı
çalıştırılabilir (`lake exe hakem`) ya da çekirdekte hesaplanabilir (`decide +kernel`).
-/

/-- Adın listedeki konumu. -/
def idxOfStr (n : String) : List String → Option Nat
  | [] => none
  | x :: xs => if x = n then some 0 else (idxOfStr n xs).map (· + 1)

/-- İspat çevirisi. `names`: kuramın aksiyom ve lemma adları (bağlamın küresel kısmı).
`dp`: bağlayıcı derinliği; `nl`: yerel hipotez sayısı. -/
def elabProof (d : Decls) (names : List String) : Nat → Nat → RProof → Option (Proof (mkSig d))
  | _,  _,  .hyp n => some (.hyp n)
  | _,  nl, .ax a => (idxOfStr a names).map (fun i => .hyp (nl + i))
  | dp, nl, .falsumE a p => do pure (.falsumE (← elabForm d dp 0 a) (← elabProof d names dp nl p))
  | dp, nl, .impI a p => do pure (.impI (← elabForm d dp 0 a) (← elabProof d names dp (nl + 1) p))
  | dp, nl, .impE p q => do pure (.impE (← elabProof d names dp nl p) (← elabProof d names dp nl q))
  | dp, nl, .andI p q => do pure (.andI (← elabProof d names dp nl p) (← elabProof d names dp nl q))
  | dp, nl, .andE1 p => do pure (.andE1 (← elabProof d names dp nl p))
  | dp, nl, .andE2 p => do pure (.andE2 (← elabProof d names dp nl p))
  | dp, nl, .orI1 b p => do pure (.orI1 (← elabForm d dp 0 b) (← elabProof d names dp nl p))
  | dp, nl, .orI2 a p => do pure (.orI2 (← elabForm d dp 0 a) (← elabProof d names dp nl p))
  | dp, nl, .orE p q r => do
    pure (.orE (← elabProof d names dp nl p) (← elabProof d names dp (nl + 1) q)
      (← elabProof d names dp (nl + 1) r))
  | dp, nl, .allI p => do pure (.allI (← elabProof d names (dp + 1) nl p))
  | dp, nl, .allE t p => do pure (.allE (← elabTerm d dp 0 t) (← elabProof d names dp nl p))
  | dp, nl, .exI a t p => do
    pure (.exI (← elabForm d (dp + 1) 0 a) (← elabTerm d dp 0 t) (← elabProof d names dp nl p))
  | dp, nl, .exE c p q => do
    pure (.exE (← elabForm d dp 0 c) (← elabProof d names dp nl p)
      (← elabProof d names (dp + 1) (nl + 1) q))
  | dp, _,  .refl t => do pure (.refl (← elabTerm d dp 0 t))
  | dp, nl, .eqE a p q => do
    pure (.eqE (← elabForm d (dp + 1) 0 a) (← elabProof d names dp nl p) (← elabProof d names dp nl q))
  | dp, _,  .em a => do pure (.em (← elabForm d dp 0 a))

/-- Argüman vektörünün tablodaki konumu: `a0 + B·a1 + B²·a2 + …`. -/
def encodeIdx : (k : Nat) → (Fin k → Nat) → Nat → Nat
  | 0,     _, _ => 0
  | k + 1, v, b => v 0 + b * encodeIdx k (fun i => v i.succ) b

def tableFn (n : Nat) (tbl : List Nat) {k : Nat} (v : Fin k → Fin (n + 1)) : Fin (n + 1) :=
  ⟨(tbl.getD (encodeIdx k (fun i => (v i).val) (n + 1)) 0) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

def tableRel (n : Nat) (tbl : List Nat) {k : Nat} (v : Fin k → Fin (n + 1)) : Bool :=
  tbl.getD (encodeIdx k (fun i => (v i).val) (n + 1)) 0 != 0

def elabModel (d : Decls) (m : RModel) : Option (FinStructure (mkSig d)) :=
  match m.size with
  | 0 => none
  | n + 1 => some
    { n := n
      fn := fun i v => tableFn n ((assoc (d.1.get i).name m.fns).getD []) v
      rel := fun r v => tableRel n ((assoc (d.2.get r).name m.rels).getD []) v }

/-- Alternatif dünyanın tabloları (yalnızca normatif semboller kullanılır). -/
def altFn (d : Decls) (W : FinStructure (mkSig d)) (alt : RModel) :
    (f : Fin d.1.length) → (Fin ((mkSig d).fnArity f) → Fin (W.n + 1)) → Fin (W.n + 1) :=
  fun f v => match assoc (d.1.get f).name alt.fns with
    | some tbl => tableFn W.n tbl v
    | none => W.fn f v

def altRel (d : Decls) (W : FinStructure (mkSig d)) (alt : RModel) :
    (r : Fin d.2.length) → (Fin ((mkSig d).relArity r) → Fin (W.n + 1)) → Bool :=
  fun r v => match assoc (d.2.get r).name alt.rels with
    | some tbl => tableRel W.n tbl v
    | none => W.rel r v

/-- Kuramın bağlamında bir ispatı denetle: aksiyomlar ve önceki lemmalar kullanılabilir. -/
def checkIn (t : Thy) (φ : Formula (mkSig t.decls)) (p : RProof) : Bool :=
  match elabProof t.decls (t.axNames ++ t.lemNames) 0 0 p with
  | some p' => check (t.axs ++ t.lems) φ p'
  | none => false

def checkModel (t : Thy) (m : RModel) : Bool :=
  match elabModel t.decls m with
  | some M => M.checkTheory t.theory
  | none => false

def checkClaim : Claim → Bool
  | .lemma _ t φ p => checkIn t φ p
  | .analogy _ ta tb σ md obs =>
    obs.map (·.1) == ta.axNames && obs.length == ta.axs.length &&
    (ta.axs.zip obs).all (fun x => checkIn tb (σ.trF x.1) x.2.2) && checkModel tb md
  | .refute _ ta tb σ φ p md =>
    checkIn ta φ p &&
    (match elabModel tb.decls md with
     | some M => M.checkTheory tb.theory && M.refutes (σ.trF φ)
     | none => false)
  | .verdict _ t φ p w alt =>
    checkIn t φ p &&
    (match elabModel t.decls w with
     | some W => W.checkTheory t.theory && (W.reinterpB (altFn t.decls W alt) (altRel t.decls W alt)).refutes φ
     | none => false)

/-- Belge ağacı denetimi (çekirdekte hesaplanabilir). -/
def checkTree (es : List SExp) : Bool :=
  match Doc.claimsTree es with
  | some cs => cs.all checkClaim
  | none => false

/-- Belge metni denetimi. -/
def checkDoc (s : String) : Bool :=
  match readSExps s with
  | some es => checkTree es
  | none => false
