import Hakem.Kernel

/-!
# Hakem — ispat kalkülüsü (v2)

İspatlar da veridir. `Proof`, birinci mertebe doğal çıkarımın (eşitlik ve dışlanan
orta ile) ispat terimidir. `infer`, bir ispatın bağlamdan hangi önermeyi çıkardığını
hesaplar. `check` bunu hedefle karşılaştırır.

Kalkülüs güven gerektirmez. Sağlamlığı (`calculus_sound`, `Challenge.lean`) bir kez
ispatlanır. O ispattan sonra `check T.axioms φ p = true` hesabı, `T.Entails φ` için
yeterlidir. Bu hesabı Lean çekirdeği yapar (`decide +kernel`); taktik, ayrıştırıcı ya
da derleyici devreye girmez.
-/

variable {S : Signature}

/-! ## Sözdizimsel eşitlik -/

def Term.beq [DecidableEq S.Fn] (t u : Term S) : Bool :=
  match t, u with
  | .var n,   .var m   => decide (n = m)
  | .dflt,    .dflt    => true
  | .app f a, .app g b =>
    if h : f = g then allFin _ (fun i => (a i).beq (b (Fin.cast (congrArg S.fnArity h) i)))
    else false
  | _, _ => false
termination_by structural t

def Formula.beq [DecidableEq S.Fn] [DecidableEq S.Rel] (φ ψ : Formula S) : Bool :=
  match φ, ψ with
  | .falsum,   .falsum   => true
  | .eq t u,   .eq t' u' => t.beq t' && u.beq u'
  | .rel r a,  .rel s b  =>
    if h : r = s then allFin _ (fun i => (a i).beq (b (Fin.cast (congrArg S.relArity h) i)))
    else false
  | .imp φ ψ,  .imp φ' ψ' => φ.beq φ' && ψ.beq ψ'
  | .and φ ψ,  .and φ' ψ' => φ.beq φ' && ψ.beq ψ'
  | .or φ ψ,   .or φ' ψ'  => φ.beq φ' && ψ.beq ψ'
  | .all φ,    .all φ'    => φ.beq φ'
  | .ex φ,     .ex φ'     => φ.beq φ'
  | _, _ => false
termination_by structural φ

/-! ## Bağlam işlemleri -/

/-- Serbest değişkenleri bir artır (bağlayıcıya girerken bağlam için). -/
def Formula.shift (φ : Formula S) : Formula S := φ.subst (fun n => .var (n + 1))

/-- Değişken 0'a `t` koy, ötekileri bir azalt. -/
def instSubst (t : Term S) : Nat → Term S
  | 0     => t
  | n + 1 => .var n

/-! ## İspat terimleri -/

inductive Proof (S : Signature) where
  /-- Bağlamdaki `i`. önerme. -/
  | hyp     : Nat → Proof S
  /-- `⊥ ⊢ φ`. -/
  | falsumE : Formula S → Proof S → Proof S
  /-- `φ, Γ ⊢ ψ` ise `Γ ⊢ φ → ψ`. -/
  | impI    : Formula S → Proof S → Proof S
  /-- `φ → ψ` ve `φ` ise `ψ`. -/
  | impE    : Proof S → Proof S → Proof S
  | andI    : Proof S → Proof S → Proof S
  | andE1   : Proof S → Proof S
  | andE2   : Proof S → Proof S
  /-- `φ` ise `φ ∨ ψ`. -/
  | orI1    : Formula S → Proof S → Proof S
  /-- `ψ` ise `φ ∨ ψ`. -/
  | orI2    : Formula S → Proof S → Proof S
  /-- `φ ∨ ψ`, `φ, Γ ⊢ χ`, `ψ, Γ ⊢ χ` ise `χ`. -/
  | orE     : Proof S → Proof S → Proof S → Proof S
  /-- `↑Γ ⊢ φ` ise `Γ ⊢ ∀ φ`. -/
  | allI    : Proof S → Proof S
  /-- `∀ φ` ise `φ[t]`. -/
  | allE    : Term S → Proof S → Proof S
  /-- `φ[t]` ise `∃ φ`. -/
  | exI     : Formula S → Term S → Proof S → Proof S
  /-- `∃ φ` ve `φ, ↑Γ ⊢ ↑χ` ise `χ`. -/
  | exE     : Formula S → Proof S → Proof S → Proof S
  /-- `t = t`. -/
  | refl    : Term S → Proof S
  /-- `t = u` ve `φ[t]` ise `φ[u]`. -/
  | eqE     : Formula S → Proof S → Proof S → Proof S
  /-- `φ ∨ ¬ φ`. -/
  | em      : Formula S → Proof S

/-- İspatın bağlamdan çıkardığı önerme (geçersizse `none`). -/
def infer [DecidableEq S.Fn] [DecidableEq S.Rel] : List (Formula S) → Proof S → Option (Formula S)
  | Γ, .hyp i => Γ[i]?
  | Γ, .falsumE φ p => match infer Γ p with
    | some .falsum => some φ
    | _ => none
  | Γ, .impI φ p => (infer (φ :: Γ) p).map (Formula.imp φ)
  | Γ, .impE p q => match infer Γ p, infer Γ q with
    | some (.imp φ ψ), some φ' => if φ.beq φ' then some ψ else none
    | _, _ => none
  | Γ, .andI p q => match infer Γ p, infer Γ q with
    | some φ, some ψ => some (.and φ ψ)
    | _, _ => none
  | Γ, .andE1 p => match infer Γ p with
    | some (.and φ _) => some φ
    | _ => none
  | Γ, .andE2 p => match infer Γ p with
    | some (.and _ ψ) => some ψ
    | _ => none
  | Γ, .orI1 ψ p => (infer Γ p).map (fun φ => .or φ ψ)
  | Γ, .orI2 φ p => (infer Γ p).map (fun ψ => .or φ ψ)
  | Γ, .orE p q r => match infer Γ p with
    | some (.or φ ψ) => match infer (φ :: Γ) q, infer (ψ :: Γ) r with
      | some χ, some χ' => if χ.beq χ' then some χ else none
      | _, _ => none
    | _ => none
  | Γ, .allI p => (infer (Γ.map Formula.shift) p).map Formula.all
  | Γ, .allE t p => match infer Γ p with
    | some (.all φ) => some (φ.subst (instSubst t))
    | _ => none
  | Γ, .exI φ t p => match infer Γ p with
    | some χ => if χ.beq (φ.subst (instSubst t)) then some (.ex φ) else none
    | none => none
  | Γ, .exE χ p q => match infer Γ p with
    | some (.ex φ) => match infer (φ :: Γ.map Formula.shift) q with
      | some χ' => if χ'.beq χ.shift then some χ else none
      | none => none
    | _ => none
  | _, .refl t => some (.eq t t)
  | Γ, .eqE φ p q => match infer Γ p, infer Γ q with
    | some (.eq t u), some χ => if χ.beq (φ.subst (instSubst t)) then some (φ.subst (instSubst u))
      else none
    | _, _ => none
  | _, .em φ => some (.or φ φ.not)

/-- `p`, `Γ` bağlamında `φ`'nin ispatıdır. -/
def check [DecidableEq S.Fn] [DecidableEq S.Rel] (Γ : List (Formula S)) (φ : Formula S)
    (p : Proof S) : Bool :=
  match infer Γ p with
  | some ψ => ψ.beq φ
  | none   => false
