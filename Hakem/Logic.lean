/-!
# Hakem — mantık (v2)

Disiplinlerin, analojilerin ve argümanların **veri** olarak yazıldığı dil:
birinci mertebe mantık, eşitlikli, de Bruijn değişkenli.

* Bir disiplinin sözlüğü bir `Signature`'dır. Her sembolün bir **rolü** vardır:
  `tanim`, `ampirik` ya da `normatif`. Rol öncüle değil sembole aittir. Bir
  önermenin normatif olup olmadığı içindeki sembollerden hesaplanır
  (`Formula.descriptive`); beyan edilmez.
* Bir analoji, bir sözlükten ötekine **sembol eşlemesidir** (`SigMorph`). Her
  sembol hedef dilde bir terime ya da formüle gider. Eşleme sözlüğün (çapaların)
  kendisidir.
* Anlam: `Structure` (taşıyıcı ve yorumlar) ile `Formula.eval`.

Bu dosyada yalnızca tanımlar vardır. Bütün teoremler ayrı ispat dosyalarındadır ve
güven gerektirmez.
-/

/-! ## Sözdizimi -/

/-- Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
`normatif`: değeri değer seçimiyle belirlenir. -/
inductive Role where
  | tanim
  | ampirik
  | normatif
  deriving DecidableEq, Repr

/-- Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri. -/
structure Signature where
  Fn       : Type
  Rel      : Type
  fnArity  : Fn → Nat
  relArity : Rel → Nat
  fnRole   : Fn → Role
  relRole  : Rel → Role

variable {S S₁ S₂ S₃ : Signature}

/-- Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi. -/
inductive Term (S : Signature) where
  | var  : Nat → Term S
  | dflt : Term S
  | app  : (f : S.Fn) → (Fin (S.fnArity f) → Term S) → Term S

/-- Formül. `all`/`ex` değişken 0'ı bağlar. -/
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

/-- Sonlu bir aileye `&&`. -/
def allFin : (k : Nat) → (Fin k → Bool) → Bool
  | 0,     _ => true
  | k + 1, p => p 0 && allFin k (fun i => p i.succ)

/-- Terimdeki her fonksiyon sembolü `pf`'yi sağlar. -/
def Term.onlySyms (pf : S.Fn → Bool) : Term S → Bool
  | .var _   => true
  | .dflt    => true
  | .app f a => pf f && allFin _ (fun i => (a i).onlySyms pf)

/-- Formüldeki her sembol `pf`/`pr`'yi sağlar. -/
def Formula.onlySyms (pf : S.Fn → Bool) (pr : S.Rel → Bool) : Formula S → Bool
  | .falsum  => true
  | .eq t u  => t.onlySyms pf && u.onlySyms pf
  | .rel r a => pr r && allFin _ (fun i => (a i).onlySyms pf)
  | .imp φ ψ => φ.onlySyms pf pr && ψ.onlySyms pf pr
  | .and φ ψ => φ.onlySyms pf pr && ψ.onlySyms pf pr
  | .or φ ψ  => φ.onlySyms pf pr && ψ.onlySyms pf pr
  | .all φ   => φ.onlySyms pf pr
  | .ex φ    => φ.onlySyms pf pr

/-- Betimsel formül: hiçbir normatif sembol içermez. -/
def Formula.descriptive (φ : Formula S) : Bool :=
  φ.onlySyms (fun f => decide (S.fnRole f ≠ .normatif)) (fun r => decide (S.relRole r ≠ .normatif))

/-- Paralel ikame. -/
def Term.subst (σ : Nat → Term S) : Term S → Term S
  | .var n   => σ n
  | .dflt    => .dflt
  | .app f a => .app f (fun i => (a i).subst σ)

/-- Bütün serbest değişkenleri bir artırır. -/
def Term.shift (t : Term S) : Term S := t.subst (fun n => .var (n + 1))

/-- Bağlayıcının altına geçen ikame. -/
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

/-- Yapı: taşıyıcı, seçkin öğe, sembol yorumları. -/
structure Structure (S : Signature) where
  D    : Type
  dflt : D
  fn   : (f : S.Fn) → (Fin (S.fnArity f) → D) → D
  rel  : (r : S.Rel) → (Fin (S.relArity r) → D) → Prop

/-- Ortamı bir öğeyle genişlet (değişken 0). -/
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

/-- Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel). -/
def Structure.Sat (M : Structure S) (φ : Formula S) : Prop :=
  ∀ env, φ.eval M env

/-! ## Sözlük eşlemesi (analojinin sözdizimi) -/

/-- Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
`relMap r`: hedef dilde bir formül; aynı biçimde. -/
structure SigMorph (S₁ S₂ : Signature) where
  fnMap  : (f : S₁.Fn) → Term S₂
  relMap : (r : S₁.Rel) → Formula S₂

/-- Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur. -/
def argSubst {k : Nat} (a : Fin k → Term S) : Nat → Term S :=
  fun n => if h : n < k then a ⟨n, h⟩ else .dflt

def SigMorph.trT (σ : SigMorph S₁ S₂) : Term S₁ → Term S₂
  | .var n   => .var n
  | .dflt    => .dflt
  | .app f a => (σ.fnMap f).subst (argSubst (fun i => σ.trT (a i)))

/-- Bir önermenin hedef dile çevirisi. -/
def SigMorph.trF (σ : SigMorph S₁ S₂) : Formula S₁ → Formula S₂
  | .falsum  => .falsum
  | .eq t u  => .eq (σ.trT t) (σ.trT u)
  | .rel r a => (σ.relMap r).subst (argSubst (fun i => σ.trT (a i)))
  | .imp φ ψ => .imp (σ.trF φ) (σ.trF ψ)
  | .and φ ψ => .and (σ.trF φ) (σ.trF ψ)
  | .or φ ψ  => .or (σ.trF φ) (σ.trF ψ)
  | .all φ   => .all (σ.trF φ)
  | .ex φ    => .ex (σ.trF φ)

/-- Eşlemelerin bileşimi: önce `σ`, sonra `τ`. -/
def SigMorph.comp (σ : SigMorph S₁ S₂) (τ : SigMorph S₂ S₃) : SigMorph S₁ S₃ where
  fnMap  := fun f => τ.trT (σ.fnMap f)
  relMap := fun r => τ.trF (σ.relMap r)

/-- Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur. -/
def argEnv (M : Structure S) {k : Nat} (v : Fin k → M.D) : Nat → M.D :=
  fun n => if h : n < k then v ⟨n, h⟩ else M.dflt

/-- İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
sembolü, eşlemenin hedefte gösterdiği şey olarak yorumlanır. -/
def SigMorph.reduct (σ : SigMorph S₁ S₂) (M : Structure S₂) : Structure S₁ where
  D    := M.D
  dflt := M.dflt
  fn   := fun f v => (σ.fnMap f).eval M (argEnv M v)
  rel  := fun r v => (σ.relMap r).eval M (argEnv M v)

/-- İki eşleme `pf`/`pr`'nin seçtiği sembollerde aynıdır. -/
def SigMorph.AgreeOn (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool) (σ τ : SigMorph S₁ S₂) : Prop :=
  (∀ f, pf f = true → σ.fnMap f = τ.fnMap f) ∧ (∀ r, pr r = true → σ.relMap r = τ.relMap r)

/-! ## Veri yazımı için yardımcılar -/

/-- Tek argüman. -/
def vec1 {α : Type} (a : α) : Fin 1 → α := fun _ => a

/-- İki argüman: 0. ve 1. -/
def vec2 {α : Type} (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b

/-- Sıfır argüman. -/
def vec0 {α : Type} : Fin 0 → α := fun i => i.elim0

/-- Üç argüman: 0., 1., 2. -/
def vec3 {α : Type} (a b c : α) : Fin 3 → α :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else c
