import Hakem.Finite

/-!
# Sınama durumu: olgu ve değer (veri olarak)

`Ought` normatif bir semboldür. Öncüllerin hangisinin normatif olduğu sembollerden
hesaplanır; beyan edilmez.
-/

inductive PolFn  | act          deriving DecidableEq
inductive PolRel | Harm | Ought deriving DecidableEq

/-- OKUMA: politika sözlüğü. `act`: belirli bir faaliyet (ampirik). `Harm x`: x zarar
verir (ampirik). `Ought x`: x önlenmelidir (normatif). -/
abbrev PolSig : Signature where
  Fn := PolFn
  Rel := PolRel
  fnArity := fun _ => 0
  relArity := fun _ => 1
  fnRole := fun _ => .ampirik
  relRole := fun | .Harm => .ampirik | .Ought => .normatif

/-- OKUMA: olgu: faaliyet zarar verir. -/
def harmFact : Formula PolSig := .rel .Harm (vec1 (.app .act vec0))

/-- OKUMA: değer öncülü: zarar veren her şey önlenmelidir. -/
def harmNorm : Formula PolSig := .all (.imp (.rel .Harm (vec1 (.var 0))) (.rel .Ought (vec1 (.var 0))))

/-- OKUMA: sonuç: faaliyet önlenmelidir. -/
def preventAct : Formula PolSig := .rel .Ought (vec1 (.app .act vec0))

/-- OKUMA: olgu ve değer öncülüyle kuram. -/
def WithNorm : Theory PolSig where
  axioms := [harmFact, harmNorm]

/-- OKUMA: yalnızca olgularla kuram. -/
def FactsOnly : Theory PolSig where
  axioms := [harmFact]

/-- OKUMA: olgu ve değer öncülünden sonucun doğal çıkarım ispatı. Veridir. -/
def preventProof : Proof PolSig :=
  .impE (.allE (.app .act vec0) (.hyp 1)) (.hyp 0)

/-- OKUMA: tek öğeli tanık dünya (veri): her şey zarar verir ve önlenmelidir. -/
def polWorld : FinStructure PolSig where
  n := 0
  fn := fun _ _ => 0
  rel := fun _ _ => true

/-- OKUMA: alternatif: yalnızca normatif `Ought` yeniden yorumlanır (hiçbir şey
önlenmemeli). -/
def polAlt : FinStructure PolSig := polWorld.reinterpB polWorld.fn (fun _ _ => false)
