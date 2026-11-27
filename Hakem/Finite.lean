import Hakem.Calculus

/-!
# Hakem — sonlu modeller (v2)

Karşı örnekler ve tanık dünyalar da veridir. `FinStructure`, taşıyıcısı `Fin (n+1)`
olan, yorumları hesaplanabilir bir yapıdır. `evalB` bir formülü bu yapıda **hesaplar**.
Kapalı formüllerde hesap ile anlam örtüşür (`finite_sat_iff`, `Challenge.lean`).
Bu yüzden "bu yapı bu kuramın modelidir" ve "bu yapıda bu önerme yanlıştır" iddiaları
çekirdek hesabıyla (`decide +kernel`) denetlenir.
-/

variable {S : Signature}

/-- Sonlu ailede `||`. -/
def anyFin (k : Nat) (p : Fin k → Bool) : Bool := !allFin k (fun i => !p i)

/-- Terimdeki her değişken `< k`. -/
def Term.varsBelow (k : Nat) : Term S → Bool
  | .var n   => decide (n < k)
  | .dflt    => true
  | .app _ a => allFin _ (fun i => (a i).varsBelow k)

/-- Formüldeki her serbest değişken `< k`. -/
def Formula.varsBelow : Nat → Formula S → Bool
  | _, .falsum  => true
  | k, .eq t u  => t.varsBelow k && u.varsBelow k
  | k, .rel _ a => allFin _ (fun i => (a i).varsBelow k)
  | k, .imp φ ψ => φ.varsBelow k && ψ.varsBelow k
  | k, .and φ ψ => φ.varsBelow k && ψ.varsBelow k
  | k, .or φ ψ  => φ.varsBelow k && ψ.varsBelow k
  | k, .all φ   => φ.varsBelow (k + 1)
  | k, .ex φ    => φ.varsBelow (k + 1)

/-- Kapalı formül (cümle). -/
def Formula.closed (φ : Formula S) : Bool := φ.varsBelow 0

/-- Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar. -/
structure FinStructure (S : Signature) where
  n   : Nat
  fn  : (f : S.Fn) → (Fin (S.fnArity f) → Fin (n + 1)) → Fin (n + 1)
  rel : (r : S.Rel) → (Fin (S.relArity r) → Fin (n + 1)) → Bool

/-- Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır. -/
abbrev FinStructure.toStructure (M : FinStructure S) : Structure S where
  D    := Fin (M.n + 1)
  dflt := 0
  fn   := M.fn
  rel  := fun r v => M.rel r v = true

/-- Formülün sonlu yapıda hesaplanması. -/
def FinStructure.evalB (M : FinStructure S) : (Nat → Fin (M.n + 1)) → Formula S → Bool
  | _,   .falsum  => false
  | env, .eq t u  => decide (t.eval M.toStructure env = u.eval M.toStructure env)
  | env, .rel r a => M.rel r (fun i => (a i).eval M.toStructure env)
  | env, .imp φ ψ => !(M.evalB env φ) || M.evalB env ψ
  | env, .and φ ψ => M.evalB env φ && M.evalB env ψ
  | env, .or φ ψ  => M.evalB env φ || M.evalB env ψ
  | env, .all φ   => allFin (M.n + 1) (fun d => M.evalB (cons d env) φ)
  | env, .ex φ    => anyFin (M.n + 1) (fun d => M.evalB (cons d env) φ)

/-- Sonlu yapı kuramın her aksiyomunu (kapalı olarak) doğrular. -/
def FinStructure.checkTheory (M : FinStructure S) (T : Theory S) : Bool :=
  T.axioms.all (fun ψ => ψ.closed && M.evalB (fun _ => 0) ψ)

/-- Sonlu yapıda kapalı bir formül yanlıştır. -/
def FinStructure.refutes (M : FinStructure S) (φ : Formula S) : Bool :=
  φ.closed && !(M.evalB (fun _ => 0) φ)

/-- Tanık dünyanın normatif sembollerini değiştirerek elde edilen sonlu alternatif.
`g`/`h` yalnızca normatif sembollerde kullanılır. -/
def FinStructure.reinterpB (M : FinStructure S)
    (g : (f : S.Fn) → (Fin (S.fnArity f) → Fin (M.n + 1)) → Fin (M.n + 1))
    (h : (r : S.Rel) → (Fin (S.relArity r) → Fin (M.n + 1)) → Bool) : FinStructure S where
  n   := M.n
  fn  := fun f => if S.fnRole f = .normatif then g f else M.fn f
  rel := fun r => if S.relRole r = .normatif then h r else M.rel r
