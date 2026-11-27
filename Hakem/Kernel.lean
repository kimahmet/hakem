import Hakem.Logic

/-!
# Hakem — kernel vocabulary

The meaning of verdicts is fixed here: theory, analogy, metaphor certificate, policy
verdict. All are defined over **data** in the language of `Hakem.Logic`. They do not
depend on the number, size or kind of disciplines.

The general laws showing that this vocabulary behaves (transfer, composition, metaphor,
Hume's law) are stated as claims in `Challenge.lean`. They are proved once, in the
kernel, for every possible input.
-/

variable {S S₁ S₂ : Signature}

/-- Theory: axioms and an (optional) class of admissible structures.
`admissible` connects to standard mathematical objects (e.g. "the carrier is ℕ").
It is a Lean predicate and is part of the meaning base. -/
structure Theory (S : Signature) where
  axioms     : List (Formula S)
  admissible : Structure S → Prop := fun _ => True

namespace Theory

/-- `M` is a model of the theory. -/
def Models (T : Theory S) (M : Structure S) : Prop :=
  T.admissible M ∧ ∀ φ ∈ T.axioms, M.Sat φ

/-- The theory entails `φ`: every model satisfies `φ`. -/
def Entails (T : Theory S) (φ : Formula S) : Prop :=
  ∀ M, T.Models M → M.Sat φ

/-- Subtheory: extra axioms. A partial analogy is an analogy into a subtheory. -/
def extend (T : Theory S) (extra : List (Formula S)) : Theory S where
  axioms     := T.axioms ++ extra
  admissible := T.admissible

end Theory

/-- Analogy certificate. `σ` says what every source symbol corresponds to in the target.
Every model of the target, read through `σ`, is a model of the source: the target
entails the translations of the source axioms. At least one model of the target is
exhibited; otherwise transfer would be vacuously true. -/
structure Analogy (A : Theory S₁) (B : Theory S₂) where
  σ         : SigMorph S₁ S₂
  adm       : ∀ M, B.Models M → A.admissible (σ.reduct M)
  preserves : ∀ φ ∈ A.axioms, B.Entails (σ.trF φ)
  model     : Structure S₂
  model_ok  : B.Models model

/-- Metaphor certificate. `glossary` is the proposed glossary. `pf`/`pr` select its binding
part (the anchors). The source entails a `φ` written only with anchored symbols; in a
model of the target, the glossary's translation of `φ` fails. Then no analogy whose
anchors agree with this glossary exists. -/
structure Refutation (A : Theory S₁) (B : Theory S₂)
    (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool) (glossary : SigMorph S₁ S₂) where
  φ      : Formula S₁
  thm    : A.Entails φ
  only   : φ.onlySyms pf pr = true
  cex    : Structure S₂
  cex_ok : B.Models cex
  fails  : ¬ cex.Sat (glossary.trF φ)

/-- Change the interpretations of normative symbols only. The carrier and descriptive
(definitional and empirical) symbols stay as they are. -/
def Structure.reinterp (M : Structure S)
    (g : (f : S.Fn) → (Fin (S.fnArity f) → M.D) → M.D)
    (h : (r : S.Rel) → (Fin (S.relArity r) → M.D) → Prop) : Structure S where
  D    := M.D
  dflt := M.dflt
  fn   := fun f => if S.fnRole f = .normative then g f else M.fn f
  rel  := fun r => if S.relRole r = .normative then h r else M.rel r

/-- Policy verdict: `T ⊨ φ`, together with a world satisfying all premises of the theory
and an alternative, obtained by reinterpreting **only the normative symbols** of that
world, in which `φ` fails. With the facts fixed, the value choice decides the outcome. -/
structure PolicyVerdict (T : Theory S) (φ : Formula S) where
  entails  : T.Entails φ
  world    : Structure S
  world_ok : T.Models world
  g        : (f : S.Fn) → (Fin (S.fnArity f) → world.D) → world.D
  h        : (r : S.Rel) → (Fin (S.relArity r) → world.D) → Prop
  alt_adm  : T.admissible (world.reinterp g h)
  fails    : ¬ (world.reinterp g h).Sat φ

/-! ## Background: standard mathematical objects -/

/-- Isomorphism of structures: an invertible map preserving all interpretations. -/
structure Structure.Iso (M N : Structure S) where
  to    : M.D → N.D
  inv   : N.D → M.D
  left  : ∀ x, inv (to x) = x
  right : ∀ y, to (inv y) = y
  dflt  : to M.dflt = N.dflt
  fn    : ∀ f v, to (M.fn f v) = N.fn f (fun i => to (v i))
  rel   : ∀ r v, M.rel r v ↔ N.rel r (fun i => to (v i))

/-- Theory with background. `ι` embeds a standard vocabulary (e.g. the numbers, order and
functions of ℕ) into the discipline's vocabulary. Admissible structures are those whose
standard part is isomorphic to `B`, so that "number" really means number. -/
def Theory.withBackground {S₀ : Signature} (axioms : List (Formula S)) (ι : SigMorph S₀ S)
    (B : Structure S₀) : Theory S where
  axioms     := axioms
  admissible := fun M => Nonempty ((ι.reduct M).Iso B)
