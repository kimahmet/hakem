-- OTOMATİK ÜRETİLDİ: tools/gen_solution.py. Elle düzenleme.
import Hakem
import Solution.Background
import Solution.Calculus
import Solution.Corpus
import Solution.Finite
import Solution.Lang
import Solution.Meta
import Kulliyat

/-!
# İddialar (güvenilen metin)

İspat yoktur (`sorry`); ispatlar güvenilmeyen taraftan (`Solution`) gelir. Yargıç,
aynı adlı teoremlerin terim olarak aynı ifadeyi kanıtladığını, anlam tabanının aynı
olduğunu, yalnızca izinli aksiyomların kullanıldığını ve bağımsız çekirdeğin dökümü
kabul ettiğini denetler. OKUMA satırları denetlenmez.

## I. Genel yasalar
Her sözlük, her kuram, her analoji ve her politika argümanı için geçerlidir.

## II. Dil
Hakem dilinde yazılmış her belge için geçerlidir: denetleyici sağlamdır.

## III. Külliyat
Dilde yazılmış belgeler. Her biri yalnızca çekirdek hesabıyla denetlenir.
-/

/-! ## I. Genel yasalar -/

/-- OKUMA: Tatmin koşulu. Bir önermenin çevirisi hedef dünyada doğrudur ancak ve ancak
önerme, o dünyanın kaynak diliyle okunuşunda doğrudur. -/
theorem satisfaction : ∀ {S₁ S₂ : Signature} (σ : SigMorph S₁ S₂) (M : Structure S₂)
    (φ : Formula S₁), M.Sat (σ.trF φ) ↔ (σ.reduct M).Sat φ := Proofs.satisfaction

/-- OKUMA: Aktarım. Kaynak kuramın gerektirdiği her önermenin çevirisini hedef kuram
gerektirir. -/
theorem transfer : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} (a : Analogy A B)
    {φ : Formula S₁}, A.Entails φ → B.Entails (a.σ.trF φ) := Proofs.transfer

/-- OKUMA: Bir analoji varsa kaynak kuramın da modeli vardır (aktarım boş değildir). -/
theorem source_consistent : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂},
    Analogy A B → ∃ M, A.Models M := Proofs.source_consistent

/-- OKUMA: Bileşim. Analojiler zincirlenir; zincirin sözlüğü, sözlüklerin bileşimidir. -/
theorem compose_exists : ∀ {S₁ S₂ S₃ : Signature} {A : Theory S₁} {B : Theory S₂}
    {C : Theory S₃} (a : Analogy A B) (b : Analogy B C),
    ∃ c : Analogy A C, c.σ = a.σ.comp b.σ := Proofs.compose_exists

/-- OKUMA: Metafor. Bir karşı örnek, çapaları önerilen sözlükle aynı olan her analojiyi
dışlar. -/
theorem refutation_sound : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂}
    {pf : S₁.Fn → Bool} {pr : S₁.Rel → Bool} {gl : SigMorph S₁ S₂},
    Refutation A B pf pr gl → ∀ a : Analogy A B, a.σ.AgreeOn pf pr gl → False := Proofs.refutation_sound

/-- OKUMA: Hume yasası. Bütün öncülleri betimsel olan (hiçbir normatif sembol içermeyen)
bir kuramdan hiçbir politika hükmü kurulamaz. -/
theorem hume_law : ∀ {S : Signature} {T : Theory S} {φ : Formula S},
    (∀ ψ ∈ T.axioms, ψ.descriptive = true) → ¬ Nonempty (PolicyVerdict T φ) := Proofs.hume_law

/-- OKUMA: Her politika hükmünde tartışma normatiftir. Alternatif dünya, bütün betimsel
sembollerde asıl dünyayla aynıdır; sonuç birinde doğru, ötekinde yanlıştır. -/
theorem verdict_same_facts : ∀ {S : Signature} {T : Theory S} {φ : Formula S}
    (v : PolicyVerdict T φ),
    (∀ f, S.fnRole f ≠ .normatif → (v.world.reinterp v.g v.h).fn f = v.world.fn f) ∧
    (∀ r, S.relRole r ≠ .normatif → (v.world.reinterp v.g v.h).rel r = v.world.rel r) ∧
    v.world.Sat φ ∧ ¬ (v.world.reinterp v.g v.h).Sat φ := Proofs.verdict_same_facts

/-! ## I-b. Veri olarak sertifikalar: kalkülüs ve sonlu modeller -/

/-- OKUMA: Kalkülüsün sağlamlığı. Denetimden geçen bir ispat verisi, kuramın önermeyi
gerektirdiğini gösterir. -/
theorem calculus_sound : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S), check T.axioms φ p = true → T.Entails φ := Proofs.calculus_sound

/-- OKUMA: Sonlu yapıda, kapalı bir formül için hesap ile doğruluk örtüşür. -/
theorem finite_sat_iff : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    φ.closed = true → (M.toStructure.Sat φ ↔ M.evalB (fun _ => 0) φ = true) := Proofs.finite_sat_iff

/-- OKUMA: Sonlu model denetimi sağlamdır. -/
theorem finite_models_sound : ∀ {S : Signature} (M : FinStructure S) (T : Theory S),
    T.admissible M.toStructure → M.checkTheory T = true → T.Models M.toStructure := Proofs.finite_models_sound

/-- OKUMA: Sonlu çürütme sağlamdır. -/
theorem finite_refutes_sound : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    M.refutes φ = true → ¬ M.toStructure.Sat φ := Proofs.finite_refutes_sound

/-- OKUMA: Veriden metafor sertifikası. Kaynakta bir ispat verisi ve hedefte sonlu bir
karşı örnek, metafor sertifikası için yeterlidir. -/
theorem refutation_of_data : ∀ {S₁ S₂ : Signature} [DecidableEq S₁.Fn] [DecidableEq S₁.Rel]
    (A : Theory S₁) (B : Theory S₂) (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool)
    (gl : SigMorph S₁ S₂) (φ : Formula S₁) (p : Proof S₁) (C : FinStructure S₂),
    B.admissible C.toStructure →
    check A.axioms φ p = true → φ.onlySyms pf pr = true → C.checkTheory B = true →
    C.refutes (gl.trF φ) = true → Nonempty (Refutation A B pf pr gl) := Proofs.refutation_of_data

/-- OKUMA: Veriden politika hükmü. Bir ispat verisi, öncülleri sağlayan sonlu bir dünya
ve yalnızca normatif sembolleri değiştirilmiş, sonucu çürüten bir alternatif yeterlidir. -/
theorem verdict_of_data : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S) (W : FinStructure S) (g h),
    (∀ M : Structure S, T.admissible M) →
    check T.axioms φ p = true → W.checkTheory T = true → (W.reinterpB g h).refutes φ = true →
    Nonempty (PolicyVerdict T φ) := Proofs.verdict_of_data

/-- OKUMA: İzomorf yapılar aynı önermeleri doğrular. -/
theorem iso_sat : ∀ {S : Signature} {M N : Structure S}, M.Iso N → ∀ φ : Formula S,
    M.Sat φ ↔ N.Sat φ := Proofs.iso_sat

/-- OKUMA: Arka plan sağlamlığı. Standart yapıda doğru olan her önerme, standart kısmı o
yapıya izomorf olan her modelde (çevirisiyle) doğrudur. -/
theorem background_sound : ∀ {S₀ S : Signature} (ι : SigMorph S₀ S) (B : Structure S₀)
    (M : Structure S), Nonempty ((ι.reduct M).Iso B) → ∀ ψ : Formula S₀, B.Sat ψ →
    M.Sat (ι.trF ψ) := Proofs.background_sound

/-- OKUMA: Arka planlı kalkülüs. İspat, kuramın aksiyomlarına ek olarak standart yapıda
doğru önermeleri (çevirileriyle) hipotez olarak kullanabilir. -/
theorem calculus_sound_bg : ∀ {S₀ S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (ι : SigMorph S₀ S) (B : Structure S₀) (bg : List (Formula S₀))
    (φ : Formula S) (p : Proof S),
    (∀ M, T.admissible M → Nonempty ((ι.reduct M).Iso B)) → (∀ ψ ∈ bg, B.Sat ψ) →
    check (T.axioms ++ bg.map ι.trF) φ p = true → T.Entails φ := Proofs.calculus_sound_bg

/-- OKUMA: Standart taşıyıcıda akıl yürütme. Arka planlı bir kuramın gerektirdiğini
göstermek için standart taşıyıcılı, standart sembolleri standart yorumlanan modellere
bakmak yeterlidir. -/
theorem entails_of_std : ∀ {S₀ S : Signature} (T : Theory S) (ι : SigMorph S₀ S)
    (B : Structure S₀), (∀ M, T.admissible M → Nonempty ((ι.reduct M).Iso B)) →
    ∀ φ : Formula S,
    (∀ (fn : (f : S.Fn) → (Fin (S.fnArity f) → B.D) → B.D)
       (rel : (r : S.Rel) → (Fin (S.relArity r) → B.D) → Prop),
       (∀ f v, (ι.reduct (⟨B.D, B.dflt, fn, rel⟩ : Structure S)).fn f v = B.fn f v) →
       (∀ r v, (ι.reduct (⟨B.D, B.dflt, fn, rel⟩ : Structure S)).rel r v ↔ B.rel r v) →
       (∀ ψ ∈ T.axioms, (⟨B.D, B.dflt, fn, rel⟩ : Structure S).Sat ψ) →
       (⟨B.D, B.dflt, fn, rel⟩ : Structure S).Sat φ) →
    T.Entails φ := Proofs.entails_of_std

/-! ## II. Dil -/

/-- OKUMA: Dilin sağlamlığı (ağaç). Denetimden geçen her belge ağacının bütün iddiaları
doğrudur. -/
theorem checkTree_sound : ∀ es : List SExp, checkTree es = true → Doc.HoldsTree es := Proofs.checkTree_sound

/-- OKUMA: Dilin sağlamlığı (metin). Denetimden geçen her belge metninin bütün iddiaları
doğrudur. -/
theorem checkDoc_sound : ∀ s : String, checkDoc s = true → Doc.Holds s := Proofs.checkDoc_sound

/-! ## III. Külliyat -/

/-- OKUMA: `corpus/korunum.hkm` belgesinin bütün iddiaları doğrudur. -/
theorem korunum_holds : Doc.HoldsTree korunum_tree := Proofs.korunum_holds

/-- OKUMA: `corpus/politika.hkm` belgesinin bütün iddiaları doğrudur. -/
theorem politika_holds : Doc.HoldsTree politika_tree := Proofs.politika_holds
