import Hakem

/-!
# İddialar (güvenilen metin)

İspat yoktur (`sorry`); ispatlar güvenilmeyen taraftan (`Solution`) gelir. Yargıç,
aynı adlı teoremlerin terim olarak aynı ifadeyi kanıtladığını, anlam tabanının aynı
olduğunu, yalnızca izinli aksiyomların kullanıldığını ve bağımsız çekirdeğin dökümü
kabul ettiğini denetler. OKUMA satırları denetlenmez.

## I. Genel yasalar
Her sözlük, her kuram, her analoji ve her politika argümanı için geçerlidir. Disiplin
sayısından ve türünden bağımsızdır. Bir kez ispatlanır.

## II. Sınama durumları
Çekirdeğin boş olmadığını ve verinin gerçekten girilebildiğini gösterir.
-/

/-! ## I. Genel yasalar -/

/-- OKUMA: Tatmin koşulu. Bir önermenin çevirisi hedef dünyada doğrudur ancak ve ancak
önerme, o dünyanın kaynak diliyle okunuşunda doğrudur. -/
theorem satisfaction : ∀ {S₁ S₂ : Signature} (σ : SigMorph S₁ S₂) (M : Structure S₂)
    (φ : Formula S₁), M.Sat (σ.trF φ) ↔ (σ.reduct M).Sat φ := sorry

/-- OKUMA: Aktarım. Kaynak kuramın gerektirdiği her önermenin çevirisini hedef kuram
gerektirir. -/
theorem transfer : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} (a : Analogy A B)
    {φ : Formula S₁}, A.Entails φ → B.Entails (a.σ.trF φ) := sorry

/-- OKUMA: Bir analoji varsa kaynak kuramın da modeli vardır (aktarım boş değildir). -/
theorem source_consistent : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂},
    Analogy A B → ∃ M, A.Models M := sorry

/-- OKUMA: Bileşim. Analojiler zincirlenir; zincirin sözlüğü, sözlüklerin bileşimidir. -/
theorem compose_exists : ∀ {S₁ S₂ S₃ : Signature} {A : Theory S₁} {B : Theory S₂}
    {C : Theory S₃} (a : Analogy A B) (b : Analogy B C),
    ∃ c : Analogy A C, c.σ = a.σ.comp b.σ := sorry

/-- OKUMA: Metafor. Bir karşı örnek, çapaları önerilen sözlükle aynı olan her analojiyi
dışlar. -/
theorem refutation_sound : ∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂}
    {pf : S₁.Fn → Bool} {pr : S₁.Rel → Bool} {gl : SigMorph S₁ S₂},
    Refutation A B pf pr gl → ∀ a : Analogy A B, a.σ.AgreeOn pf pr gl → False := sorry

/-- OKUMA: Hume yasası. Bütün öncülleri betimsel olan (hiçbir normatif sembol içermeyen)
bir kuramdan hiçbir politika hükmü kurulamaz. -/
theorem hume_law : ∀ {S : Signature} {T : Theory S} {φ : Formula S},
    (∀ ψ ∈ T.axioms, ψ.descriptive = true) → ¬ Nonempty (PolicyVerdict T φ) := sorry

/-- OKUMA: Her politika hükmünde tartışma normatiftir. Alternatif dünya, bütün betimsel
sembollerde asıl dünyayla aynıdır; sonuç birinde doğru, ötekinde yanlıştır. -/
theorem verdict_same_facts : ∀ {S : Signature} {T : Theory S} {φ : Formula S}
    (v : PolicyVerdict T φ),
    (∀ f, S.fnRole f ≠ .normatif → (v.world.reinterp v.g v.h).fn f = v.world.fn f) ∧
    (∀ r, S.relRole r ≠ .normatif → (v.world.reinterp v.g v.h).rel r = v.world.rel r) ∧
    v.world.Sat φ ∧ ¬ (v.world.reinterp v.g v.h).Sat φ := sorry

/-! ## I-b. Veri olarak sertifikalar: kalkülüs ve sonlu modeller -/

/-- OKUMA: Kalkülüsün sağlamlığı. Denetimden geçen bir ispat verisi, kuramın önermeyi
gerektirdiğini gösterir. -/
theorem calculus_sound : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S), check T.axioms φ p = true → T.Entails φ := sorry

/-- OKUMA: Sonlu yapıda, kapalı bir formül için hesap ile doğruluk örtüşür. -/
theorem finite_sat_iff : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    φ.closed = true → (M.toStructure.Sat φ ↔ M.evalB (fun _ => 0) φ = true) := sorry

/-- OKUMA: Sonlu model denetimi sağlamdır. -/
theorem finite_models_sound : ∀ {S : Signature} (M : FinStructure S) (T : Theory S),
    T.admissible M.toStructure → M.checkTheory T = true → T.Models M.toStructure := sorry

/-- OKUMA: Sonlu çürütme sağlamdır. -/
theorem finite_refutes_sound : ∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
    M.refutes φ = true → ¬ M.toStructure.Sat φ := sorry

/-- OKUMA: Veriden metafor sertifikası. Kaynakta bir ispat verisi ve hedefte sonlu bir
karşı örnek, metafor sertifikası için yeterlidir. -/
theorem refutation_of_data : ∀ {S₁ S₂ : Signature} [DecidableEq S₁.Fn] [DecidableEq S₁.Rel]
    (A : Theory S₁) (B : Theory S₂) (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool)
    (gl : SigMorph S₁ S₂) (φ : Formula S₁) (p : Proof S₁) (C : FinStructure S₂),
    B.admissible C.toStructure →
    check A.axioms φ p = true → φ.onlySyms pf pr = true → C.checkTheory B = true →
    C.refutes (gl.trF φ) = true → Nonempty (Refutation A B pf pr gl) := sorry

/-- OKUMA: Veriden politika hükmü. Bir ispat verisi, öncülleri sağlayan sonlu bir dünya
ve yalnızca normatif sembolleri değiştirilmiş, sonucu çürüten bir alternatif yeterlidir. -/
theorem verdict_of_data : ∀ {S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (φ : Formula S) (p : Proof S) (W : FinStructure S) (g h),
    (∀ M : Structure S, T.admissible M) →
    check T.axioms φ p = true → W.checkTheory T = true → (W.reinterpB g h).refutes φ = true →
    Nonempty (PolicyVerdict T φ) := sorry

/-- OKUMA: İzomorf yapılar aynı önermeleri doğrular. -/
theorem iso_sat : ∀ {S : Signature} {M N : Structure S}, M.Iso N → ∀ φ : Formula S,
    M.Sat φ ↔ N.Sat φ := sorry

/-- OKUMA: Arka plan sağlamlığı. Standart yapıda doğru olan her önerme, standart kısmı o
yapıya izomorf olan her modelde (çevirisiyle) doğrudur. -/
theorem background_sound : ∀ {S₀ S : Signature} (ι : SigMorph S₀ S) (B : Structure S₀)
    (M : Structure S), Nonempty ((ι.reduct M).Iso B) → ∀ ψ : Formula S₀, B.Sat ψ →
    M.Sat (ι.trF ψ) := sorry

/-- OKUMA: Arka planlı kalkülüs. İspat, kuramın aksiyomlarına ek olarak standart yapıda
doğru önermeleri (çevirileriyle) hipotez olarak kullanabilir. -/
theorem calculus_sound_bg : ∀ {S₀ S : Signature} [DecidableEq S.Fn] [DecidableEq S.Rel]
    (T : Theory S) (ι : SigMorph S₀ S) (B : Structure S₀) (bg : List (Formula S₀))
    (φ : Formula S) (p : Proof S),
    (∀ M, T.admissible M → Nonempty ((ι.reduct M).Iso B)) → (∀ ψ ∈ bg, B.Sat ψ) →
    check (T.axioms ++ bg.map ι.trF) φ p = true → T.Entails φ := sorry

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
    T.Entails φ := sorry

/-! ## II. Sınama durumları -/

/-- OKUMA: "Enerji = net pozisyon, alışveriş = her banka adımı" sözlüğüyle fizik →
bankacılık analojisi vardır. -/
theorem analogy_physics_banking_net :
    ∃ a : Analogy Physics Banking, a.σ = glossaryNet := sorry

/-- OKUMA: "Enerji = mevduat, alışveriş = yalnızca virman" sözlüğüyle analoji vardır
(kısmi analoji). -/
theorem analogy_physics_banking_transfers :
    ∃ a : Analogy Physics Banking, a.σ = glossaryTransfers := sorry

/-- OKUMA: Aktarılan sonuç: bankacılıkta her adım net pozisyonu korur. -/
theorem banking_net_conserved : Banking.Entails (glossaryNet.trF conservationLaw) := sorry

/-- OKUMA: "Enerji = mevduat, alışveriş = her banka adımı" sözlüğü için karşı örnek vardır. -/
theorem metaphor_physics_banking_deposits :
    Nonempty (Refutation Physics Banking (fun _ => true) (fun _ => true) glossaryDeposits) := sorry

/-- OKUMA: Bu sözlükle hiçbir analoji yoktur. -/
theorem no_analogy_with_deposits_glossary :
    ¬ ∃ a : Analogy Physics Banking, a.σ = glossaryDeposits := sorry

/-- OKUMA: "Zarar veren önlenmeli" öncülüyle "faaliyet önlenmeli" bir politika hükmüdür. -/
theorem policy_verdict_prevent : Nonempty (PolicyVerdict WithNorm preventAct) := sorry

/-- OKUMA: Yalnızca olgulardan aynı hüküm kurulamaz. -/
theorem facts_alone_no_verdict : ¬ Nonempty (PolicyVerdict FactsOnly preventAct) := sorry

/-- OKUMA: Öncül türleri beyan edilmez, sembollerden hesaplanır. -/
theorem roles_are_computed :
    harmFact.descriptive = true ∧ harmNorm.descriptive = false ∧
      preventAct.descriptive = false := sorry

/-! ## II-b. Yalnızca çekirdek hesabıyla denetlenen veriler -/

/-- OKUMA: Bankacılık analojisinin ispat yükümlülüğü bir ispat verisiyle kapanır. -/
theorem banking_net_proof_checks :
    check Banking.axioms (glossaryNet.trF conservationLaw) netProof = true := sorry

/-- OKUMA: Metafor sertifikasının parçaları veridir: fizikte ispat, bankada sonlu karşı örnek. -/
theorem bank_counterexample_checks :
    check Physics.axioms conservationLaw conservationProof = true ∧
    bankFin.checkTheory Banking = true ∧
    bankFin.refutes (glossaryDeposits.trF conservationLaw) = true := sorry

/-- OKUMA: Politika hükmünün parçaları veridir: ispat, tanık dünya, normatif alternatif. -/
theorem policy_data_checks :
    check WithNorm.axioms preventAct preventProof = true ∧
    polWorld.checkTheory WithNorm = true ∧ polAlt.refutes preventAct = true := sorry

/-! ## II-c. Karbonun sosyal maliyeti (ℕ arka planı) -/

/-- OKUMA: ℕ'de: ölçüm aralığındaki her zarar ve süre için SCC(%0,1) ≥ 120 $. -/
theorem scc_background_stern : NatStd.Sat bgStern := sorry

/-- OKUMA: ℕ'de: ölçüm aralığındaki her zarar ve süre için SCC(%1,5) < 75 $. -/
theorem scc_background_nordhaus : NatStd.Sat bgNordhaus := sorry

/-- OKUMA: Stern sonucunun ispat verisi çekirdek hesabıyla denetlenir. -/
theorem scc_stern_proof_checks :
    check (SternSCC.axioms ++ [bgStern].map embed.trF) taxAtLeast120 sternProof = true := sorry

/-- OKUMA: Nordhaus sonucunun ispat verisi çekirdek hesabıyla denetlenir. -/
theorem scc_nordhaus_proof_checks :
    check (NordhausSCC.axioms ++ [bgNordhaus].map embed.trF) taxBelow75 nordhausProof = true := sorry

/-- OKUMA: ρ = %0,1 ve Pigou seçilirse "vergi ≥ 120 $" bir politika hükmüdür: aynı olgularla
yalnızca ρ ve vergi yeniden yorumlanınca sonuç çöker. -/
theorem scc_stern_verdict : Nonempty (PolicyVerdict SternSCC taxAtLeast120) := sorry

/-- OKUMA: ρ = %1,5 ve Pigou seçilirse "vergi < 75 $" bir politika hükmüdür. -/
theorem scc_nordhaus_verdict : Nonempty (PolicyVerdict NordhausSCC taxBelow75) := sorry

/-- OKUMA: Olgular betimseldir; ρ ve Pigou öncülleri normatiftir; sonuç normatiftir.
Hepsi sembollerden hesaplanır. -/
theorem scc_roles_computed :
    sccFacts.all (·.descriptive) = true ∧ sternNorms.all (fun ψ => !ψ.descriptive) = true ∧
    nordhausNorms.all (fun ψ => !ψ.descriptive) = true ∧ taxAtLeast120.descriptive = false := sorry

/-! ## II-d. Termodinamik denge ↔ piyasa dengesi (ℤ arka planı) -/

/-- OKUMA: Termodinamikte dengede enerji eşit dağılır (en çok bir birim fark). -/
theorem thermo_equilibrium_even : Thermo.Entails thermoLaw := sorry

/-- OKUMA: "Entropi ↦ fayda, enerji ↦ miktar" sözlüğüyle termodinamik → azalan marjinal
faydalı piyasa analojisi vardır. -/
theorem analogy_thermo_marketDMU : ∃ a : Analogy Thermo MarketDMU, a.σ = thermoToMarket := sorry

/-- OKUMA: Azalan marjinal faydalı piyasada, gönüllü ticaret kalmadıysa mal eşit dağılır.
Aktarılan yasa ile gönüllülük–Clausius köprüsünden. -/
theorem market_equilibrium_even : MarketDMU.Entails marketLaw := sorry

/-- OKUMA: Aynı sözlükle termodinamik → kısıtsız piyasa bir metafordur (karşı örnek: sabit
marjinal fayda, dağılım (0, 10)). -/
theorem metaphor_thermo_market :
    Nonempty (Refutation Thermo Market (fun _ => true) (fun _ => true) thermoToMarket) := sorry
