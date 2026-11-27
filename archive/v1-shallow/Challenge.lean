import Hakem

/-!
# İddialar (güvenilen metin)

Bu dosyadaki her ifade, hakemin hüküm vereceği iddiadır. İspatı yoktur
(`sorry`). İspatlar güvenilmeyen taraftan (`Solution.lean`) gelir. Hakem,
`Solution`'daki aynı adlı teoremin **aynı ifadeyi** kanıtladığını, yalnızca izinli
aksiyomlara dayandığını ve çekirdeklerce kabul edildiğini denetler.

Her docstring'in "OKUMA" satırı, ifadenin insan dilindeki okumasıdır. Okuma
**denetlenmez**; ifadenin ne dediği Lean terimidir, okuma değil.
-/

/-! ## Korunum -/

/-- OKUMA: Muhasebede her virman toplam bakiyeyi korur. -/
theorem accounting_conserves_balance :
    Accounting.Thm (fun p => Unchanged (beforeAfter balance p)) := sorry

/-- OKUMA: Fizik → muhasebe analojisi vardır. Çapa: toplam enerji = toplam bakiye. -/
theorem analogy_physics_accounting :
    Nonempty (Analogy Physics Accounting (beforeAfter totalEnergy) (beforeAfter balance)) := sorry

/-- OKUMA: Fizik → bankacılığın yalnızca-virman alt kuramı analojisi vardır.
Çapa: toplam enerji = toplam mevduat. -/
theorem analogy_physics_bankTransfers :
    Nonempty (Analogy Physics (Banking.extend isTransfer)
      (beforeAfter totalEnergy) (beforeAfter deposits)) := sorry

/-- OKUMA: Virmanlar altında toplam mevduat korunur. -/
theorem bankTransfers_conserve_deposits :
    (Banking.extend isTransfer).Thm (fun p => Unchanged (beforeAfter deposits p)) := sorry

/-- OKUMA: "Toplam enerji = toplam mevduat" çapasıyla fizik → bankacılık (kredi dahil)
bir metafordur. Fizikte kanıtlı bir iddiayı çiğneyen bir bankacılık modeli vardır. -/
theorem metaphor_physics_banking_deposits :
    Nonempty (Refutation Physics Banking (beforeAfter totalEnergy) (beforeAfter deposits)) := sorry

/-- OKUMA: "Toplam enerji = net pozisyon (mevduat − kredi)" çapasıyla fizik → bankacılık
(kredi dahil) analojisi vardır. Hüküm disiplinlere değil, çapaya bağlıdır. -/
theorem analogy_physics_banking_net :
    Nonempty (Analogy Physics Banking (beforeAfter totalEnergy) (beforeAfter netPosition)) := sorry

/-! ## Denge -/

/-- OKUMA: Termodinamik dengede enerji iki cisim arasında eşit dağılır (en çok bir birim fark). -/
theorem thermo_equilibrium_even :
    Thermo.Thm (fun t => EquilibriumIsEven (thermoObs t)) := sorry

/-- OKUMA: Termodinamik → azalan marjinal faydalı piyasa analojisi vardır.
Çapa: (dengede mi, fark) ↦ (dengede mi, fark). -/
theorem analogy_thermo_marketDMU :
    Nonempty (Analogy Thermo MarketDMU thermoObs marketObs) := sorry

/-- OKUMA: Azalan marjinal fayda altında piyasa dengesinde mal eşit dağılır (en çok bir birim fark). -/
theorem marketDMU_equilibrium_even :
    MarketDMU.Thm (fun m => EquilibriumIsEven (marketObs m)) := sorry

/-- OKUMA: Aynı çapayla termodinamik → kısıtsız piyasa bir metafordur. Marjinal faydanın
kesin azalmadığı bir piyasada (karşı örnek: sabit marjinal fayda) dengede eşitsiz
dağılım vardır. -/
theorem metaphor_thermo_market :
    Nonempty (Refutation Thermo Market thermoObs marketObs) := sorry

/-! ## Olgu ve değer: karbonun sosyal maliyeti -/

/-- OKUMA: Pigou ölçütü ve ρ = %0,1 seçilirse, ölçüm aralığındaki her olgu için
vergi en az 120 $/tCO₂ olmalı. Olgular bu sonucu tek başına belirlemez. -/
theorem stern_verdict :
    Nonempty (Verdict SCCQuestion sternNorms (TaxAtLeast 120000000)) := sorry

/-- OKUMA: Pigou ölçütü ve ρ = %1,5 seçilirse, ölçüm aralığındaki her olgu için
vergi 75 $/tCO₂'nin altında olmalı. -/
theorem nordhaus_verdict :
    Nonempty (Verdict SCCQuestion nordhausNorms (TaxBelow 75000000)) := sorry

/-- OKUMA: Ölçüm aralığındaki her olgu için, ölçüt (Pigou) sabitken yalnızca ρ'yu
%0,1'den %1,5'e değiştirmek sonucu "≥ 120 $" iken "< 75 $" yapar. -/
theorem scc_rho_alone_decides :
    ∀ e, measured e →
      TaxAtLeast 120000000 e ⟨10, .pigou⟩ ∧ TaxBelow 75000000 e ⟨150, .pigou⟩ := sorry
