# KARAR

Bu dosya `tools/hakem.sh` tarafından üretilir. Elle düzenlenmez.

**13 / 13 iddia biçimsel kabul aldı.**

## Bu kararın anlamı

"BİÇİMSEL KABUL" yalnızca şunu söyler:

1. Aşağıda basılan Lean ifadesi Lean çekirdeğince kabul edildi (`lake build`).
2. İfade bağımsız bir çekirdekte (nanoda, Rust) yeniden denetlendi: geçti.
3. İfade, güvenilen `Challenge.lean`'deki ifadeyle terim düzeyinde aynıdır.
4. İfadenin dayandığı tanımlar (anlam tabanı) iki tarafta aynıdır.
5. İspat yalnızca `propext`, `Quot.sound`, `Classical.choice` aksiyomlarına dayanır.

Bu karar şunları **söylemez**:

- OKUMA satırının ifadeyi doğru anlattığını. Okuma insan incelemesine açıktır.
- Anlam tabanındaki tanımların gerçek disiplini doğru temsil ettiğini. İDEALLEŞTİRME notlarına bakınız.
- Ampirik değerlerin doğru olduğunu. Değer seçimlerinin doğru olduğunu.
- Saldırgan girdiye karşı tam güvenceyi. Bu yerel çalıştırma sandbox kullanmaz. Tam güvence için Linux'ta `lake comparator --paranoid` (5 çekirdek) gerekir.

---

## `accounting_conserves_balance`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Accounting.Thm fun p => Unchanged (beforeAfter balance p)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem accounting_conserves_balance :
  Theory.Thm Accounting (fun (p : Theory.Str Accounting) => Unchanged (beforeAfter balance p)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Muhasebede her virman toplam bakiyeyi korur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Theory.Thm`: [3592344556] `φ` kuramın teoremidir: her modelde doğrudur.
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Theory.Ax`: [1298832593] 
- `Accounting`: [2954813933] OKUMA: iki hesaplı defterde virmanların kuramı.
- `transitions`: [2828025917] OKUMA: `step` ile izin verilen tek adımlık değişimlerin kuramı.
- `Ledger`: [3166912659] OKUMA: iki hesaplı defter (kasa, banka).
- `Ledger.mk`: [3906739450] 
- `ledgerTransfer`: [3111449974] OKUMA: kasa ile banka arasında virman.
- `Ledger.kasa`: [4130289096] 
- `Ledger.banka`: [2353935673] 
- `Unchanged`: [3960646650] OKUMA: önce ve sonra değerleri eşit. Korunum budur.
- `beforeAfter`: [370155043] OKUMA: bir ölçünün adımdan önceki ve sonraki değeri. Çapa olarak kullanılır.
- `balance`: [4238307428] OKUMA: toplam bakiye.

---

## `analogy_physics_accounting`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Analogy Physics Accounting (beforeAfter totalEnergy) (beforeAfter balance))
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem analogy_physics_accounting :
  Nonempty (Analogy Physics Accounting (beforeAfter totalEnergy) (beforeAfter balance)) :=
  _
```

**Aksiyomlar:** 

**OKUMA (denetlenmedi):** Fizik → muhasebe analojisi vardır. Çapa: toplam enerji = toplam bakiye.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Analogy`: [3399172939] Analoji sertifikası: çapalı yorum ve `B`'nin bir modeli. Model şarttır:
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Analogy.mk`: [1654795118] 
- `Interp`: [2611793070] Yorum: `B`'nin her yapısı `A`'nın diliyle okunur ve `B` modelleri `A` modellerine gider.
- `Interp.mk`: [1218699832] 
- `Theory.Ax`: [1298832593] 
- `Interp.Anchors`: [2166312076] Çapa: `B` modellerinde, yorum altında `A`'nın `oa` gözlenebiliri `B`'nin `ob`
- `Interp.red`: [2182380329] 
- `Physics`: [2772069666] OKUMA: yalıtık iki cisimli sistemde enerji alışverişlerinin kuramı.
- `transitions`: [2828025917] OKUMA: `step` ile izin verilen tek adımlık değişimlerin kuramı.
- `Bodies`: [4109377457] OKUMA: iki cisim ve enerjileri.
- `Bodies.mk`: [3768457870] 
- `energyExchange`: [655753540] OKUMA: enerji alışverişi. Bir cisim `a` kadar verir, öteki `a` kadar alır.
- `Bodies.e1`: [269133673] 
- `Bodies.e2`: [1766690774] 
- `Accounting`: [2954813933] OKUMA: iki hesaplı defterde virmanların kuramı.
- `Ledger`: [3166912659] OKUMA: iki hesaplı defter (kasa, banka).
- `Ledger.mk`: [3906739450] 
- `ledgerTransfer`: [3111449974] OKUMA: kasa ile banka arasında virman.
- `Ledger.kasa`: [4130289096] 
- `Ledger.banka`: [2353935673] 
- `beforeAfter`: [370155043] OKUMA: bir ölçünün adımdan önceki ve sonraki değeri. Çapa olarak kullanılır.
- `totalEnergy`: [1900074533] OKUMA: toplam enerji.
- `balance`: [4238307428] OKUMA: toplam bakiye.

---

## `analogy_physics_bankTransfers`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Analogy Physics (Banking.extend isTransfer) (beforeAfter totalEnergy) (beforeAfter deposits))
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem analogy_physics_bankTransfers :
  Nonempty
    (Analogy Physics (Theory.extend Banking isTransfer) (beforeAfter totalEnergy)
      (beforeAfter deposits)) :=
  _
```

**Aksiyomlar:** 

**OKUMA (denetlenmedi):** Fizik → bankacılığın yalnızca-virman alt kuramı analojisi vardır.
Çapa: toplam enerji = toplam mevduat.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Analogy`: [3399172939] Analoji sertifikası: çapalı yorum ve `B`'nin bir modeli. Model şarttır:
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Analogy.mk`: [1654795118] 
- `Interp`: [2611793070] Yorum: `B`'nin her yapısı `A`'nın diliyle okunur ve `B` modelleri `A` modellerine gider.
- `Interp.mk`: [1218699832] 
- `Theory.Ax`: [1298832593] 
- `Interp.Anchors`: [2166312076] Çapa: `B` modellerinde, yorum altında `A`'nın `oa` gözlenebiliri `B`'nin `ob`
- `Interp.red`: [2182380329] 
- `Physics`: [2772069666] OKUMA: yalıtık iki cisimli sistemde enerji alışverişlerinin kuramı.
- `transitions`: [2828025917] OKUMA: `step` ile izin verilen tek adımlık değişimlerin kuramı.
- `Bodies`: [4109377457] OKUMA: iki cisim ve enerjileri.
- `Bodies.mk`: [3768457870] 
- `energyExchange`: [655753540] OKUMA: enerji alışverişi. Bir cisim `a` kadar verir, öteki `a` kadar alır.
- `Bodies.e1`: [269133673] 
- `Bodies.e2`: [1766690774] 
- `Theory.extend`: [2058968486] Alt kuram: ek aksiyom `P`. Kısmi analoji, alt kurama kurulan tam analojidir.
- `Banking`: [986654585] OKUMA: bankacılık kuramı (virman ve kredi).
- `Bank`: [104610261] OKUMA: bir bankanın iki mevduat hesabı ve kredi defteri.
- `Bank.mk`: [4139289883] 
- `bankStep`: [4247479789] OKUMA: bankanın izinli adımları: virman ya da kredi açma.
- `bankTransfer`: [3338369604] OKUMA: mevduat hesapları arasında virman. Kredi değişmez.
- `Bank.mevduat1`: [2568518814] 
- `Bank.mevduat2`: [2202401906] 
- `Bank.kredi`: [165301259] 
- `bankLoan`: [1325537172] OKUMA: kredi açma. Banka `a > 0` kredi verir ve bunu borçlunun hesabına mevduat
- `isTransfer`: [1914998226] OKUMA: adım bir virmandır. Kısmi analojide alt kuramı seçer.
- `beforeAfter`: [370155043] OKUMA: bir ölçünün adımdan önceki ve sonraki değeri. Çapa olarak kullanılır.
- `totalEnergy`: [1900074533] OKUMA: toplam enerji.
- `deposits`: [1333321293] OKUMA: toplam mevduat (geniş para).

---

## `bankTransfers_conserve_deposits`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
(Banking.extend isTransfer).Thm fun p => Unchanged (beforeAfter deposits p)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem bankTransfers_conserve_deposits :
  Theory.Thm (Theory.extend Banking isTransfer)
    (fun (p : Theory.Str (Theory.extend Banking isTransfer)) =>
    Unchanged (beforeAfter deposits p)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Virmanlar altında toplam mevduat korunur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Theory.Thm`: [3592344556] `φ` kuramın teoremidir: her modelde doğrudur.
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Theory.Ax`: [1298832593] 
- `Theory.extend`: [2058968486] Alt kuram: ek aksiyom `P`. Kısmi analoji, alt kurama kurulan tam analojidir.
- `Banking`: [986654585] OKUMA: bankacılık kuramı (virman ve kredi).
- `transitions`: [2828025917] OKUMA: `step` ile izin verilen tek adımlık değişimlerin kuramı.
- `Bank`: [104610261] OKUMA: bir bankanın iki mevduat hesabı ve kredi defteri.
- `Bank.mk`: [4139289883] 
- `bankStep`: [4247479789] OKUMA: bankanın izinli adımları: virman ya da kredi açma.
- `bankTransfer`: [3338369604] OKUMA: mevduat hesapları arasında virman. Kredi değişmez.
- `Bank.mevduat1`: [2568518814] 
- `Bank.mevduat2`: [2202401906] 
- `Bank.kredi`: [165301259] 
- `bankLoan`: [1325537172] OKUMA: kredi açma. Banka `a > 0` kredi verir ve bunu borçlunun hesabına mevduat
- `isTransfer`: [1914998226] OKUMA: adım bir virmandır. Kısmi analojide alt kuramı seçer.
- `Unchanged`: [3960646650] OKUMA: önce ve sonra değerleri eşit. Korunum budur.
- `beforeAfter`: [370155043] OKUMA: bir ölçünün adımdan önceki ve sonraki değeri. Çapa olarak kullanılır.
- `deposits`: [1333321293] OKUMA: toplam mevduat (geniş para).

---

## `metaphor_physics_banking_deposits`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Refutation Physics Banking (beforeAfter totalEnergy) (beforeAfter deposits))
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem metaphor_physics_banking_deposits :
  Nonempty (Refutation Physics Banking (beforeAfter totalEnergy) (beforeAfter deposits)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** "Toplam enerji = toplam mevduat" çapasıyla fizik → bankacılık (kredi dahil)
bir metafordur. Fizikte kanıtlı bir iddiayı çiğneyen bir bankacılık modeli vardır.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Refutation`: [3931022488] Metafor sertifikası: `A`'da teorem olan çapalı bir iddia ve bu iddiayı çiğneyen
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Refutation.mk`: [3867641051] 
- `Theory.Thm`: [3592344556] `φ` kuramın teoremidir: her modelde doğrudur.
- `Theory.Ax`: [1298832593] 
- `Physics`: [2772069666] OKUMA: yalıtık iki cisimli sistemde enerji alışverişlerinin kuramı.
- `transitions`: [2828025917] OKUMA: `step` ile izin verilen tek adımlık değişimlerin kuramı.
- `Bodies`: [4109377457] OKUMA: iki cisim ve enerjileri.
- `Bodies.mk`: [3768457870] 
- `energyExchange`: [655753540] OKUMA: enerji alışverişi. Bir cisim `a` kadar verir, öteki `a` kadar alır.
- `Bodies.e1`: [269133673] 
- `Bodies.e2`: [1766690774] 
- `Banking`: [986654585] OKUMA: bankacılık kuramı (virman ve kredi).
- `Bank`: [104610261] OKUMA: bir bankanın iki mevduat hesabı ve kredi defteri.
- `Bank.mk`: [4139289883] 
- `bankStep`: [4247479789] OKUMA: bankanın izinli adımları: virman ya da kredi açma.
- `bankTransfer`: [3338369604] OKUMA: mevduat hesapları arasında virman. Kredi değişmez.
- `Bank.mevduat1`: [2568518814] 
- `Bank.mevduat2`: [2202401906] 
- `Bank.kredi`: [165301259] 
- `bankLoan`: [1325537172] OKUMA: kredi açma. Banka `a > 0` kredi verir ve bunu borçlunun hesabına mevduat
- `beforeAfter`: [370155043] OKUMA: bir ölçünün adımdan önceki ve sonraki değeri. Çapa olarak kullanılır.
- `totalEnergy`: [1900074533] OKUMA: toplam enerji.
- `deposits`: [1333321293] OKUMA: toplam mevduat (geniş para).

---

## `analogy_physics_banking_net`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Analogy Physics Banking (beforeAfter totalEnergy) (beforeAfter netPosition))
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem analogy_physics_banking_net :
  Nonempty (Analogy Physics Banking (beforeAfter totalEnergy) (beforeAfter netPosition)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** "Toplam enerji = net pozisyon (mevduat − kredi)" çapasıyla fizik → bankacılık
(kredi dahil) analojisi vardır. Hüküm disiplinlere değil, çapaya bağlıdır.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Analogy`: [3399172939] Analoji sertifikası: çapalı yorum ve `B`'nin bir modeli. Model şarttır:
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Analogy.mk`: [1654795118] 
- `Interp`: [2611793070] Yorum: `B`'nin her yapısı `A`'nın diliyle okunur ve `B` modelleri `A` modellerine gider.
- `Interp.mk`: [1218699832] 
- `Theory.Ax`: [1298832593] 
- `Interp.Anchors`: [2166312076] Çapa: `B` modellerinde, yorum altında `A`'nın `oa` gözlenebiliri `B`'nin `ob`
- `Interp.red`: [2182380329] 
- `Physics`: [2772069666] OKUMA: yalıtık iki cisimli sistemde enerji alışverişlerinin kuramı.
- `transitions`: [2828025917] OKUMA: `step` ile izin verilen tek adımlık değişimlerin kuramı.
- `Bodies`: [4109377457] OKUMA: iki cisim ve enerjileri.
- `Bodies.mk`: [3768457870] 
- `energyExchange`: [655753540] OKUMA: enerji alışverişi. Bir cisim `a` kadar verir, öteki `a` kadar alır.
- `Bodies.e1`: [269133673] 
- `Bodies.e2`: [1766690774] 
- `Banking`: [986654585] OKUMA: bankacılık kuramı (virman ve kredi).
- `Bank`: [104610261] OKUMA: bir bankanın iki mevduat hesabı ve kredi defteri.
- `Bank.mk`: [4139289883] 
- `bankStep`: [4247479789] OKUMA: bankanın izinli adımları: virman ya da kredi açma.
- `bankTransfer`: [3338369604] OKUMA: mevduat hesapları arasında virman. Kredi değişmez.
- `Bank.mevduat1`: [2568518814] 
- `Bank.mevduat2`: [2202401906] 
- `Bank.kredi`: [165301259] 
- `bankLoan`: [1325537172] OKUMA: kredi açma. Banka `a > 0` kredi verir ve bunu borçlunun hesabına mevduat
- `beforeAfter`: [370155043] OKUMA: bir ölçünün adımdan önceki ve sonraki değeri. Çapa olarak kullanılır.
- `totalEnergy`: [1900074533] OKUMA: toplam enerji.
- `netPosition`: [4041380305] OKUMA: net pozisyon. Mevduat eksi kredi; bilançonun iki yakası.

---

## `thermo_equilibrium_even`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Thermo.Thm fun t => EquilibriumIsEven (thermoObs t)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem thermo_equilibrium_even :
  Theory.Thm Thermo (fun (t : Theory.Str Thermo) => EquilibriumIsEven (thermoObs t)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Termodinamik dengede enerji iki cisim arasında eşit dağılır (en çok bir birim fark).

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Theory.Thm`: [3592344556] `φ` kuramın teoremidir: her modelde doğrudur.
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Theory.Ax`: [1298832593] 
- `Thermo`: [4237014058] OKUMA: termodinamik kuramı. Aksiyomlar: entropi kesin içbükeydir, yani ısı
- `ThermoSys`: [2382598904] OKUMA: iki cisimli sistem. İki cismin entropi fonksiyonu `S` aynıdır, `state`
- `ThermoSys.mk`: [785602455] 
- `Split`: [3300463990] OKUMA: korunan bir niceliğin iki parça arasındaki dağılımı.
- `Split.mk`: [3983276553] 
- `StrictlyConcave`: [2949460236] OKUMA: `f` kesin içbükeydir. Ardışık artışlar kesin azalır.
- `ThermoSys.S`: [3977409762] 
- `Split.Feasible`: [769212726] OKUMA: bu dağılımda iki parça da negatif değil.
- `Split.x1`: [449413382] 
- `Split.x2`: [690237411] 
- `ThermoSys.state`: [1021469893] 
- `EquilibriumIsEven`: [2624732429] OKUMA: "dengedeyse dağılım eşittir (en çok bir birim fark)".
- `thermoObs`: [344136154] OKUMA: termodinamik gözlenebilirler. Sistem dengede mi; enerji farkı.
- `ThermoSys.Equilibrium`: [1012426861] OKUMA: termodinamik denge. Hiçbir süreç mümkün değil.
- `heatProcess`: [294128019] OKUMA: Clausius ölçütü. `p`'den `q`'ya bir süreç mümkündür ancak ve ancak
- `Split.gap`: [2491791204] OKUMA: iki parça arasındaki fark (`x1 - x2`).

---

## `analogy_thermo_marketDMU`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Analogy Thermo MarketDMU thermoObs marketObs)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem analogy_thermo_marketDMU : Nonempty (Analogy Thermo MarketDMU thermoObs marketObs) := _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Termodinamik → azalan marjinal faydalı piyasa analojisi vardır.
Çapa: (dengede mi, fark) ↦ (dengede mi, fark).

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Analogy`: [3399172939] Analoji sertifikası: çapalı yorum ve `B`'nin bir modeli. Model şarttır:
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Analogy.mk`: [1654795118] 
- `Interp`: [2611793070] Yorum: `B`'nin her yapısı `A`'nın diliyle okunur ve `B` modelleri `A` modellerine gider.
- `Interp.mk`: [1218699832] 
- `Theory.Ax`: [1298832593] 
- `Interp.Anchors`: [2166312076] Çapa: `B` modellerinde, yorum altında `A`'nın `oa` gözlenebiliri `B`'nin `ob`
- `Interp.red`: [2182380329] 
- `Thermo`: [4237014058] OKUMA: termodinamik kuramı. Aksiyomlar: entropi kesin içbükeydir, yani ısı
- `ThermoSys`: [2382598904] OKUMA: iki cisimli sistem. İki cismin entropi fonksiyonu `S` aynıdır, `state`
- `ThermoSys.mk`: [785602455] 
- `Split`: [3300463990] OKUMA: korunan bir niceliğin iki parça arasındaki dağılımı.
- `Split.mk`: [3983276553] 
- `StrictlyConcave`: [2949460236] OKUMA: `f` kesin içbükeydir. Ardışık artışlar kesin azalır.
- `ThermoSys.S`: [3977409762] 
- `Split.Feasible`: [769212726] OKUMA: bu dağılımda iki parça da negatif değil.
- `Split.x1`: [449413382] 
- `Split.x2`: [690237411] 
- `ThermoSys.state`: [1021469893] 
- `MarketDMU`: [2074773115] OKUMA: azalan marjinal faydalı piyasalar (alt kuram).
- `Theory.extend`: [2058968486] Alt kuram: ek aksiyom `P`. Kısmi analoji, alt kurama kurulan tam analojidir.
- `Market`: [1105006028] OKUMA: değişim piyasası kuramı. Tercihlere kısıt yoktur; yalnızca mevcut dağılım
- `Exchange`: [658301019] OKUMA: iki tüccar. Mal için fayda fonksiyonları `u` aynıdır, `alloc` malın
- `Exchange.mk`: [1302687585] 
- `Exchange.alloc`: [2928997197] 
- `DiminishingMarginalUtility`: [2558328295] OKUMA: azalan marjinal fayda.
- `Exchange.u`: [1432426348] 
- `thermoObs`: [344136154] OKUMA: termodinamik gözlenebilirler. Sistem dengede mi; enerji farkı.
- `ThermoSys.Equilibrium`: [1012426861] OKUMA: termodinamik denge. Hiçbir süreç mümkün değil.
- `heatProcess`: [294128019] OKUMA: Clausius ölçütü. `p`'den `q`'ya bir süreç mümkündür ancak ve ancak
- `Split.gap`: [2491791204] OKUMA: iki parça arasındaki fark (`x1 - x2`).
- `marketObs`: [2709313722] OKUMA: piyasa gözlenebilirleri. Piyasa dengede mi; miktar farkı.
- `Exchange.Equilibrium`: [3551839172] OKUMA: piyasa dengesi. Gönüllü ticaret kalmamıştır (Pareto-etkinlik).
- `voluntaryTrade`: [3058121065] OKUMA: gönüllü ticaret. Mal korunur ve miktarlar negatif olmaz. Bir `t`

---

## `marketDMU_equilibrium_even`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
MarketDMU.Thm fun m => EquilibriumIsEven (marketObs m)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem marketDMU_equilibrium_even :
  Theory.Thm MarketDMU (fun (m : Theory.Str MarketDMU) => EquilibriumIsEven (marketObs m)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Azalan marjinal fayda altında piyasa dengesinde mal eşit dağılır (en çok bir birim fark).

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Theory.Thm`: [3592344556] `φ` kuramın teoremidir: her modelde doğrudur.
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Theory.Ax`: [1298832593] 
- `MarketDMU`: [2074773115] OKUMA: azalan marjinal faydalı piyasalar (alt kuram).
- `Theory.extend`: [2058968486] Alt kuram: ek aksiyom `P`. Kısmi analoji, alt kurama kurulan tam analojidir.
- `Market`: [1105006028] OKUMA: değişim piyasası kuramı. Tercihlere kısıt yoktur; yalnızca mevcut dağılım
- `Exchange`: [658301019] OKUMA: iki tüccar. Mal için fayda fonksiyonları `u` aynıdır, `alloc` malın
- `Exchange.mk`: [1302687585] 
- `Split`: [3300463990] OKUMA: korunan bir niceliğin iki parça arasındaki dağılımı.
- `Split.mk`: [3983276553] 
- `Split.Feasible`: [769212726] OKUMA: bu dağılımda iki parça da negatif değil.
- `Split.x1`: [449413382] 
- `Split.x2`: [690237411] 
- `Exchange.alloc`: [2928997197] 
- `DiminishingMarginalUtility`: [2558328295] OKUMA: azalan marjinal fayda.
- `Exchange.u`: [1432426348] 
- `EquilibriumIsEven`: [2624732429] OKUMA: "dengedeyse dağılım eşittir (en çok bir birim fark)".
- `marketObs`: [2709313722] OKUMA: piyasa gözlenebilirleri. Piyasa dengede mi; miktar farkı.
- `Exchange.Equilibrium`: [3551839172] OKUMA: piyasa dengesi. Gönüllü ticaret kalmamıştır (Pareto-etkinlik).
- `voluntaryTrade`: [3058121065] OKUMA: gönüllü ticaret. Mal korunur ve miktarlar negatif olmaz. Bir `t`
- `Split.gap`: [2491791204] OKUMA: iki parça arasındaki fark (`x1 - x2`).

---

## `metaphor_thermo_market`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Refutation Thermo Market thermoObs marketObs)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem metaphor_thermo_market : Nonempty (Refutation Thermo Market thermoObs marketObs) := _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Aynı çapayla termodinamik → kısıtsız piyasa bir metafordur. Marjinal faydanın
kesin azalmadığı bir piyasada (karşı örnek: sabit marjinal fayda) dengede eşitsiz
dağılım vardır.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Refutation`: [3931022488] Metafor sertifikası: `A`'da teorem olan çapalı bir iddia ve bu iddiayı çiğneyen
- `Theory`: [3285735785] Kuram: yapılar ve aksiyomlar. Bir modeli, `Ax`'i sağlayan bir `s : Str`'dir.
- `Theory.mk`: [4004667536] 
- `Theory.Str`: [2729364318] 
- `Refutation.mk`: [3867641051] 
- `Theory.Thm`: [3592344556] `φ` kuramın teoremidir: her modelde doğrudur.
- `Theory.Ax`: [1298832593] 
- `Thermo`: [4237014058] OKUMA: termodinamik kuramı. Aksiyomlar: entropi kesin içbükeydir, yani ısı
- `ThermoSys`: [2382598904] OKUMA: iki cisimli sistem. İki cismin entropi fonksiyonu `S` aynıdır, `state`
- `ThermoSys.mk`: [785602455] 
- `Split`: [3300463990] OKUMA: korunan bir niceliğin iki parça arasındaki dağılımı.
- `Split.mk`: [3983276553] 
- `StrictlyConcave`: [2949460236] OKUMA: `f` kesin içbükeydir. Ardışık artışlar kesin azalır.
- `ThermoSys.S`: [3977409762] 
- `Split.Feasible`: [769212726] OKUMA: bu dağılımda iki parça da negatif değil.
- `Split.x1`: [449413382] 
- `Split.x2`: [690237411] 
- `ThermoSys.state`: [1021469893] 
- `Market`: [1105006028] OKUMA: değişim piyasası kuramı. Tercihlere kısıt yoktur; yalnızca mevcut dağılım
- `Exchange`: [658301019] OKUMA: iki tüccar. Mal için fayda fonksiyonları `u` aynıdır, `alloc` malın
- `Exchange.mk`: [1302687585] 
- `Exchange.alloc`: [2928997197] 
- `thermoObs`: [344136154] OKUMA: termodinamik gözlenebilirler. Sistem dengede mi; enerji farkı.
- `ThermoSys.Equilibrium`: [1012426861] OKUMA: termodinamik denge. Hiçbir süreç mümkün değil.
- `heatProcess`: [294128019] OKUMA: Clausius ölçütü. `p`'den `q`'ya bir süreç mümkündür ancak ve ancak
- `Split.gap`: [2491791204] OKUMA: iki parça arasındaki fark (`x1 - x2`).
- `marketObs`: [2709313722] OKUMA: piyasa gözlenebilirleri. Piyasa dengede mi; miktar farkı.
- `Exchange.Equilibrium`: [3551839172] OKUMA: piyasa dengesi. Gönüllü ticaret kalmamıştır (Pareto-etkinlik).
- `voluntaryTrade`: [3058121065] OKUMA: gönüllü ticaret. Mal korunur ve miktarlar negatif olmaz. Bir `t`
- `Exchange.u`: [1432426348] 

---

## `stern_verdict`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Verdict SCCQuestion sternNorms (TaxAtLeast 120000000))
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem stern_verdict :
  Nonempty (Verdict SCCQuestion sternNorms (TaxAtLeast (OfNat.ofNat 120000000))) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Pigou ölçütü ve ρ = %0,1 seçilirse, ölçüm aralığındaki her olgu için
vergi en az 120 $/tCO₂ olmalı. Olgular bu sonucu tek başına belirlemez.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Verdict`: [1413497553] Politika hükmü: "`norms` değer seçimleri yapılırsa, ölçüm aralığındaki her olgu için `C`".
- `Question`: [48923287] Politika sorusu. `E`: ölçülen koordinatlar. `N`: seçilen (değer) koordinatlar.
- `Question.mk`: [3222615907] 
- `Question.N`: [3111988493] 
- `Question.E`: [3283847841] 
- `Verdict.mk`: [1829301260] 
- `Question.facts`: [2788285581] 
- `SCCQuestion`: [3402229104] OKUMA: SCC politika sorusu.
- `Facts`: [842582985] OKUMA: ampirik koordinatlar.
- `Facts.mk`: [2037389537] 
- `Values`: [3293254189] OKUMA: normatif koordinatlar.
- `Values.mk`: [2380993278] 
- `Criterion`: [3620678455] OKUMA: politika ölçütü. `pigou`: vergi marjinal sosyal maliyete eşit olmalı.
- `Criterion.pigou`: [1404234356] 
- `Criterion.laissezFaire`: [2972272900] 
- `measured`: [3441030612] OKUMA: ölçüm aralığı (ÖRNEK değerler, ampirik tahmin değil).
- `Facts.damage`: [856121433] 
- `Facts.horizon`: [185298772] 
- `sternNorms`: [3672334455] OKUMA: Stern (2006) türü seçim. Pigou ölçütü, ρ = %0,1.
- `Values.criterion`: [3518424098] 
- `Values.rho`: [3168885374] 
- `TaxAtLeast`: [155877268] OKUMA: önerilen vergi en az `x` µ$/tCO₂.
- `recommendedTax`: [1260082584] OKUMA: ölçütün önerdiği vergi, µ$/tCO₂.
- `recommendedTax.match_1`: [4272526356] 
- `Criterion.casesOn`: [698711377] 
- `Criterion.rec`: [546252169] 
- `scc`: [2590175101] OKUMA: karbonun sosyal maliyeti, µ$/tCO₂.
- `discountedSum`: [2443568555] OKUMA: iskontolu toplam `v + v/(1+ρ) + v/(1+ρ)² + …`, `n` dönem.
- `discountedSum.match_1`: [523340485] 

---

## `nordhaus_verdict`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Nonempty (Verdict SCCQuestion nordhausNorms (TaxBelow 75000000))
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem nordhaus_verdict :
  Nonempty (Verdict SCCQuestion nordhausNorms (TaxBelow (OfNat.ofNat 75000000))) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Pigou ölçütü ve ρ = %1,5 seçilirse, ölçüm aralığındaki her olgu için
vergi 75 $/tCO₂'nin altında olmalı.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Verdict`: [1413497553] Politika hükmü: "`norms` değer seçimleri yapılırsa, ölçüm aralığındaki her olgu için `C`".
- `Question`: [48923287] Politika sorusu. `E`: ölçülen koordinatlar. `N`: seçilen (değer) koordinatlar.
- `Question.mk`: [3222615907] 
- `Question.N`: [3111988493] 
- `Question.E`: [3283847841] 
- `Verdict.mk`: [1829301260] 
- `Question.facts`: [2788285581] 
- `SCCQuestion`: [3402229104] OKUMA: SCC politika sorusu.
- `Facts`: [842582985] OKUMA: ampirik koordinatlar.
- `Facts.mk`: [2037389537] 
- `Values`: [3293254189] OKUMA: normatif koordinatlar.
- `Values.mk`: [2380993278] 
- `Criterion`: [3620678455] OKUMA: politika ölçütü. `pigou`: vergi marjinal sosyal maliyete eşit olmalı.
- `Criterion.pigou`: [1404234356] 
- `Criterion.laissezFaire`: [2972272900] 
- `measured`: [3441030612] OKUMA: ölçüm aralığı (ÖRNEK değerler, ampirik tahmin değil).
- `Facts.damage`: [856121433] 
- `Facts.horizon`: [185298772] 
- `nordhausNorms`: [1730849531] OKUMA: Nordhaus (DICE) türü seçim. Pigou ölçütü, ρ = %1,5.
- `Values.criterion`: [3518424098] 
- `Values.rho`: [3168885374] 
- `TaxBelow`: [1314254359] OKUMA: önerilen vergi `x` µ$/tCO₂'den az.
- `recommendedTax`: [1260082584] OKUMA: ölçütün önerdiği vergi, µ$/tCO₂.
- `recommendedTax.match_1`: [4272526356] 
- `Criterion.casesOn`: [698711377] 
- `Criterion.rec`: [546252169] 
- `scc`: [2590175101] OKUMA: karbonun sosyal maliyeti, µ$/tCO₂.
- `discountedSum`: [2443568555] OKUMA: iskontolu toplam `v + v/(1+ρ) + v/(1+ρ)² + …`, `n` dönem.
- `discountedSum.match_1`: [523340485] 

---

## `scc_rho_alone_decides`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ (e : Facts),
  measured e →
    TaxAtLeast 120000000 e { rho := 10, criterion := Criterion.pigou } ∧
      TaxBelow 75000000 e { rho := 150, criterion := Criterion.pigou }
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem scc_rho_alone_decides :
  forall (e : Facts),
  measured e → And
    (TaxAtLeast (OfNat.ofNat 120000000) e (Values.mk (OfNat.ofNat 10) Criterion.pigou))
    (TaxBelow (OfNat.ofNat 75000000) e (Values.mk (OfNat.ofNat 150) Criterion.pigou)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Ölçüm aralığındaki her olgu için, ölçüt (Pigou) sabitken yalnızca ρ'yu
%0,1'den %1,5'e değiştirmek sonucu "≥ 120 $" iken "< 75 $" yapar.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Facts`: [842582985] OKUMA: ampirik koordinatlar.
- `Facts.mk`: [2037389537] 
- `measured`: [3441030612] OKUMA: ölçüm aralığı (ÖRNEK değerler, ampirik tahmin değil).
- `Facts.damage`: [856121433] 
- `Facts.horizon`: [185298772] 
- `TaxAtLeast`: [155877268] OKUMA: önerilen vergi en az `x` µ$/tCO₂.
- `Values`: [3293254189] OKUMA: normatif koordinatlar.
- `Values.mk`: [2380993278] 
- `Criterion`: [3620678455] OKUMA: politika ölçütü. `pigou`: vergi marjinal sosyal maliyete eşit olmalı.
- `Criterion.pigou`: [1404234356] 
- `Criterion.laissezFaire`: [2972272900] 
- `recommendedTax`: [1260082584] OKUMA: ölçütün önerdiği vergi, µ$/tCO₂.
- `recommendedTax.match_1`: [4272526356] 
- `Criterion.casesOn`: [698711377] 
- `Criterion.rec`: [546252169] 
- `Values.criterion`: [3518424098] 
- `scc`: [2590175101] OKUMA: karbonun sosyal maliyeti, µ$/tCO₂.
- `discountedSum`: [2443568555] OKUMA: iskontolu toplam `v + v/(1+ρ) + v/(1+ρ)² + …`, `n` dönem.
- `discountedSum.match_1`: [523340485] 
- `Values.rho`: [3168885374] 
- `TaxBelow`: [1314254359] OKUMA: önerilen vergi `x` µ$/tCO₂'den az.


