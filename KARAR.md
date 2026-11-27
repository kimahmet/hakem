# KARAR

Bu dosya `tools/hakem.sh` tarafından üretilir. Elle düzenlenmez.

**21 / 21 iddia biçimsel kabul aldı.**

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

## `satisfaction`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₁ S₂ : Signature} (σ : SigMorph S₁ S₂) (M : Structure S₂) (φ : Formula S₁), M.Sat (σ.trF φ) ↔ (σ.reduct M).Sat φ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem satisfaction :
  forall {S₁ S₂ : Signature} (σ : SigMorph S₁ S₂) (M : Structure S₂) (φ : Formula S₁),
  Iff (Structure.Sat M (SigMorph.trF σ φ)) (Structure.Sat (SigMorph.reduct σ M) φ) :=
  _
```

**Aksiyomlar:** Quot.sound, propext

**OKUMA (denetlenmedi):** Tatmin koşulu. Bir önermenin çevirisi hedef dünyada doğrudur ancak ve ancak
önerme, o dünyanın kaynak diliyle okunuşunda doğrudur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Signature.Fn`: [1658714567] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.fnArity`: [763541887] 
- `Signature.Rel`: [3095078984] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Formula.rel`: [3663972162] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `SigMorph.fnMap`: [461941377] 
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `SigMorph.relMap`: [3323659712] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.

---

## `transfer`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} (a : Analogy A B) {φ : Formula S₁},
  A.Entails φ → B.Entails (a.σ.trF φ)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem transfer :
  forall {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} (a : Analogy A B)
    {φ : Formula S₁},
  Theory.Entails A φ → Theory.Entails B (SigMorph.trF (Analogy.σ a) φ) :=
  _
```

**Aksiyomlar:** Quot.sound, propext

**OKUMA (denetlenmedi):** Aktarım. Kaynak kuramın gerektirdiği her önermenin çevirisini hedef kuram
gerektirir.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `Analogy.σ`: [2934450448] 

---

## `source_consistent`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} (a : Analogy A B), ∃ M, A.Models M
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem source_consistent :
  forall {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂},
  Analogy A B → Exists (fun (M : Structure S₁) => Theory.Models A M) :=
  _
```

**Aksiyomlar:** Quot.sound, propext

**OKUMA (denetlenmedi):** Bir analoji varsa kaynak kuramın da modeli vardır (aktarım boş değildir).

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.

---

## `compose_exists`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₁ S₂ S₃ : Signature} {A : Theory S₁} {B : Theory S₂} {C : Theory S₃} (a : Analogy A B) (b : Analogy B C),
  ∃ c, c.σ = a.σ.comp b.σ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem compose_exists :
  forall {S₁ S₂ S₃ : Signature} {A : Theory S₁} {B : Theory S₂} {C : Theory S₃}
    (a : Analogy A B) (b : Analogy B C),
  Exists
    (fun (c : Analogy A C) => Eq (Analogy.σ c) (SigMorph.comp (Analogy.σ a) (Analogy.σ b))) :=
  _
```

**Aksiyomlar:** Quot.sound, propext

**OKUMA (denetlenmedi):** Bileşim. Analojiler zincirlenir; zincirin sözlüğü, sözlüklerin bileşimidir.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `Analogy.σ`: [2934450448] 
- `SigMorph.comp`: [4087931904] Eşlemelerin bileşimi: önce `σ`, sonra `τ`.

---

## `refutation_sound`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂} {pf : S₁.Fn → Bool} {pr : S₁.Rel → Bool} {gl : SigMorph S₁ S₂}
  (a : Refutation A B pf pr gl) (a : Analogy A B), SigMorph.AgreeOn pf pr a.σ gl → False
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem refutation_sound :
  forall {S₁ S₂ : Signature} {A : Theory S₁} {B : Theory S₂}
    {pf : Signature.Fn S₁ → Bool} {pr : Signature.Rel S₁ → Bool} {gl : SigMorph S₁ S₂},
  Refutation A B pf pr gl → (forall (a : Analogy A B),
  SigMorph.AgreeOn pf pr (Analogy.σ a) gl → False) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Metafor. Bir karşı örnek, çapaları önerilen sözlükle aynı olan her analojiyi
dışlar.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Refutation`: [618331221] Metafor sertifikası. `glossary`, önerilen sözlüktür. `pf`/`pr` sözlüğün bağlayıcı
- `Refutation.mk`: [1987474353] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `Formula.onlySyms`: [2677709904] Formüldeki her sembol `pf`/`pr`'yi sağlar.
- `Formula.onlySyms.match_1`: [3446722069] 
- `Term.onlySyms`: [1893188890] Terimdeki her fonksiyon sembolü `pf`'yi sağlar.
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `SigMorph.fnMap`: [461941377] 
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `SigMorph.relMap`: [3323659712] 
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.AgreeOn`: [1063400748] İki eşleme `pf`/`pr`'nin seçtiği sembollerde aynıdır.
- `Analogy.σ`: [2934450448] 

---

## `hume_law`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} {T : Theory S} {φ : Formula S},
  (∀ (ψ : Formula S), ψ ∈ T.axioms → ψ.descriptive = true) → ¬Nonempty (PolicyVerdict T φ)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem hume_law :
  forall {S : Signature} {T : Theory S} {φ : Formula S},
  (forall (ψ : Formula S),
    Membership.mem (Theory.axioms T) ψ → Eq (Formula.descriptive ψ) Bool.true) →
  Not (Nonempty (PolicyVerdict T φ)) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Hume yasası. Bütün öncülleri betimsel olan (hiçbir normatif sembol içermeyen)
bir kuramdan hiçbir politika hükmü kurulamaz.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Theory.axioms`: [2865576458] 
- `Formula.descriptive`: [3510510651] Betimsel formül: hiçbir normatif sembol içermez.
- `Formula.onlySyms`: [2677709904] Formüldeki her sembol `pf`/`pr`'yi sağlar.
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.onlySyms.match_1`: [3446722069] 
- `Formula.casesOn`: [824629045] 
- `Term.onlySyms`: [1893188890] Terimdeki her fonksiyon sembolü `pf`'yi sağlar.
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `Signature.fnRole`: [3533609429] 
- `instDecidableEqRole`: [4090796487] 
- `Role.ctorIdx`: [3717224365] 
- `Role.casesOn`: [2538655878] 
- `Role.rec`: [3824428781] 
- `Role.ofNat`: [1323357135] 
- `Role.ofNat_ctorIdx`: [1788762641] 
- `Signature.relRole`: [1842763906] 
- `PolicyVerdict`: [1124954806] Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
- `PolicyVerdict.mk`: [3985630505] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Term.eval`: [704183430] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `Structure.reinterp`: [683133002] Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve

---

## `verdict_same_facts`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} {T : Theory S} {φ : Formula S} (v : PolicyVerdict T φ),
  (∀ (f : S.Fn), S.fnRole f ≠ Role.normatif → (v.world.reinterp v.g v.h).fn f = v.world.fn f) ∧
    (∀ (r : S.Rel), S.relRole r ≠ Role.normatif → (v.world.reinterp v.g v.h).rel r = v.world.rel r) ∧
      v.world.Sat φ ∧ ¬(v.world.reinterp v.g v.h).Sat φ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem verdict_same_facts :
  forall {S : Signature} {T : Theory S} {φ : Formula S} (v : PolicyVerdict T φ),
  And
    (forall (f : Signature.Fn S),
    Ne (Signature.fnRole S f) Role.normatif → Eq
      (Structure.fn
        (Structure.reinterp (PolicyVerdict.world v) (PolicyVerdict.g v) (PolicyVerdict.h v)) f)
      (Structure.fn (PolicyVerdict.world v) f))
    (And
      (forall (r : Signature.Rel S),
      Ne (Signature.relRole S r) Role.normatif → Eq
        (Structure.rel
          (Structure.reinterp (PolicyVerdict.world v) (PolicyVerdict.g v) (PolicyVerdict.h v)) r)
        (Structure.rel (PolicyVerdict.world v) r))
      (And (Structure.Sat (PolicyVerdict.world v) φ)
        (Not
          (Structure.Sat
            (Structure.reinterp (PolicyVerdict.world v) (PolicyVerdict.g v) (PolicyVerdict.h v))
            φ)))) :=
  _
```

**Aksiyomlar:** 

**OKUMA (denetlenmedi):** Her politika hükmünde tartışma normatiftir. Alternatif dünya, bütün betimsel
sembollerde asıl dünyayla aynıdır; sonuç birinde doğru, ötekinde yanlıştır.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `PolicyVerdict`: [1124954806] Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
- `PolicyVerdict.mk`: [3985630505] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `Structure.reinterp`: [683133002] Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve
- `Signature.fnRole`: [3533609429] 
- `instDecidableEqRole`: [4090796487] 
- `Role.ctorIdx`: [3717224365] 
- `Role.casesOn`: [2538655878] 
- `Role.rec`: [3824428781] 
- `Role.ofNat`: [1323357135] 
- `Role.ofNat_ctorIdx`: [1788762641] 
- `Signature.relRole`: [1842763906] 
- `PolicyVerdict.world`: [3269489341] 
- `PolicyVerdict.g`: [2782943670] 
- `PolicyVerdict.h`: [2520830368] 

---

## `calculus_sound`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} [inst : DecidableEq S.Fn] [inst_1 : DecidableEq S.Rel] (T : Theory S) (φ : Formula S) (p : Proof S),
  check T.axioms φ p = true → T.Entails φ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem calculus_sound :
  forall {S : Signature}
    [inst._@.Solution.Calculus.4172918617._hygCtx._hyg.6 : DecidableEq (Signature.Fn S)]
    [inst._@.Solution.Calculus.4172918617._hygCtx._hyg.9 : DecidableEq (Signature.Rel S)]
    (T : Theory S) (φ : Formula S) (p : Proof S),
  Eq (check (Theory.axioms T) φ p) Bool.true → Theory.Entails T φ :=
  _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** Kalkülüsün sağlamlığı. Denetimden geçen bir ispat verisi, kuramın önermeyi
gerektirdiğini gösterir.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Signature.Fn`: [1658714567] 
- `Signature.Rel`: [3095078984] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Proof`: [170549367] 
- `Proof.hyp`: [1582129081] Bağlamdaki `i`. önerme.
- `Proof.falsumE`: [2366242677] `⊥ ⊢ φ`.
- `Proof.impI`: [3931984999] `φ, Γ ⊢ ψ` ise `Γ ⊢ φ → ψ`.
- `Proof.impE`: [1061357771] `φ → ψ` ve `φ` ise `ψ`.
- `Proof.andI`: [3658691116] 
- `Proof.andE1`: [3684149015] 
- `Proof.andE2`: [3276072308] 
- `Proof.orI1`: [1747576057] `φ` ise `φ ∨ ψ`.
- `Proof.orI2`: [3585741943] `ψ` ise `φ ∨ ψ`.
- `Proof.orE`: [3538543134] `φ ∨ ψ`, `φ, Γ ⊢ χ`, `ψ, Γ ⊢ χ` ise `χ`.
- `Proof.allI`: [559766548] `↑Γ ⊢ φ` ise `Γ ⊢ ∀ φ`.
- `Proof.allE`: [3331931983] `∀ φ` ise `φ[t]`.
- `Proof.exI`: [91387409] `φ[t]` ise `∃ φ`.
- `Proof.exE`: [1733893540] `∃ φ` ve `φ, ↑Γ ⊢ ↑χ` ise `χ`.
- `Proof.refl`: [1567304393] `t = t`.
- `Proof.eqE`: [1451317691] `t = u` ve `φ[t]` ise `φ[u]`.
- `Proof.em`: [894115869] `φ ∨ ¬ φ`.
- `check`: [3860000501] `p`, `Γ` bağlamında `φ`'nin ispatıdır.
- `infer.match_14`: [1029085789] 
- `infer`: [2821546232] İspatın bağlamdan çıkardığı önerme (geçersizse `none`).
- `Proof.brecOn`: [295508102] 
- `Proof.below`: [182045753] 
- `Proof.rec`: [4041985547] 
- `Proof.brecOn.go`: [2706797434] 
- `infer.match_20`: [231083464] 
- `Proof.casesOn`: [3404206879] 
- `infer.match_1`: [1775870579] 
- `Formula.ctorIdx`: [349303546] 
- `Formula.casesOn`: [824629045] 
- `Formula.rec`: [3232664870] 
- `infer.match_4`: [3274694551] 
- `Formula.beq`: [1367984369] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.beq.match_1`: [3869710647] 
- `Term.beq`: [4258871897] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.beq.match_1`: [1847837073] 
- `Term.casesOn`: [3327370182] 
- `Term.ctorIdx`: [2167574816] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `infer.match_6`: [663720379] 
- `infer.match_8`: [4138212058] 
- `infer.match_10`: [1414614076] 
- `Formula.shift`: [393530866] Serbest değişkenleri bir artır (bağlayıcıya girerken bağlam için).
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `Term.subst`: [162456198] Paralel ikame.
- `Term.onlySyms.match_1`: [264759630] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `liftSubst.match_1`: [1420932622] 
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `infer.match_12`: [1393948476] 
- `instSubst`: [2122467743] Değişken 0'a `t` koy, ötekileri bir azalt.
- `instSubst.match_1`: [2214616506] 
- `infer.match_16`: [258745636] 
- `infer.match_18`: [2860817874] 
- `Formula.not`: [231130077] `¬ φ`.
- `Theory.axioms`: [2865576458] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Term.eval`: [704183430] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).

---

## `finite_sat_iff`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} (M : FinStructure S) (φ : Formula S),
  φ.closed = true → (M.toStructure.Sat φ ↔ M.evalB (fun x => 0) φ = true)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem finite_sat_iff :
  forall {S : Signature} (M : FinStructure S) (φ : Formula S),
  Eq (Formula.closed φ) Bool.true → Iff (Structure.Sat (FinStructure.toStructure M) φ)
    (Eq
      (FinStructure.evalB M
        (fun (x._@.Solution.Finite.1742834118._hygCtx._hyg.31 : Nat) => OfNat.ofNat 0) φ)
      Bool.true) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Sonlu yapıda, kapalı bir formül için hesap ile doğruluk örtüşür.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `FinStructure`: [2240455362] Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar.
- `FinStructure.mk`: [3184878320] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Formula.rel`: [3663972162] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Formula.closed`: [3593464037] Kapalı formül (cümle).
- `Formula.varsBelow`: [2276081188] Formüldeki her serbest değişken `< k`.
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.varsBelow.match_1`: [3890479493] 
- `Formula.casesOn`: [824629045] 
- `Term.varsBelow`: [989945896] Terimdeki her değişken `< k`.
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.varsBelow.match_1`: [2471661240] 
- `Term.casesOn`: [3327370182] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Term.eval`: [704183430] 
- `Term.onlySyms.match_1`: [264759630] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `FinStructure.toStructure`: [3009531569] Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır.
- `FinStructure.n`: [1325356739] 
- `FinStructure.fn`: [508190427] 
- `FinStructure.rel`: [2799040893] 
- `FinStructure.evalB`: [2539266348] Formülün sonlu yapıda hesaplanması.
- `FinStructure.evalB.match_1`: [1169364348] 
- `anyFin`: [166542815] Sonlu ailede `||`.

---

## `finite_models_sound`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} (M : FinStructure S) (T : Theory S),
  T.admissible M.toStructure → M.checkTheory T = true → T.Models M.toStructure
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem finite_models_sound :
  forall {S : Signature} (M : FinStructure S) (T : Theory S),
  Theory.admissible T (FinStructure.toStructure M) → Eq (FinStructure.checkTheory M T)
      Bool.true →
  Theory.Models T (FinStructure.toStructure M) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Sonlu model denetimi sağlamdır.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `FinStructure`: [2240455362] Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar.
- `FinStructure.mk`: [3184878320] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Formula.rel`: [3663972162] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Theory.admissible`: [3746421213] 
- `FinStructure.toStructure`: [3009531569] Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır.
- `FinStructure.n`: [1325356739] 
- `FinStructure.fn`: [508190427] 
- `FinStructure.rel`: [2799040893] 
- `FinStructure.checkTheory`: [2600167987] Sonlu yapı kuramın her aksiyomunu (kapalı olarak) doğrular.
- `Theory.axioms`: [2865576458] 
- `Formula.closed`: [3593464037] Kapalı formül (cümle).
- `Formula.varsBelow`: [2276081188] Formüldeki her serbest değişken `< k`.
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.varsBelow.match_1`: [3890479493] 
- `Formula.casesOn`: [824629045] 
- `Term.varsBelow`: [989945896] Terimdeki her değişken `< k`.
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.varsBelow.match_1`: [2471661240] 
- `Term.casesOn`: [3327370182] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `FinStructure.evalB`: [2539266348] Formülün sonlu yapıda hesaplanması.
- `FinStructure.evalB.match_1`: [1169364348] 
- `Structure.D`: [1437261765] 
- `Term.eval`: [704183430] 
- `Term.onlySyms.match_1`: [264759630] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `anyFin`: [166542815] Sonlu ailede `||`.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Structure.rel`: [855465701] 

---

## `finite_refutes_sound`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} (M : FinStructure S) (φ : Formula S), M.refutes φ = true → ¬M.toStructure.Sat φ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem finite_refutes_sound :
  forall {S : Signature} (M : FinStructure S) (φ : Formula S),
  Eq (FinStructure.refutes M φ) Bool.true → Not
    (Structure.Sat (FinStructure.toStructure M) φ) :=
  _
```

**Aksiyomlar:** propext, Quot.sound

**OKUMA (denetlenmedi):** Sonlu çürütme sağlamdır.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `FinStructure`: [2240455362] Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar.
- `FinStructure.mk`: [3184878320] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Formula.rel`: [3663972162] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `FinStructure.refutes`: [3141469118] Sonlu yapıda kapalı bir formül yanlıştır.
- `Formula.closed`: [3593464037] Kapalı formül (cümle).
- `Formula.varsBelow`: [2276081188] Formüldeki her serbest değişken `< k`.
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.varsBelow.match_1`: [3890479493] 
- `Formula.casesOn`: [824629045] 
- `Term.varsBelow`: [989945896] Terimdeki her değişken `< k`.
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.varsBelow.match_1`: [2471661240] 
- `Term.casesOn`: [3327370182] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `FinStructure.evalB`: [2539266348] Formülün sonlu yapıda hesaplanması.
- `FinStructure.n`: [1325356739] 
- `FinStructure.evalB.match_1`: [1169364348] 
- `Structure.D`: [1437261765] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `FinStructure.toStructure`: [3009531569] Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır.
- `FinStructure.fn`: [508190427] 
- `FinStructure.rel`: [2799040893] 
- `Term.eval`: [704183430] 
- `Term.onlySyms.match_1`: [264759630] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `anyFin`: [166542815] Sonlu ailede `||`.
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Structure.rel`: [855465701] 

---

## `refutation_of_data`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₁ S₂ : Signature} [inst : DecidableEq S₁.Fn] [inst_1 : DecidableEq S₁.Rel] (A : Theory S₁) (B : Theory S₂)
  (pf : S₁.Fn → Bool) (pr : S₁.Rel → Bool) (gl : SigMorph S₁ S₂) (φ : Formula S₁) (p : Proof S₁) (C : FinStructure S₂),
  B.admissible C.toStructure →
    check A.axioms φ p = true →
      Formula.onlySyms pf pr φ = true →
        C.checkTheory B = true → C.refutes (gl.trF φ) = true → Nonempty (Refutation A B pf pr gl)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem refutation_of_data :
  forall {S₁ S₂ : Signature}
    [inst._@.Solution.Finite.3814173984._hygCtx._hyg.7 : DecidableEq (Signature.Fn S₁)]
    [inst._@.Solution.Finite.3814173984._hygCtx._hyg.10 : DecidableEq (Signature.Rel S₁)]
    (A : Theory S₁) (B : Theory S₂) (pf : Signature.Fn S₁ → Bool)
    (pr : Signature.Rel S₁ → Bool) (gl : SigMorph S₁ S₂) (φ : Formula S₁)
    (p : Proof S₁) (C : FinStructure S₂),
  Theory.admissible B (FinStructure.toStructure C) → Eq (check (Theory.axioms A) φ p)
      Bool.true →
  Eq (Formula.onlySyms pf pr φ) Bool.true → Eq (FinStructure.checkTheory C B) Bool.true → Eq
      (FinStructure.refutes C (SigMorph.trF gl φ)) Bool.true →
  Nonempty (Refutation A B pf pr gl) :=
  _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** Veriden metafor sertifikası. Kaynakta bir ispat verisi ve hedefte sonlu bir
karşı örnek, metafor sertifikası için yeterlidir.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Signature.Fn`: [1658714567] 
- `Signature.Rel`: [3095078984] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Proof`: [170549367] 
- `Proof.hyp`: [1582129081] Bağlamdaki `i`. önerme.
- `Proof.falsumE`: [2366242677] `⊥ ⊢ φ`.
- `Proof.impI`: [3931984999] `φ, Γ ⊢ ψ` ise `Γ ⊢ φ → ψ`.
- `Proof.impE`: [1061357771] `φ → ψ` ve `φ` ise `ψ`.
- `Proof.andI`: [3658691116] 
- `Proof.andE1`: [3684149015] 
- `Proof.andE2`: [3276072308] 
- `Proof.orI1`: [1747576057] `φ` ise `φ ∨ ψ`.
- `Proof.orI2`: [3585741943] `ψ` ise `φ ∨ ψ`.
- `Proof.orE`: [3538543134] `φ ∨ ψ`, `φ, Γ ⊢ χ`, `ψ, Γ ⊢ χ` ise `χ`.
- `Proof.allI`: [559766548] `↑Γ ⊢ φ` ise `Γ ⊢ ∀ φ`.
- `Proof.allE`: [3331931983] `∀ φ` ise `φ[t]`.
- `Proof.exI`: [91387409] `φ[t]` ise `∃ φ`.
- `Proof.exE`: [1733893540] `∃ φ` ve `φ, ↑Γ ⊢ ↑χ` ise `χ`.
- `Proof.refl`: [1567304393] `t = t`.
- `Proof.eqE`: [1451317691] `t = u` ve `φ[t]` ise `φ[u]`.
- `Proof.em`: [894115869] `φ ∨ ¬ φ`.
- `FinStructure`: [2240455362] Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar.
- `FinStructure.mk`: [3184878320] 
- `Theory.admissible`: [3746421213] 
- `FinStructure.toStructure`: [3009531569] Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır.
- `FinStructure.n`: [1325356739] 
- `FinStructure.fn`: [508190427] 
- `FinStructure.rel`: [2799040893] 
- `check`: [3860000501] `p`, `Γ` bağlamında `φ`'nin ispatıdır.
- `infer.match_14`: [1029085789] 
- `infer`: [2821546232] İspatın bağlamdan çıkardığı önerme (geçersizse `none`).
- `Proof.brecOn`: [295508102] 
- `Proof.below`: [182045753] 
- `Proof.rec`: [4041985547] 
- `Proof.brecOn.go`: [2706797434] 
- `infer.match_20`: [231083464] 
- `Proof.casesOn`: [3404206879] 
- `infer.match_1`: [1775870579] 
- `Formula.ctorIdx`: [349303546] 
- `Formula.casesOn`: [824629045] 
- `Formula.rec`: [3232664870] 
- `infer.match_4`: [3274694551] 
- `Formula.beq`: [1367984369] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.beq.match_1`: [3869710647] 
- `Term.beq`: [4258871897] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.beq.match_1`: [1847837073] 
- `Term.casesOn`: [3327370182] 
- `Term.ctorIdx`: [2167574816] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `infer.match_6`: [663720379] 
- `infer.match_8`: [4138212058] 
- `infer.match_10`: [1414614076] 
- `Formula.shift`: [393530866] Serbest değişkenleri bir artır (bağlayıcıya girerken bağlam için).
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `Term.subst`: [162456198] Paralel ikame.
- `Term.onlySyms.match_1`: [264759630] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `liftSubst.match_1`: [1420932622] 
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `infer.match_12`: [1393948476] 
- `instSubst`: [2122467743] Değişken 0'a `t` koy, ötekileri bir azalt.
- `instSubst.match_1`: [2214616506] 
- `infer.match_16`: [258745636] 
- `infer.match_18`: [2860817874] 
- `Formula.not`: [231130077] `¬ φ`.
- `Theory.axioms`: [2865576458] 
- `Formula.onlySyms`: [2677709904] Formüldeki her sembol `pf`/`pr`'yi sağlar.
- `Formula.onlySyms.match_1`: [3446722069] 
- `Term.onlySyms`: [1893188890] Terimdeki her fonksiyon sembolü `pf`'yi sağlar.
- `FinStructure.checkTheory`: [2600167987] Sonlu yapı kuramın her aksiyomunu (kapalı olarak) doğrular.
- `Formula.closed`: [3593464037] Kapalı formül (cümle).
- `Formula.varsBelow`: [2276081188] Formüldeki her serbest değişken `< k`.
- `Formula.varsBelow.match_1`: [3890479493] 
- `Term.varsBelow`: [989945896] Terimdeki her değişken `< k`.
- `Term.varsBelow.match_1`: [2471661240] 
- `FinStructure.evalB`: [2539266348] Formülün sonlu yapıda hesaplanması.
- `FinStructure.evalB.match_1`: [1169364348] 
- `Structure.D`: [1437261765] 
- `Term.eval`: [704183430] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `anyFin`: [166542815] Sonlu ailede `||`.
- `FinStructure.refutes`: [3141469118] Sonlu yapıda kapalı bir formül yanlıştır.
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `SigMorph.trT`: [4048100617] 
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `Refutation`: [618331221] Metafor sertifikası. `glossary`, önerilen sözlüktür. `pf`/`pr` sözlüğün bağlayıcı
- `Refutation.mk`: [1987474353] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Structure.rel`: [855465701] 

---

## `verdict_of_data`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} [inst : DecidableEq S.Fn] [inst_1 : DecidableEq S.Rel] (T : Theory S) (φ : Formula S) (p : Proof S)
  (W : FinStructure S) (g : (f : S.Fn) → (Fin (S.fnArity f) → Fin (W.n + 1)) → Fin (W.n + 1))
  (h : (r : S.Rel) → (Fin (S.relArity r) → Fin (W.n + 1)) → Bool),
  (∀ (M : Structure S), T.admissible M) →
    check T.axioms φ p = true →
      W.checkTheory T = true → (W.reinterpB g h).refutes φ = true → Nonempty (PolicyVerdict T φ)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem verdict_of_data :
  forall {S : Signature}
    [inst._@.Solution.Finite.3196690387._hygCtx._hyg.6 : DecidableEq (Signature.Fn S)]
    [inst._@.Solution.Finite.3196690387._hygCtx._hyg.9 : DecidableEq (Signature.Rel S)]
    (T : Theory S) (φ : Formula S) (p : Proof S) (W : FinStructure S)
    (g :
      (forall (f : Signature.Fn S),
      (Fin (Signature.fnArity S f) → Fin (HAdd.hAdd (FinStructure.n W) (OfNat.ofNat 1))) → Fin
        (HAdd.hAdd (FinStructure.n W) (OfNat.ofNat 1))))
    (h :
      (forall (r : Signature.Rel S),
      (Fin (Signature.relArity S r) → Fin (HAdd.hAdd (FinStructure.n W) (OfNat.ofNat 1))) →
      Bool)),
  (forall (M : Structure S), Theory.admissible T M) → Eq (check (Theory.axioms T) φ p)
      Bool.true →
  Eq (FinStructure.checkTheory W T) Bool.true → Eq
      (FinStructure.refutes (FinStructure.reinterpB W g h) φ) Bool.true →
  Nonempty (PolicyVerdict T φ) :=
  _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** Veriden politika hükmü. Bir ispat verisi, öncülleri sağlayan sonlu bir dünya
ve yalnızca normatif sembolleri değiştirilmiş, sonucu çürüten bir alternatif yeterlidir.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Signature.Fn`: [1658714567] 
- `Signature.Rel`: [3095078984] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Proof`: [170549367] 
- `Proof.hyp`: [1582129081] Bağlamdaki `i`. önerme.
- `Proof.falsumE`: [2366242677] `⊥ ⊢ φ`.
- `Proof.impI`: [3931984999] `φ, Γ ⊢ ψ` ise `Γ ⊢ φ → ψ`.
- `Proof.impE`: [1061357771] `φ → ψ` ve `φ` ise `ψ`.
- `Proof.andI`: [3658691116] 
- `Proof.andE1`: [3684149015] 
- `Proof.andE2`: [3276072308] 
- `Proof.orI1`: [1747576057] `φ` ise `φ ∨ ψ`.
- `Proof.orI2`: [3585741943] `ψ` ise `φ ∨ ψ`.
- `Proof.orE`: [3538543134] `φ ∨ ψ`, `φ, Γ ⊢ χ`, `ψ, Γ ⊢ χ` ise `χ`.
- `Proof.allI`: [559766548] `↑Γ ⊢ φ` ise `Γ ⊢ ∀ φ`.
- `Proof.allE`: [3331931983] `∀ φ` ise `φ[t]`.
- `Proof.exI`: [91387409] `φ[t]` ise `∃ φ`.
- `Proof.exE`: [1733893540] `∃ φ` ve `φ, ↑Γ ⊢ ↑χ` ise `χ`.
- `Proof.refl`: [1567304393] `t = t`.
- `Proof.eqE`: [1451317691] `t = u` ve `φ[t]` ise `φ[u]`.
- `Proof.em`: [894115869] `φ ∨ ¬ φ`.
- `FinStructure`: [2240455362] Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar.
- `FinStructure.mk`: [3184878320] 
- `FinStructure.n`: [1325356739] 
- `Theory.admissible`: [3746421213] 
- `check`: [3860000501] `p`, `Γ` bağlamında `φ`'nin ispatıdır.
- `infer.match_14`: [1029085789] 
- `infer`: [2821546232] İspatın bağlamdan çıkardığı önerme (geçersizse `none`).
- `Proof.brecOn`: [295508102] 
- `Proof.below`: [182045753] 
- `Proof.rec`: [4041985547] 
- `Proof.brecOn.go`: [2706797434] 
- `infer.match_20`: [231083464] 
- `Proof.casesOn`: [3404206879] 
- `infer.match_1`: [1775870579] 
- `Formula.ctorIdx`: [349303546] 
- `Formula.casesOn`: [824629045] 
- `Formula.rec`: [3232664870] 
- `infer.match_4`: [3274694551] 
- `Formula.beq`: [1367984369] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.beq.match_1`: [3869710647] 
- `Term.beq`: [4258871897] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.beq.match_1`: [1847837073] 
- `Term.casesOn`: [3327370182] 
- `Term.ctorIdx`: [2167574816] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `infer.match_6`: [663720379] 
- `infer.match_8`: [4138212058] 
- `infer.match_10`: [1414614076] 
- `Formula.shift`: [393530866] Serbest değişkenleri bir artır (bağlayıcıya girerken bağlam için).
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `Term.subst`: [162456198] Paralel ikame.
- `Term.onlySyms.match_1`: [264759630] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `liftSubst.match_1`: [1420932622] 
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `infer.match_12`: [1393948476] 
- `instSubst`: [2122467743] Değişken 0'a `t` koy, ötekileri bir azalt.
- `instSubst.match_1`: [2214616506] 
- `infer.match_16`: [258745636] 
- `infer.match_18`: [2860817874] 
- `Formula.not`: [231130077] `¬ φ`.
- `Theory.axioms`: [2865576458] 
- `FinStructure.checkTheory`: [2600167987] Sonlu yapı kuramın her aksiyomunu (kapalı olarak) doğrular.
- `Formula.closed`: [3593464037] Kapalı formül (cümle).
- `Formula.varsBelow`: [2276081188] Formüldeki her serbest değişken `< k`.
- `Formula.varsBelow.match_1`: [3890479493] 
- `Term.varsBelow`: [989945896] Terimdeki her değişken `< k`.
- `Term.varsBelow.match_1`: [2471661240] 
- `FinStructure.evalB`: [2539266348] Formülün sonlu yapıda hesaplanması.
- `FinStructure.evalB.match_1`: [1169364348] 
- `Structure.D`: [1437261765] 
- `FinStructure.toStructure`: [3009531569] Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır.
- `FinStructure.fn`: [508190427] 
- `FinStructure.rel`: [2799040893] 
- `Term.eval`: [704183430] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `anyFin`: [166542815] Sonlu ailede `||`.
- `FinStructure.refutes`: [3141469118] Sonlu yapıda kapalı bir formül yanlıştır.
- `FinStructure.reinterpB`: [3876393088] Tanık dünyanın normatif sembollerini değiştirerek elde edilen sonlu alternatif.
- `Signature.fnRole`: [3533609429] 
- `instDecidableEqRole`: [4090796487] 
- `Role.ctorIdx`: [3717224365] 
- `Role.casesOn`: [2538655878] 
- `Role.rec`: [3824428781] 
- `Role.ofNat`: [1323357135] 
- `Role.ofNat_ctorIdx`: [1788762641] 
- `Signature.relRole`: [1842763906] 
- `PolicyVerdict`: [1124954806] Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
- `PolicyVerdict.mk`: [3985630505] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Structure.rel`: [855465701] 
- `Structure.reinterp`: [683133002] Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve

---

## `iso_sat`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S : Signature} {M N : Structure S} (a : M.Iso N) (φ : Formula S), M.Sat φ ↔ N.Sat φ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem iso_sat :
  forall {S : Signature} {M N : Structure S},
  Structure.Iso M N → (forall (φ : Formula S),
  Iff (Structure.Sat M φ) (Structure.Sat N φ)) :=
  _
```

**Aksiyomlar:** Quot.sound, propext

**OKUMA (denetlenmedi):** İzomorf yapılar aynı önermeleri doğrular.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Structure.Iso`: [3804893765] İki yapı arasında izomorfizma: ters çevrilebilir, bütün yorumları koruyan eşleme.
- `Structure.Iso.mk`: [417343216] 
- `Structure.D`: [1437261765] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Formula.rel`: [3663972162] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 

---

## `background_sound`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₀ S : Signature} (ι : SigMorph S₀ S) (B : Structure S₀) (M : Structure S),
  Nonempty ((ι.reduct M).Iso B) → ∀ (ψ : Formula S₀), B.Sat ψ → M.Sat (ι.trF ψ)
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem background_sound :
  forall {S₀ S : Signature} (ι : SigMorph S₀ S) (B : Structure S₀) (M : Structure S)
    (a._@._internal._hyg.0 : Nonempty (Structure.Iso (SigMorph.reduct ι M) B)) (ψ : Formula S₀),
  Structure.Sat B ψ → Structure.Sat M (SigMorph.trF ι ψ) :=
  _
```

**Aksiyomlar:** Quot.sound, propext

**OKUMA (denetlenmedi):** Arka plan sağlamlığı. Standart yapıda doğru olan her önerme, standart kısmı o
yapıya izomorf olan her modelde (çevirisiyle) doğrudur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Signature.Fn`: [1658714567] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.fnArity`: [763541887] 
- `Signature.Rel`: [3095078984] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Formula.rel`: [3663972162] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Structure.Iso`: [3804893765] İki yapı arasında izomorfizma: ters çevrilebilir, bütün yorumları koruyan eşleme.
- `Structure.Iso.mk`: [417343216] 
- `Structure.D`: [1437261765] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `SigMorph.relMap`: [3323659712] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.

---

## `calculus_sound_bg`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₀ S : Signature} [inst : DecidableEq S.Fn] [inst_1 : DecidableEq S.Rel] (T : Theory S) (ι : SigMorph S₀ S)
  (B : Structure S₀) (bg : List (Formula S₀)) (φ : Formula S) (p : Proof S),
  (∀ (M : Structure S), T.admissible M → Nonempty ((ι.reduct M).Iso B)) →
    (∀ (ψ : Formula S₀), ψ ∈ bg → B.Sat ψ) → check (T.axioms ++ List.map ι.trF bg) φ p = true → T.Entails φ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem calculus_sound_bg :
  forall {S₀ S : Signature}
    [inst._@.Solution.Background.1305699675._hygCtx._hyg.7 : DecidableEq (Signature.Fn S)]
    [inst._@.Solution.Background.1305699675._hygCtx._hyg.10 : DecidableEq (Signature.Rel S)]
    (T : Theory S) (ι : SigMorph S₀ S) (B : Structure S₀) (bg : List (Formula S₀))
    (φ : Formula S) (p : Proof S),
  (forall (M : Structure S),
    Theory.admissible T M → Nonempty (Structure.Iso (SigMorph.reduct ι M) B)) →
  (forall (ψ : Formula S₀), Membership.mem bg ψ → Structure.Sat B ψ) → Eq
      (check (HAppend.hAppend (Theory.axioms T) (List.map (SigMorph.trF ι) bg)) φ p) Bool.true →
  Theory.Entails T φ :=
  _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** Arka planlı kalkülüs. İspat, kuramın aksiyomlarına ek olarak standart yapıda
doğru önermeleri (çevirileriyle) hipotez olarak kullanabilir.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Signature.Fn`: [1658714567] 
- `Signature.Rel`: [3095078984] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Proof`: [170549367] 
- `Proof.hyp`: [1582129081] Bağlamdaki `i`. önerme.
- `Proof.falsumE`: [2366242677] `⊥ ⊢ φ`.
- `Proof.impI`: [3931984999] `φ, Γ ⊢ ψ` ise `Γ ⊢ φ → ψ`.
- `Proof.impE`: [1061357771] `φ → ψ` ve `φ` ise `ψ`.
- `Proof.andI`: [3658691116] 
- `Proof.andE1`: [3684149015] 
- `Proof.andE2`: [3276072308] 
- `Proof.orI1`: [1747576057] `φ` ise `φ ∨ ψ`.
- `Proof.orI2`: [3585741943] `ψ` ise `φ ∨ ψ`.
- `Proof.orE`: [3538543134] `φ ∨ ψ`, `φ, Γ ⊢ χ`, `ψ, Γ ⊢ χ` ise `χ`.
- `Proof.allI`: [559766548] `↑Γ ⊢ φ` ise `Γ ⊢ ∀ φ`.
- `Proof.allE`: [3331931983] `∀ φ` ise `φ[t]`.
- `Proof.exI`: [91387409] `φ[t]` ise `∃ φ`.
- `Proof.exE`: [1733893540] `∃ φ` ve `φ, ↑Γ ⊢ ↑χ` ise `χ`.
- `Proof.refl`: [1567304393] `t = t`.
- `Proof.eqE`: [1451317691] `t = u` ve `φ[t]` ise `φ[u]`.
- `Proof.em`: [894115869] `φ ∨ ¬ φ`.
- `Theory.admissible`: [3746421213] 
- `Structure.Iso`: [3804893765] İki yapı arasında izomorfizma: ters çevrilebilir, bütün yorumları koruyan eşleme.
- `Structure.Iso.mk`: [417343216] 
- `Structure.D`: [1437261765] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `SigMorph.relMap`: [3323659712] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `check`: [3860000501] `p`, `Γ` bağlamında `φ`'nin ispatıdır.
- `infer.match_14`: [1029085789] 
- `infer`: [2821546232] İspatın bağlamdan çıkardığı önerme (geçersizse `none`).
- `Proof.brecOn`: [295508102] 
- `Proof.below`: [182045753] 
- `Proof.rec`: [4041985547] 
- `Proof.brecOn.go`: [2706797434] 
- `infer.match_20`: [231083464] 
- `Proof.casesOn`: [3404206879] 
- `infer.match_1`: [1775870579] 
- `Formula.ctorIdx`: [349303546] 
- `infer.match_4`: [3274694551] 
- `Formula.beq`: [1367984369] 
- `Formula.beq.match_1`: [3869710647] 
- `Term.beq`: [4258871897] 
- `Term.beq.match_1`: [1847837073] 
- `Term.ctorIdx`: [2167574816] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `infer.match_6`: [663720379] 
- `infer.match_8`: [4138212058] 
- `infer.match_10`: [1414614076] 
- `Formula.shift`: [393530866] Serbest değişkenleri bir artır (bağlayıcıya girerken bağlam için).
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `Term.subst`: [162456198] Paralel ikame.
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `infer.match_12`: [1393948476] 
- `instSubst`: [2122467743] Değişken 0'a `t` koy, ötekileri bir azalt.
- `instSubst.match_1`: [2214616506] 
- `infer.match_16`: [258745636] 
- `infer.match_18`: [2860817874] 
- `Formula.not`: [231130077] `¬ φ`.
- `Theory.axioms`: [2865576458] 
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.

---

## `entails_of_std`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ {S₀ S : Signature} (T : Theory S) (ι : SigMorph S₀ S) (B : Structure S₀),
  (∀ (M : Structure S), T.admissible M → Nonempty ((ι.reduct M).Iso B)) →
    ∀ (φ : Formula S),
      (∀ (fn : (f : S.Fn) → (Fin (S.fnArity f) → B.D) → B.D) (rel : (r : S.Rel) → (Fin (S.relArity r) → B.D) → Prop),
          (∀ (f : S₀.Fn) (v : Fin (S₀.fnArity f) → (ι.reduct { D := B.D, dflt := B.dflt, fn := fn, rel := rel }).D),
              (ι.reduct { D := B.D, dflt := B.dflt, fn := fn, rel := rel }).fn f v = B.fn f v) →
            (∀ (r : S₀.Rel) (v : Fin (S₀.relArity r) → (ι.reduct { D := B.D, dflt := B.dflt, fn := fn, rel := rel }).D),
                (ι.reduct { D := B.D, dflt := B.dflt, fn := fn, rel := rel }).rel r v ↔ B.rel r v) →
              (∀ (ψ : Formula S), ψ ∈ T.axioms → { D := B.D, dflt := B.dflt, fn := fn, rel := rel }.Sat ψ) →
                { D := B.D, dflt := B.dflt, fn := fn, rel := rel }.Sat φ) →
        T.Entails φ
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem entails_of_std :
  forall {S₀ S : Signature} (T : Theory S) (ι : SigMorph S₀ S) (B : Structure S₀)
    (a._@._internal._hyg.0 :
      (forall (M : Structure S),
      Theory.admissible T M → Nonempty (Structure.Iso (SigMorph.reduct ι M) B)))
    (φ : Formula S),
  (forall (fn :
        (forall (f : Signature.Fn S),
        (Fin (Signature.fnArity S f) → Structure.D B) → Structure.D B))
      (rel :
        (forall (r : Signature.Rel S),
        (Fin (Signature.relArity S r) → Structure.D B) → Sort 0)),
    (forall (f : Signature.Fn S₀)
        (v :
          Fin (Signature.fnArity S₀ f) → Structure.D
            (SigMorph.reduct ι (Structure.mk (Structure.D B) (Structure.dflt B) fn rel))),
      Eq
        (Structure.fn (SigMorph.reduct ι (Structure.mk (Structure.D B) (Structure.dflt B) fn rel))
          f v) (Structure.fn B f v)) →
    (forall (r : Signature.Rel S₀)
        (v :
          Fin (Signature.relArity S₀ r) → Structure.D
            (SigMorph.reduct ι (Structure.mk (Structure.D B) (Structure.dflt B) fn rel))),
      Iff
        (Structure.rel (SigMorph.reduct ι (Structure.mk (Structure.D B) (Structure.dflt B) fn rel))
          r v) (Structure.rel B r v)) →
    (forall (ψ : Formula S),
      Membership.mem (Theory.axioms T) ψ → Structure.Sat
        (Structure.mk (Structure.D B) (Structure.dflt B) fn rel) ψ) →
    Structure.Sat (Structure.mk (Structure.D B) (Structure.dflt B) fn rel) φ) →
  Theory.Entails T φ :=
  _
```

**Aksiyomlar:** Quot.sound, propext

**OKUMA (denetlenmedi):** Standart taşıyıcıda akıl yürütme. Arka planlı bir kuramın gerektirdiğini
göstermek için standart taşıyıcılı, standart sembolleri standart yorumlanan modellere
bakmak yeterlidir.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `Theory.admissible`: [3746421213] 
- `Structure.Iso`: [3804893765] İki yapı arasında izomorfizma: ters çevrilebilir, bütün yorumları koruyan eşleme.
- `Structure.Iso.mk`: [417343216] 
- `Structure.D`: [1437261765] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `SigMorph.relMap`: [3323659712] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.

---

## `checkTree_sound`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ (es : List SExp), checkTree es = true → Doc.HoldsTree es
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem checkTree_sound :
  forall (es : List SExp), Eq (checkTree es) Bool.true → Doc.HoldsTree es :=
  _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** Dilin sağlamlığı (ağaç). Denetimden geçen her belge ağacının bütün iddiaları
doğrudur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `SExp`: [3073815181] 
- `SExp.atom`: [1575481063] 
- `SExp.list`: [967939908] 
- `checkTree`: [2781305355] Belge ağacı denetimi (çekirdekte hesaplanabilir).
- `checkTree.match_1`: [72387886] 
- `Claim`: [2189297646] 
- `Claim.lemma`: [2452430524] 
- `Thy`: [1389576421] Belgede tanımlanmış bir kuram. `lems`: belgede daha önce ispatlanmış lemmalar.
- `Thy.mk`: [3643845920] 
- `Decls`: [3316322311] Bir sözlüğün bildirimleri: fonksiyon ve bağıntı sembolleri.
- `SymDecl`: [2749061068] Sözlükte bir sembol bildirimi.
- `SymDecl.mk`: [1229373939] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `mkSig`: [1688038800] Bildirimlerden çekirdek imzası: semboller konumlarıyla adlandırılır.
- `SymDecl.arity`: [2044778255] 
- `SymDecl.role`: [2794591844] 
- `Thy.decls`: [334432947] 
- `RProof`: [233264427] 
- `RProof.hyp`: [1993164921] 
- `RProof.ax`: [2189395407] 
- `RProof.falsumE`: [3534982120] 
- `RForm`: [2675377604] 
- `RForm.fals`: [3363398736] 
- `RForm.eq`: [791121055] 
- `RTerm`: [1661914510] 
- `RTerm.bvar`: [2599763770] 
- `RTerm.pvar`: [1884706316] 
- `RTerm.app`: [3368164085] 
- `RForm.rel`: [84336506] 
- `RForm.not`: [1225123013] 
- `RForm.imp`: [3692202615] 
- `RForm.and`: [110748553] 
- `RForm.or`: [3359165227] 
- `RForm.all`: [1414513199] 
- `RForm.ex`: [4003114692] 
- `RProof.impI`: [3934811706] 
- `RProof.impE`: [3845325626] 
- `RProof.andI`: [366441629] 
- `RProof.andE1`: [1375574360] 
- `RProof.andE2`: [3903135099] 
- `RProof.orI1`: [479907980] 
- `RProof.orI2`: [2342614922] 
- `RProof.orE`: [3776144315] 
- `RProof.allI`: [3771646107] 
- `RProof.allE`: [750372631] 
- `RProof.exI`: [2937654209] 
- `RProof.exE`: [1417888429] 
- `RProof.refl`: [1137800419] 
- `RProof.eqE`: [431284722] 
- `RProof.em`: [1504969571] 
- `Claim.analogy`: [3454005540] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `RModel`: [2033180821] Sonlu model: boyut ve sembol tabloları.
- `RModel.mk`: [3198866306] 
- `Claim.refute`: [3230209087] 
- `Claim.verdict`: [2208626721] 
- `Doc.claimsTree`: [2587901094] Ağacın iddiaları.
- `REntry`: [3124201176] 
- `REntry.sig`: [3618653341] 
- `REntry.theory`: [256492747] 
- `REntry.lemma`: [2718592224] 
- `REntry.morph`: [4279589055] 
- `REntry.analogy`: [3373879027] 
- `REntry.refute`: [1055410128] 
- `REntry.verdict`: [3153441733] 
- `decodeDoc`: [333026062] Belge: `(hakem 1)` başlığı ve girdiler.
- `decodeDoc.match_1`: [3173164757] 
- `SExp.ctorIdx`: [2990764349] 
- `SExp.casesOn`: [941673166] 
- `SExp.rec`: [2573800420] 
- `decodeEntry`: [3712296972] 
- `decodeEntry.match_1`: [1467387877] 
- `decodeSyms`: [2335141713] 
- `decodeSyms.match_3`: [512925019] 
- `decodeSyms.match_1`: [3845527704] 
- `atomNat`: [1948146438] 
- `atomStr`: [3925532187] 
- `atomStr.match_1`: [2562554843] 
- `natOf`: [2631933090] 
- `natOf.match_1`: [484743063] 
- `digitsVal`: [694345105] Ondalık rakamlar (boş olmayan). Çekirdekte hesaplanabilir.
- `digitsVal.match_1`: [2646483098] 
- `parseRole`: [1074365706] 
- `parseRole.match_1`: [2887956856] 
- `decodeAxioms`: [545211485] 
- `decodeAxioms.match_1`: [1325332987] 
- `decodeForm`: [2388413392] 
- `SExp.brecOn`: [2806796013] 
- `SExp.below`: [3563948132] 
- `SExp.below_1`: [404870531] 
- `SExp.rec_1`: [1689471608] 
- `SExp.brecOn.go`: [3730011375] 
- `decodeForm.match_1`: [3698940012] 
- `decodeTerm`: [3972666909] 
- `decodeTerm.match_1`: [3935024780] 
- `varOf`: [1482356032] 
- `varOf.match_1`: [100982862] 
- `decodeTerms.match_1`: [3089562333] 
- `decodeTerms`: [3089816077] 
- `SExp.brecOn_1`: [3975836573] 
- `SExp.brecOn_1.go`: [12761714] 
- `decodeProof`: [1632378884] 
- `decodeProof.match_1`: [180968552] 
- `decodeLam`: [3036950829] `(lam A)`: bir bağlayıcı açan formül gövdesi.
- `decodeLam.match_1`: [3050461991] 
- `decodeMaps`: [707308461] 
- `decodeMaps.match_3`: [2125358204] 
- `decodeMaps.match_1`: [144810865] 
- `decodeModel`: [397012479] 
- `decodeModel.match_1`: [3208704751] 
- `decodeTables`: [3982956021] `(fn AD DEĞER*)` ya da `(rel AD DEĞER*)` tablolarını ayır.
- `decodeTables.match_3`: [2394935814] 
- `decodeTables.match_1`: [2508995467] 
- `decodeNats`: [525760094] 
- `decodeObligs`: [1710791292] 
- `decodeObligs.match_1`: [1298299603] 
- `decodeAlt`: [1796669943] 
- `decodeAlt.match_1`: [205763390] 
- `elabEntries`: [186620017] 
- `Env`: [2408811407] 
- `Env.mk`: [2247466989] 
- `RMorph`: [2634691863] 
- `RMorph.mk`: [2316295450] 
- `elabEntries.match_3`: [325035368] 
- `Env.step`: [368347877] 
- `Env.step.match_1`: [927564257] 
- `REntry.casesOn`: [3134087968] 
- `REntry.rec`: [3645293157] 
- `Env.sigs`: [1222705087] 
- `Env.thys`: [976870444] 
- `Env.morphs`: [1904479159] 
- `assoc`: [3868243185] Adı `n` olan ilk kaydın değeri.
- `assoc.match_1`: [617368043] 
- `elabForm`: [1491084353] 
- `RForm.brecOn`: [2806964713] 
- `RForm.below`: [3774534684] 
- `RForm.rec`: [4174447585] 
- `RForm.brecOn.go`: [1562352028] 
- `elabForm.match_1`: [1253981329] 
- `RForm.casesOn`: [1837839408] 
- `elabTerm`: [4167972223] 
- `RTerm.brecOn`: [4185461122] 
- `RTerm.below`: [2986324463] 
- `RTerm.rec`: [3961874955] 
- `RTerm.below_1`: [1583189205] 
- `RTerm.rec_1`: [278840558] 
- `RTerm.brecOn.go`: [1472000957] 
- `elabTerm.match_1`: [2506280841] 
- `RTerm.casesOn`: [1178199322] 
- `lookupFn`: [2813877894] 
- `findName`: [843583788] Adı `n` olan ilk bildirimin konumu.
- `findName.match_1`: [443251984] 
- `SymDecl.name`: [352997443] 
- `elabTerms.match_1`: [3768198478] 
- `lookupRel`: [2803573005] 
- `elabTerms`: [2747421192] 
- `RTerm.brecOn_1`: [1207431103] 
- `RTerm.brecOn_1.go`: [1837957255] 
- `Formula.not`: [231130077] `¬ φ`.
- `findThy`: [503251989] 
- `findThy.match_1`: [1115952792] 
- `Thy.name`: [4092451250] 
- `Thy.sig`: [770978300] 
- `Thy.axNames`: [3587344655] 
- `Thy.axs`: [3794229443] 
- `Thy.lemNames`: [2888964172] 
- `Thy.lems`: [1923109754] 
- `RMorph.s1`: [2979346865] 
- `RMorph.s2`: [3429999379] 
- `elabMorph`: [4160793280] Eşleme: kaynak sözlüğün her sembolü için hedefte bir terim/formül (parametreler `pJ`).
- `RMorph.fns`: [616406521] 
- `RMorph.rels`: [2399529719] 
- `elabEntries.match_1`: [1193710091] 
- `checkClaim`: [420290249] 
- `checkClaim.match_1`: [1904340112] 
- `Claim.casesOn`: [3030964935] 
- `Claim.rec`: [3976005343] 
- `checkIn`: [509552963] Kuramın bağlamında bir ispatı denetle: aksiyomlar ve önceki lemmalar kullanılabilir.
- `checkIn.match_1`: [2266356281] 
- `Proof`: [170549367] 
- `Proof.hyp`: [1582129081] Bağlamdaki `i`. önerme.
- `Proof.falsumE`: [2366242677] `⊥ ⊢ φ`.
- `Proof.impI`: [3931984999] `φ, Γ ⊢ ψ` ise `Γ ⊢ φ → ψ`.
- `Proof.impE`: [1061357771] `φ → ψ` ve `φ` ise `ψ`.
- `Proof.andI`: [3658691116] 
- `Proof.andE1`: [3684149015] 
- `Proof.andE2`: [3276072308] 
- `Proof.orI1`: [1747576057] `φ` ise `φ ∨ ψ`.
- `Proof.orI2`: [3585741943] `ψ` ise `φ ∨ ψ`.
- `Proof.orE`: [3538543134] `φ ∨ ψ`, `φ, Γ ⊢ χ`, `ψ, Γ ⊢ χ` ise `χ`.
- `Proof.allI`: [559766548] `↑Γ ⊢ φ` ise `Γ ⊢ ∀ φ`.
- `Proof.allE`: [3331931983] `∀ φ` ise `φ[t]`.
- `Proof.exI`: [91387409] `φ[t]` ise `∃ φ`.
- `Proof.exE`: [1733893540] `∃ φ` ve `φ, ↑Γ ⊢ ↑χ` ise `χ`.
- `Proof.refl`: [1567304393] `t = t`.
- `Proof.eqE`: [1451317691] `t = u` ve `φ[t]` ise `φ[u]`.
- `Proof.em`: [894115869] `φ ∨ ¬ φ`.
- `elabProof`: [1974041590] İspat çevirisi. `names`: kuramın aksiyom ve lemma adları (bağlamın küresel kısmı).
- `RProof.brecOn`: [2404765738] 
- `RProof.below`: [3279663114] 
- `RProof.rec`: [1791891314] 
- `RProof.brecOn.go`: [2642063031] 
- `elabProof.match_1`: [3689151911] 
- `RProof.casesOn`: [823818495] 
- `idxOfStr`: [1781923072] Adın listedeki konumu.
- `idxOfStr.match_1`: [2225950912] 
- `check`: [3860000501] `p`, `Γ` bağlamında `φ`'nin ispatıdır.
- `infer.match_14`: [1029085789] 
- `infer`: [2821546232] İspatın bağlamdan çıkardığı önerme (geçersizse `none`).
- `Proof.brecOn`: [295508102] 
- `Proof.below`: [182045753] 
- `Proof.rec`: [4041985547] 
- `Proof.brecOn.go`: [2706797434] 
- `infer.match_20`: [231083464] 
- `Proof.casesOn`: [3404206879] 
- `infer.match_1`: [1775870579] 
- `Formula.ctorIdx`: [349303546] 
- `Formula.casesOn`: [824629045] 
- `Formula.rec`: [3232664870] 
- `infer.match_4`: [3274694551] 
- `Formula.beq`: [1367984369] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.beq.match_1`: [3869710647] 
- `Term.beq`: [4258871897] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.beq.match_1`: [1847837073] 
- `Term.casesOn`: [3327370182] 
- `Term.ctorIdx`: [2167574816] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `infer.match_6`: [663720379] 
- `infer.match_8`: [4138212058] 
- `infer.match_10`: [1414614076] 
- `Formula.shift`: [393530866] Serbest değişkenleri bir artır (bağlayıcıya girerken bağlam için).
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `Term.subst`: [162456198] Paralel ikame.
- `Term.onlySyms.match_1`: [264759630] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `liftSubst.match_1`: [1420932622] 
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `infer.match_12`: [1393948476] 
- `instSubst`: [2122467743] Değişken 0'a `t` koy, ötekileri bir azalt.
- `instSubst.match_1`: [2214616506] 
- `infer.match_16`: [258745636] 
- `infer.match_18`: [2860817874] 
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `checkModel`: [2203415650] 
- `checkModel.match_1`: [553740502] 
- `FinStructure`: [2240455362] Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar.
- `FinStructure.mk`: [3184878320] 
- `elabModel`: [3181307502] 
- `elabModel.match_1`: [1251572971] 
- `RModel.size`: [3589570862] 
- `tableFn`: [2471330444] 
- `encodeIdx`: [1503949429] Argüman vektörünün tablodaki konumu: `a0 + B·a1 + B²·a2 + …`.
- `encodeIdx.match_1`: [1498084951] 
- `RModel.fns`: [3892410573] 
- `tableRel`: [1090760840] 
- `RModel.rels`: [880016012] 
- `FinStructure.checkTheory`: [2600167987] Sonlu yapı kuramın her aksiyomunu (kapalı olarak) doğrular.
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Theory.axioms`: [2865576458] 
- `Formula.closed`: [3593464037] Kapalı formül (cümle).
- `Formula.varsBelow`: [2276081188] Formüldeki her serbest değişken `< k`.
- `Formula.varsBelow.match_1`: [3890479493] 
- `Term.varsBelow`: [989945896] Terimdeki her değişken `< k`.
- `Term.varsBelow.match_1`: [2471661240] 
- `FinStructure.evalB`: [2539266348] Formülün sonlu yapıda hesaplanması.
- `FinStructure.n`: [1325356739] 
- `FinStructure.evalB.match_1`: [1169364348] 
- `Structure.D`: [1437261765] 
- `FinStructure.toStructure`: [3009531569] Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır.
- `FinStructure.fn`: [508190427] 
- `FinStructure.rel`: [2799040893] 
- `Term.eval`: [704183430] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `anyFin`: [166542815] Sonlu ailede `||`.
- `Thy.theory`: [3100761276] Kuramın çekirdek karşılığı: yalnızca aksiyomlar (lemmalar anlamın parçası değildir).
- `FinStructure.refutes`: [3141469118] Sonlu yapıda kapalı bir formül yanlıştır.
- `FinStructure.reinterpB`: [3876393088] Tanık dünyanın normatif sembollerini değiştirerek elde edilen sonlu alternatif.
- `Signature.fnRole`: [3533609429] 
- `instDecidableEqRole`: [4090796487] 
- `Role.ctorIdx`: [3717224365] 
- `Role.casesOn`: [2538655878] 
- `Role.rec`: [3824428781] 
- `Role.ofNat`: [1323357135] 
- `Role.ofNat_ctorIdx`: [1788762641] 
- `Signature.relRole`: [1842763906] 
- `altFn`: [2776466343] Alternatif dünyanın tabloları (yalnızca normatif semboller kullanılır).
- `altFn.match_1`: [3935349920] 
- `altRel`: [3069200494] 
- `Doc.HoldsTree`: [1741281594] **Belge ağacının anlamı**: çevrilir ve bütün iddiaları doğrudur.
- `Claim.Holds`: [3676168205] Bir iddianın anlamı. Sertifikalar (ispat, model) bu anlama girmez.
- `Claim.Holds.match_1`: [1390319471] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Structure.rel`: [855465701] 
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `Analogy.σ`: [2934450448] 
- `Refutation`: [618331221] Metafor sertifikası. `glossary`, önerilen sözlüktür. `pf`/`pr` sözlüğün bağlayıcı
- `Refutation.mk`: [1987474353] 
- `Formula.onlySyms`: [2677709904] Formüldeki her sembol `pf`/`pr`'yi sağlar.
- `Term.onlySyms`: [1893188890] Terimdeki her fonksiyon sembolü `pf`'yi sağlar.
- `Formula.mentionsFn`: [1541366290] 
- `Formula.mentionsFn.match_1`: [1086497885] 
- `Term.mentionsFn`: [3784459156] 
- `Term.mentionsFn.match_1`: [211956374] 
- `Formula.mentionsRel`: [231503431] 
- `PolicyVerdict`: [1124954806] Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
- `PolicyVerdict.mk`: [3985630505] 
- `Structure.reinterp`: [683133002] Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve

---

## `checkDoc_sound`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
∀ (s : String), checkDoc s = true → Doc.Holds s
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem checkDoc_sound : forall (s : String), Eq (checkDoc s) Bool.true → Doc.Holds s := _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** Dilin sağlamlığı (metin). Denetimden geçen her belge metninin bütün iddiaları
doğrudur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `checkDoc`: [705372209] Belge metni denetimi.
- `checkDoc.match_1`: [789429641] 
- `SExp`: [3073815181] 
- `SExp.atom`: [1575481063] 
- `SExp.list`: [967939908] 
- `readSExps`: [1421158076] 
- `parseToks`: [3065299083] Yığınlı ayrıştırıcı. Yığının her katı, açık bir listenin (ters) öğeleridir.
- `Tok`: [2865026334] 
- `Tok.lp`: [1787908831] 
- `Tok.rp`: [2689139325] 
- `Tok.atom`: [3607363451] 
- `parseToks.match_1`: [174640003] 
- `Tok.casesOn`: [1716003121] 
- `Tok.rec`: [667380414] 
- `tokenize`: [719102856] 
- `tokenizeAux`: [2644575496] Karakterlerden simgeler. `buf`: biriken atom (ters), `cmt`: yorum içinde mi.
- `tokenizeAux.match_1`: [1691736858] 
- `flushTok`: [1371742722] 
- `isSpace`: [2576717197] 
- `checkTree`: [2781305355] Belge ağacı denetimi (çekirdekte hesaplanabilir).
- `checkTree.match_1`: [72387886] 
- `Claim`: [2189297646] 
- `Claim.lemma`: [2452430524] 
- `Thy`: [1389576421] Belgede tanımlanmış bir kuram. `lems`: belgede daha önce ispatlanmış lemmalar.
- `Thy.mk`: [3643845920] 
- `Decls`: [3316322311] Bir sözlüğün bildirimleri: fonksiyon ve bağıntı sembolleri.
- `SymDecl`: [2749061068] Sözlükte bir sembol bildirimi.
- `SymDecl.mk`: [1229373939] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `mkSig`: [1688038800] Bildirimlerden çekirdek imzası: semboller konumlarıyla adlandırılır.
- `SymDecl.arity`: [2044778255] 
- `SymDecl.role`: [2794591844] 
- `Thy.decls`: [334432947] 
- `RProof`: [233264427] 
- `RProof.hyp`: [1993164921] 
- `RProof.ax`: [2189395407] 
- `RProof.falsumE`: [3534982120] 
- `RForm`: [2675377604] 
- `RForm.fals`: [3363398736] 
- `RForm.eq`: [791121055] 
- `RTerm`: [1661914510] 
- `RTerm.bvar`: [2599763770] 
- `RTerm.pvar`: [1884706316] 
- `RTerm.app`: [3368164085] 
- `RForm.rel`: [84336506] 
- `RForm.not`: [1225123013] 
- `RForm.imp`: [3692202615] 
- `RForm.and`: [110748553] 
- `RForm.or`: [3359165227] 
- `RForm.all`: [1414513199] 
- `RForm.ex`: [4003114692] 
- `RProof.impI`: [3934811706] 
- `RProof.impE`: [3845325626] 
- `RProof.andI`: [366441629] 
- `RProof.andE1`: [1375574360] 
- `RProof.andE2`: [3903135099] 
- `RProof.orI1`: [479907980] 
- `RProof.orI2`: [2342614922] 
- `RProof.orE`: [3776144315] 
- `RProof.allI`: [3771646107] 
- `RProof.allE`: [750372631] 
- `RProof.exI`: [2937654209] 
- `RProof.exE`: [1417888429] 
- `RProof.refl`: [1137800419] 
- `RProof.eqE`: [431284722] 
- `RProof.em`: [1504969571] 
- `Claim.analogy`: [3454005540] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `RModel`: [2033180821] Sonlu model: boyut ve sembol tabloları.
- `RModel.mk`: [3198866306] 
- `Claim.refute`: [3230209087] 
- `Claim.verdict`: [2208626721] 
- `Doc.claimsTree`: [2587901094] Ağacın iddiaları.
- `REntry`: [3124201176] 
- `REntry.sig`: [3618653341] 
- `REntry.theory`: [256492747] 
- `REntry.lemma`: [2718592224] 
- `REntry.morph`: [4279589055] 
- `REntry.analogy`: [3373879027] 
- `REntry.refute`: [1055410128] 
- `REntry.verdict`: [3153441733] 
- `decodeDoc`: [333026062] Belge: `(hakem 1)` başlığı ve girdiler.
- `decodeDoc.match_1`: [3173164757] 
- `SExp.ctorIdx`: [2990764349] 
- `SExp.casesOn`: [941673166] 
- `SExp.rec`: [2573800420] 
- `decodeEntry`: [3712296972] 
- `decodeEntry.match_1`: [1467387877] 
- `decodeSyms`: [2335141713] 
- `decodeSyms.match_3`: [512925019] 
- `decodeSyms.match_1`: [3845527704] 
- `atomNat`: [1948146438] 
- `atomStr`: [3925532187] 
- `atomStr.match_1`: [2562554843] 
- `natOf`: [2631933090] 
- `natOf.match_1`: [484743063] 
- `digitsVal`: [694345105] Ondalık rakamlar (boş olmayan). Çekirdekte hesaplanabilir.
- `digitsVal.match_1`: [2646483098] 
- `parseRole`: [1074365706] 
- `parseRole.match_1`: [2887956856] 
- `decodeAxioms`: [545211485] 
- `decodeAxioms.match_1`: [1325332987] 
- `decodeForm`: [2388413392] 
- `SExp.brecOn`: [2806796013] 
- `SExp.below`: [3563948132] 
- `SExp.below_1`: [404870531] 
- `SExp.rec_1`: [1689471608] 
- `SExp.brecOn.go`: [3730011375] 
- `decodeForm.match_1`: [3698940012] 
- `decodeTerm`: [3972666909] 
- `decodeTerm.match_1`: [3935024780] 
- `varOf`: [1482356032] 
- `varOf.match_1`: [100982862] 
- `decodeTerms.match_1`: [3089562333] 
- `decodeTerms`: [3089816077] 
- `SExp.brecOn_1`: [3975836573] 
- `SExp.brecOn_1.go`: [12761714] 
- `decodeProof`: [1632378884] 
- `decodeProof.match_1`: [180968552] 
- `decodeLam`: [3036950829] `(lam A)`: bir bağlayıcı açan formül gövdesi.
- `decodeLam.match_1`: [3050461991] 
- `decodeMaps`: [707308461] 
- `decodeMaps.match_3`: [2125358204] 
- `decodeMaps.match_1`: [144810865] 
- `decodeModel`: [397012479] 
- `decodeModel.match_1`: [3208704751] 
- `decodeTables`: [3982956021] `(fn AD DEĞER*)` ya da `(rel AD DEĞER*)` tablolarını ayır.
- `decodeTables.match_3`: [2394935814] 
- `decodeTables.match_1`: [2508995467] 
- `decodeNats`: [525760094] 
- `decodeObligs`: [1710791292] 
- `decodeObligs.match_1`: [1298299603] 
- `decodeAlt`: [1796669943] 
- `decodeAlt.match_1`: [205763390] 
- `elabEntries`: [186620017] 
- `Env`: [2408811407] 
- `Env.mk`: [2247466989] 
- `RMorph`: [2634691863] 
- `RMorph.mk`: [2316295450] 
- `elabEntries.match_3`: [325035368] 
- `Env.step`: [368347877] 
- `Env.step.match_1`: [927564257] 
- `REntry.casesOn`: [3134087968] 
- `REntry.rec`: [3645293157] 
- `Env.sigs`: [1222705087] 
- `Env.thys`: [976870444] 
- `Env.morphs`: [1904479159] 
- `assoc`: [3868243185] Adı `n` olan ilk kaydın değeri.
- `assoc.match_1`: [617368043] 
- `elabForm`: [1491084353] 
- `RForm.brecOn`: [2806964713] 
- `RForm.below`: [3774534684] 
- `RForm.rec`: [4174447585] 
- `RForm.brecOn.go`: [1562352028] 
- `elabForm.match_1`: [1253981329] 
- `RForm.casesOn`: [1837839408] 
- `elabTerm`: [4167972223] 
- `RTerm.brecOn`: [4185461122] 
- `RTerm.below`: [2986324463] 
- `RTerm.rec`: [3961874955] 
- `RTerm.below_1`: [1583189205] 
- `RTerm.rec_1`: [278840558] 
- `RTerm.brecOn.go`: [1472000957] 
- `elabTerm.match_1`: [2506280841] 
- `RTerm.casesOn`: [1178199322] 
- `lookupFn`: [2813877894] 
- `findName`: [843583788] Adı `n` olan ilk bildirimin konumu.
- `findName.match_1`: [443251984] 
- `SymDecl.name`: [352997443] 
- `elabTerms.match_1`: [3768198478] 
- `lookupRel`: [2803573005] 
- `elabTerms`: [2747421192] 
- `RTerm.brecOn_1`: [1207431103] 
- `RTerm.brecOn_1.go`: [1837957255] 
- `Formula.not`: [231130077] `¬ φ`.
- `findThy`: [503251989] 
- `findThy.match_1`: [1115952792] 
- `Thy.name`: [4092451250] 
- `Thy.sig`: [770978300] 
- `Thy.axNames`: [3587344655] 
- `Thy.axs`: [3794229443] 
- `Thy.lemNames`: [2888964172] 
- `Thy.lems`: [1923109754] 
- `RMorph.s1`: [2979346865] 
- `RMorph.s2`: [3429999379] 
- `elabMorph`: [4160793280] Eşleme: kaynak sözlüğün her sembolü için hedefte bir terim/formül (parametreler `pJ`).
- `RMorph.fns`: [616406521] 
- `RMorph.rels`: [2399529719] 
- `elabEntries.match_1`: [1193710091] 
- `checkClaim`: [420290249] 
- `checkClaim.match_1`: [1904340112] 
- `Claim.casesOn`: [3030964935] 
- `Claim.rec`: [3976005343] 
- `checkIn`: [509552963] Kuramın bağlamında bir ispatı denetle: aksiyomlar ve önceki lemmalar kullanılabilir.
- `checkIn.match_1`: [2266356281] 
- `Proof`: [170549367] 
- `Proof.hyp`: [1582129081] Bağlamdaki `i`. önerme.
- `Proof.falsumE`: [2366242677] `⊥ ⊢ φ`.
- `Proof.impI`: [3931984999] `φ, Γ ⊢ ψ` ise `Γ ⊢ φ → ψ`.
- `Proof.impE`: [1061357771] `φ → ψ` ve `φ` ise `ψ`.
- `Proof.andI`: [3658691116] 
- `Proof.andE1`: [3684149015] 
- `Proof.andE2`: [3276072308] 
- `Proof.orI1`: [1747576057] `φ` ise `φ ∨ ψ`.
- `Proof.orI2`: [3585741943] `ψ` ise `φ ∨ ψ`.
- `Proof.orE`: [3538543134] `φ ∨ ψ`, `φ, Γ ⊢ χ`, `ψ, Γ ⊢ χ` ise `χ`.
- `Proof.allI`: [559766548] `↑Γ ⊢ φ` ise `Γ ⊢ ∀ φ`.
- `Proof.allE`: [3331931983] `∀ φ` ise `φ[t]`.
- `Proof.exI`: [91387409] `φ[t]` ise `∃ φ`.
- `Proof.exE`: [1733893540] `∃ φ` ve `φ, ↑Γ ⊢ ↑χ` ise `χ`.
- `Proof.refl`: [1567304393] `t = t`.
- `Proof.eqE`: [1451317691] `t = u` ve `φ[t]` ise `φ[u]`.
- `Proof.em`: [894115869] `φ ∨ ¬ φ`.
- `elabProof`: [1974041590] İspat çevirisi. `names`: kuramın aksiyom ve lemma adları (bağlamın küresel kısmı).
- `RProof.brecOn`: [2404765738] 
- `RProof.below`: [3279663114] 
- `RProof.rec`: [1791891314] 
- `RProof.brecOn.go`: [2642063031] 
- `elabProof.match_1`: [3689151911] 
- `RProof.casesOn`: [823818495] 
- `idxOfStr`: [1781923072] Adın listedeki konumu.
- `idxOfStr.match_1`: [2225950912] 
- `check`: [3860000501] `p`, `Γ` bağlamında `φ`'nin ispatıdır.
- `infer.match_14`: [1029085789] 
- `infer`: [2821546232] İspatın bağlamdan çıkardığı önerme (geçersizse `none`).
- `Proof.brecOn`: [295508102] 
- `Proof.below`: [182045753] 
- `Proof.rec`: [4041985547] 
- `Proof.brecOn.go`: [2706797434] 
- `infer.match_20`: [231083464] 
- `Proof.casesOn`: [3404206879] 
- `infer.match_1`: [1775870579] 
- `Formula.ctorIdx`: [349303546] 
- `Formula.casesOn`: [824629045] 
- `Formula.rec`: [3232664870] 
- `infer.match_4`: [3274694551] 
- `Formula.beq`: [1367984369] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.beq.match_1`: [3869710647] 
- `Term.beq`: [4258871897] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.beq.match_1`: [1847837073] 
- `Term.casesOn`: [3327370182] 
- `Term.ctorIdx`: [2167574816] 
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `infer.match_6`: [663720379] 
- `infer.match_8`: [4138212058] 
- `infer.match_10`: [1414614076] 
- `Formula.shift`: [393530866] Serbest değişkenleri bir artır (bağlayıcıya girerken bağlam için).
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `Term.subst`: [162456198] Paralel ikame.
- `Term.onlySyms.match_1`: [264759630] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `liftSubst.match_1`: [1420932622] 
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `infer.match_12`: [1393948476] 
- `instSubst`: [2122467743] Değişken 0'a `t` koy, ötekileri bir azalt.
- `instSubst.match_1`: [2214616506] 
- `infer.match_16`: [258745636] 
- `infer.match_18`: [2860817874] 
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `checkModel`: [2203415650] 
- `checkModel.match_1`: [553740502] 
- `FinStructure`: [2240455362] Sonlu yapı: taşıyıcı `Fin (n+1)`, fonksiyonlar ve `Bool` değerli bağıntılar.
- `FinStructure.mk`: [3184878320] 
- `elabModel`: [3181307502] 
- `elabModel.match_1`: [1251572971] 
- `RModel.size`: [3589570862] 
- `tableFn`: [2471330444] 
- `encodeIdx`: [1503949429] Argüman vektörünün tablodaki konumu: `a0 + B·a1 + B²·a2 + …`.
- `encodeIdx.match_1`: [1498084951] 
- `RModel.fns`: [3892410573] 
- `tableRel`: [1090760840] 
- `RModel.rels`: [880016012] 
- `FinStructure.checkTheory`: [2600167987] Sonlu yapı kuramın her aksiyomunu (kapalı olarak) doğrular.
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Theory.axioms`: [2865576458] 
- `Formula.closed`: [3593464037] Kapalı formül (cümle).
- `Formula.varsBelow`: [2276081188] Formüldeki her serbest değişken `< k`.
- `Formula.varsBelow.match_1`: [3890479493] 
- `Term.varsBelow`: [989945896] Terimdeki her değişken `< k`.
- `Term.varsBelow.match_1`: [2471661240] 
- `FinStructure.evalB`: [2539266348] Formülün sonlu yapıda hesaplanması.
- `FinStructure.n`: [1325356739] 
- `FinStructure.evalB.match_1`: [1169364348] 
- `Structure.D`: [1437261765] 
- `FinStructure.toStructure`: [3009531569] Sonlu yapının anlamsal karşılığı. Seçkin öğe 0'dır.
- `FinStructure.fn`: [508190427] 
- `FinStructure.rel`: [2799040893] 
- `Term.eval`: [704183430] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `anyFin`: [166542815] Sonlu ailede `||`.
- `Thy.theory`: [3100761276] Kuramın çekirdek karşılığı: yalnızca aksiyomlar (lemmalar anlamın parçası değildir).
- `FinStructure.refutes`: [3141469118] Sonlu yapıda kapalı bir formül yanlıştır.
- `FinStructure.reinterpB`: [3876393088] Tanık dünyanın normatif sembollerini değiştirerek elde edilen sonlu alternatif.
- `Signature.fnRole`: [3533609429] 
- `instDecidableEqRole`: [4090796487] 
- `Role.ctorIdx`: [3717224365] 
- `Role.casesOn`: [2538655878] 
- `Role.rec`: [3824428781] 
- `Role.ofNat`: [1323357135] 
- `Role.ofNat_ctorIdx`: [1788762641] 
- `Signature.relRole`: [1842763906] 
- `altFn`: [2776466343] Alternatif dünyanın tabloları (yalnızca normatif semboller kullanılır).
- `altFn.match_1`: [3935349920] 
- `altRel`: [3069200494] 
- `Doc.Holds`: [3009099504] **Belge metninin anlamı**: okunur ve ağacı doğrudur.
- `Doc.HoldsTree`: [1741281594] **Belge ağacının anlamı**: çevrilir ve bütün iddiaları doğrudur.
- `Claim.Holds`: [3676168205] Bir iddianın anlamı. Sertifikalar (ispat, model) bu anlama girmez.
- `Claim.Holds.match_1`: [1390319471] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Formula.eval`: [1446459881] 
- `Formula.eval.match_1`: [650301004] 
- `Structure.rel`: [855465701] 
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `Analogy.σ`: [2934450448] 
- `Refutation`: [618331221] Metafor sertifikası. `glossary`, önerilen sözlüktür. `pf`/`pr` sözlüğün bağlayıcı
- `Refutation.mk`: [1987474353] 
- `Formula.onlySyms`: [2677709904] Formüldeki her sembol `pf`/`pr`'yi sağlar.
- `Term.onlySyms`: [1893188890] Terimdeki her fonksiyon sembolü `pf`'yi sağlar.
- `Formula.mentionsFn`: [1541366290] 
- `Formula.mentionsFn.match_1`: [1086497885] 
- `Term.mentionsFn`: [3784459156] 
- `Term.mentionsFn.match_1`: [211956374] 
- `Formula.mentionsRel`: [231503431] 
- `PolicyVerdict`: [1124954806] Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
- `PolicyVerdict.mk`: [3985630505] 
- `Structure.reinterp`: [683133002] Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve

---

## `korunum_holds`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Doc.HoldsTree korunum_tree
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem korunum_holds : Doc.HoldsTree korunum_tree := _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** `corpus/korunum.hkm` belgesinin bütün iddiaları doğrudur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Doc.HoldsTree`: [1741281594] **Belge ağacının anlamı**: çevrilir ve bütün iddiaları doğrudur.
- `SExp`: [3073815181] 
- `SExp.atom`: [1575481063] 
- `SExp.list`: [967939908] 
- `Claim`: [2189297646] 
- `Claim.lemma`: [2452430524] 
- `Thy`: [1389576421] Belgede tanımlanmış bir kuram. `lems`: belgede daha önce ispatlanmış lemmalar.
- `Thy.mk`: [3643845920] 
- `Decls`: [3316322311] Bir sözlüğün bildirimleri: fonksiyon ve bağıntı sembolleri.
- `SymDecl`: [2749061068] Sözlükte bir sembol bildirimi.
- `SymDecl.mk`: [1229373939] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `mkSig`: [1688038800] Bildirimlerden çekirdek imzası: semboller konumlarıyla adlandırılır.
- `SymDecl.arity`: [2044778255] 
- `SymDecl.role`: [2794591844] 
- `Thy.decls`: [334432947] 
- `RProof`: [233264427] 
- `RProof.hyp`: [1993164921] 
- `RProof.ax`: [2189395407] 
- `RProof.falsumE`: [3534982120] 
- `RForm`: [2675377604] 
- `RForm.fals`: [3363398736] 
- `RForm.eq`: [791121055] 
- `RTerm`: [1661914510] 
- `RTerm.bvar`: [2599763770] 
- `RTerm.pvar`: [1884706316] 
- `RTerm.app`: [3368164085] 
- `RForm.rel`: [84336506] 
- `RForm.not`: [1225123013] 
- `RForm.imp`: [3692202615] 
- `RForm.and`: [110748553] 
- `RForm.or`: [3359165227] 
- `RForm.all`: [1414513199] 
- `RForm.ex`: [4003114692] 
- `RProof.impI`: [3934811706] 
- `RProof.impE`: [3845325626] 
- `RProof.andI`: [366441629] 
- `RProof.andE1`: [1375574360] 
- `RProof.andE2`: [3903135099] 
- `RProof.orI1`: [479907980] 
- `RProof.orI2`: [2342614922] 
- `RProof.orE`: [3776144315] 
- `RProof.allI`: [3771646107] 
- `RProof.allE`: [750372631] 
- `RProof.exI`: [2937654209] 
- `RProof.exE`: [1417888429] 
- `RProof.refl`: [1137800419] 
- `RProof.eqE`: [431284722] 
- `RProof.em`: [1504969571] 
- `Claim.analogy`: [3454005540] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `RModel`: [2033180821] Sonlu model: boyut ve sembol tabloları.
- `RModel.mk`: [3198866306] 
- `Claim.refute`: [3230209087] 
- `Claim.verdict`: [2208626721] 
- `Doc.claimsTree`: [2587901094] Ağacın iddiaları.
- `REntry`: [3124201176] 
- `REntry.sig`: [3618653341] 
- `REntry.theory`: [256492747] 
- `REntry.lemma`: [2718592224] 
- `REntry.morph`: [4279589055] 
- `REntry.analogy`: [3373879027] 
- `REntry.refute`: [1055410128] 
- `REntry.verdict`: [3153441733] 
- `decodeDoc`: [333026062] Belge: `(hakem 1)` başlığı ve girdiler.
- `decodeDoc.match_1`: [3173164757] 
- `SExp.ctorIdx`: [2990764349] 
- `SExp.casesOn`: [941673166] 
- `SExp.rec`: [2573800420] 
- `decodeEntry`: [3712296972] 
- `decodeEntry.match_1`: [1467387877] 
- `decodeSyms`: [2335141713] 
- `decodeSyms.match_3`: [512925019] 
- `decodeSyms.match_1`: [3845527704] 
- `atomNat`: [1948146438] 
- `atomStr`: [3925532187] 
- `atomStr.match_1`: [2562554843] 
- `natOf`: [2631933090] 
- `natOf.match_1`: [484743063] 
- `digitsVal`: [694345105] Ondalık rakamlar (boş olmayan). Çekirdekte hesaplanabilir.
- `digitsVal.match_1`: [2646483098] 
- `parseRole`: [1074365706] 
- `parseRole.match_1`: [2887956856] 
- `decodeAxioms`: [545211485] 
- `decodeAxioms.match_1`: [1325332987] 
- `decodeForm`: [2388413392] 
- `SExp.brecOn`: [2806796013] 
- `SExp.below`: [3563948132] 
- `SExp.below_1`: [404870531] 
- `SExp.rec_1`: [1689471608] 
- `SExp.brecOn.go`: [3730011375] 
- `decodeForm.match_1`: [3698940012] 
- `decodeTerm`: [3972666909] 
- `decodeTerm.match_1`: [3935024780] 
- `varOf`: [1482356032] 
- `varOf.match_1`: [100982862] 
- `decodeTerms.match_1`: [3089562333] 
- `decodeTerms`: [3089816077] 
- `SExp.brecOn_1`: [3975836573] 
- `SExp.brecOn_1.go`: [12761714] 
- `decodeProof`: [1632378884] 
- `decodeProof.match_1`: [180968552] 
- `decodeLam`: [3036950829] `(lam A)`: bir bağlayıcı açan formül gövdesi.
- `decodeLam.match_1`: [3050461991] 
- `decodeMaps`: [707308461] 
- `decodeMaps.match_3`: [2125358204] 
- `decodeMaps.match_1`: [144810865] 
- `decodeModel`: [397012479] 
- `decodeModel.match_1`: [3208704751] 
- `decodeTables`: [3982956021] `(fn AD DEĞER*)` ya da `(rel AD DEĞER*)` tablolarını ayır.
- `decodeTables.match_3`: [2394935814] 
- `decodeTables.match_1`: [2508995467] 
- `decodeNats`: [525760094] 
- `decodeObligs`: [1710791292] 
- `decodeObligs.match_1`: [1298299603] 
- `decodeAlt`: [1796669943] 
- `decodeAlt.match_1`: [205763390] 
- `elabEntries`: [186620017] 
- `Env`: [2408811407] 
- `Env.mk`: [2247466989] 
- `RMorph`: [2634691863] 
- `RMorph.mk`: [2316295450] 
- `elabEntries.match_3`: [325035368] 
- `Env.step`: [368347877] 
- `Env.step.match_1`: [927564257] 
- `REntry.casesOn`: [3134087968] 
- `REntry.rec`: [3645293157] 
- `Env.sigs`: [1222705087] 
- `Env.thys`: [976870444] 
- `Env.morphs`: [1904479159] 
- `assoc`: [3868243185] Adı `n` olan ilk kaydın değeri.
- `assoc.match_1`: [617368043] 
- `elabForm`: [1491084353] 
- `RForm.brecOn`: [2806964713] 
- `RForm.below`: [3774534684] 
- `RForm.rec`: [4174447585] 
- `RForm.brecOn.go`: [1562352028] 
- `elabForm.match_1`: [1253981329] 
- `RForm.casesOn`: [1837839408] 
- `elabTerm`: [4167972223] 
- `RTerm.brecOn`: [4185461122] 
- `RTerm.below`: [2986324463] 
- `RTerm.rec`: [3961874955] 
- `RTerm.below_1`: [1583189205] 
- `RTerm.rec_1`: [278840558] 
- `RTerm.brecOn.go`: [1472000957] 
- `elabTerm.match_1`: [2506280841] 
- `RTerm.casesOn`: [1178199322] 
- `lookupFn`: [2813877894] 
- `findName`: [843583788] Adı `n` olan ilk bildirimin konumu.
- `findName.match_1`: [443251984] 
- `SymDecl.name`: [352997443] 
- `elabTerms.match_1`: [3768198478] 
- `lookupRel`: [2803573005] 
- `elabTerms`: [2747421192] 
- `RTerm.brecOn_1`: [1207431103] 
- `RTerm.brecOn_1.go`: [1837957255] 
- `Formula.not`: [231130077] `¬ φ`.
- `findThy`: [503251989] 
- `findThy.match_1`: [1115952792] 
- `Thy.name`: [4092451250] 
- `Thy.sig`: [770978300] 
- `Thy.axNames`: [3587344655] 
- `Thy.axs`: [3794229443] 
- `Thy.lemNames`: [2888964172] 
- `Thy.lems`: [1923109754] 
- `RMorph.s1`: [2979346865] 
- `RMorph.s2`: [3429999379] 
- `elabMorph`: [4160793280] Eşleme: kaynak sözlüğün her sembolü için hedefte bir terim/formül (parametreler `pJ`).
- `RMorph.fns`: [616406521] 
- `RMorph.rels`: [2399529719] 
- `elabEntries.match_1`: [1193710091] 
- `Claim.Holds`: [3676168205] Bir iddianın anlamı. Sertifikalar (ispat, model) bu anlama girmez.
- `Claim.Holds.match_1`: [1390319471] 
- `Claim.casesOn`: [3030964935] 
- `Claim.rec`: [3976005343] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `Thy.theory`: [3100761276] Kuramın çekirdek karşılığı: yalnızca aksiyomlar (lemmalar anlamın parçası değildir).
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `Analogy.σ`: [2934450448] 
- `Refutation`: [618331221] Metafor sertifikası. `glossary`, önerilen sözlüktür. `pf`/`pr` sözlüğün bağlayıcı
- `Refutation.mk`: [1987474353] 
- `Formula.onlySyms`: [2677709904] Formüldeki her sembol `pf`/`pr`'yi sağlar.
- `Term.onlySyms`: [1893188890] Terimdeki her fonksiyon sembolü `pf`'yi sağlar.
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `Formula.mentionsFn`: [1541366290] 
- `Formula.mentionsFn.match_1`: [1086497885] 
- `Term.mentionsFn`: [3784459156] 
- `Term.mentionsFn.match_1`: [211956374] 
- `anyFin`: [166542815] Sonlu ailede `||`.
- `Formula.mentionsRel`: [231503431] 
- `PolicyVerdict`: [1124954806] Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
- `PolicyVerdict.mk`: [3985630505] 
- `Structure.reinterp`: [683133002] Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve
- `Signature.fnRole`: [3533609429] 
- `instDecidableEqRole`: [4090796487] 
- `Role.ctorIdx`: [3717224365] 
- `Role.casesOn`: [2538655878] 
- `Role.rec`: [3824428781] 
- `Role.ofNat`: [1323357135] 
- `Role.ofNat_ctorIdx`: [1788762641] 
- `Signature.relRole`: [1842763906] 
- `korunum_tree`: [1488642363] `corpus/korunum.hkm` belgesinin ağacı (okuyucunun çıktısı).

---

## `politika_holds`

**DURUM: BİÇİMSEL KABUL**

**İfade** (güvenilen ortamda basıldı):

```lean
Doc.HoldsTree politika_tree
```

**İfade** (bağımsız çekirdeğin yazıcısıyla, gösterimsiz):

```lean
theorem politika_holds : Doc.HoldsTree politika_tree := _
```

**Aksiyomlar:** propext, Quot.sound, Classical.choice

**OKUMA (denetlenmedi):** `corpus/politika.hkm` belgesinin bütün iddiaları doğrudur.

**Anlam tabanı** (insanlarca okunması gereken tanımlar; [parmak izi]):

- `Doc.HoldsTree`: [1741281594] **Belge ağacının anlamı**: çevrilir ve bütün iddiaları doğrudur.
- `SExp`: [3073815181] 
- `SExp.atom`: [1575481063] 
- `SExp.list`: [967939908] 
- `Claim`: [2189297646] 
- `Claim.lemma`: [2452430524] 
- `Thy`: [1389576421] Belgede tanımlanmış bir kuram. `lems`: belgede daha önce ispatlanmış lemmalar.
- `Thy.mk`: [3643845920] 
- `Decls`: [3316322311] Bir sözlüğün bildirimleri: fonksiyon ve bağıntı sembolleri.
- `SymDecl`: [2749061068] Sözlükte bir sembol bildirimi.
- `SymDecl.mk`: [1229373939] 
- `Role`: [797138619] Sembol rolü. `tanim`: yapısal/tanımsal sözcük. `ampirik`: değeri ölçümle belirlenir.
- `Role.tanim`: [2855634760] 
- `Role.ampirik`: [66000930] 
- `Role.normatif`: [4225390613] 
- `Formula`: [395866084] Formül. `all`/`ex` değişken 0'ı bağlar.
- `Signature`: [803959591] Sözlük: fonksiyon ve bağıntı sembolleri, ikilikleri ve rolleri.
- `Signature.mk`: [2002802763] 
- `Formula.falsum`: [3598518368] 
- `Formula.eq`: [1721264610] 
- `Term`: [3464200595] Terim. `var n`: de Bruijn değişkeni. `dflt`: her yapının seçkin öğesi.
- `Term.var`: [3182685870] 
- `Term.dflt`: [2967580261] 
- `Term.app`: [2427952379] 
- `Signature.Fn`: [1658714567] 
- `Signature.fnArity`: [763541887] 
- `Formula.rel`: [3663972162] 
- `Signature.Rel`: [3095078984] 
- `Signature.relArity`: [201288398] 
- `Formula.imp`: [127129141] 
- `Formula.and`: [2518415763] 
- `Formula.or`: [2711191473] 
- `Formula.all`: [1090218314] 
- `Formula.ex`: [2014662513] 
- `mkSig`: [1688038800] Bildirimlerden çekirdek imzası: semboller konumlarıyla adlandırılır.
- `SymDecl.arity`: [2044778255] 
- `SymDecl.role`: [2794591844] 
- `Thy.decls`: [334432947] 
- `RProof`: [233264427] 
- `RProof.hyp`: [1993164921] 
- `RProof.ax`: [2189395407] 
- `RProof.falsumE`: [3534982120] 
- `RForm`: [2675377604] 
- `RForm.fals`: [3363398736] 
- `RForm.eq`: [791121055] 
- `RTerm`: [1661914510] 
- `RTerm.bvar`: [2599763770] 
- `RTerm.pvar`: [1884706316] 
- `RTerm.app`: [3368164085] 
- `RForm.rel`: [84336506] 
- `RForm.not`: [1225123013] 
- `RForm.imp`: [3692202615] 
- `RForm.and`: [110748553] 
- `RForm.or`: [3359165227] 
- `RForm.all`: [1414513199] 
- `RForm.ex`: [4003114692] 
- `RProof.impI`: [3934811706] 
- `RProof.impE`: [3845325626] 
- `RProof.andI`: [366441629] 
- `RProof.andE1`: [1375574360] 
- `RProof.andE2`: [3903135099] 
- `RProof.orI1`: [479907980] 
- `RProof.orI2`: [2342614922] 
- `RProof.orE`: [3776144315] 
- `RProof.allI`: [3771646107] 
- `RProof.allE`: [750372631] 
- `RProof.exI`: [2937654209] 
- `RProof.exE`: [1417888429] 
- `RProof.refl`: [1137800419] 
- `RProof.eqE`: [431284722] 
- `RProof.em`: [1504969571] 
- `Claim.analogy`: [3454005540] 
- `SigMorph`: [409552907] Sembol eşlemesi. `fnMap f`: hedef dilde bir terim; `var i`, `f`'nin `i`. argümanıdır.
- `SigMorph.mk`: [641419062] 
- `RModel`: [2033180821] Sonlu model: boyut ve sembol tabloları.
- `RModel.mk`: [3198866306] 
- `Claim.refute`: [3230209087] 
- `Claim.verdict`: [2208626721] 
- `Doc.claimsTree`: [2587901094] Ağacın iddiaları.
- `REntry`: [3124201176] 
- `REntry.sig`: [3618653341] 
- `REntry.theory`: [256492747] 
- `REntry.lemma`: [2718592224] 
- `REntry.morph`: [4279589055] 
- `REntry.analogy`: [3373879027] 
- `REntry.refute`: [1055410128] 
- `REntry.verdict`: [3153441733] 
- `decodeDoc`: [333026062] Belge: `(hakem 1)` başlığı ve girdiler.
- `decodeDoc.match_1`: [3173164757] 
- `SExp.ctorIdx`: [2990764349] 
- `SExp.casesOn`: [941673166] 
- `SExp.rec`: [2573800420] 
- `decodeEntry`: [3712296972] 
- `decodeEntry.match_1`: [1467387877] 
- `decodeSyms`: [2335141713] 
- `decodeSyms.match_3`: [512925019] 
- `decodeSyms.match_1`: [3845527704] 
- `atomNat`: [1948146438] 
- `atomStr`: [3925532187] 
- `atomStr.match_1`: [2562554843] 
- `natOf`: [2631933090] 
- `natOf.match_1`: [484743063] 
- `digitsVal`: [694345105] Ondalık rakamlar (boş olmayan). Çekirdekte hesaplanabilir.
- `digitsVal.match_1`: [2646483098] 
- `parseRole`: [1074365706] 
- `parseRole.match_1`: [2887956856] 
- `decodeAxioms`: [545211485] 
- `decodeAxioms.match_1`: [1325332987] 
- `decodeForm`: [2388413392] 
- `SExp.brecOn`: [2806796013] 
- `SExp.below`: [3563948132] 
- `SExp.below_1`: [404870531] 
- `SExp.rec_1`: [1689471608] 
- `SExp.brecOn.go`: [3730011375] 
- `decodeForm.match_1`: [3698940012] 
- `decodeTerm`: [3972666909] 
- `decodeTerm.match_1`: [3935024780] 
- `varOf`: [1482356032] 
- `varOf.match_1`: [100982862] 
- `decodeTerms.match_1`: [3089562333] 
- `decodeTerms`: [3089816077] 
- `SExp.brecOn_1`: [3975836573] 
- `SExp.brecOn_1.go`: [12761714] 
- `decodeProof`: [1632378884] 
- `decodeProof.match_1`: [180968552] 
- `decodeLam`: [3036950829] `(lam A)`: bir bağlayıcı açan formül gövdesi.
- `decodeLam.match_1`: [3050461991] 
- `decodeMaps`: [707308461] 
- `decodeMaps.match_3`: [2125358204] 
- `decodeMaps.match_1`: [144810865] 
- `decodeModel`: [397012479] 
- `decodeModel.match_1`: [3208704751] 
- `decodeTables`: [3982956021] `(fn AD DEĞER*)` ya da `(rel AD DEĞER*)` tablolarını ayır.
- `decodeTables.match_3`: [2394935814] 
- `decodeTables.match_1`: [2508995467] 
- `decodeNats`: [525760094] 
- `decodeObligs`: [1710791292] 
- `decodeObligs.match_1`: [1298299603] 
- `decodeAlt`: [1796669943] 
- `decodeAlt.match_1`: [205763390] 
- `elabEntries`: [186620017] 
- `Env`: [2408811407] 
- `Env.mk`: [2247466989] 
- `RMorph`: [2634691863] 
- `RMorph.mk`: [2316295450] 
- `elabEntries.match_3`: [325035368] 
- `Env.step`: [368347877] 
- `Env.step.match_1`: [927564257] 
- `REntry.casesOn`: [3134087968] 
- `REntry.rec`: [3645293157] 
- `Env.sigs`: [1222705087] 
- `Env.thys`: [976870444] 
- `Env.morphs`: [1904479159] 
- `assoc`: [3868243185] Adı `n` olan ilk kaydın değeri.
- `assoc.match_1`: [617368043] 
- `elabForm`: [1491084353] 
- `RForm.brecOn`: [2806964713] 
- `RForm.below`: [3774534684] 
- `RForm.rec`: [4174447585] 
- `RForm.brecOn.go`: [1562352028] 
- `elabForm.match_1`: [1253981329] 
- `RForm.casesOn`: [1837839408] 
- `elabTerm`: [4167972223] 
- `RTerm.brecOn`: [4185461122] 
- `RTerm.below`: [2986324463] 
- `RTerm.rec`: [3961874955] 
- `RTerm.below_1`: [1583189205] 
- `RTerm.rec_1`: [278840558] 
- `RTerm.brecOn.go`: [1472000957] 
- `elabTerm.match_1`: [2506280841] 
- `RTerm.casesOn`: [1178199322] 
- `lookupFn`: [2813877894] 
- `findName`: [843583788] Adı `n` olan ilk bildirimin konumu.
- `findName.match_1`: [443251984] 
- `SymDecl.name`: [352997443] 
- `elabTerms.match_1`: [3768198478] 
- `lookupRel`: [2803573005] 
- `elabTerms`: [2747421192] 
- `RTerm.brecOn_1`: [1207431103] 
- `RTerm.brecOn_1.go`: [1837957255] 
- `Formula.not`: [231130077] `¬ φ`.
- `findThy`: [503251989] 
- `findThy.match_1`: [1115952792] 
- `Thy.name`: [4092451250] 
- `Thy.sig`: [770978300] 
- `Thy.axNames`: [3587344655] 
- `Thy.axs`: [3794229443] 
- `Thy.lemNames`: [2888964172] 
- `Thy.lems`: [1923109754] 
- `RMorph.s1`: [2979346865] 
- `RMorph.s2`: [3429999379] 
- `elabMorph`: [4160793280] Eşleme: kaynak sözlüğün her sembolü için hedefte bir terim/formül (parametreler `pJ`).
- `RMorph.fns`: [616406521] 
- `RMorph.rels`: [2399529719] 
- `elabEntries.match_1`: [1193710091] 
- `Claim.Holds`: [3676168205] Bir iddianın anlamı. Sertifikalar (ispat, model) bu anlama girmez.
- `Claim.Holds.match_1`: [1390319471] 
- `Claim.casesOn`: [3030964935] 
- `Claim.rec`: [3976005343] 
- `Theory.Entails`: [1484695865] Kuram `φ`'yi gerektirir: her modeli `φ`'yi doğrular.
- `Theory`: [1990323494] Kuram: aksiyomlar ve (isteğe bağlı) kabul edilebilir yapılar sınıfı.
- `Theory.mk`: [1704561965] 
- `Structure`: [3424008557] Yapı: taşıyıcı, seçkin öğe, sembol yorumları.
- `Structure.mk`: [143874633] 
- `Theory.Models`: [1317857373] `M`, kuramın bir modelidir.
- `Theory.admissible`: [3746421213] 
- `Theory.axioms`: [2865576458] 
- `Structure.Sat`: [3921994137] Yapı formülü doğrular: her ortamda (serbest değişkenler evrensel).
- `Structure.D`: [1437261765] 
- `Formula.eval`: [1446459881] 
- `Formula.brecOn`: [504118012] 
- `Formula.below`: [556943929] 
- `Formula.rec`: [3232664870] 
- `Formula.brecOn.go`: [4170179613] 
- `Formula.eval.match_1`: [650301004] 
- `Formula.casesOn`: [824629045] 
- `Term.eval`: [704183430] 
- `Term.brecOn`: [473429679] 
- `Term.below`: [2094337743] 
- `Term.rec`: [1099968821] 
- `Term.brecOn.go`: [4204339191] 
- `Term.onlySyms.match_1`: [264759630] 
- `Term.casesOn`: [3327370182] 
- `Structure.dflt`: [840633822] 
- `Structure.fn`: [898929416] 
- `Structure.rel`: [855465701] 
- `cons`: [535952647] Ortamı bir öğeyle genişlet (değişken 0).
- `liftSubst.match_1`: [1420932622] 
- `Thy.theory`: [3100761276] Kuramın çekirdek karşılığı: yalnızca aksiyomlar (lemmalar anlamın parçası değildir).
- `Analogy`: [1056386474] Analoji sertifikası. `σ`, kaynağın her sembolünün hedefte neye karşılık geldiğini
- `Analogy.mk`: [3725451412] 
- `SigMorph.reduct`: [1384140407] İndirgeme: hedef dünyayı kaynağın diliyle okumak. Taşıyıcı aynı kalır; kaynak
- `argEnv`: [3007921011] Argüman vektörünü ortama çevir; ikilik dışı değişkenler seçkin öğe olur.
- `SigMorph.fnMap`: [461941377] 
- `SigMorph.relMap`: [3323659712] 
- `SigMorph.trF`: [3132433532] Bir önermenin hedef dile çevirisi.
- `Formula.onlySyms.match_1`: [3446722069] 
- `SigMorph.trT`: [4048100617] 
- `Term.subst`: [162456198] Paralel ikame.
- `argSubst`: [3619969487] Argüman listesini ikameye çevir; ikilik dışı değişkenler `dflt` olur.
- `Formula.subst`: [3479023318] 
- `Formula.subst.match_1`: [2916418953] 
- `liftSubst`: [887563426] Bağlayıcının altına geçen ikame.
- `Term.shift`: [3687471488] Bütün serbest değişkenleri bir artırır.
- `Analogy.σ`: [2934450448] 
- `Refutation`: [618331221] Metafor sertifikası. `glossary`, önerilen sözlüktür. `pf`/`pr` sözlüğün bağlayıcı
- `Refutation.mk`: [1987474353] 
- `Formula.onlySyms`: [2677709904] Formüldeki her sembol `pf`/`pr`'yi sağlar.
- `Term.onlySyms`: [1893188890] Terimdeki her fonksiyon sembolü `pf`'yi sağlar.
- `allFin`: [3051285956] Sonlu bir aileye `&&`.
- `allFin.match_1`: [4001745398] 
- `Formula.mentionsFn`: [1541366290] 
- `Formula.mentionsFn.match_1`: [1086497885] 
- `Term.mentionsFn`: [3784459156] 
- `Term.mentionsFn.match_1`: [211956374] 
- `anyFin`: [166542815] Sonlu ailede `||`.
- `Formula.mentionsRel`: [231503431] 
- `PolicyVerdict`: [1124954806] Politika hükmü: `T ⊨ φ`. Ayrıca kuramın bütün öncüllerini sağlayan bir dünya ve
- `PolicyVerdict.mk`: [3985630505] 
- `Structure.reinterp`: [683133002] Yalnızca normatif sembollerin yorumunu değiştir. Taşıyıcı, betimsel (tanım ve
- `Signature.fnRole`: [3533609429] 
- `instDecidableEqRole`: [4090796487] 
- `Role.ctorIdx`: [3717224365] 
- `Role.casesOn`: [2538655878] 
- `Role.rec`: [3824428781] 
- `Role.ofNat`: [1323357135] 
- `Role.ofNat_ctorIdx`: [1788762641] 
- `Signature.relRole`: [1842763906] 
- `politika_tree`: [827753284] `corpus/politika.hkm` belgesinin ağacı (okuyucunun çıktısı).


