import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.KEM.IncrementalKEM.FromMLKEM
import SecureMessaging.KEM.MLKEM.Correctness.EasyCryptBoundary

/-! # Blueprint chapter: Incremental KEM -/

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Incremental KEM" =>

:::group "incremental_kem"
Incremental Key Encapsulation Mechanism (Incremental KEM).
:::

:::defTitle "incremental_kem_scheme" "Incremental KEM scheme"
:::

:::::::definition "incremental_kem_scheme" (parent := "incremental_kem") (lean := "KEMScheme.IncrementalStructure") (tags := "gh-224") (uses := "kem_scheme")
Adapted from {Informal.citet MLKEM_Braid}[], Section 1.2.

An *incremental KEM* is a {bpref "kem_scheme"}[KEM] with public-key space $`\mathsf{PK}`,
secret-key space $`\mathsf{SK}`, shared-key space $`K`, ciphertext space $`C`, and algorithms
$`(\mathsf{KeyGen},\mathsf{Encaps},\mathsf{Decaps})` for which there exist

- a header space $`H`, a vector space $`V`, and a validity predicate
  $`\mathsf{Valid}:H\times V\to\{\mathsf{true},\mathsf{false}\}` such that
  $`\mathsf{PK}\simeq\{(h,v)\in H\times V\mid\mathsf{Valid}(h,v)\}`, so that every public key has
  the form $`pk=(h,v)`;
- component spaces $`C_1` and $`C_2` such that $`C\simeq C_1\times C_2`, so that every ciphertext
  has the form $`c=(c_1,c_2)`;
- a state space $`S` and randomized algorithms $`\mathsf{Encaps}_1:H\to S\times C_1\times K` and
  $`\mathsf{Encaps}_2:S\times H\times V\to C_2` such that for every $`pk\in\mathsf{PK}`,
  $`\mathsf{Encaps}(pk)` is equal, as a computation, to the staged encapsulation below.

$$`
\begin{array}{l}
\mathsf{Encaps}(pk):\\
\quad(h,v)\gets pk\\
\quad(\sigma,c_1,k)\gets\mathsf{Encaps}_1(h)\\
\quad c_2\gets\mathsf{Encaps}_2(\sigma,h,v)\\
\quad\Return((c_1,c_2),k)
\end{array}
`

:::leanPillCaption "incremental KEM interface"
:::

```anchor IncrementalStructure (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.Defs)
structure IncrementalStructure (kem : KEMScheme m K PK SK C) where
  /-- Public-key header type. -/
  PKheader : Type
  /-- Public-key vector type. -/
  PKvector : Type
  /-- First ciphertext component. -/
  C₁ : Type
  /-- Second ciphertext component. -/
  C₂ : Type
  /-- Encapsulation state carried from the first stage to the second. -/
  St : Type
  /-- Consistency check of a vector part against a header. -/
  validPK : PKheader → PKvector → Bool
  /-- There is a bijection between public keys and header/vector pairs that pass `validPK`. -/
  splitPK : PK ≃ { parts : PKheader × PKvector // validPK parts.1 parts.2 = true }
  /-- The ciphertext splits as `ct = (ct1, ct2)`. -/
  splitC : C ≃ C₁ × C₂
  /-- First stage of encaps: from the header alone, returns the state, `ct1`, and the shared key. -/
  encaps1 : PKheader → m (St × C₁ × K)
  /-- Second stage of encaps: returns the second ciphertext component `ct2`. -/
  encaps2 : St → PKheader → PKvector → m C₂
  /-- For every public key, `kem.encaps` is equal to first running `encaps1`
  on the derived header, then running `encaps2` on the resulting state. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (hdr, vec) := (splitPK pk).1
    let (st, c1, k) ← encaps1 hdr
    let c2 ← encaps2 st hdr vec
    pure (splitC.symm (c1, c2), k))
```
:::::::

:::defTitle "incremental_kem_det" "Incremental KEM with explicit coins"
:::

:::::::definition "incremental_kem_det" (parent := "incremental_kem") (lean := "KEMScheme.IncrementalKEMDet") (tags := "gh-224") (uses := "incremental_kem_scheme")
An *incremental KEM with explicit coins* is an {bpref "incremental_kem_scheme"}[incremental KEM]
with header space $`H`, vector space $`V`, state space $`S`, and algorithms
$`\mathsf{KeyGen}`, $`\mathsf{Encaps}_1`, $`\mathsf{Encaps}_2`, $`\mathsf{Decaps}` for which
there exist coin spaces $`R_K` and $`R_1` with distributions $`\mathcal D_K` on $`R_K` and
$`\mathcal D_1` on $`R_1` such that

- $`\mathsf{KeyGen}` and $`\mathsf{Encaps}_1` are deterministic given their coins, written
  $`\mathsf{KeyGen}(;r_K)\to(pk,sk)` for $`r_K\in R_K` and
  $`\mathsf{Encaps}_1(h;r_1)\to(\sigma,c_1,k)` for a header $`h\in H` and $`r_1\in R_1`;
- $`\mathsf{Encaps}_2(\sigma,h,v)\to c_2` and $`\mathsf{Decaps}(sk,c)\to k` are deterministic,
  with $`\bot` on rejection;
- $`\mathsf{KeyGen}()` and $`\mathsf{Encaps}_1(h)` draw the coins and run the deterministic
  algorithm on them, as below.

$$`
\begin{array}{l}
\mathsf{KeyGen}():\quad r_K\sample\mathcal D_K;\quad\Return\mathsf{KeyGen}(;r_K)\\
\mathsf{Encaps}_1(h):\quad r_1\sample\mathcal D_1;\quad\Return\mathsf{Encaps}_1(h;r_1)
\end{array}
`

Its randomness-leaking variants return $`r_K` and $`r_1` and nothing for the second stage. A
protocol may instead draw the coins at its own sending steps.

:::leanPillCaption "algorithms with explicit coins and coin samplers"
:::

```anchor IncrementalKEMDet (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.Derandomized)
structure IncrementalKEMDet (m : Type → Type u) (K PK SK C : Type) where
  /-- Public-key header. -/
  PKheader : Type
  /-- Public-key vector. -/
  PKvector : Type
  /-- First ciphertext component. -/
  C₁ : Type
  /-- Second ciphertext component. -/
  C₂ : Type
  /-- Secret state retained between encapsulation stages. -/
  St : Type
  /-- Key-generation coins. -/
  KeygenRand : Type
  /-- First-stage encapsulation coins. -/
  Encaps1Rand : Type
  /-- Consistency of a public-key header and vector. -/
  validPK : PKheader → PKvector → Bool
  /-- Public keys are precisely the valid header/vector pairs. -/
  splitPK : PK ≃ { parts : PKheader × PKvector // validPK parts.1 parts.2 = true }
  /-- Ciphertext decomposition into its two components. -/
  splitC : C ≃ C₁ × C₂
  /-- Key generation from explicit coins. -/
  keygenDet : KeygenRand → PK × SK
  /-- First-stage encapsulation from a header and explicit coins. -/
  encaps1Det : PKheader → Encaps1Rand → St × C₁ × K
  /-- Second-stage encapsulation using the retained state. -/
  encaps2Det : St → PKheader → PKvector → C₂
  /-- Decapsulation, with `none` denoting rejection. -/
  decapsDet : SK → C → Option K
  /-- Sampler for key-generation coins. -/
  sampleKeygen : m KeygenRand
  /-- Sampler for first-stage encapsulation coins. -/
  sampleEncaps1 : m Encaps1Rand
```

:::::::

:::group "incremental_kem_incremental_kem_from_ml_kem"
Incremental KEM from ML-KEM.
:::

:::defTitle "incremental_kem_from_ml_kem_spec" "Incremental KEM from ML-KEM construction"
:::

::::definition "incremental_kem_from_ml_kem_spec" (parent := "incremental_kem_incremental_kem_from_ml_kem") (lean := "MLKEM.incrementalHeader, MLKEM.EncapsulationState, MLKEM.incrementalEncaps1, MLKEM.incrementalEncaps2, MLKEM.mlkemIncremental, MLKEM.mlkemIncrementalDet") (tags := "gh-226") (uses := "incremental_kem_scheme, ml_kem_scheme, incremental_kem_det")
$`\todo`

:::leanPillCaption "public-key header (ρ, H(ek))"
:::

```anchor incrementalHeader (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def incrementalHeader {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding) :
    Seed32 × PublicKeyHash :=
  (ek.rho, encapsulationKeyHash encoding prims ek)
```

:::leanPillCaption "state carried between encapsulation stages"
:::

```anchor incrementalEncapsulationState (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
structure EncapsulationState (params : Params) where
  /-- NTT-domain form of the ephemeral vector `y`, used to compute the second ciphertext
  component. -/
  yHat : TqVec params.k
  /-- Second encapsulation-noise polynomial, added to the second ciphertext component. -/
  e2 : Rq
  /-- Sampled 32-byte ML-KEM message embedded in the second ciphertext component. -/
  message : Message
```

:::leanPillCaption "first stage: derive state, u, and the shared secret"
:::

```anchor incrementalEncaps1 (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def incrementalEncaps1 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (hdr : Seed32 × PublicKeyHash) (m : Message) :
    EncapsulationState params × encoding.EncodedU × SharedSecret :=
  let (k, r) := prims.gEncaps m hdr.2
  let aHat := prims.publicMatrix hdr.1
  let y := prims.sampleVecEta1 r 0
  let e1 := prims.sampleVecEta2 r params.k
  let e2 := prims.prfEta2 r (2 * params.k)
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  ({ yHat, e2, message := m }, encoding.byteEncodeDUVec (encoding.compressDU u), k)
```

:::leanPillCaption "second stage: derive v from the public-key vector"
:::

```anchor incrementalEncaps2 (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def incrementalEncaps2 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (st : EncapsulationState params)
    (vec : encoding.EncodedTHat) : encoding.EncodedV :=
  let tHat := encoding.byteDecode12Vec vec
  let mu := encoding.decompress1 (encoding.byteDecode1 st.message)
  let v := ring.invNTT (ring.dot tHat st.yHat) + st.e2 + mu
  encoding.byteEncodeDV (encoding.compressDV v)
```

:::leanPillCaption "complete incremental ML-KEM construction"
:::

```anchor mlkemIncremental (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def mlkemIncremental (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalStructure
    where
  PKheader := Seed32 × PublicKeyHash
  PKvector := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedTHat
  C₁ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedU
  C₂ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedV
  St := EncapsulationState (ParameterSet.params p)
  validPK hdr vec := decide
    (encapsulationKeyHash (Concrete.concreteEncoding (ParameterSet.params p)) prims
        { tHatEncoded := vec, rho := hdr.1 } = hdr.2)
  splitPK :=
    { toFun := fun ek => ⟨(incrementalHeader prims ek, ek.tHatEncoded), by simp [incrementalHeader]⟩
      invFun := fun parts => { tHatEncoded := parts.1.2, rho := parts.1.1.1 }
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨rho, h⟩, vec⟩, hvalid⟩
        have hh := of_decide_eq_true hvalid
        apply Subtype.ext
        simp only [incrementalHeader, hh] }
  splitC :=
    { toFun := fun c => (c.uEncoded, c.vEncoded)
      invFun := fun uv => { uEncoded := uv.1, vEncoded := uv.2 }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  encaps1 := fun hdr => do
    let m ←$ᵗ Message
    return incrementalEncaps1 ring prims hdr m
  encaps2 := fun st _hdr vec => return (incrementalEncaps2 ring st vec)
  factor := by
    intro ek
    simp only [mlkemScheme, asKEMScheme, Equiv.coe_fn_symm_mk,
      bind_assoc, pure_bind]
    rfl
```

Its variant {bpref "incremental_kem_det"}[with explicit coins] keeps the header $`(\rho,\mathsf H(ek))`
and the vector $`\hat{\mathbf t}`, and takes the seeds of FIPS 203 as coins:

- $`r_K=d\mathbin\|z`, uniform over 64-byte strings, with $`d,z` the key-generation seeds;
- $`r_1=m`, uniform over 32-byte strings, with $`m` the encapsulation message.

:::leanPillCaption "ML-KEM instantiation"
:::

```anchor mlkemIncrementalDet (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def mlkemIncrementalDet (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    IncrementalKEMDet ProbComp SharedSecret
      (EncapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (DecapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (Ciphertext (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p))) :=
  let inc := mlkemIncremental p ring prims
  { PKheader := inc.PKheader
    PKvector := inc.PKvector
    C₁ := inc.C₁
    C₂ := inc.C₂
    St := inc.St
    KeygenRand := Bytes 64
    Encaps1Rand := Message
    validPK := inc.validPK
    splitPK := inc.splitPK
    splitC := inc.splitC
    keygenDet := fun r => keygenInternal ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims (r.take 32) (r.drop 32)
    encaps1Det := incrementalEncaps1 ring prims
    encaps2Det := fun st _hdr vec => incrementalEncaps2 ring st vec
    decapsDet := fun sk c => some (decapsInternal ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims sk c)
    sampleKeygen := $ᵗ Bytes 64
    sampleEncaps1 := $ᵗ Message }
```
::::

:::defTitle "incremental_kem_from_ml_kem_correctness" "Incremental ML-KEM-768 correctness from EasyCrypt assumptions"
:::

::::theorem "incremental_kem_from_ml_kem_correctness" (parent := "incremental_kem_incremental_kem_from_ml_kem") (lean := "MLKEM.incrementalCorrectExp_failure_le_mlkem768_easycrypt") (tags := "gh-226") (uses := "incremental_kem_from_ml_kem_spec, ml_kem_correctness_easycrypt")
$`\todo`

:::leanPillCaption "staged ML-KEM-768 correctness bound"
:::

```anchor incrementalCorrectExp_failure_le_mlkem768_easycrypt (project := ".") (module := SecureMessaging.KEM.MLKEM.Correctness.EasyCryptBoundary)
theorem incrementalCorrectExp_failure_le_mlkem768_easycrypt {failprob hsadv prfadv : ℝ≥0∞}
    (hcb : EasyCryptMLKEM768.correctnessBoundError ≤ failprob)
    (hhs : EasyCryptMLKEM768.smoothingAdvantage ≤ hsadv)
    (hkg : EasyCryptMLKEM768.keygenPRFAdvantage ≤ prfadv)
    (henc : EasyCryptMLKEM768.encapsPRFAdvantage ≤ prfadv) :
    Pr{let x ← (mlkemIncremental .MLKEM768 Concrete.concreteNTTRingOps
          Concrete.mlkem768Primitives).CorrectExp}[x = false]
      ≤ failprob + hsadv + 2 * prfadv
```
::::

:::defTitle "incremental_kem_rand_leak" "Incremental KEM randomness leakage"
:::

::::definition "incremental_kem_rand_leak" (parent := "incremental_kem") (lean := "KEMScheme.IncrementalRandLeak, MLKEM.mlkemIncrementalRandLeak") (tags := "gh-246") (uses := "incremental_kem_scheme, incremental_kem_from_ml_kem_spec")

:::leanPillCaption "incremental KEM randomness leakage"
:::

```anchor IncrementalRandLeak (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.Defs)
structure IncrementalRandLeak (kem : KEMScheme m K PK SK C)
    (inc : kem.IncrementalStructure) where
  /-- Randomness space for key generation. -/
  KeygenRand : Type
  /-- Randomness space for the first encapsulation stage. -/
  Encaps1Rand : Type
  /-- Randomness space for the second encapsulation stage. -/
  Encaps2Rand : Type
  /-- Key generation together with the randomness used to sample the key pair. -/
  keygenRleak : m ((PK × SK) × KeygenRand)
  /-- First-stage encapsulation together with its randomness. -/
  encaps1Rleak : inc.PKheader → m ((inc.St × inc.C₁ × K) × Encaps1Rand)
  /-- Second-stage encapsulation together with its randomness. -/
  encaps2Rleak : inc.St → inc.PKheader → inc.PKvector → m (inc.C₂ × Encaps2Rand)
  /-- First component: ordinary key generation is the first component of
  `keygenRleak`. -/
  keygen_fst :
    (do
      let out ← keygenRleak
      pure out.1) = kem.keygen
  /-- First component: ordinary first-stage encapsulation is the first component of
  `encaps1Rleak hdr`. -/
  encaps1_fst : ∀ hdr,
    (do
      let out ← encaps1Rleak hdr
      pure out.1) = inc.encaps1 hdr
  /-- First component: ordinary second-stage encapsulation is the first component of
  `encaps2Rleak st hdr vec`. -/
  encaps2_fst : ∀ st hdr vec,
    (do
      let out ← encaps2Rleak st hdr vec
      pure out.1) = inc.encaps2 st hdr vec
```

:::leanPillCaption "ML-KEM incremental randomness leakage"
:::

```anchor mlkemIncrementalRandLeak (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def mlkemIncrementalRandLeak (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalRandLeak (mlkemIncremental p ring prims) where
  KeygenRand := Seed32 × Seed32
  Encaps1Rand := Message
  Encaps2Rand := Unit
  keygenRleak := do
    let d ← $ᵗ Seed32
    let z ← $ᵗ Seed32
    return (keygenInternal ring (Concrete.concreteEncoding (ParameterSet.params p)) prims d z,
      (d, z))
  encaps1Rleak := fun hdr => do
    let m ← $ᵗ Message
    return (incrementalEncaps1 ring prims hdr m, m)
  encaps2Rleak := fun st _hdr vec =>
    return (incrementalEncaps2 ring st vec, ())
  keygen_fst := by
    simp only [mlkemScheme, asKEMScheme, keygen, bind_assoc, pure_bind]
  encaps1_fst := fun _hdr => by
    simp only [mlkemIncremental, bind_assoc, pure_bind]
  encaps2_fst := fun _st _hdr _vec => by
    simp only [mlkemIncremental, pure_bind]
```
::::

*References:*

- {Informal.citet MLKEM_Braid}[]
- {Informal.citet FIPS203}[]
