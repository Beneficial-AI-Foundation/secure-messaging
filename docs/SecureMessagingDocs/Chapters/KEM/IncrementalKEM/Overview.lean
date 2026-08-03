import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.KEM.IncrementalKEM.FromMLKEM

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

::::definition "incremental_kem_scheme" (parent := "incremental_kem") (lean := "KEMScheme.IncrementalStructure")
$`\todo`

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

{githubLabel}`github` {githubIssue 224}[]
::::

:::group "incremental_kem_incremental_kem_from_ml_kem"
Incremental KEM from ML-KEM.
:::

:::defTitle "incremental_kem_from_ml_kem_spec" "Incremental KEM from ML-KEM construction"
:::

::::definition "incremental_kem_from_ml_kem_spec" (parent := "incremental_kem_incremental_kem_from_ml_kem") (lean := "MLKEM.incrementalHeader, MLKEM.EncapsulationState, MLKEM.incrementalEncaps1, MLKEM.incrementalEncaps2, MLKEM.mlkemIncremental")
$`\todo`

:::leanPillCaption "header"
:::

```anchor incrementalHeader (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def incrementalHeader {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding) :
    Seed32 × PublicKeyHash :=
  (ek.rho, encapsulationKeyHash encoding prims ek)
```

:::leanPillCaption "encapsulation state"
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

:::leanPillCaption "encaps1"
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

:::leanPillCaption "encaps2"
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

:::leanPillCaption "IncrementalStructure instance"
:::

```anchor mlkemIncremental (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def mlkemIncremental (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalStructure
```

{usesLabel}`uses` {uses "incremental_kem_scheme"}[] · {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 226}[]
::::

*References:*

- {Informal.citet MLKEM_Braid}[]
- {Informal.citet FIPS203}[]
