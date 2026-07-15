import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.OnOffKEM.Defs
import SecureMessaging.KEM.OnOffKEM.FromKPKE

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

#doc (Manual) "On-Off KEM" =>

:::group "on_off_kem"
Online-Offline Key Encapsulation Mechanism (On-Off KEM).
:::

:::defTitle "on_off_kem_scheme" "On-Off KEM scheme"
:::

::::definition "on_off_kem_scheme" (parent := "on_off_kem") (lean := "KEMScheme.OnOffStructure")
$`\todo`

```anchor OnOffStructure (project := ".") (module := SecureMessaging.KEM.OnOffKEM.Defs)
structure OnOffStructure (kem : KEMScheme m K PK SK C) where
  /-- Offline encapsulation state space. -/
  St : Type
  /-- Offline ciphertext space. -/
  C₀ : Type
  /-- Online ciphertext space. -/
  C₁ : Type
  /-- The ciphertext space splits as `ct = (ct0, ct1)`. -/
  split : C ≃ C₀ × C₁
  /-- Offline encapsulation `Enc.Off`: key-independent, returns a state and `ct0`. -/
  encapsOff : m (St × C₀)
  /-- Online encapsulation `Enc.On`: from the state and `pk`, returns `ct1` and the shared key. -/
  encapsOn : St → PK → m (C₁ × K)
  /-- For every public key, `kem.encaps` is equal to first running `encapsOff`,
  then running `encapsOn st pk`. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (st, c0) ← encapsOff
    let (c1, k) ← encapsOn st pk
    pure (split.symm (c0, c1), k))
```

{githubLabel}`github` {githubIssue 40}[]
::::

:::defTitle "on_off_kem_rand_leak" "On-Off KEM randomness leakage"
:::

::::definition "on_off_kem_rand_leak" (parent := "on_off_kem") (lean := "KEMScheme.OnOffRandLeak")

```anchor OnOffRandLeak (project := ".") (module := SecureMessaging.KEM.OnOffKEM.Defs)
structure OnOffRandLeak (kem : KEMScheme m K PK SK C)
    (onoff : kem.OnOffStructure) where
  /-- Randomness space for key generation. -/
  KeygenRand : Type
  /-- Randomness space for offline encapsulation. -/
  OffRand : Type
  /-- Randomness space for online encapsulation. -/
  OnRand : Type
  /-- Key generation together with the randomness used to sample the key pair. -/
  keygenRleak : m ((PK × SK) × KeygenRand)
  /-- Offline encapsulation together with its randomness. -/
  encapsOffRleak : m ((onoff.St × onoff.C₀) × OffRand)
  /-- Online encapsulation together with its randomness. -/
  encapsOnRleak : onoff.St → PK → m ((onoff.C₁ × K) × OnRand)
  /-- First component: ordinary key generation is the first component of
  `keygenRleak`. -/
  keygen_fst :
    (do
      let out ← keygenRleak
      pure out.1) = kem.keygen
  /-- First component: ordinary offline encapsulation is the first component of
  `encapsOffRleak`. -/
  encapsOff_fst :
    (do
      let out ← encapsOffRleak
      pure out.1) = onoff.encapsOff
  /-- First component: ordinary online encapsulation is the first component of
  `encapsOnRleak st pk`. -/
  encapsOn_fst : ∀ st pk,
    (do
      let out ← encapsOnRleak st pk
      pure out.1) = onoff.encapsOn st pk
```

{usesLabel}`uses` {uses "on_off_kem_scheme"}[]
::::

:::group "on_off_kem_on_off_kem_from_ml_kem"
On-Off KEM from ML-KEM.
:::

:::defTitle "on_off_kem_from_ml_kem_spec" "On-Off KEM from ML-KEM construction"
:::

::::::definition "on_off_kem_from_ml_kem_spec" (parent := "on_off_kem_on_off_kem_from_ml_kem") (lean := "KPKEOnOff.scheme, KPKEOnOff.onOff")
$`\todo`

The KEM is built directly on `MLKEM.KPKE`: `encaps` is `KPKE.encrypt` on a freshly
sampled message (the shared key), and `decaps` is `KPKE.decrypt`.

:::leanPillCaption "the KEM scheme (keygen, encaps = `KPKE.encrypt`, decaps)"
:::

```anchor schemeFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def scheme :
    KEMScheme ProbComp Message encoding.EncodedTHat encoding.EncodedTHat
      (encoding.EncodedU × encoding.EncodedV) where
  keygen := keygen params encoding ring prims rho
  encaps ek := do
    let coins ← $ᵗ Coins
    let msg ← $ᵗ Message
    let ct := KPKE.encrypt ring encoding prims
      ({ tHatEncoded := ek, rho := rho } : KPKE.PublicKey params encoding) msg coins
    pure ((ct.uEncoded, ct.vEncoded), msg)
  decaps := decaps params encoding ring prims
```

:::leanPillCaption "decapsulation via `KPKE.decrypt`"
:::

```anchor decapsFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def decaps (sk : encoding.EncodedTHat) (c : encoding.EncodedU × encoding.EncodedV) :
    ProbComp (Option Message) :=
  pure (some (KPKE.decrypt ring encoding prims
    ({ sHatEncoded := sk } : KPKE.SecretKey params encoding)
    ({ uEncoded := c.1, vEncoded := c.2 } : KPKE.Ciphertext params encoding)))
```

:::leanPillCaption "offline encapsulation `Enc.Off` (computes `ct0`, key-independent)"
:::

```anchor encapsOffFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def encapsOff : ProbComp ((Coins × TqVec params.k) × encoding.EncodedU) := do
  let coins ← $ᵗ Coins
  let aHat := prims.publicMatrix rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  pure ((coins, yHat), encoding.byteEncodeDUVec (encoding.compressDU u))
```

:::leanPillCaption "online encapsulation `Enc.On` (computes `ct1` and the shared key)"
:::

```anchor encapsOnFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def encapsOn (st : Coins × TqVec params.k) (ek : encoding.EncodedTHat) :
    ProbComp (encoding.EncodedV × Message) := do
  let (coins, yHat) := st
  let tHat := encoding.byteDecode12Vec ek
  let e2 := prims.prfEta2 coins (2 * params.k)
  let msg ← $ᵗ Message
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  pure (encoding.byteEncodeDV (encoding.compressDV v), msg)
```

:::leanPillCaption "online-offline structure; `factor` proves `encapsOff` then `encapsOn` equals `encaps`"
:::

```anchor onOffFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def onOff : (scheme params encoding ring prims rho).OnOffStructure where
  St := Coins × TqVec params.k
  C₀ := encoding.EncodedU
  C₁ := encoding.EncodedV
  split := Equiv.refl (encoding.EncodedU × encoding.EncodedV)
  encapsOff := encapsOff params encoding ring prims rho
  encapsOn := encapsOn params encoding ring prims
  factor ek := by
    simp only [scheme, encapsOff, encapsOn, KPKE.encrypt, bind_assoc, pure_bind,
      Equiv.refl_symm, Equiv.coe_refl, id_eq]
```

{usesLabel}`uses` {uses "on_off_kem_scheme"}[] · {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 41}[]
::::::
