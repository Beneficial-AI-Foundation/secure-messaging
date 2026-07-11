import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.OnOffKEM.Defs

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
`OnOffRandLeak` refines ordinary KEM randomness leakage into the three
randomized phases used by an on-off KEM: key generation, offline encapsulation,
and online encapsulation.  Its projection fields require the first component of
each leaking algorithm to coincide with the corresponding ordinary algorithm.

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

::::definition "on_off_kem_from_ml_kem_spec" (parent := "on_off_kem_on_off_kem_from_ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "on_off_kem_scheme"}[] · {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 41}[]
::::
