import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.IncrementalKEM.Defs

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

#doc (Manual) "Incremental KEM Definitions" =>

:::group "incremental_kem"
Incremental Key Encapsulation Mechanism (Incremental KEM).
:::

:::defTitle "incremental_kem_scheme" "Incremental KEM scheme"
:::

::::definition "incremental_kem_scheme" (parent := "incremental_kem") (lean := "KEMScheme.IncrementalStructure")
$`\todo`

```anchor IncrementalStructure (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.Defs)
structure IncrementalStructure (kem : KEMScheme m K PK SK C) where
  /-- Public-key header space. For ML-KEM: `ek_seed || SHA3-256(ek_seed || ek_vector)`. -/
  PKheader : Type
  /-- Vector part of the public-key space. For ML-KEM: `ek_vector`. -/
  PKvector : Type
  /-- First ciphertext component space. -/
  C₁ : Type
  /-- Second ciphertext component space. -/
  C₂ : Type
  /-- Encapsulation state space carried from the first stage to the second. -/
  St : Type
  /-- The public key splits as `pk = (hdr, vec)`. -/
  splitPK : PK ≃ PKheader × PKvector
  /-- The ciphertext splits as `ct = (ct1, ct2)`. -/
  splitC : C ≃ C₁ × C₂
  /-- Consistency check of a vector part against a header. For ML-KEM this is the
  hash check `SHA3-256(ek_seed || ek_vector) = hek`. Protocols must check `validPK`
  before running `encaps2` on a received vector. -/
  validPK : PKheader → PKvector → Bool
  /-- First encapsulation stage `Encaps1`: from the public-key header alone, returns
  the encapsulation state, the first ciphertext component, and the shared key. -/
  encaps1 : PKheader → m (St × C₁ × K)
  /-- Second encapsulation stage `Encaps2`: from the state and the full public key,
  returns the second ciphertext component. -/
  encaps2 : St → PKheader → PKvector → m C₂
  /-- The KEM's encapsulation is the first stage followed by the second stage,
  with the two ciphertext components recombined via `splitC`. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (hdr, vec) := splitPK pk
    let (st, c1, k) ← encaps1 hdr
    let c2 ← encaps2 st hdr vec
    pure (splitC.symm (c1, c2), k))
```

{githubLabel}`github` {githubIssue 224}[]
::::
