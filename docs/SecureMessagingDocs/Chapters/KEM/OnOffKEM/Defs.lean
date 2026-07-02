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

#doc (Manual) "On-Off KEM Definitions" =>

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
  /-- `kem.encaps` is the two phases in sequence, recombined via `split`. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (st, c0) ← encapsOff
    let (c1, k) ← encapsOn st pk
    pure (split.symm (c0, c1), k))
```

{githubLabel}`github` {githubIssue 40}[]
::::
