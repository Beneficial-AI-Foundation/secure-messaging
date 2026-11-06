import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Chapters.KEM.MLKEM
import SecureMessagingDocs.Chapters.KEM.FrodoKEM
import SecureMessagingDocs.Chapters.KEM.OnOffKEM.Overview
import SecureMessagingDocs.Chapters.KEM.IncrementalKEM.Overview

/-! # Blueprint chapter: Key Encapsulation Mechanism -/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Key Encapsulation Mechanism" =>

*References:*

- {Informal.citet SCKA25}[]
- {Informal.citet FIPS203}[]
- {Informal.citet FrodoKEM}[]
- {Informal.citet MLKEM_Braid}[]

:::group "kem"
Key encapsulation mechanism (KEM).
:::

:::defTitle "kem_scheme" "KEM scheme"
:::

:::::::definition "kem_scheme" (parent := "kem") (lean := "KEMScheme")
A *key encapsulation mechanism* (KEM) with public-key space $`\mathsf{PK}`, secret-key space
$`\mathsf{SK}`, shared-key space $`K`, and ciphertext space $`C` consists of three algorithms:

- $`\mathsf{KeyGen}()\to(pk,sk)`: randomized key generation;
- $`\mathsf{Encaps}(pk)\to(c,k)`: randomized encapsulation of a fresh shared key $`k\in K` under
  $`pk`, with ciphertext $`c\in C`;
- $`\mathsf{Decaps}(sk,c)\to k`: decapsulation, returning $`k\in K` or $`\bot` on rejection.
:::::::

{include 1 SecureMessagingDocs.Chapters.KEM.MLKEM}

{include 1 SecureMessagingDocs.Chapters.KEM.FrodoKEM}

{include 1 SecureMessagingDocs.Chapters.KEM.OnOffKEM.Overview}

{include 1 SecureMessagingDocs.Chapters.KEM.IncrementalKEM.Overview}

{blueprint_graph}

{blueprint_summary}
