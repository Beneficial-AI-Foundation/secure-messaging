import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "PRF-PRNG" =>

*References:*

- {Informal.citet ACD19}[]

:::group "prf_prng"
Pseudorandom Function-Generator (PRF-PRNG).
:::

# Definitions

:::definition "prf_prng_scheme" (parent := "prf_prng")
_PRF-PRNG scheme_ (issue \#34).
:::

:::definition "prf_prng_security" (parent := "prf_prng")
_PRF-PRNG scheme — security_ (issue \#34).
{uses "prf_prng_scheme"}[].
:::

# Constructions

## PRF-PRNG-from-\{PRP,PRG\}

:::group "prf_prng_prf_prng_from_prp_prg"
PRF-PRNG-from-\{PRP,PRG\}.
:::

:::definition "prf_prng_from_prp_prg_spec" (parent := "prf_prng_prf_prng_from_prp_prg")
_PRF-PRNG-from-\{PRP,PRG\} construction_ (issue \#36).
{uses "prf_prng_scheme"}[].
:::

:::theorem "prf_prng_from_prp_prg_security" (parent := "prf_prng_prf_prng_from_prp_prg")
_PRF-PRNG-from-\{PRP,PRG\} — security_ (issue \#37).
{uses "prf_prng_from_prp_prg_spec"}[].
{uses "prf_prng_scheme"}[].
{uses "prf_prng_security"}[].
:::

