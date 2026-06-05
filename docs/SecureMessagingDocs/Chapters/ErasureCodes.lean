import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Erasure Codes" =>

*References:*

- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

:::group "erasure_codes"
Erasure Codes.
:::

# Definitions

:::definition "erasure_code_scheme" (parent := "erasure_codes")
_Erasure Code Scheme_ (issue \#116).
:::

:::definition "erasure_code_correctness" (parent := "erasure_codes")
_Erasure Code Scheme — correctness_ (issue \#116).
{uses "erasure_code_scheme"}[].
:::

# Constructions

## Reed-Solomon

:::group "erasure_codes_reed_solomon"
Reed-Solomon.
:::


- [RFC 5510](https://datatracker.ietf.org/doc/rfc5510/)
- [signalapp/SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet/tree/main/src/encoding)
- [mlkembraid](https://signal.org/docs/specifications/mlkembraid/)

:::definition "reed_solomon_erasure_code_correctness" (parent := "erasure_codes_reed_solomon")
_Reed-Solomon erasure code — correctness_ (issue \#117).
{uses "erasure_code_scheme"}[].
:::

