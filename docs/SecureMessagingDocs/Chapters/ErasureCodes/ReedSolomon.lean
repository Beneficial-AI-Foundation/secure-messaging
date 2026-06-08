import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Reed-Solomon" =>

*References:*

- [RFC 5510](https://datatracker.ietf.org/doc/rfc5510/)
- [signalapp/SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet/tree/main/src/encoding)
- [mlkembraid](https://signal.org/docs/specifications/mlkembraid/)

:::group "erasure_codes_reed_solomon"
Reed-Solomon.
:::

:::defTitle "reed_solomon_erasure_code_correctness" "Reed-Solomon erasure code correctness"
:::

::::definition "reed_solomon_erasure_code_correctness" (parent := "erasure_codes_reed_solomon")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "erasure_code_scheme"}[] · {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 117}[]
::::
