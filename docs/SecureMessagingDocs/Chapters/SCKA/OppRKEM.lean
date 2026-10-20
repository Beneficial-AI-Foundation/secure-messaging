import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Opp-RKEM-CKA" =>

:::group "cka_protocols_opp_rkem_cka"
Opp-RKEM-CKA.
:::

:::defTitle "opp_rkem_cka_spec" "Opp-RKEM-CKA protocol"
:::

::::definition "opp_rkem_cka_spec" (parent := "cka_protocols_opp_rkem_cka") (tags := "gh-112") (uses := "scka_scheme, erasure_code_scheme, rkem_scheme")
*Erratum 1: Sending is blocked under the strict failure convention.*

Figure 19, `CKA-Send-A`, lines 13–21, has the same absent-ciphertext pattern as
Figures 17–18, with an extra conjunct in line 14.
Under the paper's §2 failure convention, encoding an absent ciphertext aborts the send
while the party waits for the peer's encapsulation key.
See the {ref "opp-bikem-errata"}[Opp-BiKEM errata box] for the execution trace and analysis of this shared issue.

The proposed paper correction is to guard lines 19–21 with `if ct_P ≠ ⊥`.
While waiting, the message then carries only epochs and acknowledgements, with `ch = ⊥` and `b = ⊥`.
The construction and its formal implementation remain to be specified below.

$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "opp_rkem_cka_correctness" "Opp-RKEM-CKA correctness"
:::

::::theorem "opp_rkem_cka_correctness" (parent := "cka_protocols_opp_rkem_cka") (tags := "gh-113") (uses := "opp_rkem_cka_spec, scka_correctness, erasure_code_correctness, rkem_correctness")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "opp_rkem_cka_security" "Opp-RKEM-CKA security"
:::

::::theorem "opp_rkem_cka_security" (parent := "cka_protocols_opp_rkem_cka") (tags := "gh-114") (uses := "opp_rkem_cka_spec, scka_security, erasure_code_scheme, rkem_forward_security, rkem_ratchet_sim")
$`\todo`

:::leanPill "missing"
:::
::::
