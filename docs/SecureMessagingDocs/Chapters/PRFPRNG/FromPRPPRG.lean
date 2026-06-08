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

#doc (Manual) "PRF-PRNG from PRP and PRG" =>

*References:*

- {Informal.citet ACD19}[]

:::group "prf_prng_prf_prng_from_prp_prg"
PRF-PRNG from PRP and PRG.
:::

:::defTitle "prf_prng_from_prp_prg_spec" "PRF-PRNG from PRP and PRG construction"
:::

::::definition "prf_prng_from_prp_prg_spec" (parent := "prf_prng_prf_prng_from_prp_prg")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "prf_prng_scheme"}[] · {githubLabel}`github` {githubIssue 36}[]
::::

:::defTitle "prf_prng_from_prp_prg_security" "PRF-PRNG from PRP and PRG security"
:::

::::theorem "prf_prng_from_prp_prg_security" (parent := "prf_prng_prf_prng_from_prp_prg")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "prf_prng_from_prp_prg_spec"}[] · {uses "prf_prng_scheme"}[] · {uses "prf_prng_security"}[] · {githubLabel}`github` {githubIssue 37}[]
::::
