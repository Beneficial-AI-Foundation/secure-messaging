import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.CKA.Defs

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

#doc (Manual) "CKA Definitions" =>


:::defTitle "cka" "(Continuous Key Agreement - CKA scheme)"
:::

:::definition "cka" (lean := "CKAScheme")
$`\todo`

:::



:::defTitle "cka_oracles" "CKA game oracles"
:::

:::::::definition "cka_oracles" (lean := "CKAScheme.GameState, CKAScheme.GameParams, CKAScheme.isChallengeEpoch,
CKAScheme.allowCorrPCS, CKAScheme.allowCorrFS, CKAScheme.allowCorr, CKAScheme.oracleSendA, CKAScheme.oracleSendB,
CKAScheme.oracleSendA_rleak, CKAScheme.oracleSendB_rleak, CKAScheme.oracleRecvA, CKAScheme.oracleRecvB,
CKAScheme.oracleChallA, CKAScheme.oracleChallB, CKAScheme.oracleCorruptA, CKAScheme.oracleCorruptB")
$`\todo`

*Game state* $`(\stA, \stB, \rho_\mathsf{A}, \rho_\mathsf{B}, K_\mathsf{A}, K_\mathsf{B}, \mathsf{correct}, \mathsf{last}, t_\mathsf{A}, t_\mathsf{B})`

- $`\stA`, $`\stB`: local protocol states for parties A and B.
- $`\rho_\mathsf{A}`, $`\rho_\mathsf{B}`: pending messages sent by A and B.
- $`K_\mathsf{A}`, $`K_\mathsf{B}`: sender keys associated with pending sent messages.
- $`\mathsf{correct}`: records whether all delivered epoch keys have matched so far.
- $`\mathsf{last}`: the last oracle action, used to enforce alternating communication.
- $`t_\mathsf{A}`, $`t_\mathsf{B}`: per-party epoch counters.


*Game parameters* $`(t^*, \Delta_\mathsf{FS}, \Delta_\mathsf{PCS}, \mathsf{chall})`

- $`t^*`: challenge epoch selected for the security experiment.
- $`\Delta_\mathsf{FS}`: forward-secrecy delay after which post-challenge corruption is allowed.
- $`\Delta_\mathsf{PCS}`: post-compromise-security delay before the challenge during which corruption is disallowed.
- $`\mathsf{chall}`: party selected for the challenge oracle.


*Predicates*

$`\allow(t_\mathsf{A},t_\mathsf{B},t^*,\Delta_\mathsf{FS},\Delta_\mathsf{PCS},P) \;\Leftrightarrow\; \max(t_\mathsf{A},t_\mathsf{B})+\Delta_\mathsf{PCS}\leq t^* \;\vee\; t^*+\Delta_\mathsf{FS}\leq t_P`$




::::::gameGrid
:::::gameCell "\\OSendA" (kind := "oracle")
$`t_\mathsf{A}\gets t_\mathsf{A}+1;\quad (K_\mathsf{A},\rho_\mathsf{A},\stA) \sample \SendA(\stA);\quad \Return(\rho_\mathsf{A},K_\mathsf{A})`

:::::

:::::gameCell "\\OSendB" (kind := "oracle")
$`t_\mathsf{B}\gets t_\mathsf{B}+1;\quad (K_\mathsf{B},\rho_\mathsf{B},\stB) \sample \SendB(\stB);\quad \Return(\rho_\mathsf{B},K_\mathsf{B})`

:::::


:::::gameCell "\\OSendARLeak" (kind := "oracle")
$`\req\;\max(t_\mathsf{A}+1,t_\mathsf{B})+\Delta_\mathsf{PCS}\leq t^*;\quad (K_\mathsf{A},\rho_\mathsf{A},\stA,r) \sample \SendARLeak(\stA);\quad t_\mathsf{A}\gets t_\mathsf{A}+1;\quad \Return(\rho_\mathsf{A},K_\mathsf{A},r)`

:::::

:::::gameCell "\\OSendBRLeak" (kind := "oracle")
$`\req\;\max(t_\mathsf{A},t_\mathsf{B}+1)+\Delta_\mathsf{PCS}\leq t^*;\quad (K_\mathsf{B},\rho_\mathsf{B},\stB,r) \sample \SendBRLeak(\stB);\quad t_\mathsf{B}\gets t_\mathsf{B}+1;\quad \Return(\rho_\mathsf{B},K_\mathsf{B},r)`

:::::

:::::gameCell "\\ORecA" (kind := "oracle")
$`t_\mathsf{A}\gets t_\mathsf{A}+1;\quad (K,\stA) \getsval \RecA(\stA,\rho_\mathsf{B});\quad \mathsf{correct} \gets \mathsf{correct}\wedge(K_\mathsf{B}{=}K)`

:::::

:::::gameCell "\\ORecB" (kind := "oracle")
$`t_\mathsf{B}\gets t_\mathsf{B}+1;\quad (K,\stB) \getsval \RecB(\stB,\rho_\mathsf{A});\quad \mathsf{correct} \gets \mathsf{correct}\wedge(K_\mathsf{A}{=}K)`

:::::

:::::gameCell "\\OChallA" (kind := "oracle")
$`t_\mathsf{A}\gets t_\mathsf{A}+1;\quad \req\;\mathsf{chall}{=}\mathsf{A}\wedge t_\mathsf{A}=t^*;\quad (K_\mathsf{A},\rho_\mathsf{A},\stA) \sample \SendA(\stA)`

$`\mathsf{if}\;b\;\mathsf{then}\;K \sample \mathcal K\;\mathsf{else}\;K \gets K_\mathsf{A};\quad \Return(\rho_\mathsf{A},K)`

:::::

:::::gameCell "\\OChallB" (kind := "oracle")
$`t_\mathsf{B}\gets t_\mathsf{B}+1;\quad \req\;\mathsf{chall}{=}\mathsf{B}\wedge t_\mathsf{B}=t^*;\quad (K_\mathsf{B},\rho_\mathsf{B},\stB) \sample \SendB(\stB)`

$`\mathsf{if}\;b\;\mathsf{then}\;K \sample \mathcal K\;\mathsf{else}\;K \gets K_\mathsf{B};\quad \Return(\rho_\mathsf{B},K)`

:::::

:::::gameCell "\\OCorrA" (kind := "oracle")
$`\req\;\allow(t_\mathsf{A},t_\mathsf{B},t^*,\Delta_\mathsf{FS},\Delta_\mathsf{PCS},\mathsf{A});\quad \Return\stA`

:::::

:::::gameCell "\\OCorrB" (kind := "oracle")
$`\req\;\allow(t_\mathsf{A},t_\mathsf{B},t^*,\Delta_\mathsf{FS},\Delta_\mathsf{PCS},\mathsf{B});\quad \Return\stB`

:::::
::::::

{usesLabel}`uses` {uses "cka"}[]
:::::::


:::defTitle "cka_correct" "CKA correctness"
:::

:::::::definition "cka_correct" (lean := "CKAScheme.correctnessExp, CKAScheme.ckaCorrectnessImpl, CKAScheme.CKACorrectnessAdversary")
$`\todo`

Let $`\O = \{\OSendA, \ORecA, \OSendB, \ORecB\}`.







::::::gameGrid
:::::gameCell "\\Exp{\\textsf{cor}}{\\textsf{CKA}}(\\adv)" (kind := "game")
$`\lcka \sample \mathsf{Init\text{-}KeyGen}(1^\lambda);\quad \stA \getsval \InitA(\lcka);\quad \stB \getsval \InitB(\lcka)`

$`b' \getsval \adv^{\O};\quad \Return \mathsf{correct}`
:::::
::::::


{usesLabel}`uses` {uses "cka"}[] · {uses "cka_oracles"}[]
:::::::

:::defTitle "cka_security" "CKA security experiment"
:::

:::::::definition "cka_security" (lean := "CKAScheme.securityExp, CKAScheme.ckaSecurityImpl, CKAScheme.CKAAdversary")
$`\todo`

Let $`\O = \{\OSendA, \ORecA, \OChallA, \OCorrA, \OSendARLeak, \OSendB, \ORecB, \OChallB, \OCorrB, \OSendBRLeak\}`$.







::::::gameGrid
:::::gameCell "\\Exp{\\textsf{sec}}{\\textsf{CKA}}(\\adv)" (kind := "game")
$`\lcka \sample \mathsf{Init\text{-}KeyGen}(1^\lambda);\quad \stA \getsval \InitA(\lcka);\quad \stB \getsval \InitB(\lcka);\quad t_\mathsf{A},t_\mathsf{B} \getsval 0;\quad b \sample \{0,1\}`

$`b' \getsval \adv^{\O};\quad \Return[b'=b]`
:::::
::::::


{usesLabel}`uses` {uses "cka"}[] · {uses "cka_oracles"}[]
:::::::


:::defTitle "cka_advantage" "CKA guess advantage"
:::

:::definition "cka_advantage" (lean := "CKAScheme.securityAdvantage")
$`\todo`

$$`\Adv{\textsf{guess}}(\adv, gp)
  \;=\; \Bigl|\, \Pr\bigl[\,\Exp{\textsf{sec}}{\textsf{CKA}}(\adv,gp) = 1\,\bigr] - \tfrac12 \,\Bigr|
  \;=\; \Bigl|\, \Pr[\,b' = b\,] - \tfrac12 \,\Bigr|`


{usesLabel}`uses` {uses "cka_security"}[]
:::
