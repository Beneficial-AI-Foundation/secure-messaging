import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.AEAD.Defs

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

#doc (Manual) "AEAD Definitions" =>

:::defTitle "aead" "Authenticated Encryption with Associated Data - AEAD scheme"
:::

:::definition "aead" (lean := "AEADScheme")
$`\todo`
:::


:::defTitle "aead_oracles" "AEAD game oracles"
:::

:::::::definition "aead_oracles" (lean := "AEADScheme.oracleEncrypt, AEADScheme.oracleDecrypt")
$`\todo`

::::::gameGrid
:::::gameCell "\\Oenc(a,m)" (kind := "oracle") (state := "\\gamestate\\; (e^*\\text{ - challenge ciphertext}, b\\text{ - challenge bit})")
$`\pif\;e^*\neq\bot\;\pthen\;\Return\bot`

$`\pif\;b\;\pthen\;e^* \sample \mathcal C\;\pelse\;e^* \gets \Enc(K,a,m);\quad \Return e^*`
:::::

:::::gameCell "\\Odec(a,e)" (kind := "oracle") (state := "\\gamestate\\; (e^*\\text{ - challenge ciphertext}, b\\text{ - challenge bit})")
$`\pif\;b\,\vee\,e{ = }e^*\;\pthen\;\Return\bot\;\pelse\;\Return \Dec(K,a,e)`
:::::
::::::

{usesLabel}`uses` {uses "aead"}[]
:::::::

:::defTitle "aead_correct" "AEAD correctness"
:::

:::definition "aead_correct" (lean := "AEADScheme.Correct")
$`\todo`

{usesLabel}`uses` {uses "aead"}[]
:::

:::defTitle "aead_security_exp" "AEAD security experiment"
:::

:::::::definition "aead_security_exp" (lean := "AEADScheme.securityExp, AEADScheme.aeadSecurityImpl, AEADScheme.OneTime_CCA_Adversary")
$`\todo`

Let $`\O = \{\Oenc, \Odec\}` and denote by $`\adv^{\O}` an adversary with oracle access to $`\O`.

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{1\\text{-}CCA}}{\\textsf{AEAD}}(\\adv)" (kind := "game")
$`K \sample \mathcal K;\quad b \sample \bit;\quad b' \gets \adv^{\O};\quad \Return(b'=b)`
:::::
::::::

{usesLabel}`uses` {uses "aead"}[] · {uses "aead_oracles"}[]
:::::::


:::defTitle "aead_guess_advantage" "AEAD guess advantage"
:::

:::definition "aead_guess_advantage" (lean := "AEADScheme.guessAdvantage")
$`\todo`

$$`\mathsf{Adv}^{\textsf{guess}}_{\textsf{AEAD}}(\adv)
  = \Bigl|\, \Pr[\,b' = b\,] - \tfrac{1}{2} \,\Bigr|`

{usesLabel}`uses` {uses "aead_security_exp"}[]
:::
