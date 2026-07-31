import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.AEAD.GCM.Construction

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

#doc (Manual) "GCM" =>

*References:*

- {Informal.citet NIST_GCM}[]

:::group "aead_gcm"
GCM.
:::

:::defTitle "aead_gcm_spec" "AEAD-GCM construction"
:::

::::definition "aead_gcm_spec" (parent := "aead_gcm") (lean := "gcmOneTimeAEAD")
$`\todo`

```anchor gcmOneTimeAEAD (project := ".") (module := SecureMessaging.AEAD.GCM.Construction)
def gcmOneTimeAEAD {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 c
```

{usesLabel}`uses` {uses "aead"}[] · {githubLabel}`github` {githubIssue 21}[]
::::

:::defTitle "aead_gcm_correctness" "AEAD-GCM correctness"
:::

::::theorem "aead_gcm_correctness" (parent := "aead_gcm") (lean := "gcmOneTimeAEAD_correct")
$`\todo`

```anchor gcmOneTimeAEAD_correct (project := ".") (module := SecureMessaging.AEAD.GCM.Construction)
theorem gcmOneTimeAEAD_correct {K : Type} (prp : PRPScheme K (BitVec 128)) {L : ℕ}
    (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp L hL).Correct
```

{usesLabel}`uses` {uses "aead_gcm_spec"}[] · {uses "aead_correctness"}[] · {githubLabel}`github` {githubIssue 22}[]
::::

:::defTitle "aead_gcm_security" "AEAD-GCM security"
:::

::::theorem "aead_gcm_security" (parent := "aead_gcm")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead_gcm_spec"}[] · {uses "aead_security_exp"}[] · {githubLabel}`github` {githubIssue 23}[]
::::
