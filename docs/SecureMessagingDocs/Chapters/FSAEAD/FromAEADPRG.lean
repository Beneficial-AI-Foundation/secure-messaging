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

#doc (Manual) "FS-AEAD from AEAD and PRG" =>

*References:*

- {Informal.citet ACD19}[]

:::group "fs_aead_fs_aead_from_aead_prg"
FS-AEAD from AEAD and PRG.
:::

:::defTitle "fs_aead_from_aead_prg_spec" "FS-AEAD from AEAD and PRG construction"
:::

::::definition "fs_aead_from_aead_prg_spec" (parent := "fs_aead_fs_aead_from_aead_prg") (tags := "gh-31") (uses := "fs_aead_scheme, aead, prf_prng_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "fs_aead_from_aead_prg_correctness" "FS-AEAD from AEAD and PRG correctness"
:::

::::theorem "fs_aead_from_aead_prg_correctness" (parent := "fs_aead_fs_aead_from_aead_prg") (tags := "gh-29") (uses := "fs_aead_from_aead_prg_spec, fs_aead_scheme, aead_correctness, prf_prng_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "fs_aead_from_aead_prg_security" "FS-AEAD from AEAD and PRG security"
:::

::::theorem "fs_aead_from_aead_prg_security" (parent := "fs_aead_fs_aead_from_aead_prg") (tags := "gh-32") (uses := "fs_aead_from_aead_prg_spec, fs_aead_scheme, fs_aead_security, aead_security_exp, prf_prng_security")
$`\todo`

:::leanPill "missing"
:::
::::
