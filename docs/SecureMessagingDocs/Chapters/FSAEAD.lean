import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Forward-Secure AEAD" =>

*References:*

- {Informal.citet ACD19}[]

:::group "fs_aead"
Forward-Secure AEAD (FS-AEAD).
:::

# Definitions

:::definition "fs_aead_scheme" (parent := "fs_aead")
_FS-AEAD scheme_ (issue \#28).
:::

:::definition "fs_aead_security" (parent := "fs_aead")
_FS-AEAD scheme — security_ (issue \#28).
{uses "fs_aead_scheme"}[].
:::

# Constructions

## FS-AEAD-from-\{AEAD,PRG\}

:::group "fs_aead_fs_aead_from_aead_prg"
FS-AEAD-from-\{AEAD,PRG\}.
:::


- {Informal.citet ACD19}[]

:::theorem "fs_aead_from_aead_prg_correctness" (parent := "fs_aead_fs_aead_from_aead_prg")
_FS-AEAD-from-\{AEAD,PRG\} — correctness_ (issue \#29).
{uses "fs_aead_from_aead_prg_spec"}[].
{uses "fs_aead_scheme"}[].
:::

:::definition "fs_aead_from_aead_prg_spec" (parent := "fs_aead_fs_aead_from_aead_prg")
_FS-AEAD-from-\{AEAD,PRG\} construction_ (issue \#31).
{uses "fs_aead_scheme"}[].
:::

:::theorem "fs_aead_from_aead_prg_security" (parent := "fs_aead_fs_aead_from_aead_prg")
_FS-AEAD-from-\{AEAD,PRG\} — security_ (issue \#32).
{uses "fs_aead_from_aead_prg_spec"}[].
{uses "fs_aead_scheme"}[].
{uses "fs_aead_security"}[].
:::

