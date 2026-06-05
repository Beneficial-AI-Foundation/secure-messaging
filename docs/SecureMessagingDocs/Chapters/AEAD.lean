import Verso
import VersoManual
import VersoBlueprint
import SecureMessaging.AEAD.Defs
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Authenticated Encryption with Associated Data" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

:::group "aead"
Authenticated Encryption with Associated Data (AEAD).
:::

```lean "sig_aead_scheme"
#check @AEADScheme
```

# AES-GCM

:::group "aead_aes_gcm"
AES-GCM.
:::


- {Informal.citet NIST_GCM}[]

:::definition "aead_aes_gcm_spec" (parent := "aead_aes_gcm")
_AEAD-AES-GCM_ (issue \#21).
:::

:::theorem "aead_aes_gcm_correctness" (parent := "aead_aes_gcm")
_AEAD-AES-GCM — correctness_ (issue \#22).
{uses "aead_aes_gcm_spec"}[].
:::

:::theorem "aead_aes_gcm_security" (parent := "aead_aes_gcm")
_AEAD-AES-GCM — security_ (issue \#23).
{uses "aead_aes_gcm_spec"}[].
:::

# Encrypt-then-MAC

:::group "aead_encrypt_then_mac"
Encrypt-then-MAC.
:::


- {Informal.citet BN00}[]
- {Informal.citet Rog02}[]

:::definition "aead_etm_spec" (parent := "aead_encrypt_then_mac")
_AEAD-encrypt-then-mac construction_ (issue \#24).
:::

:::theorem "aead_etm_correctness" (parent := "aead_encrypt_then_mac")
_AEAD-encrypt-then-mac — correctness_ (issue \#25).
{uses "aead_etm_spec"}[].
:::

:::theorem "aead_etm_security" (parent := "aead_encrypt_then_mac")
_AEAD-encrypt-then-mac — security_ (issue \#26).
{uses "aead_etm_spec"}[].
:::

