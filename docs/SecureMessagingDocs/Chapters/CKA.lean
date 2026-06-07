import Verso
import VersoManual
import VersoBlueprint
import SecureMessaging.CKA.Defs
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Continuous Key Agreement" =>

*References:*

- {Informal.citet ACD19}[]

:::group "cka"
Continuous Key Agreement (CKA).
:::

```lean "sig_cka_scheme"
#check @CKAScheme
```

# CKA-from-KEM

:::group "cka_cka_from_kem"
CKA-from-KEM.
:::


- {Informal.citet ACD19}[]

:::definition "cka_from_kem_spec" (parent := "cka_cka_from_kem")
_CKA-from-KEM construction_ (issue \#3).
:::

:::theorem "cka_from_kem_correctness" (parent := "cka_cka_from_kem")
_CKA-fom-KEM — correctness_ (issue \#4).
{uses "cka_from_kem_spec"}[].
:::

:::theorem "cka_from_kem_security" (parent := "cka_cka_from_kem")
_CKA-fom-KEM — security_ (issue \#5).
{uses "cka_from_kem_spec"}[].
:::

# CKA-from-DDH

:::group "cka_cka_from_ddh"
CKA-from-DDH.
:::


- {Informal.citet ACD19}[]

:::theorem "cka_from_ddh_security" (parent := "cka_cka_from_ddh")
_CKA-fom-DDH — security_ (issue \#10).
:::

# CKA-from-LWE

:::group "cka_cka_from_lwe"
CKA-from-LWE.
:::


- {Informal.citet ACD19}[]

:::definition "cka_from_lwe_spec" (parent := "cka_cka_from_lwe")
_CKA-fom-LWE construction_ (issue \#12).
:::

:::theorem "cka_from_lwe_correctness" (parent := "cka_cka_from_lwe")
_CKA-fom-LWE — correctness_ (issue \#13).
{uses "cka_from_lwe_spec"}[].
:::

:::theorem "cka_from_lwe_security" (parent := "cka_cka_from_lwe")
_CKA-fom-LWE — security_ (issue \#14).
{uses "cka_from_lwe_spec"}[].
:::

