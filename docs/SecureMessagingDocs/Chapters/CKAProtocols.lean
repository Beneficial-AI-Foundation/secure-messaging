import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "CKA Protocol Constructions" =>

CKA protocols instantiate the CKA abstraction using various KEM-based
building blocks. We distinguish non-opportunistic protocols (standard
alternating communication) and opportunistic protocols (which allow
out-of-order or bandwidth-constrained communication).

:::group "cka_protocols"
CKA protocol constructions.
:::

# SCKA Protocol Scheme (issue \#93)

:::definition "scka_protocol_scheme" (parent := "cka_protocols")
_SCKA protocol scheme_ (\#93, {Informal.citet SCKA25}[]).
Syntax for a Sparse Continuous Key Agreement protocol: extends
{uses "cka_scheme"}[] to bandwidth-constrained two-party settings
with {uses "on_off_kem_scheme"}[] as a building block.
:::

# UniKEM-CKA (issues \#90, \#97–99)

:::definition "unikem_cka_spec" (parent := "cka_protocols")
_UniKEM-CKA protocol_ (\#97). CKA construction from a unidirectional KEM
(Section 4, {Informal.citet TR25}[]).
{uses "cka_scheme"}[] is the target interface.
:::

:::theorem "unikem_cka_correctness" (parent := "cka_protocols")
_Correctness of UniKEM-CKA_ (\#98).
{uses "unikem_cka_spec"}[] satisfies CKA correctness per
{uses "cka_correctness_exp"}[].
:::

:::theorem "unikem_cka_security" (parent := "cka_protocols")
_Security of UniKEM-CKA_ (\#99).
{uses "unikem_cka_spec"}[] is secure in the CKA sense per
{uses "cka_security_exp"}[].
:::

# BiKEM-CKA (issues \#91, \#100–102)

:::definition "bikem_cka_spec" (parent := "cka_protocols")
_BiKEM-CKA protocol_ (\#100). CKA construction from a bidirectional KEM
(Section 4, {Informal.citet TR25}[]).
{uses "cka_scheme"}[] is the target interface.
:::

:::theorem "bikem_cka_correctness" (parent := "cka_protocols")
_Correctness of BiKEM-CKA_ (\#101).
{uses "bikem_cka_spec"}[] satisfies CKA correctness per
{uses "cka_correctness_exp"}[].
:::

:::theorem "bikem_cka_security" (parent := "cka_protocols")
_Security of BiKEM-CKA_ (\#102).
{uses "bikem_cka_spec"}[] is secure in the CKA sense per
{uses "cka_security_exp"}[].
:::

# RKEM-CKA (issues \#92, \#103–105)

:::definition "rkem_cka_spec" (parent := "cka_protocols")
_RKEM-CKA protocol_ (\#103). CKA construction from a ratcheting KEM
(Section 4, {Informal.citet TR25}[]).
{uses "cka_scheme"}[] is the target interface.
{uses "rkem_scheme"}[] provides the ratcheting KEM.
:::

:::theorem "rkem_cka_correctness" (parent := "cka_protocols")
_Correctness of RKEM-CKA_ (\#104).
{uses "rkem_cka_spec"}[] satisfies CKA correctness per
{uses "cka_correctness_exp"}[].
:::

:::theorem "rkem_cka_security" (parent := "cka_protocols")
_Security of RKEM-CKA_ (\#105).
{uses "rkem_cka_spec"}[] is secure in the CKA sense per
{uses "cka_security_exp"}[].
:::

# Opp-UniKEM-CKA (issues \#94, \#106–108)

:::definition "opp_unikem_cka_spec" (parent := "cka_protocols")
_Opp-UniKEM-CKA protocol_ (\#106). Opportunistic CKA construction
from a unidirectional KEM ({Informal.citet SCKA25}[]).
{uses "scka_protocol_scheme"}[] is the target interface.
:::

:::theorem "opp_unikem_cka_correctness" (parent := "cka_protocols")
_Correctness of Opp-UniKEM-CKA_ (\#107).
{uses "opp_unikem_cka_spec"}[] satisfies SCKA correctness.
:::

:::theorem "opp_unikem_cka_security" (parent := "cka_protocols")
_Security of Opp-UniKEM-CKA_ (\#108).
{uses "opp_unikem_cka_spec"}[] is secure in the SCKA sense.
:::

# Opp-BiKEM-CKA (issues \#95, \#109–111)

:::definition "opp_bikem_cka_spec" (parent := "cka_protocols")
_Opp-BiKEM-CKA protocol_ (\#109). Opportunistic CKA construction
from a bidirectional KEM ({Informal.citet SCKA25}[]).
{uses "scka_protocol_scheme"}[] is the target interface.
:::

:::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols")
_Correctness of Opp-BiKEM-CKA_ (\#110).
{uses "opp_bikem_cka_spec"}[] satisfies SCKA correctness.
:::

:::theorem "opp_bikem_cka_security" (parent := "cka_protocols")
_Security of Opp-BiKEM-CKA_ (\#111).
{uses "opp_bikem_cka_spec"}[] is secure in the SCKA sense.
:::

# Opp-RKEM-CKA (issues \#96, \#112–114)

:::definition "opp_rkem_cka_spec" (parent := "cka_protocols")
_Opp-RKEM-CKA protocol_ (\#112). Opportunistic CKA construction
from a ratcheting KEM ({Informal.citet SCKA25}[]).
{uses "scka_protocol_scheme"}[] is the target interface.
{uses "rkem_scheme"}[] provides the ratcheting KEM.
:::

:::theorem "opp_rkem_cka_correctness" (parent := "cka_protocols")
_Correctness of Opp-RKEM-CKA_ (\#113).
{uses "opp_rkem_cka_spec"}[] satisfies SCKA correctness.
:::

:::theorem "opp_rkem_cka_security" (parent := "cka_protocols")
_Security of Opp-RKEM-CKA_ (\#114).
{uses "opp_rkem_cka_spec"}[] is secure in the SCKA sense.
:::
