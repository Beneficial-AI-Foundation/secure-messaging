import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Sparse Continuous Key Agreement" =>

:::group "cka_protocols"
SCKA protocol constructions.
:::

# SCKA

:::group "cka_protocols_scka"
SCKA.
:::

:::definition "scka_scheme" (parent := "cka_protocols_scka")
_SCKA protocol scheme_ (issue \#93).
{uses "on_off_kem_scheme"}[].
:::

:::definition "scka_correctness" (parent := "cka_protocols_scka")
_SCKA protocol scheme — correctness_ (issue \#93).
{uses "scka_scheme"}[].
:::

:::definition "scka_security" (parent := "cka_protocols_scka")
_SCKA protocol scheme — security_ (issue \#93).
{uses "scka_scheme"}[].
:::

# UniKEM-CKA

:::group "cka_protocols_unikem_cka"
UniKEM-CKA.
:::

:::definition "unikem_cka_spec" (parent := "cka_protocols_unikem_cka")
_UniKEM-CKA protocol_ (issue \#97).
{uses "on_off_kem_scheme"}[].
:::

:::theorem "unikem_cka_correctness" (parent := "cka_protocols_unikem_cka")
_UniKEM-CKA protocol — correctness_ (issue \#98).
{uses "unikem_cka_spec"}[].
:::

:::theorem "unikem_cka_security" (parent := "cka_protocols_unikem_cka")
_UniKEM-CKA protocol — security_ (issue \#99).
{uses "unikem_cka_spec"}[].
:::

# BiKEM-CKA

:::group "cka_protocols_bikem_cka"
BiKEM-CKA.
:::

:::definition "bikem_cka_spec" (parent := "cka_protocols_bikem_cka")
_BiKEM-CKA protocol_ (issue \#100).
{uses "on_off_kem_scheme"}[].
:::

:::theorem "bikem_cka_correctness" (parent := "cka_protocols_bikem_cka")
_BiKEM-CKA protocol — correctness_ (issue \#101).
{uses "bikem_cka_spec"}[].
:::

:::theorem "bikem_cka_security" (parent := "cka_protocols_bikem_cka")
_BiKEM-CKA protocol — security_ (issue \#102).
{uses "bikem_cka_spec"}[].
:::

# RKEM-CKA

:::group "cka_protocols_rkem_cka"
RKEM-CKA.
:::

:::definition "rkem_cka_spec" (parent := "cka_protocols_rkem_cka")
_RKEM-CKA protocol_ (issue \#103).
{uses "on_off_kem_scheme"}[].
:::

:::theorem "rkem_cka_correctness" (parent := "cka_protocols_rkem_cka")
_RKEM-CKA protocol — correctness_ (issue \#104).
{uses "rkem_cka_spec"}[].
:::

:::theorem "rkem_cka_security" (parent := "cka_protocols_rkem_cka")
_RKEM-CKA protocol — security_ (issue \#105).
{uses "rkem_cka_spec"}[].
:::

# Opp-UniKEM-CKA

:::group "cka_protocols_opp_unikem_cka"
Opp-UniKEM-CKA.
:::

:::definition "opp_unikem_cka_spec" (parent := "cka_protocols_opp_unikem_cka")
_Opp-UniKEM-CKA protocol_ (issue \#106).
{uses "on_off_kem_scheme"}[].
:::

:::theorem "opp_unikem_cka_correctness" (parent := "cka_protocols_opp_unikem_cka")
_Opp-UniKEM-CKA protocol — correctness_ (issue \#107).
{uses "opp_unikem_cka_spec"}[].
:::

:::theorem "opp_unikem_cka_security" (parent := "cka_protocols_opp_unikem_cka")
_Opp-UniKEM-CKA protocol — security_ (issue \#108).
{uses "opp_unikem_cka_spec"}[].
:::

# Opp-BiKEM-CKA

:::group "cka_protocols_opp_bikem_cka"
Opp-BiKEM-CKA.
:::

:::definition "opp_bikem_cka_spec" (parent := "cka_protocols_opp_bikem_cka")
_Opp-BiKEM-CKA protocol_ (issue \#109).
{uses "on_off_kem_scheme"}[].
:::

:::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols_opp_bikem_cka")
_Opp-BiKEM-CKA protocol — correctness_ (issue \#110).
{uses "opp_bikem_cka_spec"}[].
:::

:::theorem "opp_bikem_cka_security" (parent := "cka_protocols_opp_bikem_cka")
_Opp-BiKEM-CKA protocol — security_ (issue \#111).
{uses "opp_bikem_cka_spec"}[].
:::

# Opp-RKEM-CKA

:::group "cka_protocols_opp_rkem_cka"
Opp-RKEM-CKA.
:::

:::definition "opp_rkem_cka_spec" (parent := "cka_protocols_opp_rkem_cka")
_Opp-RKEM-CKA protocol_ (issue \#112).
{uses "on_off_kem_scheme"}[].
:::

:::theorem "opp_rkem_cka_correctness" (parent := "cka_protocols_opp_rkem_cka")
_Opp-RKEM-CKA protocol — correctness_ (issue \#113).
{uses "opp_rkem_cka_spec"}[].
:::

:::theorem "opp_rkem_cka_security" (parent := "cka_protocols_opp_rkem_cka")
_Opp-RKEM-CKA protocol — security_ (issue \#114).
{uses "opp_rkem_cka_spec"}[].
:::

