import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Online-Offline KEM" =>

*References:*

- {Informal.citet SCKA25}[]

:::group "on_off_kem"
Online-Offline Key Encapsulation Mechanism (On-Off KEM).
:::

# Definitions

:::definition "on_off_kem_scheme" (parent := "on_off_kem")
_On-Off KEM scheme_ (issue \#40).
:::

:::definition "on_off_kem_correctness" (parent := "on_off_kem")
_On-Off KEM scheme — correctness_ (issue \#40).
{uses "on_off_kem_scheme"}[].
:::

:::definition "on_off_kem_security" (parent := "on_off_kem")
_On-Off KEM scheme — security_ (issue \#40).
{uses "on_off_kem_scheme"}[].
:::

# Constructions

## On-Off-KEM-from-ML-KEM

:::group "on_off_kem_on_off_kem_from_ml_kem"
On-Off-KEM-from-ML-KEM.
:::

:::definition "on_off_kem_from_ml_kem_spec" (parent := "on_off_kem_on_off_kem_from_ml_kem")
_On-Off-KEM-from-ML-KEM construction_ (issue \#41).
{uses "on_off_kem_scheme"}[].
:::

:::theorem "on_off_kem_from_ml_kem_security" (parent := "on_off_kem_on_off_kem_from_ml_kem")
_On-Off-KEM-from-ML-KEM — security_ (issue \#42).
{uses "on_off_kem_from_ml_kem_spec"}[].
{uses "on_off_kem_scheme"}[].
{uses "on_off_kem_security"}[].
:::

