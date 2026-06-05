import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Secure Messaging" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

:::group "secure_messaging"
Secure Messaging protocols.
:::

# Double Ratchet

:::group "secure_messaging_double_ratchet"
Double Ratchet.
:::


- {Informal.citet ACD19}[]

:::definition "secure_messaging_double_ratchet_scheme" (parent := "secure_messaging_double_ratchet")
_secure messaging scheme (Double Ratchet)_ (issue \#121).
{uses "fs_aead_scheme"}[].
{uses "prf_prng_scheme"}[].
:::

:::definition "secure_messaging_double_ratchet_correctness" (parent := "secure_messaging_double_ratchet")
_secure messaging scheme (Double Ratchet) — correctness_ (issue \#121).
{uses "secure_messaging_double_ratchet_scheme"}[].
:::

:::definition "secure_messaging_double_ratchet_authenticity" (parent := "secure_messaging_double_ratchet")
_secure messaging scheme (Double Ratchet) — authenticity_ (issue \#121).
{uses "secure_messaging_double_ratchet_scheme"}[].
:::

:::definition "secure_messaging_double_ratchet_privacy" (parent := "secure_messaging_double_ratchet")
_secure messaging scheme (Double Ratchet) — privacy_ (issue \#121).
{uses "secure_messaging_double_ratchet_scheme"}[].
:::

:::definition "secure_messaging_double_ratchet_security" (parent := "secure_messaging_double_ratchet")
_secure messaging scheme (Double Ratchet) — security_ (issue \#121).
{uses "secure_messaging_double_ratchet_scheme"}[].
:::

# Abstract Protocol (Double Ratchet)

:::group "secure_messaging_abstract_protocol_double_ratchet"
Abstract Protocol (Double Ratchet).
:::

:::definition "secure_messaging_abstract_double_ratchet_spec" (parent := "secure_messaging_abstract_protocol_double_ratchet")
_secure messaging abstract protocol (Double Ratchet)_ (issue \#124).
{uses "fs_aead_scheme"}[].
{uses "prf_prng_scheme"}[].
:::

:::theorem "secure_messaging_abstract_double_ratchet_correctness" (parent := "secure_messaging_abstract_protocol_double_ratchet")
_secure messaging abstract protocol (Double Ratchet) — correctness_ (issue \#125).
{uses "secure_messaging_abstract_double_ratchet_spec"}[].
:::

:::theorem "secure_messaging_abstract_double_ratchet_authenticity" (parent := "secure_messaging_abstract_protocol_double_ratchet")
_secure messaging abstract protocol (Double Ratchet) — authenticity_ (issue \#126).
{uses "secure_messaging_abstract_double_ratchet_spec"}[].
:::

:::theorem "secure_messaging_abstract_double_ratchet_privacy" (parent := "secure_messaging_abstract_protocol_double_ratchet")
_secure messaging abstract protocol (Double Ratchet) — privacy_ (issue \#127).
{uses "secure_messaging_abstract_double_ratchet_spec"}[].
:::

:::theorem "secure_messaging_abstract_double_ratchet_security" (parent := "secure_messaging_abstract_protocol_double_ratchet")
_secure messaging abstract protocol (Double Ratchet) — security_ (issue \#128).
{uses "secure_messaging_abstract_double_ratchet_spec"}[].
:::

# Signal Protocol (Double Ratchet)

:::group "secure_messaging_signal_protocol_double_ratchet"
Signal Protocol (Double Ratchet).
:::

:::definition "secure_messaging_signal_double_ratchet_spec" (parent := "secure_messaging_signal_protocol_double_ratchet")
_secure messaging Signal protocol (Double Ratchet)_ (issue \#129).
{uses "fs_aead_scheme"}[].
{uses "prf_prng_scheme"}[].
:::

:::theorem "secure_messaging_signal_double_ratchet_correctness" (parent := "secure_messaging_signal_protocol_double_ratchet")
_secure messaging Signal protocol (Double Ratchet) — correctness_ (issue \#130).
{uses "secure_messaging_signal_double_ratchet_spec"}[].
:::

:::theorem "secure_messaging_signal_double_ratchet_authenticity" (parent := "secure_messaging_signal_protocol_double_ratchet")
_secure messaging Signal protocol (Double Ratchet) — authenticity_ (issue \#131).
{uses "secure_messaging_signal_double_ratchet_spec"}[].
:::

:::theorem "secure_messaging_signal_double_ratchet_privacy" (parent := "secure_messaging_signal_protocol_double_ratchet")
_secure messaging Signal protocol (Double Ratchet) — privacy_ (issue \#132).
{uses "secure_messaging_signal_double_ratchet_spec"}[].
:::

:::theorem "secure_messaging_signal_double_ratchet_security" (parent := "secure_messaging_signal_protocol_double_ratchet")
_secure messaging Signal protocol (Double Ratchet) — security_ (issue \#133).
{uses "secure_messaging_signal_double_ratchet_spec"}[].
:::

# Triple Ratchet

:::group "secure_messaging_triple_ratchet"
Triple Ratchet.
:::


- {Informal.citet TR25}[]

:::definition "secure_messaging_triple_ratchet_scheme" (parent := "secure_messaging_triple_ratchet")
_secure messaging scheme (Triple Ratchet)_ (issue \#134).
{uses "fs_aead_scheme"}[].
{uses "prf_prng_scheme"}[].
:::

:::definition "secure_messaging_triple_ratchet_spec" (parent := "secure_messaging_triple_ratchet")
_secure messaging protocol (Triple Ratchet)_ (issue \#136).
{uses "fs_aead_scheme"}[].
{uses "prf_prng_scheme"}[].
:::

:::theorem "secure_messaging_triple_ratchet_correctness" (parent := "secure_messaging_triple_ratchet")
_secure messaging protocol (Triple Ratchet) — correctness_ (issue \#137).
{uses "secure_messaging_triple_ratchet_spec"}[].
:::

:::theorem "secure_messaging_triple_ratchet_authenticity" (parent := "secure_messaging_triple_ratchet")
_secure messaging protocol (Triple Ratchet) — authenticity_ (issue \#138).
{uses "secure_messaging_triple_ratchet_spec"}[].
:::

:::theorem "secure_messaging_triple_ratchet_privacy" (parent := "secure_messaging_triple_ratchet")
_secure messaging protocol (Triple Ratchet) — privacy_ (issue \#139).
{uses "secure_messaging_triple_ratchet_spec"}[].
:::

:::theorem "secure_messaging_triple_ratchet_security" (parent := "secure_messaging_triple_ratchet")
_secure messaging protocol (Triple Ratchet) — security_ (issue \#140).
{uses "secure_messaging_triple_ratchet_spec"}[].
:::

# SCKA

:::group "secure_messaging_scka"
SCKA.
:::


- {Informal.citet SCKA25}[]

:::definition "secure_messaging_scka_scheme" (parent := "secure_messaging_scka")
_secure messaging scheme (SCKA)_ (issue \#142).
{uses "fs_aead_scheme"}[].
{uses "prf_prng_scheme"}[].
:::

:::definition "secure_messaging_scka_spec" (parent := "secure_messaging_scka")
_secure messaging protocol (SCKA)_ (issue \#144).
{uses "fs_aead_scheme"}[].
{uses "prf_prng_scheme"}[].
:::

:::theorem "secure_messaging_scka_correctness" (parent := "secure_messaging_scka")
_secure messaging protocol (SCKA) — correctness_ (issue \#145).
{uses "secure_messaging_scka_spec"}[].
:::

:::theorem "secure_messaging_scka_authenticity" (parent := "secure_messaging_scka")
_secure messaging protocol (SCKA) — authenticity_ (issue \#146).
{uses "secure_messaging_scka_spec"}[].
:::

:::theorem "secure_messaging_scka_privacy" (parent := "secure_messaging_scka")
_secure messaging protocol (SCKA) — privacy_ (issue \#147).
{uses "secure_messaging_scka_spec"}[].
:::

:::theorem "secure_messaging_scka_security" (parent := "secure_messaging_scka")
_secure messaging protocol (SCKA) — security_ (issue \#148).
{uses "secure_messaging_scka_spec"}[].
:::

