import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Secure Messaging Protocols" =>

Full secure messaging protocols combining all lower-level primitives
into end-to-end encrypted communication systems.

:::group "secure_messaging"
Secure Messaging protocols.
:::

# Double Ratchet (issues \#118, \#121–133)

The Double Ratchet protocol ({Informal.citet ACD19}[]) composes CKA, FS-AEAD, and PRF-PRNG
into the Signal-style messaging protocol. We formalize both an abstract
protocol (parameterized by generic CKA/FS-AEAD/PRF-PRNG) and the concrete
Signal instantiation.

## Scheme Definition

:::definition "double_ratchet_scheme" (parent := "secure_messaging")
_Double Ratchet scheme_ (\#121, {Informal.citet ACD19}[]).
Specification of the Double Ratchet messaging scheme: syntax for
$`(\Init, \Send, \Recv)` over a CKA, FS-AEAD, and PRF-PRNG.
{uses "cka_scheme"}[]
{uses "fs_aead_scheme"}[]
{uses "prf_prng_scheme"}[]
:::

## Abstract Protocol

:::definition "double_ratchet_abstract_spec" (parent := "secure_messaging")
_Double Ratchet abstract protocol_ (\#124, {Informal.citet ACD19}[]).
Specification of the abstract Double Ratchet protocol parameterized by
generic primitives.
{uses "double_ratchet_scheme"}[] defines the scheme.
:::

:::theorem "double_ratchet_abstract_correctness" (parent := "secure_messaging")
_Correctness of abstract Double Ratchet_ (\#125).
{uses "double_ratchet_abstract_spec"}[] satisfies messaging correctness:
received messages match sent messages in order.
:::

:::theorem "double_ratchet_abstract_authenticity" (parent := "secure_messaging")
_Authenticity of abstract Double Ratchet_ (\#126).
{uses "double_ratchet_abstract_spec"}[] satisfies messaging authenticity:
the adversary cannot forge valid ciphertexts.
:::

:::theorem "double_ratchet_abstract_privacy" (parent := "secure_messaging")
_Privacy of abstract Double Ratchet_ (\#127).
{uses "double_ratchet_abstract_spec"}[] satisfies messaging privacy:
ciphertexts reveal no information about plaintexts.
:::

:::theorem "double_ratchet_abstract_security" (parent := "secure_messaging")
_Security of abstract Double Ratchet_ (\#128).
{uses "double_ratchet_abstract_spec"}[] satisfies full messaging security
combining {uses "double_ratchet_abstract_authenticity"}[] and
{uses "double_ratchet_abstract_privacy"}[].
:::

:::theorem "double_ratchet_abstract_verify" (parent := "secure_messaging")
_Verify abstract Double Ratchet protocol_ (\#122).
End-to-end verification that {uses "double_ratchet_abstract_spec"}[] satisfies
{uses "double_ratchet_abstract_correctness"}[],
{uses "double_ratchet_abstract_authenticity"}[], and
{uses "double_ratchet_abstract_privacy"}[].
:::

## Signal Protocol Instantiation

:::definition "double_ratchet_signal_spec" (parent := "secure_messaging")
_Double Ratchet Signal protocol_ (\#129, {Informal.citet ACD19}[]).
Concrete instantiation of the Double Ratchet with Signal's specific
CKA (X3DH + DH ratchet), FS-AEAD (AES-256-CBC + HMAC), and PRF-PRNG
(HKDF).
{uses "double_ratchet_scheme"}[] defines the scheme.
:::

:::theorem "double_ratchet_signal_correctness" (parent := "secure_messaging")
_Correctness of Signal Double Ratchet_ (\#130).
{uses "double_ratchet_signal_spec"}[] satisfies messaging correctness.
:::

:::theorem "double_ratchet_signal_authenticity" (parent := "secure_messaging")
_Authenticity of Signal Double Ratchet_ (\#131).
{uses "double_ratchet_signal_spec"}[] satisfies messaging authenticity.
:::

:::theorem "double_ratchet_signal_privacy" (parent := "secure_messaging")
_Privacy of Signal Double Ratchet_ (\#132).
{uses "double_ratchet_signal_spec"}[] satisfies messaging privacy.
:::

:::theorem "double_ratchet_signal_security" (parent := "secure_messaging")
_Security of Signal Double Ratchet_ (\#133).
{uses "double_ratchet_signal_spec"}[] satisfies full messaging security
combining {uses "double_ratchet_signal_authenticity"}[] and
{uses "double_ratchet_signal_privacy"}[].
:::

:::theorem "double_ratchet_signal_verify" (parent := "secure_messaging")
_Verify Signal Double Ratchet protocol_ (\#123).
End-to-end verification that {uses "double_ratchet_signal_spec"}[] satisfies
{uses "double_ratchet_signal_correctness"}[],
{uses "double_ratchet_signal_authenticity"}[], and
{uses "double_ratchet_signal_privacy"}[].
:::

# Triple Ratchet (issues \#119, \#134–140)

The Triple Ratchet protocol ({Informal.citet TR25}[]) extends the Double Ratchet with
an RKEM-based third ratchet for improved bandwidth efficiency
and hybrid post-quantum security.

:::definition "triple_ratchet_scheme" (parent := "secure_messaging")
_Triple Ratchet scheme_ (\#134, {Informal.citet TR25}[]).
Specification of the Triple Ratchet messaging scheme incorporating
{uses "rkem_scheme"}[] for the third ratchet layer.
{uses "double_ratchet_scheme"}[]
:::

:::definition "triple_ratchet_spec" (parent := "secure_messaging")
_Triple Ratchet protocol_ (\#136, {Informal.citet TR25}[]).
Full specification of the Triple Ratchet protocol.
{uses "triple_ratchet_scheme"}[] defines the scheme.
:::

:::theorem "triple_ratchet_correctness" (parent := "secure_messaging")
_Correctness of Triple Ratchet_ (\#137).
{uses "triple_ratchet_spec"}[] satisfies messaging correctness.
:::

:::theorem "triple_ratchet_authenticity" (parent := "secure_messaging")
_Authenticity of Triple Ratchet_ (\#138).
{uses "triple_ratchet_spec"}[] satisfies messaging authenticity.
:::

:::theorem "triple_ratchet_privacy" (parent := "secure_messaging")
_Privacy of Triple Ratchet_ (\#139).
{uses "triple_ratchet_spec"}[] satisfies messaging privacy.
:::

:::theorem "triple_ratchet_security" (parent := "secure_messaging")
_Security of Triple Ratchet_ (\#140).
{uses "triple_ratchet_spec"}[] satisfies full messaging security
combining {uses "triple_ratchet_authenticity"}[] and
{uses "triple_ratchet_privacy"}[].
:::

:::theorem "triple_ratchet_verify" (parent := "secure_messaging")
_Verify Triple Ratchet protocol_ (\#135).
End-to-end verification that {uses "triple_ratchet_spec"}[] satisfies
{uses "triple_ratchet_correctness"}[],
{uses "triple_ratchet_authenticity"}[], and
{uses "triple_ratchet_privacy"}[].
:::

# SCKA Messaging (issues \#17, \#120, \#142–148)

SCKA-based messaging ({Informal.citet SCKA25}[]) adapts the secure messaging framework to
bandwidth-constrained settings using Sparse Continuous Key Agreement.

:::definition "scka_messaging_scheme" (parent := "secure_messaging")
_SCKA messaging scheme_ (\#142, {Informal.citet SCKA25}[]).
Specification of the SCKA-based messaging scheme.
{uses "scka_protocol_scheme"}[]
{uses "fs_aead_scheme"}[]
:::

:::definition "scka_messaging_spec" (parent := "secure_messaging")
_SCKA messaging protocol_ (\#144, {Informal.citet SCKA25}[]).
Full specification of the SCKA-based messaging protocol.
{uses "scka_messaging_scheme"}[] defines the scheme.
:::

:::theorem "scka_messaging_correctness" (parent := "secure_messaging")
_Correctness of SCKA messaging_ (\#145).
{uses "scka_messaging_spec"}[] satisfies messaging correctness.
:::

:::theorem "scka_messaging_authenticity" (parent := "secure_messaging")
_Authenticity of SCKA messaging_ (\#146).
{uses "scka_messaging_spec"}[] satisfies messaging authenticity.
:::

:::theorem "scka_messaging_privacy" (parent := "secure_messaging")
_Privacy of SCKA messaging_ (\#147).
{uses "scka_messaging_spec"}[] satisfies messaging privacy.
:::

:::theorem "scka_messaging_security" (parent := "secure_messaging")
_Security of SCKA messaging_ (\#148).
{uses "scka_messaging_spec"}[] satisfies full messaging security
combining {uses "scka_messaging_authenticity"}[] and
{uses "scka_messaging_privacy"}[].
:::

:::theorem "scka_messaging_verify" (parent := "secure_messaging")
_Verify SCKA messaging protocol_ (\#143).
End-to-end verification that {uses "scka_messaging_spec"}[] satisfies
{uses "scka_messaging_correctness"}[],
{uses "scka_messaging_authenticity"}[], and
{uses "scka_messaging_privacy"}[].
:::
