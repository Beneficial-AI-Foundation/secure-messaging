import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Protocol-Level Schemes" =>

Top-level protocol definitions that compose the lower-level primitives
into complete secure messaging systems.

# SCKA

SCKA generalizes CKA for bandwidth-constrained settings where key
agreement messages may be sent sparsely (\[SCKA25\]).

:::group "scka"
Sparse Continuous Key Agreement (SCKA).
:::

:::definition "scka_scheme" (parent := "scka")
_SCKA scheme_ (\[SCKA25\]).
Syntax, correctness, and security definitions for SCKA, extending
{uses "cka_scheme"}[] to bandwidth-constrained two-party settings
with {uses "on_off_kem_scheme"}[] as a building block.
:::

# Secure Messaging

Full secure messaging protocols combining all lower-level primitives.

:::group "secure_messaging"
Secure Messaging protocols.
:::

:::definition "double_ratchet" (parent := "secure_messaging")
_Double Ratchet protocol_ (\[ACD19\]).
Composition of {uses "cka_scheme"}[], {uses "fs_aead_scheme"}[], and
{uses "prf_prng_scheme"}[] into the Signal-style Double Ratchet
messaging protocol.
:::

:::definition "triple_ratchet" (parent := "secure_messaging")
_Triple Ratchet protocol_ (\[TR25\]).
Extension of the Double Ratchet incorporating
{uses "rkem_scheme"}[] for improved bandwidth efficiency
and hybrid post-quantum security.
{uses "double_ratchet"}[]
:::

:::definition "scka_messaging" (parent := "secure_messaging")
_SCKA-based messaging_ (\[SCKA25\]).
Secure messaging protocol using {uses "scka_scheme"}[] for
bandwidth-constrained two-party communication.
:::

# Cross-Cutting Concerns

:::definition "query_bounded_adversaries"
_Query-bounded adversaries and security predicates._
Structured adversary bounding (query-bounded, eventually PPT) and
security predicates of the form
$`\forall \mathcal{A},\; \text{IsBounded}(\mathcal{A}) \Rightarrow \text{Adv}(\mathcal{A}) \leq \varepsilon`.
:::
