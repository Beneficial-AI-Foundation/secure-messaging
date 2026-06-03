import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Higher-Level Primitives" =>

Building blocks that compose the base AEAD and CKA primitives into
richer cryptographic abstractions.

# Forward-Secure AEAD (issues \#27–32)

FS-AEAD extends AEAD with forward secrecy: past ciphertexts remain
confidential even if the current key is compromised
(Section 4.2, \[ACD19\]).

:::group "fs_aead"
Forward-Secure AEAD (FS-AEAD).
:::

:::definition "fs_aead_scheme" (parent := "fs_aead")
_FS-AEAD scheme_ (\#28, Definition 14, \[ACD19\]).
An FS-AEAD scheme augments {uses "aead_scheme"}[] with a state-evolving
encryption interface: each encryption updates the sender's state so that
old keys are erased.
:::

:::definition "fs_aead_construction" (parent := "fs_aead")
_FS-AEAD-from-AEAD-PRG_ (\#31). Construction from an AEAD scheme and a
pseudorandom generator (Section 4.2, \[ACD19\]).
Each encryption step applies the PRG to the current key to derive the
message key and the next-epoch key.
{uses "fs_aead_scheme"}[] is the target interface.
:::

:::theorem "fs_aead_correctness" (parent := "fs_aead")
_Correctness of FS-AEAD construction_ (\#29).
{uses "fs_aead_construction"}[] satisfies FS-AEAD correctness.
:::

:::theorem "fs_aead_security" (parent := "fs_aead")
_Security of FS-AEAD construction_ (\#32).
{uses "fs_aead_construction"}[] is FS-AEAD secure under the security of
the underlying AEAD and PRG.
{uses "aead_security_exp"}[]
:::

:::theorem "fs_aead_verify" (parent := "fs_aead")
_Verify FS-AEAD-from-AEAD-PRG construction_ (\#30).
End-to-end verification that {uses "fs_aead_construction"}[] satisfies
{uses "fs_aead_correctness"}[] and {uses "fs_aead_security"}[].
:::

# PRF-PRNG (issues \#33–37)

A PRF-PRNG is a stateful pseudorandom generator that produces
pseudorandom outputs from an evolving internal state
(Section 4.3, \[ACD19\]).

:::group "prf_prng"
Pseudorandom Function-Generator (PRF-PRNG).
:::

:::definition "prf_prng_scheme" (parent := "prf_prng")
_PRF-PRNG scheme_ (\#34, Section 4.3, \[ACD19\]).
A stateful pseudorandom generator with syntax and security definitions.
:::

:::definition "prf_prng_construction" (parent := "prf_prng")
_PRF-PRNG-from-PRP-PRG_ (\#36). Construction from a pseudorandom permutation
and a pseudorandom generator (Section 4.3.2, \[ACD19\]).
{uses "prf_prng_scheme"}[] is the target interface.
:::

:::theorem "prf_prng_security" (parent := "prf_prng")
_Security of PRF-PRNG construction_ (\#37).
{uses "prf_prng_construction"}[] is PRF-PRNG secure under PRP and PRG
security.
:::

:::theorem "prf_prng_verify" (parent := "prf_prng")
_Verify PRF-PRNG-from-PRP-PRG construction_ (\#35).
End-to-end verification that {uses "prf_prng_construction"}[] satisfies
{uses "prf_prng_security"}[].
:::

# On-Off KEM (issues \#39–42)

An On-Off KEM generalizes standard KEMs to support both online
(interactive) and offline (non-interactive) encapsulation modes
(Definition 2.1, \[SCKA25\]).

:::group "on_off_kem"
Online-Offline Key Encapsulation Mechanism (On-Off KEM).
:::

:::definition "on_off_kem_scheme" (parent := "on_off_kem")
_On-Off KEM scheme_ (\#40, Definition 2.1, \[SCKA25\]).
Syntax, correctness, and security definitions for On-Off KEMs.
:::

:::definition "on_off_kem_from_ml_kem" (parent := "on_off_kem")
_On-Off-KEM-from-ML-KEM_ (\#41). Construction from the ML-KEM
(Module Lattice KEM) standard.
{uses "on_off_kem_scheme"}[] is the target interface.
:::

:::theorem "on_off_kem_from_ml_kem_correctness" (parent := "on_off_kem")
_Correctness of On-Off-KEM-from-ML-KEM_ (\#41).
{uses "on_off_kem_from_ml_kem"}[] satisfies On-Off KEM correctness.
:::

:::theorem "on_off_kem_from_ml_kem_security" (parent := "on_off_kem")
_Security of On-Off-KEM-from-ML-KEM_ (\#42).
{uses "on_off_kem_from_ml_kem"}[] is secure in the On-Off KEM sense.
:::

# Erasure Codes (issues \#115–117)

Erasure codes enable recovery of data from a subset of encoded fragments,
providing redundancy against data loss.

:::group "erasure_codes"
Erasure Codes.
:::

:::definition "erasure_code_scheme" (parent := "erasure_codes")
_Erasure Code scheme_ (\#116).
Syntax and correctness definitions for erasure codes:
an encoding function that maps data to $`n` fragments such that
any $`k` suffice for recovery.
:::

:::definition "reed_solomon_spec" (parent := "erasure_codes")
_Reed-Solomon erasure code_ (\#117). Construction of an erasure code using
Reed-Solomon polynomial interpolation.
{uses "erasure_code_scheme"}[] is the target interface.
:::

:::theorem "reed_solomon_correctness" (parent := "erasure_codes")
_Correctness of Reed-Solomon erasure code_ (\#117).
{uses "reed_solomon_spec"}[] satisfies {uses "erasure_code_scheme"}[] correctness:
any $`k`-of-$`n` fragments suffice to recover the original data.
:::

# Cross-Cutting Concerns

:::definition "query_bounded_adversaries"
_Query-bounded adversaries and security predicates_ (\#59).
Structured adversary bounding (query-bounded, eventually PPT) and
security predicates of the form
$`\forall \mathcal{A},\; \text{IsBounded}(\mathcal{A}) \Rightarrow \text{Adv}(\mathcal{A}) \leq \varepsilon`.
:::
