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

# Forward-Secure AEAD

FS-AEAD extends AEAD with forward secrecy: past ciphertexts remain
confidential even if the current key is compromised
(Section 4.2, \[ACD19\]).

:::group "fs_aead"
Forward-Secure AEAD (FS-AEAD).
:::

:::definition "fs_aead_scheme" (parent := "fs_aead")
_FS-AEAD scheme_ (Definition 14, \[ACD19\]).
An FS-AEAD scheme augments {uses "aead_scheme"}[] with a state-evolving
encryption interface: each encryption updates the sender's state so that
old keys are erased.
:::

:::definition "fs_aead_construction" (parent := "fs_aead")
_FS-AEAD-from-AEAD-PRG._ Construction from an AEAD scheme and a
pseudorandom generator (Section 4.2, \[ACD19\]).
Each encryption step applies the PRG to the current key to derive the
message key and the next-epoch key.
{uses "fs_aead_scheme"}[] is the target interface.
:::

:::theorem "fs_aead_correctness" (parent := "fs_aead")
_Correctness of FS-AEAD construction._
{uses "fs_aead_construction"}[] satisfies FS-AEAD correctness.
:::

:::theorem "fs_aead_verify" (parent := "fs_aead")
_Verification of FS-AEAD construction._
End-to-end verification of {uses "fs_aead_construction"}[]
(Section 4.2, \[ACD19\]).
:::

:::theorem "fs_aead_security" (parent := "fs_aead")
_Security of FS-AEAD construction._
{uses "fs_aead_construction"}[] is FS-AEAD secure under the security of
the underlying AEAD and PRG.
{uses "aead_security_exp"}[]
:::

# PRF-PRNG

A PRF-PRNG is a stateful pseudorandom generator that produces
pseudorandom outputs from an evolving internal state
(Section 4.3, \[ACD19\]).

:::group "prf_prng"
Pseudorandom Function-Generator (PRF-PRNG).
:::

:::definition "prf_prng_scheme" (parent := "prf_prng")
_PRF-PRNG scheme_ (Section 4.3, \[ACD19\]).
A stateful pseudorandom generator with syntax and security definitions.
:::

:::definition "prf_prng_construction" (parent := "prf_prng")
_PRF-PRNG-from-PRP-PRG._ Construction from a pseudorandom permutation
and a pseudorandom generator (Section 4.3.2, \[ACD19\]).
{uses "prf_prng_scheme"}[] is the target interface.
:::

:::theorem "prf_prng_verify" (parent := "prf_prng")
_Verification of PRF-PRNG construction._
End-to-end verification of {uses "prf_prng_construction"}[]
(Section 4.3.2, \[ACD19\]).
:::

:::theorem "prf_prng_security" (parent := "prf_prng")
_Security of PRF-PRNG construction._
{uses "prf_prng_construction"}[] is PRF-PRNG secure under PRP and PRG
security.
:::

# On-Off KEM

An On-Off KEM generalizes standard KEMs to support both online
(interactive) and offline (non-interactive) encapsulation modes
(Definition 2.1, \[SCKA25\]).

:::group "on_off_kem"
Online-Offline Key Encapsulation Mechanism (On-Off KEM).
:::

:::definition "on_off_kem_scheme" (parent := "on_off_kem")
_On-Off KEM scheme_ (Definition 2.1, \[SCKA25\]).
Syntax, correctness, and security definitions for On-Off KEMs.
:::

:::definition "on_off_kem_from_ml_kem" (parent := "on_off_kem")
_On-Off-KEM-from-ML-KEM._ Construction from the ML-KEM
(Module Lattice KEM) standard, with correctness proof.
{uses "on_off_kem_scheme"}[] is the target interface.
:::

:::theorem "on_off_kem_from_ml_kem_security" (parent := "on_off_kem")
_Security of On-Off-KEM-from-ML-KEM._
{uses "on_off_kem_from_ml_kem"}[] is secure in the On-Off KEM sense.
:::

# RKEM

An RKEM provides key encapsulation with ratcheting: each operation
advances the state, providing forward secrecy and post-compromise security
(Section 5.1, \[TR25\]).

:::group "rkem"
Ratcheting Key Encapsulation Mechanism (RKEM).
:::

:::definition "rkem_scheme" (parent := "rkem")
_RKEM scheme_ (Section 5.1, \[TR25\]).
Syntax, correctness, and forward-security definitions for RKEMs.
:::

:::definition "rkem_from_ddh" (parent := "rkem")
_RKEM-from-DDH._ Construction from the DDH assumption
(Appendix 3, \[TR25\]).
{uses "rkem_scheme"}[] is the target interface.
:::
