import Verso
import VersoManual
import VersoBlueprint
import SecureMessaging.AEAD.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Authenticated Encryption with Associated Data" =>

AEAD provides both confidentiality and integrity for messages,
with additional unencrypted associated data authenticated alongside the ciphertext.

References:
\[ACD19\] Alwen, Coretti, Dodis. _The Double Ratchet_, 2019.
\[BN00\] Bellare, Namprempre. _Authenticated Encryption_, 2000.
\[NIST-SP800-38D\] NIST. _GCM_, 2007.

:::group "aead"
Authenticated Encryption with Associated Data (AEAD).
:::

# Scheme Definition

:::definition "aead_scheme" (parent := "aead") (lean := "AEADScheme")
An *AEAD scheme* $`\Pi = (\text{KeyGen}, \text{Enc}, \text{Dec})` over spaces
$`(\mathcal{M}, \mathcal{AD}, \mathcal{K}, \mathcal{C})` consists of a probabilistic
key-generation algorithm and deterministic encryption/decryption algorithms
(Definition 1, \[ACD19\]).
:::

:::definition "aead_correctness" (parent := "aead") (lean := "AEADScheme.Correct")
_Correctness._ For all $`k \in \mathcal{K}`, $`a \in \mathcal{AD}`, $`m \in \mathcal{M}`:
$$`\text{Dec}(k, a, \text{Enc}(k, a, m)) = m`
{uses "aead_scheme"}[] is correct when decryption inverts encryption.
:::

:::definition "aead_security_exp" (parent := "aead") (lean := "AEADScheme.securityExp")
_Experiment_ $`\text{Exp}^{\text{ot-cca}}_{\Pi, \mathcal{A}}`.
The one-time CCA security experiment samples a key and challenge bit,
gives the adversary access to encryption and decryption oracles,
and outputs whether the adversary's guess matches the bit
(Definition 2, \[ACD19\]).
{uses "aead_scheme"}[] defines the scheme under attack.
:::

:::theorem "aead_advantage_equivalence" (parent := "aead") (lean := "AEADScheme.guessAdvantage_eq_distAdvantage_div_two")
The guess-based advantage equals half the distinguishing advantage:
$$`\text{Adv}^{\text{ot-cca}}_{\Pi}(\mathcal{A}) = \tfrac{1}{2}\,\text{Adv}^{\text{dist}}_{\Pi}(\mathcal{A})`
{uses "aead_security_exp"}[] defines the security experiment.
:::

# AEAD-AES-GCM (issues \#20–23)

:::definition "aead_aes_gcm_spec" (parent := "aead")
_AEAD-AES-GCM_ (\#21). Construction of an AEAD scheme from AES-GCM as specified
in NIST SP 800-38D.
{uses "aead_scheme"}[] is the target interface.
:::

:::theorem "aead_aes_gcm_correctness" (parent := "aead")
_Correctness of AEAD-AES-GCM_ (\#22). The AES-GCM construction satisfies
{uses "aead_correctness"}[].
:::

:::theorem "aead_aes_gcm_security" (parent := "aead")
_Security of AEAD-AES-GCM_ (\#23). The AES-GCM construction is secure
in the sense of {uses "aead_security_exp"}[].
:::

# AEAD-Encrypt-then-MAC (issues \#19, \#24–26)

:::definition "aead_etm_spec" (parent := "aead")
_AEAD-Encrypt-then-MAC_ (\#24). Generic construction of an AEAD scheme from a
symmetric encryption scheme and a MAC via the Encrypt-then-MAC composition
(\[BN00\]).
{uses "aead_scheme"}[] is the target interface.
:::

:::theorem "aead_etm_correctness" (parent := "aead")
_Correctness of Encrypt-then-MAC_ (\#25). The EtM construction satisfies
{uses "aead_correctness"}[].
:::

:::theorem "aead_etm_security" (parent := "aead")
_Security of Encrypt-then-MAC_ (\#26). The EtM construction is secure
in the sense of {uses "aead_security_exp"}[].
:::
