import Verso
import VersoManual
import VersoBlueprint
import SecureMessaging.CKA.Defs
import SecureMessaging.CKA.FromDDH.Construction
import SecureMessaging.CKA.FromDDH.Correctness

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Continuous Key Agreement" =>

CKA provides ongoing key agreement between two parties who alternate
sending and receiving messages, producing fresh shared keys at each epoch.

References:
\[ACD19\] Alwen, Coretti, Dodis. _The Double Ratchet_, 2019. Section 4.1.
\[TR25\] Dodis, Jost, Katsumata, Prest, Schmidt. _Triple Ratchet_, 2025.

:::group "cka"
Continuous Key Agreement (CKA).
:::

# Scheme Definition

:::definition "cka_scheme" (parent := "cka") (lean := "CKAScheme")
A _CKA scheme_ consists of algorithms $`(\text{Init}, \text{Send}, \text{Recv})` where
$`\text{Init}` produces initial states for both parties, $`\text{Send}` outputs a
message and shared key from the sender's state, and $`\text{Recv}` recovers the
shared key from the receiver's state and a received message
(Definition 6, \[ACD19\]; Definition 2.12, \[TR25\]).
:::

:::definition "cka_correctness_exp" (parent := "cka") (lean := "CKAScheme.correctnessExp")
_Correctness experiment._ For every valid sequence of Send/Recv operations,
the shared keys produced by sender and receiver agree.
{uses "cka_scheme"}[] defines the scheme under test.
:::

:::definition "cka_security_exp" (parent := "cka") (lean := "CKAScheme.securityExp")
_Security experiment_ $`\text{Exp}^{\text{cka}}_{\Pi, \mathcal{A}}`.
The adversary controls the send/receive schedule and has access to corruption,
randomness-leakage, and challenge oracles. Security requires that challenge keys
are indistinguishable from random under appropriate trivial-win conditions
(Definition 7, \[ACD19\]; Definition 2.12, \[TR25\]).
{uses "cka_scheme"}[] defines the scheme under attack.
:::

:::definition "cka_security_advantage" (parent := "cka") (lean := "CKAScheme.ckaGuessAdvantage")
_Advantage._ $`\text{Adv}^{\text{cka}}_{\Pi}(\mathcal{A}, \text{gp}) = |2\Pr[\text{Exp}^{\text{cka}}_{\Pi,\mathcal{A},\text{gp}} = 1] - 1|`.
{uses "cka_security_exp"}[] defines the experiment.
:::

:::theorem "cka_advantage_equivalence" (parent := "cka") (lean := "CKAScheme.ckaGuessAdvantage_eq_ckaDistAdvantage_div_two")
The CKA guess advantage equals half the distinguishing advantage:
$`\text{guessAdv} = \text{distAdv} / 2`.
{uses "cka_security_advantage"}[] defines the advantage.
:::

# CKA-from-KEM (issues \#2–5)

:::definition "cka_from_kem_spec" (parent := "cka")
_CKA-from-KEM_ (\#3). Construction of a CKA scheme from a Key Encapsulation
Mechanism: each send encapsulates a fresh key, each receive decapsulates
(Section 4.1.2, \[ACD19\]).
{uses "cka_scheme"}[] is the target interface.
:::

:::theorem "cka_from_kem_correctness" (parent := "cka")
_Correctness of CKA-from-KEM_ (\#4). The KEM-based construction satisfies
{uses "cka_correctness_exp"}[].
:::

:::theorem "cka_from_kem_security" (parent := "cka")
_Security of CKA-from-KEM_ (\#5, Theorem 2, \[ACD19\]).
The KEM-based CKA is secure in the sense of {uses "cka_security_exp"}[]
under standard KEM security assumptions.
:::

# CKA-from-DDH (issues \#7, \#10)

:::definition "cka_from_ddh_spec" (parent := "cka") (lean := "ddhCKA")
_CKA-from-DDH._ Construction of a CKA scheme using
Diffie–Hellman key exchanges in a cyclic group
(Section 4.1.2, \[ACD19\]).
{uses "cka_scheme"}[] is the target interface.
:::

:::theorem "cka_from_ddh_correctness" (parent := "cka") (lean := "ddhCKA.correctness")
_Correctness of CKA-from-DDH._ The DDH-based construction satisfies
{uses "cka_correctness_exp"}[].
:::

:::theorem "cka_from_ddh_security" (parent := "cka")
_Security of CKA-from-DDH_ (\#10, Theorem 3, \[ACD19\]).
The DDH-based CKA is secure in the sense of {uses "cka_security_exp"}[]
under the DDH assumption.
:::

# CKA-from-LWE (issues \#11–14)

:::definition "cka_from_lwe_spec" (parent := "cka")
_CKA-from-LWE_ (\#12). Post-quantum construction of a CKA scheme
from lattice-based key exchange
(Section 4.1.2, \[ACD19\]).
{uses "cka_scheme"}[] is the target interface.
:::

:::theorem "cka_from_lwe_correctness" (parent := "cka")
_Correctness of CKA-from-LWE_ (\#13). The LWE-based construction satisfies
{uses "cka_correctness_exp"}[].
:::

:::theorem "cka_from_lwe_security" (parent := "cka")
_Security of CKA-from-LWE_ (\#14, Theorem 4, \[ACD19\]).
The LWE-based CKA is secure in the sense of {uses "cka_security_exp"}[]
under the LWE assumption.
:::
