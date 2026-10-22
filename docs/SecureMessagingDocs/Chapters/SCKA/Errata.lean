import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Bibliography

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Errata" =>
%%%
tag := "scka-errata"
htmlSplit := .never
%%%

During formalization, we found the following issues in {Informal.citet SCKA25}[].
Errata 1–3 concern Opp-BiKEM-CKA and errata 4–6 concern Opp-UniKEM-CKA.
The pseudocode in each {bpref "opp_bikem_cka_spec"}[Opp-BiKEM] and
{bpref "opp_unikem_cka_spec"}[Opp-UniKEM] protocol definition marks the corrections with boxes.
The Lean implementations record them in the module docstrings of
`SecureMessaging/SCKA/OppBiKEM/Construction.lean` and `SecureMessaging/SCKA/OppUniKEM/Construction.lean`.
Line numbers refer to the paper's figures.

::::erratum "1" "Opp-BiKEM sending is blocked under the strict failure convention" (scope := "Opp-BiKEM-CKA, Figures 17–18")

In Figures 17–18, $`\CKASend{P}` can reach line 19, $`\chunk\gets\Encode(\ct_P,\ich)`,
with $`\ct_P=\bot`, where $`P` stands for either $`\A` or $`\B`.
This state occurs in normal honest runs.

The paper's §2 notational convention says that a failing statement aborts the
algorithm and discards its state changes. Under this convention, $`\Encode(\bot,\cdot)` fails.
The send aborts, as does the $`\mathsf{SM}\text{-}\mathsf{Send}\text{-}P` call that invokes it.
A party cannot send any message while it waits for its peer's encapsulation key.

In Figure 17, $`\CKASend{\A}`, lines 13–19 read as follows.
Figure 18, $`\CKASend{\B}`, is symmetric.

$$`\begin{array}{rl}
{\scriptstyle 13} & \mathsf{else\ if}\;\neg\ACK[\tres{\A}].\ctxtrec\;\pthen \pcomment{\ct_\A\text{ not yet received by }\B} \\
{\scriptstyle 14} & \quad\pif\;\ct_\A=\bot\wedge\ACK[\tres{\A}].\ekrec\;\pthen \\
{\scriptstyle 15} & \qquad t_{I_\A}\gets\tres{\A},\quad\ich\gets0 \\
{\scriptstyle 16} & \qquad(\ct_\A,I_\A)\sample\mathsf{Enc}(\mathsf{EK}_\B[\tres{\A}]) \\
{\scriptstyle 17} & \quad\ich\gets\ich+1 \\
{\scriptstyle 18} & \quad b\gets1 \\
{\scriptstyle 19} & \quad\chunk\gets\Encode(\ct_\A,\ich) \pcomment{\ct_\A\text{ may still be }\bot\text{ here}}
\end{array}`

When execution reaches line 13 but line 14 does not hold, $`\ct_\A` is still $`\bot` at line 19.
B acknowledges A's key, but A does not yet decode B's key.

The parties send their encapsulation keys concurrently.
A's key can therefore arrive and receive an acknowledgement before A decodes B's key.
Under the strict §2 convention, line 16 fails in $`\CKASend{\A}`,
and A cannot send any secure-messaging message until it decodes $`\ek_\B`.
Figure 19, {bpref "opp_rkem_cka_spec"}[Opp-RKEM-CKA], has the same pattern in $`\CKASend{\A}` lines 13–21.

*Correction.* The {cellref "opp-bikem-shared-send"}[shared send] sends no chunk while the ciphertext is absent.

*Formalisation.* `OppBiKEM/Construction.lean` records this as correction 4 in its module docstring.

::::

::::erratum "2" "Opp-BiKEM public-key acknowledgements use the wrong indices" (scope := "Opp-BiKEM-CKA, Figures 17–18")

In Figures 17–18, Send line 21 sends the $`\ekrec` acknowledgement at the wrong epoch.
Rec line 8 also records it at the wrong epoch.
The following table gives the printed and corrected indices.

:::table +header (align := left)
*
  * Line
  * Printed
  * Corrected
*
  * Figure 17, $`\CKASend{\A}` line 21
  * $`\ACK[\treq{\A}+1].\ekrec`
  * $`\ACK[\treq{\A}-1].\ekrec`
*
  * Figure 17, $`\CKARec{\A}` line 8
  * $`\ACK[\treq{\B}-1].\ekrec\gets\mathsf{true}`
  * $`\ACK[\treq{\B}+1].\ekrec\gets\mathsf{true}`
*
  * Figure 18, $`\CKASend{\B}` line 21
  * $`\ACK[\treq{\B}-1].\ekrec`
  * $`\ACK[\treq{\B}+1].\ekrec`
*
  * Figure 18, $`\CKARec{\B}` line 8
  * $`\ACK[\treq{\A}+1].\ekrec\gets\mathsf{true}`
  * $`\ACK[\treq{\A}-1].\ekrec\gets\mathsf{true}`
:::

The corrected indices identify the entries set when a party decodes its peer's key:
$`\ACK[\treq{\A}-1].\ekrec` in Rec-A line 19 and $`\ACK[\treq{\B}+1].\ekrec` in Rec-B line 19.
The printed indices differ by two epochs, and with them, neither party learns that its first public key arrived.

*Correction.* The boxes in the {cellref "opp-bikem-shared-send"}[shared send] and {cellref "opp-bikem-shared-recv"}[shared receive] mark the corrected indices.

*Formalisation.* `OppBiKEM/Construction.lean` records them as correction 3 in its module docstring.

::::

::::erratum "3" "Opp-BiKEM variable typos in Send-B and Rec-A" (scope := "Opp-BiKEM-CKA, Figures 17–18")

In Figure 18, $`\CKASend{\B}`, lines 8, 9, and 13 use $`\tres{\A}`, which is absent from B's state.
The corrected variable is $`\boxed{\tres{\B}}`, as in lines 14–16.
The corrected expressions are $`\mathsf{DK}_\B[\tres{\B}-1]\gets\dk_\B`,
$`\neg\ACK[\tres{\B}-1].\ekrec`, and $`\neg\ACK[\tres{\B}].\ctxtrec`.

In Figure 17, $`\CKARec{\A}`, line 22 reads $`\ct_\A\gets\Decode(\Lch)`, which overwrites A's own ciphertext.
The corrected assignment is $`\boxed{\ct_\B}\gets\Decode(\Lch)`, as used in lines 23 and 27.

*Correction.* The boxes in the {cellref "opp-bikem-shared-send"}[shared send] and {cellref "opp-bikem-shared-recv"}[shared receive] mark the corrected variables.

*Formalisation.* `OppBiKEM/Construction.lean` records them as correction 1 in its module docstring.

::::

::::erratum "4" "Opp-UniKEM acknowledgements are recorded in the wrong epoch" (scope := "Opp-UniKEM-CKA, Figure 16")

Let $`t` be the receiver's epoch and $`(\chunk,\ack',t',b)` the received message.
In Figure 16, $`\CKARec{\A}` and $`\CKARec{\B}` end by copying the sender's acknowledgement,
regardless of $`t` after processing:

* $`\CKARec{\A}` executes $`\pif\;\ack'.\ekrec\;\pthen\;\ack.\ekrec\gets\mathsf{true}`.
* $`\CKARec{\B}` (lines 12–13) executes $`\pif\;\ack'.\ctrec\;\pthen\;\ack.\ctrec\gets\mathsf{true}`.

The acknowledgement belongs to epoch $`t'`.
When $`t\ne t'`, it marks the receiver's current payload as delivered although the peer did not receive it.

*Correction.* Record the acknowledgement only if $`t=t'` after processing:
$`\pif\;\ack'.\ekrec\wedge\boxed{t=t'}` in Rec-A and $`\pif\;\ack'.\ctrec\wedge\boxed{t=t'}` in Rec-B.
The boxes in {cellref "opp-unikem-rec-a"}[Rec-A] and {cellref "opp-unikem-rec-b"}[Rec-B] mark this guard.

*Formalisation.* `OppUniKEM/Construction.lean` implements it under "Acknowledgements" in its module docstring.

::::

::::erratum "5" "Opp-UniKEM Rec-B returns the receiver's epoch" (scope := "Opp-UniKEM-CKA, Figure 16")

$`\CKARec{\B}` (Figure 16, line 15) returns $`((\bot,\bot),\,t-1,\,\mathsf{st})`, where $`t` is B's epoch.
The matching-epoch condition (Figure 1, $`\mathsf{Receive}\text{-}P` line 4:
$`\mathsf{assert}\;t^{\mathrm{rcv}}_P=t^{\mathrm{snd}}_{\bar P}`) requires the sender's value.
$`\CKASend{\A}` computes that value as the message epoch minus one, $`t'-1`.
$`\CKARec{\A}` already returns $`t'-1`.

The two values differ when B is ahead of the message.
A sends $`\rho_1` in epoch $`t`, which the adversary withholds while epoch $`t` completes.
A then sends $`\rho_2` in epoch $`t+1`.
Delivering $`\rho_2` moves B to epoch $`t+1`.
Delivering $`\rho_1` afterwards makes B return $`t`, while $`\rho_1` was sent with $`t^{\mathrm{snd}}_\A=t-1`.
The correctness assertion fails.

*Correction.* Return $`\boxed{t'-1}`. The box in {cellref "opp-unikem-rec-b"}[Rec-B] marks the corrected value.

*Formalisation.* `OppUniKEM/Construction.lean` implements it under "Receiving epoch" in its module docstring.

::::

::::erratum "6" "Opp-UniKEM Rec-A's chunk guards and abort behaviour made explicit" (scope := "Opp-UniKEM-CKA, Figure 16")

The corrections to Figure 16's $`\CKARec{\A}` distinguish absent chunks,
incomplete decoding, and failure after decoding the online ciphertext $`\ctone`.
Both ciphertext-decoding branches require $`\chunk\ne\bot`.
If the message contains no chunk, A neither inserts $`\bot` into $`\Lch` nor attempts decoding.

If decoding is incomplete, A retains the received chunk in $`\Lch` and remains in the same epoch.
Acknowledgement processing continues only if $`t=t'` after processing,
with $`t` denoting A's epoch and $`t'` the message's epoch.
Incomplete decoding does not abort the receive.

After decoding a current-epoch $`\ctone`, A requires both $`\dkA` and $`\ctzero` to decapsulate.
If either input is absent, or decapsulation returns $`\bot`, the entire receive aborts under the paper's §2 failure convention.
The abort discards local state changes and skips acknowledgement processing.
Only successful decapsulation produces the epoch key, erases the epoch's secrets, and advances A to epoch $`t+1`.

*Correction.* The boxes in {cellref "opp-unikem-rec-a"}[Rec-A] mark these checks.

::::
