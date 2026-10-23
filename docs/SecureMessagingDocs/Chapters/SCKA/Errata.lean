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

::::erratum "1" "Unhandled absent-ciphertext case" (scope := "Opp-BiKEM-CKA, Figures 17–18")

After correcting the acknowledgement indices (erratum 2), an honest run of Figures 17–18
can reach $`\CKASend{P}` line 19, $`\chunk\gets\Encode(\ct_P,\ich)`,
with $`\ct_P=\bot`, where $`P` stands for either $`\A` or $`\B`.

The consequences of failing to handle this case depend on the exact implementation of $`\Encode`/$`\Decode`.

If encoding non-existent data fails, per the paper's §2 notational convention,
the processing is aborted and state changes are discarded.
As a consequence, a party cannot send any message while it waits for its peer's encapsulation key.

Otherwise, if encoding/decoding absent data is handled gracefully, values for $`\ich` of real chunks will be non-consecutive,
which does not cause significant problems.
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

The parties send their encapsulation keys concurrently.
A's key can therefore be acknowledged while $`\ct_\A=\bot` and A still waits to decode B's key.
In this case, execution reaches line 13, skips lines 15–16, and reaches line 19 with $`\ct_\A=\bot`.

*Correction.* Guard lines 17–19 of Figures 17–18 with $`\boxed{\pif\;\ct_P\ne\bot}`.
While a party waits for its peer's key, its message carries only epochs and acknowledgements,
with $`\chunk=\bot` and $`b=\bot`, and $`\ich` is unchanged.
The box in the {cellref "opp-bikem-shared-send"}[shared send] marks this guard.

*Formalisation.* `OppBiKEM/Construction.lean` uses this guard, recorded as correction 4 in its module docstring.

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

* $`\CKARec{\A}` (lines 21–22) executes $`\pif\;\ack'.\ekrec\;\pthen\;\ack.\ekrec\gets\mathsf{true}`.
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

::::erratum "6" "Opp-UniKEM Rec-A: missing chunks and receive failures" (scope := "Opp-UniKEM-CKA, Figure 16")

In Figure 16, $`\CKARec{\A}` must distinguish waiting for more chunks from a failed decapsulation.

*Correction.* Within the current-epoch branch, require a chunk in both ciphertext branches:

$$`\begin{array}{rl}
{\scriptstyle 5} & \pif\;\ctzero=\bot\wedge b=0\wedge\boxed{\chunk\ne\bot}\;\pthen\;\cdots \\
{\scriptstyle 11} & \mathsf{else\ if}\;b=1\wedge\boxed{\chunk\ne\bot}\;\pthen\;\cdots
\end{array}`

If the chunk is absent, skip chunk insertion and decoding.
If decoding is incomplete, keep the chunk in $`\Lch` and stay in the same epoch.
Neither case aborts the receive. Continue to acknowledgement processing, subject to the epoch guard in erratum 4.

Once the online ciphertext $`\ctone` is decoded, check the decapsulation inputs and result:

$$`\begin{array}{rl}
{\scriptstyle\text{before }15} & \pif\;\dkA=\bot\vee\ctzero=\bot\;\pthen\;\mathsf{return}\;\bot \\
{\scriptstyle 15} & I_{\B}\gets\Decaps(\dkA,(\ctzero,\ctone)) \\
{\scriptstyle\text{after }15} & \pif\;I_{\B}=\bot\;\pthen\;\mathsf{return}\;\bot
\end{array}`

The boxes in {cellref "opp-unikem-rec-a"}[Rec-A] mark these checks.

*Formalisation.* `OppUniKEM/Construction.lean` records them under "Receive failure" in its module docstring.

::::
