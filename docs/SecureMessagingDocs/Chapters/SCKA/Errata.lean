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

::::gameCell "\\textsf{SCKA errata}" (kind := "errata")

*Erratum 1: Opp-BiKEM sending is blocked under the strict failure convention.*

In Figures 17–18, `CKA-Send-P` can reach line 19, `ch ← Encode(ct_P, i_ch)`,
with `ct_P = ⊥`, where `P` stands for either `A` or `B`.
This state occurs in normal honest runs.

The paper's §2 notational convention says that a failing statement aborts the
algorithm and discards its state changes. Under this convention, `Encode(⊥, ·)` fails.
The send aborts, as does the `SM-Send-P` call that invokes it.
A party cannot send any message while it waits for its peer's encapsulation key.

In Figure 17, `CKA-Send-A`, lines 13–19 read as follows.
Figure 18, `CKA-Send-B`, is symmetric.

```
13: elseif ¬ACK[t_res-A].ct-rec            / ct_A not yet received by B
14:   if ct_A = ⊥ ∧ ACK[t_res-A].ek-rec
15:     t_IA ← t_res-A; i_ch ← 0
16:     (ct_A, I_A) ← Enc(EK_B[t_res-A])
17:   i_ch += 1
18:   b ← 1
19:   ch ← Encode(ct_A, i_ch)               / ct_A may still be ⊥ here
```

When execution reaches line 13 but line 14 does not hold, `ct_A` is still `⊥` at line 19.
B acknowledges A's key, but A does not yet decode B's key.

The parties send their encapsulation keys concurrently.
A's key can therefore arrive and receive an acknowledgement before A decodes B's key.
Under the strict §2 convention, line 16 fails in `CKA-Send-A`,
and A cannot send any secure-messaging message until it decodes `ek_B`.
The {bpref "opp_bikem_cka_spec"}[shared send] of `OppBiKEM/Construction.lean` instead sends no chunk,
recorded as correction 4 in its module docstring.
Figure 19, {bpref "opp_rkem_cka_spec"}[Opp-RKEM-CKA], has the same pattern in `CKA-Send-A` lines 13–21.

*Erratum 2: Opp-BiKEM public-key acknowledgements use the wrong indices.*

In Figures 17–18, Send line 21 sends the `ek-rec` acknowledgement at the wrong epoch.
Rec line 8 also records it at the wrong epoch.
The following table gives the printed and corrected indices.

:::table +header (align := left)
*
  * Line
  * Printed
  * Corrected
*
  * Figure 17, `CKA-Send-A` line 21
  * `ACK[t_req-A + 1].ek-rec`
  * `ACK[t_req-A − 1].ek-rec`
*
  * Figure 17, `CKA-Rec-A` line 8
  * `ACK[t_req-B − 1].ek-rec ← true`
  * `ACK[t_req-B + 1].ek-rec ← true`
*
  * Figure 18, `CKA-Send-B` line 21
  * `ACK[t_req-B − 1].ek-rec`
  * `ACK[t_req-B + 1].ek-rec`
*
  * Figure 18, `CKA-Rec-B` line 8
  * `ACK[t_req-A + 1].ek-rec ← true`
  * `ACK[t_req-A − 1].ek-rec ← true`
:::

The corrected indices identify the entries set when a party decodes its peer's key:
`ACK[t_req-A − 1].ek-rec` in Rec-A line 19 and `ACK[t_req-B + 1].ek-rec` in Rec-B line 19.
The printed indices differ by two epochs, and with them, neither party learns that its first public key arrived.
The boxes in the {bpref "opp_bikem_cka_spec"}[shared send and receive] mark the corrected indices,
and `OppBiKEM/Construction.lean` records them as correction 3 in its module docstring.

*Erratum 3: Opp-BiKEM variable typos in Send-B and Rec-A.*

In Figure 18, `CKA-Send-B`, lines 8, 9, and 13 use `t_res-A`, which is absent from B's state.
The corrected variable is $`\boxed{t_{\mathrm{res}\text{-}B}}`, as in lines 14–16.
The corrected expressions are `DK_B[t_res-B − 1] ← dk_B`, `¬ACK[t_res-B − 1].ek-rec`, and `¬ACK[t_res-B].ct-rec`.

In Figure 17, `CKA-Rec-A`, line 22 reads `ct_A ← Decode(L_ch)`, which overwrites A's own ciphertext.
The corrected assignment is `ct_B ← Decode(L_ch)`, with $`\boxed{\mathit{ct}_B}`, as used in lines 23 and 27.
The boxes in the {bpref "opp_bikem_cka_spec"}[shared send and receive] mark the corrected variables,
and `OppBiKEM/Construction.lean` records them as correction 1 in its module docstring.

*Erratum 4: Opp-UniKEM acknowledgements are recorded in the wrong epoch.*

Let `t` be the receiver's epoch and `(ch, ack', t', b)` the received message.
In Figure 16, `CKA-Rec-A` and `CKA-Rec-B` end by copying the sender's acknowledgement,
regardless of `t` after processing:

* `CKA-Rec-A` executes `if ack'.ek-rec then ack.ek-rec ← true`.
* `CKA-Rec-B` (lines 12–13) executes `if ack'.ct0-rec then ack.ct0-rec ← true`.

The acknowledgement belongs to epoch `t'`.
When `t ≠ t'`, it marks the receiver's current payload as delivered although the peer did not receive it.

The correction is to record the acknowledgement only if $`t=t'` after processing:
`if ack'.ek-rec ∧ t = t'` in Rec-A and `if ack'.ct0-rec ∧ t = t'` in Rec-B.
The boxes in the {bpref "opp_unikem_cka_spec"}[receive algorithms] mark this guard,
and `OppUniKEM/Construction.lean` implements it under "Acknowledgements" in its module docstring.

*Erratum 5: Opp-UniKEM Rec-B returns the receiver's epoch.*

`CKA-Rec-B` (Figure 16, line 15) returns `((⊥, ⊥), t − 1, st)`, where `t` is B's epoch.
The matching-epoch condition (Figure 1, `Receive-P` line 4: `assert t_rcv_P = t_snd_P̄`) requires the sender's value.
`CKA-Send-A` computes that value as the message epoch minus one, `t' − 1`.
`CKA-Rec-A` already returns `t' − 1`.

The two values differ when B is ahead of the message.
A sends `ρ_1` in epoch `t`, which the adversary withholds while epoch `t` completes.
A then sends `ρ_2` in epoch `t + 1`.
Delivering `ρ_2` moves B to epoch `t + 1`.
Delivering `ρ_1` afterwards makes B return `t`, while `ρ_1` was sent with `t_snd_A = t − 1`.
The correctness assertion fails.

The correction is to return $`t'-1`.
The box in {bpref "opp_unikem_cka_spec"}[`Rec-B`] marks the corrected value,
and `OppUniKEM/Construction.lean` implements it under "Receiving epoch" in its module docstring.

*Erratum 6: Make Opp-UniKEM Rec-A's chunk guards and abort behavior explicit.*

The corrections to Figure 16's `CKA-Rec-A` distinguish absent chunks,
incomplete decoding, and failure after decoding the online ciphertext `ct_1`.
Both ciphertext-decoding branches require `ch ≠ ⊥`.
If the message contains no chunk, A neither inserts `⊥` into `L_ch` nor attempts decoding.

If decoding is incomplete, A retains the received chunk in `L_ch` and remains in the same epoch.
Acknowledgement processing continues only if `t = t'` after processing, with `t` denoting A's epoch and `t'` the message's epoch.
Incomplete decoding does not abort the receive.

After decoding a current-epoch `ct_1`, A requires both `dk_A` and `ct_0` to decapsulate.
If either input is absent, or decapsulation returns `⊥`, the entire receive aborts under the paper's §2 failure convention.
The abort discards local state changes and skips acknowledgement processing.
Only successful decapsulation produces the epoch key, erases the epoch's secrets, and advances A to epoch `t + 1`.
The boxes in {bpref "opp_unikem_cka_spec"}[`Rec-A`] mark these checks.

::::
