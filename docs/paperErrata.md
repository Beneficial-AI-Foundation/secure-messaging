# A list of problems found in the SCKA paper
In the course of our formalization work, we have found a number of small problems in the paper.
Here we enumerate all of them (so that they can be corrected in the paper itself).

## 1. Sending is blocked unnecessarily (if applying the notational convention strictly)

In Opp-BiKEM-CKA (Figs. 17–18 of [SCKA](https://eprint.iacr.org/2025/2267.pdf)), with `P` standing for either `A` or `B`, `CKA-Send-P` can reach line 19, `ch ← Encode(ct_P, i_ch)`, with `ct_P = ⊥`. This happens in normal honest runs. It is not an edge case.

Read with the paper's own convention (§2, *Notational conventions*: a failing statement aborts the algorithm and discards its state changes), `Encode(⊥, ·)` fails. The send therefore aborts, and so does the `SM-Send-P` that calls it. While a party waits for its peer's encapsulation key, it cannot send at all. That defeats the purpose of opportunistic sending.

## Where

Fig. 17, `CKA-Send-A`, lines 13–19 (Fig. 18 `CKA-Send-B` is symmetric):

```text
13: elseif ¬ACK[t_res-A].ct-rec            / ct_A not yet received by B
14:   if ct_A = ⊥ ∧ ACK[t_res-A].ek-rec
15:     t_IA ← t_res-A; i_ch ← 0
16:     (ct_A, I_A) ← Enc(EK_B[t_res-A])
17:   i_ch += 1
18:   b ← 1
19:   ch ← Encode(ct_A, i_ch)               / ct_A may still be ⊥ here
```

When line 13 holds but line 14 does not (B has acknowledged A's key, but A has not yet decoded B's key), `ct_A` is still ⊥ at line 19.

Fig. 19 (Opp-RKEM-CKA, `CKA-Send-A`, lines 13–21) has the same pattern, with an extra conjunct in its line 14.

Fig. 16 (Opp-UniKEM-CKA) does not have this problem. It guards its online-ciphertext branch with `elseif ek_A ≠ ⊥`.

## The state occurs in honest runs

The two parties send their encapsulation keys concurrently, and neither waits for the other: that is the point of opportunistic sending. So nothing prevents A's key from being delivered and acknowledged before A has decoded B's key, which is exactly the state above.

A concrete trace from initialization, with every message delivered once and in order. Let `n ≥ 2` be the number of chunks needed to decode an encapsulation key.

Initially (`CKA-Init-A`, `CKA-Init-B`), A has `t_res-A = −1` and `t_req-A = 0`, B has `t_res-B = 0` and `t_req-B = −1`, and both have `ACK[−1].ct-rec = ACK[0].ct-rec = true`.

1. **A sends `n` messages.** Send-A line 4 holds, so A sets `t_res-A = 1` and generates `ek_A` for epoch 2. `ACK[2].ek-rec` is false (passes the guard at line 9) so every message carries a chunk of `ek_A`.
2. **B receives them.** The first one moves `t_req-B` to 1 (Rec-B lines 11–12). After the `n`-th message, B decodes `ek_A`, stores it as `EK_A[2]` and sets `ACK[2].ek-rec` (Rec-B lines 18–19).
3. **B sends one message.** Send-B line 4 holds, so B sets `t_res-B = 2` and generates `ek_B` for epoch 1. `ACK[1].ek-rec` is false, so by line 9 the message carries the first chunk of `ek_B`. By line 21 it also carries the acknowledgement `ACK[t_req-B + 1].ek-rec = ACK[2].ek-rec = true`.
4. **A receives it.** A records the acknowledgement as `ACK[2].ek-rec` (Rec-A line 8) and moves `t_req-A` to 2 (lines 11–12). It stores the chunk of `ek_B` (lines 13–15), but one chunk is not enough to decode, so `ACK[1].ek-rec` stays false.
5. **A sends.** In Fig. 17:
   - line 4 is false, because `ACK[1].ct-rec` is false, so no new key pair is generated;
   - line 9 is false, because `ACK[2].ek-rec` holds (B has `ek_A`);
   - line 13 is true, because `ACK[1].ct-rec` is false (B has not received `ct_A`);
   - line 14 is false, because `ACK[1].ek-rec` (A's own receipt of `ek_B`, set by Rec-A line 19) is false.

   So lines 17–19 run with `ct_A = ⊥`.

The same trace with the roles swapped (B sends first) puts B in this state in Fig. 18.

The trace uses the corrected indices from errata 2 (ek-acknowledgement indices) and 3 (Send-B typos) below. With the printed indices, the acknowledgement sent in step 3 is `ACK[t_req-B − 1].ek-rec = ACK[0].ek-rec`, which is never set, so A never learns that B has `ek_A`.

## Consequences

- **Strict reading (the §2 convention):**
  - `CKA-Send-A` fails, so `SM-Send-A` (Fig. 2, line 1) fails.
  - A cannot send any secure-messaging message until it decodes `ek_B`.
  - In the trace above, this is A's send in step 5.
- **Lenient reading (`Encode(⊥, ·) = ⊥`):**
  - The message carries `(ch = ⊥, b = 1)`.
  - The receiver then runs `L_ch ∪← {⊥}` (Rec line 21), which needs its own unstated convention (`L ∪ {⊥} = L`).
  - Line 17 increments `i_ch` for no chunk. This is harmless only because line 15 resets it later.

The intended behaviour is clearly "send no ciphertext chunk while waiting", but the figures don't say so, and they conflict with the paper's own failure convention.

## How our formalisation handles it

`SecureMessaging/SCKA/OppBiKEM/Construction.lean` takes the lenient reading:
- `sendWith` sets `ch? := ct.map (…)` with `bit? := some 1` and still increments `ich`. A code comment says: "Waiting for the peer's public key can legitimately leave ct absent."
- `insertChunkAndDecode` treats an absent chunk as a no-op on the receiver side.

Elsewhere, the same file follows the strict convention: `return none` for a missing `ek` before `Encode` (line 12), and for a missing peer key before `Enc` (line 16). This deviation from the convention is deliberate but is **not** in the module doc's list of "corrections wrt the paper".

## Proposed resolution

**Paper:**
- We suggest adding guard lines 17–19 of Figs. 17–18, and lines 19–21 of Fig. 19, with `if ct_P ≠ ⊥`, in the style of Fig. 16's `elseif ek_A ≠ ⊥`. While waiting, the message then carries only epochs and acknowledgements (`ch = ⊥`, `b = ⊥`), and the receiver never sees `(⊥, b = 1)`.

**Repo:**
Keep the current encoding (`bit = some 1`, `ich` incremented) and revisit once we hear back from the authors of the paper.

## 2. Public-key acknowledgements use the wrong indices

In Opp-BiKEM-CKA (Figs. 17–18), the `ek-rec` acknowledgement is sent (Send line 21) and recorded (Rec line 8) at the wrong epoch:

| Line | Printed | Corrected |
|---|---|---|
| Fig. 17, `CKA-Send-A` line 21 | `ACK[t_req-A + 1].ek-rec` | `ACK[t_req-A − 1].ek-rec` |
| Fig. 17, `CKA-Rec-A` line 8 | `ACK[t_req-B − 1].ek-rec ← true` | `ACK[t_req-B + 1].ek-rec ← true` |
| Fig. 18, `CKA-Send-B` line 21 | `ACK[t_req-B − 1].ek-rec` | `ACK[t_req-B + 1].ek-rec` |
| Fig. 18, `CKA-Rec-B` line 8 | `ACK[t_req-A + 1].ek-rec ← true` | `ACK[t_req-A − 1].ek-rec ← true` |

The corrected indices are the entries set when a party decodes its peer's key: `ACK[t_req-A − 1].ek-rec` (Rec-A line 19) and `ACK[t_req-B + 1].ek-rec` (Rec-B line 19). The printed indices are two epochs off.

With the printed indices, neither party learns that its first public key was received. A trace from initialization, with every message delivered once and in order. Let `n ≥ 1` be the number of chunks needed to decode an encapsulation key. Send-B is read with the variable fix of erratum 3.

Initially, A has `t_res-A = −1` and `t_req-A = 0`, B has `t_res-B = 0` and `t_req-B = −1`, both have `ACK[−1].ct-rec = ACK[0].ct-rec = true`, and every `ek-rec` entry is false.

1. **A sends `n` messages.** Send-A line 4 holds, so A sets `t_res-A = 1` and generates `ek_A` for epoch 2. `ACK[2].ek-rec` is false, so each message carries a chunk of `ek_A` (line 9).
2. **B receives them.** The first one moves `t_req-B` to 1 (Rec-B lines 11–12). After the `n`-th, B decodes `ek_A` and sets `ACK[2].ek-rec` (Rec-B line 19).
3. **B sends `n` messages.** Send-B line 4 holds, so B sets `t_res-B = 2` and generates `ek_B` for epoch 1. Each message carries a chunk of `ek_B`. Line 21 acknowledges `ACK[t_req-B − 1].ek-rec = ACK[0].ek-rec`, which is false; the entry B just set is `ACK[2]`.
4. **A receives them.** Rec-A line 8 records nothing. The first message moves `t_req-A` to 2. After the `n`-th, A decodes `ek_B` and sets `ACK[1].ek-rec` (line 19). `ACK[2].ek-rec` is still false, so A keeps `ek_A` (lines 31–32).
5. **A sends.** Line 4 is false (`ek_A ≠ ⊥`) and line 9 is true (`ACK[2].ek-rec` is false), so A resends a chunk of `ek_A`. Line 21 acknowledges `ACK[t_req-A + 1].ek-rec = ACK[3].ek-rec`, which is false; the entry A just set is `ACK[1]`.
6. **B receives it and sends.** Rec-B line 8 records nothing, so B's `ACK[1].ek-rec` stays false. B keeps `ek_B` (lines 31–32) and resends a chunk of `ek_B`, again acknowledging `ACK[0].ek-rec`.

Steps 5–6 repeat forever:
- A leaves line 9 only once `ACK[2].ek-rec` holds. Rec-A line 19 sets only odd entries (`t_req-A` is even), and line 8 sets `ACK[t_req-B − 1]`, which is `ACK[2]` only once `t_req-B = 3`. That needs A to advance to `t_res-A = 3` (Send-A line 4), which needs `ek_A = ⊥`, which needs `ACK[2].ek-rec` (Rec-A lines 31–32).
- B leaves line 9 only once `ACK[1].ek-rec` holds. Rec-B line 19 sets only even entries (`t_req-B` is odd), and line 8 sets `ACK[t_req-A + 1]`, which is `ACK[1]` only for messages A sent with `t_req-A = 0`. A sent those before decoding `ek_B`, so their bit is false.

Neither party reaches the ciphertext branch (line 13), so no key is ever established. With the corrected indices, step 3 acknowledges `ACK[2]` and step 5 acknowledges `ACK[1]`, and the run proceeds.

`OppBiKEM/Construction.lean` uses the corrected indices (correction 3 in its module docstring).

## 3. Variable typos in Send-B and Rec-A

- Fig. 18, `CKA-Send-B`, lines 8, 9 and 13 use `t_res-A`, which is not in B's state. They should use `t_res-B`, as lines 14–16 do: `DK_B[t_res-B − 1] ← dk_B`, `¬ACK[t_res-B − 1].ek-rec`, `¬ACK[t_res-B].ct-rec`.
- Fig. 17, `CKA-Rec-A`, line 22 reads `ct_A ← Decode(L_ch)`, which overwrites A's own ciphertext. It should be `ct_B ← Decode(L_ch)`, as lines 23 and 27 use `ct_B`.

`OppBiKEM/Construction.lean` uses the corrected variables (correction 1 in its module docstring).

## 4. Opp-UniKEM acknowledgements are recorded in the wrong epoch

In Opp-UniKEM-CKA (Fig. 16), let `t` be the receiver's epoch and `(ch, ack', t', b)` the received message. `CKA-Rec-A` and `CKA-Rec-B` end by copying the sender's acknowledgement, whatever `t` is after processing:

- `CKA-Rec-A`: `if ack'.ek-rec then ack.ek-rec ← true`
- `CKA-Rec-B` (lines 12–13): `if ack'.ct0-rec then ack.ct0-rec ← true`

The acknowledgement belongs to epoch `t'`. When `t ≠ t'`, it marks the receiver's current payload as delivered although the peer never received it.

This happens in honest runs with in-order delivery. Every `ct_1` chunk B sends carries `ack.ek-rec = true`, since B sends `ct_1` only once it has `ek_A`. When A decodes `ct_1`, it moves to epoch `t + 1` and resets `ack`, and the final step then sets `ack.ek-rec` for epoch `t + 1`. A generates a fresh `ek_A` on its next send but, with `ack.ek-rec` already true, never sends a chunk of it. B never obtains `ek_A` and never runs `Enc.On`, so no key is established after the first epoch.

With delayed delivery, a stale message (`t' < t`) can likewise mark the current `ek_A` (Rec-A) or `ct_0` (Rec-B) as received.

**Correction:** record the acknowledgement only if `t = t'` after processing: `if ack'.ek-rec ∧ t = t'` and `if ack'.ct0-rec ∧ t = t'`.

`OppUniKEM/Construction.lean` implements this ("Acknowledgements" in its module docstring).

## 5. Opp-UniKEM `CKA-Rec-B` returns the receiver's epoch

`CKA-Rec-B` (Fig. 16, line 15) returns `((⊥, ⊥), t − 1, st)`, where `t` is B's epoch. The matching-epoch condition (Fig. 1, `Receive-P` line 4: `assert t_rcv_P = t_snd_P̄`) requires the sender's value, which `CKA-Send-A` computes as the message epoch minus one, `t' − 1`. `CKA-Rec-A` already returns `t' − 1`.

The two differ when B is ahead of the message. A sends `ρ_1` in epoch `t`, which the adversary withholds while epoch `t` completes; A then sends `ρ_2` in epoch `t + 1`. Delivering `ρ_2` moves B to epoch `t + 1`; delivering `ρ_1` afterwards makes B return `t`, while `ρ_1` was sent with `t_snd_A = t − 1`. The correctness assertion fails.

**Correction:** return `t' − 1`.

`OppUniKEM/Construction.lean` implements this ("Receiving epoch" in its module docstring).