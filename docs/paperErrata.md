# A list of problems found in the SCKA paper
In the course of our formalization work, we have found a number of (mostly small) problems in the paper.
Here we enumerate all of them (so that they could be corrected in the paper itself).

## 1. Due to the notational convention, sending is blocked unnecessarily

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

The trace uses the index corrections listed in `OppBiKEM/Construction.lean`: the Send-B typos (correction 1) and the ek-acknowledgement indices (correction 3). With the printed indices, the acknowledgement sent in step 3 is `ACK[t_req-B − 1].ek-rec = ACK[0].ek-rec`, which is never set, so A never learns that B has `ek_A`. That is a separate erratum.

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