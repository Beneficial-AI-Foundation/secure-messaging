# Opp-BiKEM correctness via the main invariant: a guided tour

This tutorial walks through the correctness proof of Opp-BiKEM-CKA on the branch
`opp-bikem-cka-correctness`. It is written to be read next to the Lean files. Links point to
`File.lean#Lline` and are relative to this file. The statements and notation are summarized in
the module docstring of
[`OppBiKEM/Correctness.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean).

The endpoint is
[`correctness_of_perfectKEM`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L253):
for a KEM with deterministic decapsulation that is perfectly correct, and for correct
public-key and ciphertext erasure codes, the SCKA correctness experiment returns `true` with
probability one, for every adversary. There is no bounded-slack assumption. No `sorry`; only
`propext`, `Classical.choice`, `Quot.sound`.

## 0. The shape of the argument in one paragraph

Fix an execution. For every epoch `e ≥ 1` the requester (A for even `e`, B for odd `e`) draws one
key pair and the responder encapsulates to it once. Record these samples in a *transcript*
`T : ℤ → EpochTranscript`. The *main invariant* says that one transcript is consistent with
everything either party holds: its retained material, every message it has recorded, its
chunk buffer, its acknowledgement sets, and its game key table. The invariant holds initially,
is preserved by every oracle query, and contains `s.correct = true`. The five game assertions
are corollaries of it. KEM correctness is used in exactly one place: the key a receiver emits
is the transcript's key for that epoch.

## 1. File map and reading order

| # | File | Role |
| --- | --- | --- |
| 0 | [`OppBiKEM/Correctness.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean) | summary: notation, results, where each proof lives |
| 1 | [`SCKA/Correctness/OracleSupport.lean`](../../SecureMessaging/SCKA/Correctness/OracleSupport.lean) | each game oracle as a pure state update, with support and distribution forms of each oracle run |
| 2 | [`OppBiKEM/Correctness/Transcript.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean) | `EpochTranscript`, `Transcript`, parities |
| 3 | [`OppBiKEM/Correctness/RecvSpec.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean) | `recv` as a decision tree |
| 4 | [`OppBiKEM/Correctness/SendFacts.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean) | support-level facts about one `send` |
| 5 | [`OppBiKEM/Correctness/RecvFacts.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvFacts.lean) | support-level facts about one `recv` |
| 6 | [`OppBiKEM/Correctness/MainInvariant.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean) | `MessageInv`, `PartyInv`, `GameInv`, prefix lemmas |
| 7 | [`MainInvariant/Init.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Init.lean) | initial state; `PerfectlyCorrect` to support-level correctness |
| 8 | [`MainInvariant/Send.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean) | the send step |
| 9 | [`MainInvariant/Recv.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean) | the receive step |
| 10 | [`MainInvariant/Game.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean) | one-step preservation with the oracle case split, lift to adversaries, final theorem |
| 11 | [`MainInvariant/SendTotal.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/SendTotal.lean) | honest sends are never rejected |
| 12 | [`KEM/CorrectnessError.lean`](../../SecureMessaging/KEM/CorrectnessError.lean) | `keypairFailure`: the KEM error conditioned on a key pair |
| 13 | [`SCKA/Correctness/Tracked.lean`](../../SecureMessaging/SCKA/Correctness/Tracked.lean) | scheme-generic tracked game: flag, invariant, `q · ε` bound |
| 14 | [`Quantitative/Core.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean) | the flag `kemFailure` and the potential `failurePotential` |
| 15 | [`Quantitative/SendDist.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendDist.lean) | `send` as `keygen >>= …` or `encaps >>= …` |
| 16 | [`Quantitative/RecvStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/RecvStep.lean) | non-send queries keep the score; invariant kept while the flag is down |
| 17 | [`Quantitative/SendStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean) | a send raises the expected score by at most `ε` |
| 18 | [`Quantitative/Main.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean) | proof outline of the quantitative bound; `correctness_failure_le`, `correctness_true_ge`, `ε = 0` corollary |

Read 0 for the statements and 6 for the invariant, then 10 to see how the invariant is used, then
8 and 9 for the proofs. Files 1 to 5 are infrastructure you can skim. Files 12 to 18 are the
quantitative layer (section 12); read the module docstring of 18 first (it is the proof
outline), then 14 and 17.

`SendFacts.lean` (`Acknowledgements.sendingHorizon`, `send_support_facts`, `SendProvenance` /
`send_provenance`, `send_ciphertextMessage_keyAck`, `send_advance_guard`) and `RecvFacts.lean`
(`recv_success_state_facts`, `recv_emitted_key_facts`, `recv_local_publicKey_eq_or_none`,
`recv_peerKeys_stable`, `recv_peerKeys_origin`) hold what the step proofs need from the
iteration files n1 to n14; the rest of those files is in the Git history before `8c66d28`.

## 2. Infrastructure: the oracles as pure updates

Each correctness-game oracle in `SCKA/Defs.lean` runs the scheme's local `send` or `recv`
and then updates the game state. `OracleSupport.lean` names those updates and restates each
oracle run in terms of them:

- [`applySendA`](../../SecureMessaging/SCKA/Correctness/OracleSupport.lean#L38) and
  [`applyRecvA`](../../SecureMessaging/SCKA/Correctness/OracleSupport.lean#L87) (and the `B`
  twins). Read them against `oracleSendA` and `oracleRecvA` in `Defs.lean`; the `correct` field
  carries the game's assertions verbatim.
- [`oracleSendA_run_cases`](../../SecureMessaging/SCKA/Correctness/OracleSupport.lean#L253) and
  [`oracleRecvA_run_cases`](../../SecureMessaging/SCKA/Correctness/OracleSupport.lean#L307):
  anything in the support of an oracle run is the no-op, a failed receive (which clears
  `correct`), or `applyX` of a local outcome. The invariant proofs use these:
  `gameInv_step_of` (section 10) and the receive cases of `Quantitative/RecvStep.lean`.
- [`oracleSendA_run_eq_sendAOutcome`](../../SecureMessaging/SCKA/Correctness/OracleSupport.lean#L389) with
  [`sendAOutcome`](../../SecureMessaging/SCKA/Correctness/OracleSupport.lean#L375): a send run as
  a computation, the local send followed by a pure outcome. The expected-value proofs of
  `Quantitative/SendStep.lean` and the totality proof of `SendTotal.lean` use these.

Downstream proofs speak about `applyX` and never unfold the `StateT` plumbing of the send and
receive oracles. There is no generic dispatch theorem over the five oracles: the case split
lives in `gameInv_step_of`, because the step needs a hypothesis on the pre-state (section 10).

## 3. The transcript

[`EpochTranscript`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L73) has
two data fields and three proofs:

```
keypair : Option (PK × SK)        -- the requester's key pair
enc     : Option (C × K)          -- the responder's ciphertext and key
keypair_mem, enc_mem              -- support membership of each sample
enc_keypair                       -- encapsulation requires the key pair
```

[`Transcript`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L87) is
`ℤ → EpochTranscript`, indexed by the construction's integer epochs; only epochs `≥ 1` are
ever populated. The two constructors used by the send step are
[`ofKeypair`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L102) and
[`setEnc`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L116).

Role parities are made explicit at
[`Role.reqParity`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L39) and
`Role.resParity`: A requests at even epochs and responds at odd ones, B the reverse. The simp
lemmas `Role.peer_reqParity` and `Role.peer_resParity` say the peer's parities are swapped.
Almost every parity argument in the proofs is the idiom

```
cases role <;> simp only [Role.offset, Role.reqParity, Role.resParity] at h ⊢ <;> omega
```

## 4. `recv` as a decision tree

In `Construction.lean`, `recv` is written with `let mut` and early `return`, which elaborates to a deeply nested term.
[`recvSpec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L46) is the same
function written as an explicit decision tree over three named pieces:

- [`recvAck`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L27): the
  acknowledgement sets after ingesting the message's two flags;
- [`recvReq`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L32): the requester
  epoch, advanced by two if the message is ahead;
- [`recvFinish`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L37): assembling
  the post-state and clearing acknowledged outgoing material.

[`recv_eq_recvSpec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L87) proves
the two agree. It is the one brute-force proof in the development: a uniform case split over
about two hundred leaves, each closed by `rfl`, and it needs a raised heartbeat budget. Every
later fact about a receive is read off `recvSpec` with one case split per named condition.

## 5. The main invariant

### 5.1 Message honesty

[`MessageInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L65) is what a
party guarantees about each message it has recorded in its outgoing table, relative to its
*current* state and the transcript. Read the fields in three groups.

- Epoch bookkeeping: `epoch` (the recorded sending epoch is the carried one),
  parities, `res_le` / `req_le` (carried epochs never exceed the current ones).
- Payload honesty: `pk_chunk` (a bit-0 chunk encodes the transcript's public key for the
  sender's key epoch `ρ.tRes + offset`), `ct_chunk` (a bit-1 chunk encodes the transcript's
  ciphertext for `ρ.tRes`), `no_chunk`.
- Flags and horizon: `ct_flag`, `ek_flag` (flags are backed by the sender's own sets),
  `bit1_acked`, and `horizon_mem` / `horizon_req`, which pin down what the advertised
  sending epoch means.

### 5.2 The per-party invariant

[`PartyInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L108) takes the
party's role, the transcript, its own state `st`, the peer's state `peer`, its own outgoing table,
both key tables and its game horizon. Fields, by group:

| Group | Fields | Meaning |
| --- | --- | --- |
| shape | `res_parity`, `req_parity`, `res_lower`, `req_lower`, `init_acks`, `res_le_peer_req`, `peer_req_le_res` | parities, bootstrap values, lockstep |
| own key pairs | `keypair_pos`, `keypair_future`, `ek_T`, `dk_T`, `T_dk`, `dk_shape`, `ek_acked`, `keypair_current` | which epochs of `T` carry my key pair; `ek` and `dk` are the transcript's; at most one secret key is retained, at the key epoch `resEpoch + offset` |
| own encapsulations | `enc_future`, `enc_current`, `ct_T`, `ct_acked`, `enc_ekRec` | which epochs carry my encapsulation; `ct` is the transcript's; encapsulating needed my key acknowledged |
| decoded peer keys | `ekPeer_T`, `ekPeer_parity`, `ekPeer_le` | a decoded key is the transcript's key for that epoch |
| key tables | `key_zero`, `key_res`, `key_req` | at responder parity the table is written at encapsulation, at requester parity at decapsulation |
| ciphertext acks | `ctRec_req_enc`, `ctRec_req_le`, `ctRec_res_peer`, `ctRec_res_le`, `ctRec_req_closed`, `ctRec_res_closed` | what each entry is backed by, plus downward closure per parity |
| public-key acks | `ekRec_res`, `ekRec_req` | parity-separated reading of public-key acknowledgements |
| buffer | `buffer` | see 5.3 |
| horizon | `horizon` | the game horizon is at most the sending horizon |
| messages | `msgs`, `msgs_flag_mono`, `msgs_stale` | every recorded message is honest; see 5.4 |

Note that `PartyInv` never reads the `peerKey` argument. Key consistency is obtained through
the transcript, not by relating the two tables directly.

### 5.3 The shared buffer

[`BufferConsistent`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L50) is
the BiKEM analogue of UniKEM's `ChunksAConsistent`. One buffer holds both payloads, so the
predicate is phase-indexed by the receiver's own state:

```
if reqEpoch ∈ ctRec                    then buffer = ∅
else if ekPeer (reqEpoch - offset) = none then honest sub-threshold chunks of the peer's key
else                                       honest sub-threshold chunks of this epoch's ciphertext
```

"Honest sub-threshold chunks" is `payloadChunks ecp payload I` with `I.card < nchunk`
(`ErasureCode/Payload.lean`). A payload the transcript has not produced yet has an empty
buffer.

### 5.4 The two fields the proof forced

Reading `recv` (`Construction.lean`) shows that a *stale* message, one with `ρ.tRes` below the
receiver's requester epoch, still ingests the flags but skips the cleanup that clears `ct`. If
such a message could acknowledge the receiver's *current* responder epoch for the first time,
`ct` would survive the next epoch advance and be transmitted as the new epoch's ciphertext.
The invariant therefore has to say that this never happens:

- [`msgs_stale`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L225): a
  message the peer already considers stale carries no new ciphertext acknowledgement.
- [`msgs_flag_mono`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L220):
  among my recorded messages, a ciphertext flag at a lower responder epoch is at most the
  requester epoch of any message at a higher responder epoch, and the flag transfers on
  equality.

The second is what makes the first preservable when a receiver advances: see the last block of
[`partyInv_recv_noKey`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L272)
(the `msgs_stale` obligation for the peer). This is a genuine protocol fact, not bookkeeping.

### 5.5 The game invariant

[`GameInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L241):

```
s.correct = true ∧ ∃ T, PartyInv .A T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA
                     ∧ PartyInv .B T s.stB s.stA s.msgB s.keyB s.keyA s.tcurB
```

The transcript is existential and shared. Role symmetry means there is one send step and one
receive step, each applied twice.

## 6. Consequences that discharge the game assertions

The game's known-prefix assertion is the hardest to see, so it gets dedicated lemmas in
`MainInvariant.lean`:

- [`ctRec_prefix`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L263):
  if `t` and `t - 1` are acknowledged, every positive `s ≤ t` is, by the two closure fields.
- [`sendingHorizon_attained`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L292)
  and [`horizon_prefix`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L307):
  a positive sending horizon is such a `t`, so every epoch up to it is acknowledged.
- [`keys_of_ctRec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L317):
  an acknowledged positive epoch has a key in *both* tables. This is the only lemma that needs
  both parties' invariants: at my requester parity I decapsulated (`key_req`) and the peer
  encapsulated (`key_res` of the peer); at my responder parity the roles swap through
  `ctRec_res_peer`.
- [`knownPrefix_of_partyInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L347):
  the game's `List.all` check, for any bound up to the sending horizon.

## 7. Initialisation

[`gameInv_init`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Init.lean#L29)
uses the empty transcript. The only field worth checking by hand is `buffer`: A starts with
requester epoch `0` and B with `-1`, both in the bootstrap set `{-1, 0}`, so the first branch of
`BufferConsistent` applies and the buffer must be empty, which it is.

The same file holds the bridge from the KEM's probabilistic definition to the pointwise fact the
proof consumes:
[`DecapsCorrectOnSupport`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Init.lean#L53)
and
[`decapsCorrectOnSupport_of_perfectlyCorrect`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Init.lean#L59).
The latter uses `probOutput_eq_one_iff` to turn `Pr[CorrectExp = true] = 1` into
`support CorrectExp = {true}` and places `false` in the support by contradiction.

## 8. The send step

[`partyInv_send_step`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L931)
is the statement to read first. Given both invariants and a supported local send by `roleS`, it
returns the three game assertions of a send (monotonicity, known prefix, unique and consistent
key) and a new transcript `T'` with both invariants restored. The emitted message is recorded
at index `n`, and an emitted key through
[`recordKey`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L229).

The proof is organised around the three kinds of send:

| Kind | Lemma | Transcript update |
| --- | --- | --- |
| plain (resend or wait) | [`send_step_plain`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L598) | none |
| epoch advance with key generation | [`send_step_advance`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L652) | `ofKeypair` at `resEpoch' + offset` |
| encapsulation | [`send_step_encaps`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L801) | `setEnc` at `resEpoch` |

The assembly also proves that an emitted key excludes an advance in the same send (a fresh key
is never already acknowledged: `ekRec_req`, then the peer's `ekPeer_T`, then `keypair_future`).

Two generic lemmas do most of the work and are worth understanding:

- [`partyInv_sender_of_send`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L352):
  the sender's post-state invariant. The kind-independent fields are proved once; the twelve
  kind-dependent facts (`f_*`) are hypotheses, next to seven hypotheses relating the new
  transcript and key table to the old ones.
- [`partyInv_peer_of_send`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L122):
  the peer's invariant after the send, parameterised by six "the transcript did not change
  where the peer looks" hypotheses.

Honesty of the new message comes from
[`MessageInv.of_send`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L283),
which reads `SendProvenance`, the ciphertext guard and the sender's own `ek_T` / `ct_T`.

Where the facts come from: `send_provenance` gives the per-send bookkeeping (epoch
transition, unchanged acknowledgements, advertised flags, chunk encoding, support memberships);
the advance gate `resEpoch ∈ ctRec ∧ resEpoch + offset ∈ ctRec` is
[`send_advance_guard`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean#L295);
the bit-1 guard is `send_ciphertextMessage_keyAck` from `SendFacts.lean`.

## 9. The receive step

[`partyInv_recv_step`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L967)
says more than preservation: for a message recorded in the peer's table, the receive
*succeeds*, the receive epoch matches the recorded one, the known-prefix check passes, an emitted
key is fresh and agrees with the peer's table, and both invariants hold afterwards with the same
transcript. Its hypothesis `hdec` is transcript-level KEM correctness, the single point where
the KEM is trusted.

### 9.1 Facts about the incoming message

The section starting at
[`recv_msgInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L87)
derives everything about the message from the *peer's* invariant, since the message is in the
peer's table. The ones to know:

- [`recvReq_eq_tRes`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L112):
  a non-stale message lands the requester epoch exactly on `ρ.tRes`. This is lockstep
  (`res_le_peer_req`) plus parity, and it is why no slack assumption is needed.
- [`recv_advance_prev`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L121):
  on an advance the previous requester epoch is already acknowledged. The peer's gate required
  it, and the peer's responder-parity entries are my own (`ctRec_res_peer`). This is what makes
  the buffer empty at an advance.
- [`recv_bit1_ekPeer`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L161):
  phase causality. A ciphertext chunk for `ρ.tRes` implies I hold the peer's key for it, so a
  bit-1 chunk never enters a buffer that is collecting public-key chunks.
- [`recv_horizon_mem`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L181)
  and [`recv_tcur_le`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L221):
  after ingesting the flags, every epoch up to the message's advertised horizon is acknowledged,
  so the new game horizon is still below my sending horizon. This is where `horizon_mem` and
  `horizon_req` of `MessageInv` earn their keep.

### 9.2 The post-state lemmas

Rather than proving forty fields five times, the post-states are covered by three lemmas:

- [`partyInv_recv_noKey`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L272):
  any non-stale receive that emits no key. It is parameterised by the new peer-key map and the
  new acknowledgements, so it covers the "no payload", "chunk below threshold" and "public key
  decoded and installed" outcomes, with the buffer fact supplied as a hypothesis.
- [`partyInv_decaps_local`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L530):
  the decapsulation transition on an arbitrary invariant state: drop the secret key for `q`,
  acknowledge `q`, write the transcript key into the table. The main theorem applies it to the
  output of `partyInv_recv_noKey`.
- [`partyInv_recv_stale`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L841):
  a stale message changes only acknowledgements, and by `msgs_stale` its ciphertext flag is a
  no-op.

### 9.3 The buffer in each case

- [`recv_buffer_pk`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L749):
  on the public-key path the buffer is honest chunks of the peer's key for this epoch and the
  message carries one more such chunk. The subtle part is ruling out "current epoch already
  acknowledged while the peer key is undecoded":
  [`recv_ekPeer_of_ctRec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L732)
  goes acknowledgement, encapsulation, the peer's `enc_ekRec`, my `ekRec_req`.
- [`recv_buffer_ct`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L782):
  the ciphertext analogue.
- [`recv_buffer_unchanged`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L808):
  when nothing is inserted; on an advance the buffer was empty by `recv_advance_prev`.

In each path the decoder is resolved by `decode_payloadChunks` or `decode_payloadChunks_none`
from `ErasureCode/Payload.lean` according to whether the inserted index reaches the threshold.

### 9.4 Where the KEM is trusted

In the ciphertext-decoded branch of `partyInv_recv_step`, the secret key is found by `T_dk`
(every generated key is retained until its epoch is decapsulated), identified as the transcript's
by `dk_T`, and then `hdec` says decapsulation returns the transcript key. That is the whole use of
KEM correctness. Since the quantitative work, `hdec` is only demanded for ciphertexts whose epoch
is *not yet acknowledged* (`ρ.tRes ∉ stR.ack.ctRec`); acknowledged epochs are replayed, and their
keys were already recorded. Section 12 explains how `hdec` is discharged from a flag on the state.

## 10. The game level and the final theorem

[`gameInv_step_of`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L54)
is the one-step statement: every result of one oracle query from a state satisfying `GameInv`
satisfies `GameInv`, provided every transcript consistent with the pre-state is `DecapsReady`
for both parties (the secret key of each epoch the party may still decapsulate recovers the
transcript key). It splits on the query: `Unif` leaves the state unchanged; `SendA` and `SendB`
go through `oracleSendA_run_cases` / `oracleSendB_run_cases` and one application of
`partyInv_send_step .A` / `.B`; `RecvA` and `RecvB` through `oracleRecvA_run_cases` /
`oracleRecvB_run_cases` and one application of `partyInv_recv_step` with `roleR := .A` / `.B`.
The two "local receive failed" outcomes are refuted because the receive step proves success.
The `correct` field of the pure update is closed from the step lemma's three assertions; the
`simp only` calls there are matching the game's Boolean expression to those facts.

The `DecapsReady` hypothesis is why the case split is not delegated to a generic dispatch
theorem with conclusion `QueryImpl.PreservesInv impl GameInv`: such a theorem asks for each
oracle fact at every state satisfying `GameInv`, and `DecapsReady` is not part of `GameInv`.
The two proofs discharge it differently.
[`gameInv_preserved`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L192)
supplies it at every state from `DecapsCorrectOnSupport` (a perfectly correct KEM), giving
`QueryImpl.PreservesInv`. The quantitative proof supplies it only at states that are not bad
(`gameInv_step_of_noFailure`, section 12).

The table below is the whole correspondence between the game's assertions in `SCKA/Defs.lean`
and the lemmas that discharge them.

| Game assertion | Send | Receive |
| --- | --- | --- |
| monotonicity `tcur ≤ tsnd` | `horizon` field | n/a (game takes `max`) |
| matching epoch `trcv = tsnd` | n/a | `MessageInv.epoch` via `recv_msgInv` |
| unique epoch | `key_res` with `enc = none` | `key_req` with `q ∉ ctRec` |
| consistent keys | peer's `key_req` and `ctRec_req_enc` | peer's `key_res` and `hdec` |
| known prefix | `knownPrefix_of_partyInv` | `knownPrefix_of_partyInv` on the post-state, using `recv_tcur_le` |
| receive never fails | n/a | `T_dk` for the key, `hdec` for decapsulation |

[`simulateQ_gameInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L207)
lifts to arbitrary adversaries with VCVio's `simulateQ_run_preservesInv`.
[`correctnessExp_eq_map`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L235)
rewrites the experiment as the final `correct` bit mapped over the run, and
[`correctness_of_perfectKEM`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L253)
shows `Pr[= false] = 0` through `probEvent_eq_zero_iff` and the invariant's `correct` field, then
converts to `Pr[= true] = 1` with `probOutput_false_eq_sub`.

## 11. Idioms you will meet

- **Parity by cases.** `cases role <;> simp only [Role.offset, Role.reqParity, Role.resParity] at ... <;> omega`.
  Do not expect `omega` to see through an `if role = .A then ... else ...`; case first.
- **Decidable `if`s.** Rewriting under `if c then a else b` with an `iff` about `c` fails because
  the `Decidable` instance depends on `c`. Use `by_cases` with `if_pos` / `if_neg`, or state the
  goal with `show`/`change` so the condition is syntactically the one in your hypothesis.
  `bufferConsistent_recvFinish`
  ([Recv.lean:702](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L702))
  exists for exactly this reason.
- **`Int.toNat`.** Game tables are indexed by `ℕ`, local epochs by `ℤ`. Every key-table field
  carries `0 < e`, and `Int.toNat_of_nonneg` recovers `e` from `e.toNat`.
- **Section variables.** `Recv.lean` keeps both invariants and the message hypothesis as section
  variables with `include`; lemmas that do not use the receiver's invariant say `omit hR in`.
- **`recordKey`.** Both step theorems state the updated key table as `recordKey keys key?`, which
  reduces by `simp` once `key?` is known; `Game.lean` cases on `key?` first.

## 12. The imperfect KEM: `Pr[fail] ≤ q · ε`

Files 12 to 18. The statement is `correctness_failure_le` in
[`Quantitative/Main.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean):
for a KEM with deterministic decapsulation, correct erasure codes, and an adversary making at most
`q` send queries (`SCKAScheme.SendQueryBound adv q`), the game returns `false` with probability at
most `q · kem.correctnessError`. `correctness_true_ge` is the complementary form, and
`correctness_of_perfectKEM'` recovers probability one for a perfectly correct KEM as the `ε = 0`
instance (the direct proof `correctness_of_perfectKEM` from section 10 is kept).

### 12.1 The shape of the argument

The game is run *tracked*: next to the game state we carry a Boolean flag. The flag is raised the
first time a party holds a decapsulation key, the peer holds a ciphertext for that epoch, and the
two disagree about the key. Two facts about the tracked run are proved separately and combined
by a generic layer:

1. **Soundness.** While the flag is down, `GameInv` holds. This is exactly section 7 to 10 with
   `hdec` discharged from "the flag is down" (`decapsReady_of_noFailure`,
   `gameInv_step_of_noFailure` in `RecvStep.lean`). Since `GameInv` contains `s.correct = true`,
   the game can only fail after the flag went up.
2. **Rarity.** The probability that the flag is ever raised is at most `q · ε`. This is a
   potential argument: a score on tracked states that is `1` once the flag is up, never decreases
   in expectation except on send queries, and increases by at most `ε` there.

The combination is scheme-generic and lives in
[`SCKA/Correctness/Tracked.lean`](../../SecureMessaging/SCKA/Correctness/Tracked.lean):
`trackedImpl impl bad` wraps any oracle implementation, `trackedInv Inv bad` is the invariant
"flag up, or `Inv` and flag down", `tracked_bad_le_of_score_step` turns a per-step score bound into
`Pr[flag] ≤ q · ε`, and `correctness_failure_le_of_tracked_bad` turns that into a bound on
`Pr[= false]`. Nothing in this file knows about BiKEM; it is the factored-out core of UniKEM's
`Reduction/{Projection,Composition}`.

### 12.2 The flag and the potential, read off the state

[`Quantitative/Core.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean).
Both are functions of the game state alone, not of the transcript.

- `kemFailureAt hDet st peer peerKey` looks up `peer.res.resEpoch` in `st.req.dk`, takes
  `peer.res.ct`, and `peerKey` at that epoch; if all three are present it decides whether
  `decapsDet sk c ≠ some k`. `kemFailure s` is the disjunction over the two orientations.
- `pendingTerm` is the conditional error `keypairFailure kem hDet pk sk` of one retained secret
  key, paired with the public key the peer holds for it (`ekPeer`) or the one still in the local
  buffer (`req.ek`); it is `0` once the peer's key for that epoch is recorded.
  `pendingPotential` sums it over `st.req.dk`, and `failurePotential s` adds both parties.
- `trackedScore (s, flag) = if flag then 1 else failurePotential s`.

Two invariant fields were added to make this definable and bounded: `dk_shape` (a party retains
at most one secret key, at the epoch `resEpoch + offset`) and `ek_acked` (if the public-key buffer
is empty then the key was never generated or has been acknowledged). They give
`pendingPotential_le_one_of_inv` and the bridge `decaps_of_noFailure`: for an unacknowledged
epoch, "flag down" implies the transcript decapsulation equation that `partyInv_recv_step` needs.

`keypairFailure` itself is in
[`KEM/CorrectnessError.lean`](../../SecureMessaging/KEM/CorrectnessError.lean) with
`correctnessError_eq_avg_keypair`: the KEM's correctness error is the keygen-average of
`keypairFailure`, plus the keygen failure mass. (The on/off KEM has its own `failureAfterKeypair`
with an extra argument; the plain-KEM version got a different name to coexist with it.)

### 12.3 Per-step bounds

- **Non-send queries**
  ([`RecvStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/RecvStep.lean)).
  A receive either records a key, which zeroes the receiver's own pending term
  (`pendingPotential_recv_receiver`), or changes nothing the potential reads; the peer's term is
  unchanged (`pendingPotential_recv_peer`); and the flag stays down (`kemFailure_recv`, because a
  ciphertext is only stored for an epoch whose own key is not yet retained or is already acked).
  `Unif` leaves the state alone. Hence `tracked_nonSend_score_le`: the expected score does not grow.
- **Send queries**
  ([`SendDist.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendDist.lean),
  [`SendStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean)).
  `send_eq_advance` and `send_eq_encaps` rewrite `send` into `keygen >>= pure ∘ advanceSend` and
  `encaps pk >>= pure ∘ encapsSend` under the respective gates, and `send_plain_of_not` says
  anything else emits no key and keeps the epoch. Then, with `pairPotential`/`pairFailure`
  presenting the two parties symmetrically:
  - *advance*: the potential gains `keypairFailure pk sk` for the fresh pair; averaged over
    keygen this is `≤ ε` (`expectedPayoff_keygen_le`, from `correctnessError_eq_avg_keypair`);
  - *encapsulation* to the peer's `pk` with retained `sk`: with probability at most
    `keypairFailure pk sk` the flag goes up (score `1`), otherwise that term leaves the potential
    (`pairPotential_encaps`, `pairFailure_encaps`, `expectedPayoff_encaps_le`); the expectation is
    at most the old score;
  - *plain*: unchanged (`pair_plain`).
  `tracked_sendA_score_le`/`tracked_sendB_score_le` are the two orientations;
  `tracked_step_score_le` is the combined statement with `+ ε` only on `IsSendQuery t`.

### 12.4 Assembly

`Main.lean`: the initial state has no secret keys, so `kemFailure_init` and `trackedScore_init`
are immediate; `trackedBiKem_preservesInv` is `trackedImpl_preserves` applied to
`gameInv_step_of_noFailure`; `tracked_bad_le` feeds `tracked_step_score_le` into the generic
`tracked_bad_le_of_score_step`; `correctness_failure_le` feeds that into
`correctness_failure_le_of_tracked_bad` with `correctnessExp_eq_map`. All endpoints depend only on
`propext`, `Classical.choice`, `Quot.sound`.