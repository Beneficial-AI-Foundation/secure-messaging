# Opp-BiKEM-CKA correctness: a guided tour of the proof

This tutorial explains how the Lean proof of Opp-BiKEM-CKA correctness is organised: what it
proves, which lemmas the results rest on, and how the main steps work. Read it next to the Lean
sources. Links point to the line that declares the named object and are relative to this file.
Two module docstrings complement it: the one of
[`OppBiKEM/Correctness.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean) states the
results with their notation, and the one of
[`Quantitative/Main.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean)
outlines the quantitative proof.

## 1. What is proved

### 1.1 The protocol and the game

Opp-BiKEM-CKA ([`Construction.lean`](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean)) runs
one KEM instance per epoch. The *requester* of epoch `e` (A for even `e`, B for odd `e`)
generates a key pair and transmits the public key; the *responder* encapsulates to it and
transmits the ciphertext. Both payloads travel as erasure-coded chunks, at most one chunk per
message. Every message also carries the sender's two epochs (`tRes`, `tReq`), two
acknowledgement flags, and the sender's *sending epoch* (`sendingEpoch`). Epochs are integers:
`-1` and `0` are bootstrap values, and KEM instances run at epochs `≥ 1`.

The correctness game is
[`SCKAScheme.correctnessExp`](../../SecureMessaging/SCKA/Defs.lean#L730). Write
`Π := scheme kem hDet ecEk ecCt leak` for the scheme and
`G(Adv) := SCKAScheme.correctnessExp Π Adv`. The adversary `Adv` calls five oracles in any order: `SendA`, `SendB`, `RecvA n`,
`RecvB n` and `Unif`. A receive oracle delivers the `n`-th message the peer has sent, so messages
can be delayed, reordered, duplicated and replayed. The game keeps, for each party, a key table,
the table of its sent messages, and its *game epoch* `tcur`. It returns the conjunction of the
following assertions over the whole run.

| Oracle | Assertions |
| --- | --- |
| `SendA`, `SendB` | *monotonicity* `tcur ≤ tsnd` for the reported sending epoch `tsnd`; *unique epoch*: an emitted key's epoch has no key in the sender's table yet; *consistent keys*: the peer's table has no key or the same key at that epoch; *known prefix*: every epoch from `1` to `tsnd` has a key in the sender's table |
| `RecvA`, `RecvB` | the local receive succeeds; *matching epoch* `trcv = tsnd`, where `trcv` is the reported epoch and `tsnd` the one recorded when the message was sent; unique epoch and consistent keys as for a send; known prefix up to the new game epoch `max tcur trcv` |

A send that the local algorithm rejects returns nothing and leaves the game state unchanged.

### 1.2 The results

Let `ε := kem.correctnessError`. Assume that `kem` has deterministic decapsulation and that the
erasure codes `ecEk` (for public keys) and `ecCt` (for ciphertexts) are correct. The first four
results are stated in
[`OppBiKEM/Correctness.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean).

| Result | Statement |
| --- | --- |
| [`correctness_failure_le`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L87) | if `Adv` makes at most `q` send queries, then `Pr[G(Adv) = false] ≤ q · ε` |
| [`correctness_true_ge`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L110) | under the same hypotheses, `Pr[G(Adv) = true] ≥ 1 - q · ε` |
| [`correctness_of_perfectKEM'`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L134) | for a perfectly correct KEM and at most `q` send queries, `Pr[G(Adv) = true] = 1`: the `ε = 0` case of the previous line |
| [`correctness_of_perfectKEM`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L154) | for a perfectly correct KEM, `Pr[G(Adv) = true] = 1` for every adversary, without a query bound |
| [`sends_never_rejected_of_noFailure`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L221) | on every reachable state of the tracked run (section 11) whose failure flag is clear, neither party's `send` is rejected |
| [`sends_never_rejected_of_perfectKEM`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L125) | for a perfectly correct KEM, neither party's `send` is rejected on any reachable state |

`SendQueryBound Adv q` counts `SendA` and `SendB` queries only. The game does not observe a
rejected send, so the last two results complement the first four. All six depend only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

Apart from the query bound, the adversary is unrestricted.

## 2. How the proof is organised

### 2.1 The idea

Fix an execution. For every epoch `e ≥ 1`, the requester draws one key pair and the responder
encapsulates to it once. Record these samples in a *transcript* `T : ℤ → EpochTranscript`. The
*main invariant* `GameInv` says that one transcript is consistent with everything either party
holds: its retained key material, every message it has sent, its chunk buffer, its
acknowledgement sets, its key table and its game epoch. `GameInv` holds initially and contains
`correct = true`, and every game assertion is a consequence of it.

One oracle query preserves `GameInv` under a single proviso about the KEM, `DecapsReady`: every
ciphertext a party has yet to decapsulate decapsulates to the transcript's key. This is the
only place where KEM correctness enters. The two correctness proofs differ only in how they
ensure it:

- **Quantitative proof.** With an imperfect KEM, `DecapsReady` can fail. The game is run with a
  flag that is set as soon as a KEM instance has completed inconsistently. While the flag is
  clear, `DecapsReady` holds, so `GameInv` holds and the game has not failed. A potential
  argument bounds the probability that the flag is ever set by `q · ε`.
- **Perfect-KEM proof.** With a perfectly correct KEM, `DecapsReady` holds at every state, so
  `GameInv` holds at every reachable state and no query bound is needed.

### 2.2 The dependency tree

Each line names a lemma and what it says; the children of a lemma are the lemmas its proof
combines.

```text
correctness_failure_le                  Pr[G(Adv) = false] ≤ q · ε
├── correctnessExp_eq_map               G(Adv) is the final `correct` bit of the run
├── trackedBiKem_preservesInv           every query keeps J := (flag set, or GameInv and not bad)
│   └── gameInv_step_of_noFailure       one query keeps GameInv from a state that is not bad
│       ├── decapsReady_of_noFailure    not bad ⇒ DecapsReady
│       └── gameInv_step_of             one query keeps GameInv, given DecapsReady
│           ├── partyInv_send_step      a send keeps PartyInv for both parties
│           └── partyInv_recv_step      a receive keeps PartyInv for both parties
├── tracked_bad_le                      Pr[flag set] ≤ q · ε, also from trackedBiKem_preservesInv
│   ├── tracked_step_score_le           one query raises E[S] by at most ε, and only if a send
│   │   ├── tracked_sendA_score_le, tracked_sendB_score_le
│   │   └── tracked_nonSend_score_le
│   └── trackedInv_init, trackedScore_init      J holds initially, and S = 0
└── SCKAScheme.correctness_failure_le_of_tracked_bad    Pr[G(Adv) = false] ≤ Pr[flag set]

correctness_true_ge                     arithmetic on correctness_failure_le
correctness_of_perfectKEM'              ε = 0 in correctness_true_ge

correctness_of_perfectKEM               Pr[G(Adv) = true] = 1 for every Adv
├── decapsCorrectOnSupport_of_perfectlyCorrect   decapsulation is correct on all samples
├── simulateQ_gameInv                   GameInv at every reachable state
│   ├── gameInv_init                    GameInv initially
│   └── gameInv_preserved               gameInv_step_of, with DecapsReady at every state
└── correctnessExp_eq_map

sends_never_rejected_of_noFailure       trackedBiKem_preservesInv, then send_ne_none
sends_never_rejected_of_perfectKEM      simulateQ_gameInv, then send_ne_none
```

Here `S` is the tracked score of section 11: `1` once the flag is set, and otherwise the failure
potential, the summed probability that a KEM instance in progress completes inconsistently.

### 2.3 Layers

The files fall into five groups.

- **Main-invariant layer** (`Correctness/MainInvariant.lean` and `Correctness/MainInvariant/`):
  the invariant, its initial state, the send and receive steps, and one query under
  `DecapsReady`. It has no probabilities: every statement is about the supports of the local
  algorithms.
- **Quantitative layer** (`Correctness/Quantitative/`, with the generic tracked game in
  `ToVCVio` and `SCKA/Correctness/Tracked.lean`, and the KEM error in
  `KEM/CorrectnessError.lean`): the flag, the potential, and the `q · ε` bound.
- **Perfect-KEM layer** (`Correctness/PerfectKEM.lean`).
- **Send totality** (`Correctness/MainInvariant/SendTotal.lean`): `PartyInv` rules out the
  error exits of `send`.
- **Infrastructure**: the game oracles as pure updates (`SCKA/Correctness.lean`), the transcript,
  the decision-tree form of `recv`, and support-level facts about one `send` and one `recv`.

## 3. File map and reading order

File names are abbreviated; the links give the full paths.

| File | Group | Contents |
| --- | --- | --- |
| [`OppBiKEM/Construction.lean`](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean) | protocol | `State`, `Message`, `send`, `recv`, `scheme` |
| [`SCKA/Defs.lean`](../../SecureMessaging/SCKA/Defs.lean) | game | the oracles, `correctnessExp`, `SendQueryBound` |
| [`OppBiKEM/Correctness.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean) | results | notation; the four probability results |
| [`SCKA/Correctness.lean`](../../SecureMessaging/SCKA/Correctness.lean) | infrastructure | each oracle as a pure state update, with support and distribution forms of each oracle run |
| [`Correctness/Transcript.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean) | infrastructure | `EpochTranscript`, `Transcript`, role parities |
| [`Correctness/RecvSpec.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean) | infrastructure | `recv` as a decision tree |
| [`Correctness/SendFacts.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean) | infrastructure | support-level facts about one `send`; the sending horizon |
| [`Correctness/RecvFacts.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvFacts.lean) | infrastructure | support-level facts about one `recv` |
| [`Correctness/MainInvariant.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean) | invariant | `BufferConsistent`, `MessageInv`, `PartyInv`, `GameInv`; the known-prefix lemmas |
| [`MainInvariant/Init.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Init.lean) | invariant | `GameInv` initially |
| [`MainInvariant/Send.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean) | invariant | the send step |
| [`MainInvariant/Recv.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean) | invariant | the receive step |
| [`MainInvariant/Game.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean) | invariant | one query under `DecapsReady`; the experiment as a map over the run |
| [`MainInvariant/SendTotal.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/SendTotal.lean) | send totality | `send_ne_none` |
| [`KEM/CorrectnessError.lean`](../../SecureMessaging/KEM/CorrectnessError.lean) | quantitative | `keypairFailure`, the KEM error after fixing the key pair |
| [`BadFlag.lean`](../../ToVCVio/OracleComp/SimSemantics/StateT/BadFlag.lean), [`SCKA/Correctness/Tracked.lean`](../../SecureMessaging/SCKA/Correctness/Tracked.lean) | quantitative | the generic tracked game and its SCKA specialisation |
| [`Quantitative/Core.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean) | quantitative | the bad predicate, the failure potential, the tracked score |
| [`Quantitative/SendDist.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendDist.lean) | quantitative | `send` as a sampler followed by a deterministic outcome |
| [`Quantitative/RecvStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/RecvStep.lean) | quantitative | the tracked handler; `GameInv` while not bad; non-send queries keep the score |
| [`Quantitative/SendStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean) | quantitative | a send raises the expected score by at most `ε`; the combined one-query bound |
| [`Quantitative/Main.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean) | quantitative | the proof outline; `trackedBiKem_preservesInv`, `tracked_bad_le` |
| [`Correctness/PerfectKEM.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean) | perfect KEM | `GameInv` at every reachable state |

Start with `OppBiKEM/Correctness.lean` for the statements and section 2 for the structure. Then
read `MainInvariant.lean` for the invariant (section 5), `MainInvariant/Game.lean` to see how it
is used (section 10), and `MainInvariant/Send.lean` and `MainInvariant/Recv.lean` for the step
proofs (sections 8 and 9). The infrastructure (section 4) can be skimmed and consulted when a
step proof cites it. For the quantitative proof, read the module docstring of
`Quantitative/Main.lean` first, then `Quantitative/Core.lean` and `Quantitative/SendStep.lean`
(section 11). `PerfectKEM.lean` is short (section 12).

## 4. Infrastructure

### 4.1 The oracles as pure updates

Each correctness-game oracle in `SCKA/Defs.lean` runs the scheme's local `send` or `recv` and
then updates the game state. `SCKA/Correctness.lean`, shared by the SCKA correctness proofs,
names those updates and restates each oracle run in terms of them:

- [`sendAUpdate`](../../SecureMessaging/SCKA/Correctness.lean#L41) and
  [`recvAUpdate`](../../SecureMessaging/SCKA/Correctness.lean#L74), and the `B` twins. The
  `correct` field carries the game's assertions verbatim, with the known-prefix check as
  `knownPrefix`. The field lemmas `sendAUpdate_stA`, `sendAUpdate_keyA_some`, … are what the
  quantitative send step reads.
- [`mem_support_oracleSendA_run_iff`](../../SecureMessaging/SCKA/Correctness.lean#L196):
  an outcome of a `SendA` query has one of two forms:
  - `(none, s)`, if the local `sendA` rejects; the state is unchanged;
  - the response paired with `sendAUpdate s …`, if the local `sendA` returns an outcome.
- [`mem_support_oracleRecvA_run_iff`](../../SecureMessaging/SCKA/Correctness.lean#L267):
  an outcome of a `RecvA n` query has one of three forms:
  - `(none, s)`, if B has sent no message `n`; the state is unchanged;
  - `(none, { s with correct := false })`, if B's message `n` exists but the local `recvA`
    rejects it; the game counts a rejected honest message as a correctness failure;
  - the response paired with `recvAUpdate s …`, if the local `recvA` accepts the message.

  Both lemmas have `B` versions. `gameInv_step_of` (section 10) and the receive cases of
  `Quantitative/RecvStep.lean` use them.
- [`oracleSendA_run_eq`](../../SecureMessaging/SCKA/Correctness.lean#L167): a send run as a
  computation, the local outcome mapped through the update. The expected-value proofs of
  `Quantitative/SendStep.lean` use it, through a private name `sendAOutcome` for that map.

Downstream proofs speak about the updates and never unfold the `StateT` plumbing of the oracles.
The case split over the five oracles happens once, in `gameInv_step_of` (section 10).

### 4.2 The transcript

[`EpochTranscript`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L73) has
two data fields and three proofs:

```text
keypair : Option (PK × SK)        -- the requester's key pair
enc     : Option (C × K)          -- the responder's ciphertext and key
keypair_mem, enc_mem              -- each sample is in the support of its sampler
enc_keypair                       -- an encapsulation requires the key pair
```

[`Transcript`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L87) is
`ℤ → EpochTranscript`, indexed by the construction's integer epochs; on reachable states only
epochs `≥ 1` are populated. The send step updates it with
[`ofKeypair`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L102) and
[`setEnc`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L116). The support
memberships recorded here are what connects the transcript to KEM correctness (section 12).

Roles and epochs are related by
[`Role.reqParity`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L39) and
`Role.resParity` (A requests at even epochs and responds at odd ones, B the reverse) and by
[`Role.offset`](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L73) (`1` for A, `-1` for
B). The *key epoch* `resEpoch + offset` of a party is the requester-parity epoch of its current
own key pair; the peer's public key a requester at epoch `t` collects is the one for epoch
`t - offset`. The simp lemmas `Role.peer_reqParity` and `Role.peer_resParity` say that the
peer's parities are swapped.

### 4.3 `recv` as a decision tree

In `Construction.lean`, `recv` is written with `let mut` and early `return`, which elaborates to
a deeply nested term.
[`recvSpec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L46) is the same
function written as an explicit decision tree over three named pieces:

- [`recvAck`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L27): the
  acknowledgement sets after ingesting the message's two flags;
- [`recvReq`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L32): the requester
  epoch, advanced by two if the message is ahead;
- [`recvFinish`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L37): the
  post-state, with acknowledged outgoing material cleared.

[`recv_eq_recvSpec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L87) proves
that the two agree. It is the one brute-force proof of the development: a uniform case split over
about two hundred leaves, each closed by `rfl`, under a raised heartbeat budget. Every later fact
about a receive is read off `recvSpec` with one case split per named condition.

### 4.4 Facts about one send and one receive

[`SendFacts.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean) collects what
the step proofs need to know about one successful `send`:

- [`Acknowledgements.sendingHorizon`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean#L29),
  the sending epoch a party puts on its messages (section 5.1);
- [`send_support_facts`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean#L119):
  every send keeps the acknowledgements, reports the sending horizon as its sending epoch, and
  keeps the responder epoch or advances it by two;
- [`SendProvenance`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean#L148) and
  [`send_provenance`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean#L226): the
  full record of one send (epoch transition, advertised flags, chunk encoding, support
  memberships of the samples);
- [`send_ciphertextMessage_keyAck`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean#L259):
  a ciphertext message is sent only after the sender's own public key is acknowledged;
- [`send_advance_guard`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/SendFacts.lean#L295): an
  advance requires the responder epoch and the key epoch to be in `ctRec`.

The main-invariant receive step reads `recv` through `recvSpec` directly.
[`RecvFacts.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvFacts.lean) states the
facts about one `recv` that the quantitative receive step needs: the post-state of a successful
receive (`recv_success_state_facts`), the facts behind an emitted key
(`recv_emitted_key_facts`), and how a receive changes the own public key and the decoded peer
keys (`recv_local_publicKey_eq_or_none`, `recv_peerKeys_stable`, `recv_peerKeys_origin`).

## 5. The main invariant

A party's [`State`](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L154) has a responder
part `res` (the responder epoch `resEpoch`, the decoded peer public keys `ekPeer`, the outgoing
ciphertext `ct`, a chunk counter), a requester part `req` (the requester epoch `reqEpoch`, the
retained secret keys `dk`, the outgoing own public key `ek`, the chunk buffer
`receivedChunks`), and two acknowledgement sets: `ack.ctRec` holds the epochs whose ciphertext
the party has received or the peer has acknowledged, and `ack.ekRec` the same for public keys.

### 5.1 Three epochs

The invariant relates three epochs, defined in the module docstring of `MainInvariant.lean`:

- the *sending horizon* of a party, `st.ack.sendingHorizon`: the largest `t ≥ 0` with `t` and
  `t - 1` in `st.ack.ctRec`;
- the *sending epoch* of a message, `ρ.sendingEpoch`: the sender's sending horizon when it
  created `ρ`, reported to the game as `tsnd` by the send and as `trcv` by a receive;
- the *game epoch* of a party, `tcur`: the game's current epoch, set to `tsnd` by a send and
  raised to `max tcur trcv` by a receive.

The invariant keeps the game epoch at most the sending horizon (`PartyInv.tcur_le`). Section 6
shows why this gives the known-prefix assertion, and section 9.1 why a receive keeps it.

### 5.2 Message honesty

A recorded message is *honest* if it agrees with the transcript and with the sender's *current*
state: a message stays in the table and can be delivered at any later point.
[`MessageInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L101) states
this. Its fields fall into three groups:

- Epochs: `epoch` (the recorded sending epoch is the one the message carries), the parities,
  the lower bounds, and `res_le` / `req_le` (the carried epochs are at most the sender's current
  ones).
- Payload: `pk_chunk` (a public-key chunk encodes the transcript's public key for the epoch
  `ρ.tRes + offset`), `ct_chunk` (a ciphertext chunk encodes the transcript's ciphertext for
  `ρ.tRes`), `no_chunk`.
- Flags and sending epoch: `ct_flag`, `ek_flag` and `bit1_acked` (flags and ciphertext
  messages are backed by the sender's acknowledgement sets), and `sendingEpoch_mem` /
  `sendingEpoch_req` (every positive epoch up to the sending epoch is in the sender's `ctRec`,
  and the receiver acknowledges them too once it ingests the message's flags).

Honesty is established for a new message by
[`MessageInv.of_send`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L283)
and carried forward as the sender advances by
[`MessageInv.transfer`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L80)
(after a send) and
[`MessageInv.mono`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L233)
(after a receive).

### 5.3 The per-party invariant

[`PartyInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L144) takes the
party's role, the transcript, its own state `st`, the peer's state `peer`, its outgoing table,
both key tables, and its game epoch `tcur`. Its 39 fields, by group:

| Group | Fields | Meaning |
| --- | --- | --- |
| shape | `res_parity`, `req_parity`, `res_lower`, `req_lower`, `init_acks`, `res_le_peer_req`, `peer_req_le_res` | parities, bootstrap values, lockstep of the two parties' epochs |
| own key pairs | `keypair_pos`, `keypair_future`, `ek_T`, `dk_T`, `T_dk`, `dk_shape`, `ek_acked`, `keypair_current` | which epochs of `T` carry my key pair; `ek` and `dk` are the transcript's; at most one secret key is retained, at the key epoch |
| own encapsulations | `enc_future`, `enc_current`, `ct_T`, `ct_acked`, `enc_ekRec` | which epochs carry my encapsulation; `ct` is the transcript's; encapsulating needed my key acknowledged |
| decoded peer keys | `ekPeer_T`, `ekPeer_parity`, `ekPeer_le` | a decoded key is the transcript's key for that epoch |
| key tables | `key_zero`, `key_res`, `key_req` | at responder parity the table is written at encapsulation, at requester parity at decapsulation |
| ciphertext acknowledgements | `ctRec_req_enc`, `ctRec_req_le`, `ctRec_res_peer`, `ctRec_res_le`, `ctRec_req_closed`, `ctRec_res_closed` | what each entry is backed by, plus downward closure per parity |
| public-key acknowledgements | `ekRec_res`, `ekRec_req` | parity-separated reading of the public-key acknowledgements |
| buffer | `buffer` | see 5.4 |
| game epoch | `tcur_le` | the game epoch is at most the sending horizon |
| messages | `msgs`, `msgs_flag_mono`, `msgs_stale` | every recorded message is honest; see 5.5 |

`PartyInv` never reads the `peerKey` argument. Key consistency between the two tables follows
from both being tied to the transcript, not from a direct relation between them.

### 5.4 The chunk buffer

One buffer collects both incoming payloads, so
[`BufferConsistent`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L68)
selects the payload by the receiver's own state:

```text
if reqEpoch ∈ ctRec                        then buffer = ∅
else if ekPeer (reqEpoch - offset) = none  then honest sub-threshold chunks of the peer's key
else                                            honest sub-threshold chunks of the ciphertext
```

"Honest sub-threshold chunks" is `payloadChunks ecp payload I` with `I.card < nchunk`
([`ErasureCode/Payload.lean`](../../SecureMessaging/ErasureCode/Payload.lean)), for the payload
recorded in the transcript. A payload the transcript does not contain yet has an empty buffer.

### 5.5 Stale messages

A *stale* message, one with `ρ.tRes` below the receiver's requester epoch, still ingests the
flags but skips the cleanup at the end of `recv` that clears `ct`. If such a message could
acknowledge the receiver's *current* responder epoch for the first time, `ct` would survive the
next epoch advance and be transmitted as the new epoch's ciphertext. Two fields rule this out:

- [`msgs_stale`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L261): a
  message the peer already considers stale carries no new ciphertext acknowledgement.
- [`msgs_flag_mono`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L256):
  among my recorded messages, a ciphertext flag at a lower responder epoch is at most the
  requester epoch of any message at a higher responder epoch, and the flag transfers on
  equality.

The second is what keeps the first when a receiver advances: see the last block of
[`partyInv_recv_noKey`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L272),
which proves `msgs_stale` for the peer.

### 5.6 The game invariant

[`GameInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L277):

```text
s.correct = true ∧ ∃ T, PartyInv .A T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA
                     ∧ PartyInv .B T s.stB s.stA s.msgB s.keyB s.keyA s.tcurB
```

The transcript is existential and shared by both parties. Because `PartyInv` is stated for an
arbitrary role, there is one send step and one receive step, each applied once per role.

## 6. Consequences that discharge the known prefix

The known-prefix assertion follows from `tcur_le` through four lemmas in `MainInvariant.lean`:

- [`ctRec_prefix`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L299):
  if `t` and `t - 1` are acknowledged, so is every positive `s ≤ t`, by the two closure fields.
- [`sendingHorizon_attained`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L328)
  and [`sendingHorizon_prefix`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L343):
  a positive sending horizon is such a `t`, so every epoch up to it is acknowledged.
- [`keys_of_ctRec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L354):
  an acknowledged positive epoch has a key in *both* tables. This is the only lemma here that
  needs both parties' invariants: at my requester parity I decapsulated (`key_req`) and the
  peer encapsulated (the peer's `key_res`); at my responder parity the roles swap through
  `ctRec_res_peer`.
- [`knownPrefix_of_partyInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L384):
  the game's `List.all` check, for any bound up to the sending horizon.

## 7. Initialisation

[`gameInv_init`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Init.lean#L27)
uses the empty transcript. The only field worth checking by hand is `buffer`: A starts with
requester epoch `0` and B with `-1`, both in the bootstrap set `{-1, 0}` of `ctRec`, so the first
branch of `BufferConsistent` applies, and the buffer is indeed empty.

## 8. The send step

[`partyInv_send_step`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L931)
is the statement to read first. Given both invariants and a supported local send by `roleS`, it
returns the game's send assertions (monotonicity, known prefix, unique and consistent key) and a
new transcript `T'` for which both invariants hold again. The emitted message is recorded at
index `n`, and an emitted key through
[`recordKey`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L265).

A send is one of three kinds:

| Kind | Lemma | Transcript update |
| --- | --- | --- |
| plain (resend or wait) | [`send_step_plain`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L598) | none |
| epoch advance with key generation | [`send_step_advance`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L652) | `ofKeypair` at the new key epoch |
| encapsulation | [`send_step_encaps`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L801) | `setEnc` at `resEpoch` |

`partyInv_send_step` also proves that one send cannot both advance and emit a key: an emitted
key needs the sender's own public key acknowledged, and a freshly generated key is not
(`ekRec_req`, then the peer's `ekPeer_T`, then `keypair_future`).

Two generic lemmas do most of the work:

- [`partyInv_sender_of_send`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L352):
  the sender's invariant after the send. The fields that do not depend on the kind of send are
  proved once; the twelve that do are hypotheses `f_*`, next to seven hypotheses relating the
  new transcript and key table to the old ones.
- [`partyInv_peer_of_send`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L122):
  the peer's invariant after the send, given three facts about the sender's state and six
  hypotheses saying that the transcript did not change where the peer's invariant looks.

The new message is honest by `MessageInv.of_send`, which reads `SendProvenance`, the
ciphertext guard `send_ciphertextMessage_keyAck`, and the facts `f_ek_T` and `f_ct_T` about the
sender's retained public key and ciphertext. The advance gate is `send_advance_guard`.

## 9. The receive step

[`partyInv_recv_step`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L975)
says more than preservation. For a message recorded in the peer's table, the receive
*succeeds*, the reported epoch matches the recorded one, the known-prefix check passes, an
emitted key is fresh and agrees with the peer's table, and both invariants hold afterwards with
the same transcript. Its hypothesis `hdec` is the transcript-level KEM correctness of section
9.4. The proof reads `recv` through `recvSpec` and keeps both invariants and the message
hypothesis as section variables.

### 9.1 Facts about the incoming message

The section starting at
[`recv_msgInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L87)
derives everything about the message from the *peer's* invariant, since the message is in the
peer's table. The ones to know:

- [`recvReq_eq_tRes`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L112):
  a non-stale message lands the requester epoch exactly on `ρ.tRes`. This follows from lockstep
  (`res_le_peer_req`) and parity, and it is why no assumption on how far the parties drift
  apart is needed.
- [`recv_advance_prev`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L121):
  on an advance, the previous requester epoch is already acknowledged. The peer's advance gate
  required it, and the peer's responder-parity entries are my own (`ctRec_res_peer`). This is
  what makes the buffer empty at an advance.
- [`recv_bit1_ekPeer`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L161):
  a ciphertext chunk for `ρ.tRes` implies that I hold the peer's key for it, so a ciphertext
  chunk never enters a buffer that is collecting public-key chunks.
- [`recv_sendingEpoch_mem`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L181)
  and [`recv_tcur_le`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L221):
  after ingesting the flags, every epoch up to the message's sending epoch is acknowledged, so
  the new game epoch is still at most my sending horizon. This is where `sendingEpoch_mem` and
  `sendingEpoch_req` of `MessageInv` are used.

### 9.2 The post-state lemmas

The post-states are covered by three lemmas, so that the 39 fields are not proved once per
outcome:

- [`partyInv_recv_noKey`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L272):
  any non-stale receive that emits no key. It is parameterised by the new peer-key map and the
  new acknowledgements, so it covers the "no payload", "chunk below threshold" and "public key
  decoded and installed" outcomes; the buffer fact is a hypothesis.
- [`partyInv_decaps_local`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L530):
  the decapsulation transition on an arbitrary invariant state: drop the secret key for `q`,
  acknowledge `q`, and write the transcript key into the table. `partyInv_recv_step` applies it
  to the output of `partyInv_recv_noKey`.
- [`partyInv_recv_stale`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L849):
  a stale message changes only the acknowledgements, and by `msgs_stale` its ciphertext flag
  changes nothing.

### 9.3 The buffer in each case

- [`recv_buffer_pk`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L757):
  on the public-key path, the buffer holds honest chunks of the peer's key for this epoch, and
  the message carries one more such chunk. The subtle part is ruling out "current epoch already
  acknowledged while the peer key is undecoded":
  [`recv_ekPeer_of_ctRec`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L740)
  goes from the acknowledgement to the encapsulation, then through the peer's `enc_ekRec` and my
  `ekRec_req`.
- [`recv_buffer_ct`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L790):
  the ciphertext analogue.
- [`recv_buffer_unchanged`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L816):
  when nothing is inserted; on an advance the buffer was empty by `recv_advance_prev`.

In each path the decoder is resolved by `decode_payloadChunks` or `decode_payloadChunks_none`
from `ErasureCode/Payload.lean`, according to whether the inserted chunk reaches the threshold.
The new buffer is checked with
[`bufferConsistent_recvFinish`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L710),
which states `BufferConsistent` of a `recvFinish` state directly in terms of the arguments of
`recvFinish`.

### 9.4 Where the KEM is trusted

When a receive completes a ciphertext, `recv` looks up the secret key for the epoch and
decapsulates; if either fails, the receive fails. In this branch of `partyInv_recv_step`, the
secret key is found by `T_dk` (every generated key is retained until its epoch is
decapsulated), identified as the transcript's by `dk_T`, and `hdec` says that decapsulation
returns the transcript key. That is the whole use of KEM correctness. `hdec` is demanded only
for an epoch that is not yet acknowledged (`ρ.tRes ∉ stR.ack.ctRec`): the ciphertext of an
acknowledged epoch is not decapsulated again.

## 10. One oracle query

[`gameInv_step_of`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L50)
is the one-step statement: every outcome of one oracle query from a state satisfying `GameInv`
satisfies `GameInv`, provided every transcript consistent with the state is
[`DecapsReady`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L36) for
both parties. `DecapsReady role hDet T st` says that for every requester-parity epoch `q` not in
`st.ack.ctRec`, the transcript's secret key at `q` decapsulates the transcript's ciphertext at
`q` to the transcript's key; this is the `hdec` of the receive step.

The proof splits on the query:

- `Unif` leaves the state unchanged;
- `SendA` and `SendB` go through `mem_support_oracleSendA_run_iff` / `…B…` and one application
  of `partyInv_send_step .A` / `.B`;
- `RecvA` and `RecvB` go through `mem_support_oracleRecvA_run_iff` / `…B…` and one application
  of `partyInv_recv_step` with `roleR := .A` / `.B`. The "local receive failed" outcome is
  refuted, because the receive step proves success.

The `correct` field of the update is closed from the assertions the step lemma returns; the
`simp only` calls there match the game's Boolean expression to those facts.

`DecapsReady` is not part of `GameInv`, which is why `gameInv_step_of` carries it as a
hypothesis instead of concluding `QueryImpl.PreservesInv`. The quantitative proof supplies it
at states that are not bad (`gameInv_step_of_noFailure`, section 11), and the perfect-KEM proof
at every state (`gameInv_preserved`, section 12).

The table below is the whole correspondence between the game's assertions and the facts that
discharge them.

| Game assertion | Send | Receive |
| --- | --- | --- |
| monotonicity `tcur ≤ tsnd` | the `tcur_le` field | none (the game takes `max`) |
| matching epoch `trcv = tsnd` | none | `MessageInv.epoch` via `recv_msgInv` |
| unique epoch | `key_res` with `enc = none` | `key_req` with `q ∉ ctRec` |
| consistent keys | the peer's `key_req` and `ctRec_req_enc` | the peer's `key_res` and `hdec` |
| known prefix | `knownPrefix_of_partyInv` | `knownPrefix_of_partyInv` on the post-state, using `recv_tcur_le` |
| the receive succeeds | none | `T_dk` for the secret key, `hdec` for decapsulation |

[`correctnessExp_eq_map`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L195)
rewrites the experiment as the final `correct` bit mapped over the run. Both correctness proofs
start from it.

## 11. The quantitative bound: `Pr[G(Adv) = false] ≤ q · ε`

This section follows the outline in the module docstring of `Quantitative/Main.lean`, which
also fixes the notation `φ`, `V`, `S`, `J` used here.

### 11.1 The tracked game

The game is run *tracked*: next to the game state `s`, the run carries a Boolean flag `b`, set
as soon as `s` is *bad* and never cleared. Two facts about the tracked run are proved separately
and combined by a generic layer:

1. **The invariant holds while the flag is clear.** Every query preserves
   `J (s, b) := b = true ∨ (GameInv s ∧ bad s = false)`. From a state that is not bad,
   `DecapsReady` holds (`decapsReady_of_noFailure`), so this is sections 7 to 10 with `hdec`
   discharged from "not bad" (`gameInv_step_of_noFailure`). Since `GameInv` contains
   `correct = true`, the game can fail only if the flag is set.
2. **The flag is rarely set.** The probability that the flag is ever set is at most `q · ε`.
   This is a potential argument: a score on tracked states that is `1` once the flag is set,
   does not grow in expectation on non-send queries, and grows by at most `ε` in expectation on
   send queries.

The combination is generic and lives in
[`BadFlag.lean`](../../ToVCVio/OracleComp/SimSemantics/StateT/BadFlag.lean):

- [`trackedImpl`](../../ToVCVio/OracleComp/SimSemantics/StateT/BadFlag.lean#L47)
  wraps any stateful oracle implementation `impl` and sets the flag when the state becomes bad;
- [`trackedInv`](../../ToVCVio/OracleComp/SimSemantics/StateT/BadFlag.lean#L54)
  is the invariant "flag set, or `Inv` and not bad", and `trackedImpl_preserves` reduces its
  preservation to one query from a state that is not bad;
- `OracleComp.tracked_bad_le_of_score_step` turns a per-query score bound into
  `Pr[flag] ≤ score₀ + q · ε` for any class of counted queries;
- `prEvent_not_good_le_tracked_bad` bounds by `Pr[flag]` the probability that the ordinary
  run ends in a state the invariant rules out.

[`SCKA/Correctness/Tracked.lean`](../../SecureMessaging/SCKA/Correctness/Tracked.lean)
specialises the last two to the SCKA correctness game:
[`SCKAScheme.tracked_bad_le_of_score_step`](../../SecureMessaging/SCKA/Correctness/Tracked.lean#L53)
counts send queries, and
[`SCKAScheme.correctness_failure_le_of_tracked_bad`](../../SecureMessaging/SCKA/Correctness/Tracked.lean#L83)
turns a bound on the flag into a bound on `Pr[G(Adv) = false]`. Neither file depends on
Opp-BiKEM-CKA.

### 11.2 The flag and the potential

[`Quantitative/Core.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean)
defines both as functions of the game state alone, not of the transcript.

- [`kemFailureAt`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L46),
  for a party `st`, its peer `peer` and the peer's key table `peerKey`, looks up the peer's
  responder epoch `e` in `st.req.dk`, the peer's retained ciphertext, and `peerKey` at `e`. If
  all three are present, it decides whether `decapsDet sk c ≠ some k`, that is, whether this
  KEM instance has completed inconsistently. The bad predicate
  [`kemFailure`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L53)
  checks both orientations.
- [`pendingTerm`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L98)
  is the conditional error `φ(pk, sk) := keypairFailure kem hDet pk sk` of one retained secret
  key `sk`, where `pk` is the peer's decoded copy of the matching public key or the party's own
  retained copy. It is `0` once the peer's key table has an entry at that epoch, i.e. once the
  peer has encapsulated.
  [`pendingPotential`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L109)
  sums it over `st.req.dk`, and
  [`failurePotential`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L114)
  (`V(s)`) adds both parties.
- [`trackedScore`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L119)
  (`S(s, b)`) is `1` if the flag `b` is set and `V(s)` otherwise.

Two `PartyInv` fields make the potential well behaved: `dk_shape` (a party retains at most one
secret key, at its key epoch) and `ek_acked` (if no own public key is retained, then none was
generated for the key epoch or it is acknowledged). With them, the public key matching a
retained secret key is always available (`pendingKey_available`), so each pending term is `φ`
of a key pair recorded in the transcript, and a party's pending potential is at most one
(`pendingPotential_le_one_of_inv`). The bridge from the flag to the receive step is
[`decaps_of_noFailure`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L300):
for an epoch that is not yet acknowledged, "not bad" implies the transcript decapsulation
equation that `partyInv_recv_step` needs.

[`keypairFailure`](../../SecureMessaging/KEM/CorrectnessError.lean#L41) is the probability,
over encapsulation to `pk`, that decapsulation with `sk` does not recover the encapsulated key.
[`correctnessError_eq_avg_keypair`](../../SecureMessaging/KEM/CorrectnessError.lean#L59) says that
the KEM's correctness error is its average over key generation.

### 11.3 One query

- **Non-send queries**
  ([`Quantitative/RecvStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/RecvStep.lean)).
  A receive either records a key, which removes the receiver's own pending term
  (`pendingPotential_recv_receiver`), or changes nothing the potential reads; the peer's term is
  unchanged (`pendingPotential_recv_peer`); and the state does not become bad
  (`kemFailure_recv`). `Unif` leaves the state alone. Hence
  [`tracked_nonSend_score_le`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/RecvStep.lean#L430):
  the expected score does not grow. These proofs read `recv` through `RecvFacts.lean`.
- **Send queries**
  ([`Quantitative/SendDist.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendDist.lean),
  [`Quantitative/SendStep.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean)).
  [`send_eq_advance`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendDist.lean#L62)
  and
  [`send_eq_encaps`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendDist.lean#L78)
  rewrite `send` as `keygen` or `encaps pk` followed by `pure` of an explicit outcome, under the
  respective gates, and `send_plain_of_not` says that any other send emits no key and keeps the
  epoch. With `pairPotential` and `pairFailure` presenting the two parties with the sender
  first:
  - *advance*: the potential gains `φ(pk, sk)` for the fresh key pair; averaged over key
    generation this is at most `ε` (`wp_keygen_le`, from
    `correctnessError_eq_avg_keypair`);
  - *encapsulation* to the peer's `pk`, with retained `sk`: with probability at most `φ(pk, sk)`
    the flag is set (score `1`), otherwise the term `φ(pk, sk)` leaves the potential
    (`pairPotential_encaps`, `pairFailure_encaps`, `wp_encaps_le`); the expected
    score is at most the old score;
  - *plain*: nothing changes (`pair_plain`).

  `tracked_sendA_score_le` and `tracked_sendB_score_le` are the two orientations.
- **Combined.**
  [`tracked_step_score_le`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean#L664)
  states the bound for every query, with `+ ε` only when `isSendQuery t`; from a state with the
  flag set, the score stays `1`.

### 11.4 Assembly

In
[`Quantitative/Main.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean),
the initial state retains no secret keys, so `kemFailure_init` and `trackedScore_init` are
immediate.
[`trackedBiKem_preservesInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L175)
is `trackedImpl_preserves` applied to `gameInv_step_of_noFailure`, and
[`tracked_bad_le`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L197)
feeds `tracked_step_score_le` into `SCKAScheme.tracked_bad_le_of_score_step`. Finally,
`correctness_failure_le` in `Correctness.lean` feeds `tracked_bad_le` into
`SCKAScheme.correctness_failure_le_of_tracked_bad`, together with `correctnessExp_eq_map`.

## 12. The perfectly correct KEM: probability one without a query bound

[`PerfectKEM.lean`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean) proves the
facts, and `correctness_of_perfectKEM` in `Correctness.lean` combines them.
`correctness_of_perfectKEM'` needs the adversary to make at most `q` send queries, because the
potential argument does. For a perfectly correct KEM, the proviso of `gameInv_step_of` holds at
every state, so neither the flag nor the potential is needed.

[`DecapsCorrectOnSupport`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L37)
is the pointwise fact the proof uses: for every key pair in the support of key generation and
every encapsulation in the support of `encaps`, decapsulation returns the encapsulated key.
[`decapsCorrectOnSupport_of_perfectlyCorrect`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L43)
derives it from `Pr[correctnessExperiment = true] = 1`: `prEvent_eq_one_iff` gives that every
result in the support of `correctnessExperiment` is `true`, and a counterexample would put
`false` in the support.
[`transcriptDecaps_of_support`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L69)
applies it to the key pair and encapsulation recorded in a transcript, which lie in those
supports (`keypair_mem`, `enc_mem`), and
[`gameInv_preserved`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L79)
uses it to discharge `DecapsReady` in `gameInv_step_of` at every state, giving
`QueryImpl.PreservesInv`.

[`simulateQ_gameInv`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L101)
lifts this to every adversary with VCVio's `simulateQ_run_preservesInv`.
[`correctness_of_perfectKEM`](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L154)
then shows `Pr[G(Adv) = false] = 0` from `correctnessExp_eq_map`, `prEvent_eq_zero_iff` and the
invariant's `correct` field, and converts it to `Pr[G(Adv) = true] = 1` with
`prEvent_eq_false_eq_one_sub`.

## 13. Sends are never rejected

`send` has two error exits: chunking the own public key when none is retained, and
encapsulating to the peer's public key when none was decoded. The game does not observe them, so
they are covered separately.
[`send_ne_none`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/SendTotal.lean#L32)
shows that a party satisfying `PartyInv` takes neither exit: `ekRec_res` supplies the decoded
peer key, and `ek_acked` with `keypair_current` rule out a missing own key.
[`sendA_ne_none`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/SendTotal.lean#L91)
and
[`sendB_ne_none`](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/SendTotal.lean#L99)
restate it for a game state satisfying `GameInv`. `sends_never_rejected_of_noFailure` combines
them with `trackedBiKem_preservesInv`, and `sends_never_rejected_of_perfectKEM` with
`simulateQ_gameInv`.

## 14. Idioms you will meet

- **Parity by cases.**
  `cases role <;> simp only [Role.offset, Role.reqParity, Role.resParity] at h ⊢ <;> omega`.
  `omega` does not see through `if role = .A then … else …`; case on the role first.
- **Decidable `if`s.** Rewriting under `if c then a else b` with an `iff` about `c` fails,
  because the `Decidable` instance depends on `c`. Use `by_cases` with `if_pos` / `if_neg`, or
  state the goal with `show` / `change` so that the condition is syntactically the one in your
  hypothesis.
- **`Int.toNat`.** Game tables are indexed by `ℕ`, local epochs by `ℤ`. Every key-table field
  carries `0 < e`, and `Int.toNat_of_nonneg` recovers `e` from `e.toNat`.
- **Section variables.** `MainInvariant/Recv.lean` keeps both invariants and the message
  hypothesis as section variables with `include`; lemmas that do not use the receiver's
  invariant say `omit hR in`.
- **`recordKey`.** Both step lemmas state the updated key table as `recordKey keys key?`, which
  reduces by `simp` once `key?` is known; `MainInvariant/Game.lean` cases on `key?` first.
