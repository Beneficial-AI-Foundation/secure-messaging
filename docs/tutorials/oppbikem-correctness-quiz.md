# Opp-BiKEM correctness questions and answers

The central proof idea is that both parties agree with one shared transcript. The
invariant ties their key tables, retained key material, messages, acknowledgements,
chunk buffers, and reported epochs to that transcript. Correct erasure codes recover
the recorded payloads; KEM correctness supplies the remaining decapsulation equation.

The first section collects all six rounds asked in the chat, including follow-ups
and source clarifications, with polished answers. Round 6 was asked when the game
ended; its answer is supplied here. The second section gives 36 additional questions
and answers for continuing through the rest of the proof.

Read this alongside the [correctness tutorial](oppbikem-correctness-tutorial.md).
Unless a question explicitly changes the assumptions, the erasure codes are correct
and KEM decapsulation is deterministic. Statements about invariant states assume
`PartyInv` or `GameInv`; statements about all reachable states require the
appropriate perfect-KEM or tracked-run theorem.

## Questions from the game

### 1 Replaying an honest ciphertext message

**Question.** Assume a perfectly correct KEM. A receives an honest ciphertext
message, reconstructs the ciphertext, and emits the key for epoch `e`. Later, the
adversary delivers the same message again, possibly after A has advanced. How do
receive success, key emission, and the reported epoch fit together? Why does key
uniqueness not force rejection of the replay?

**Answer.** A successful receive need not emit a key. The return type has two
separate `Option` layers:

```lean
Option (Option (ℕ × K) × ℕ × State PK SK C Sym)
```

Outer `none` means receive rejection. Outer `some` with inner `none` means
successful processing without emitting another key.

When the requester epoch remains `e`, the original decapsulation has inserted
`e` into `ctRec`. For this replay the ciphertext guard
`q ∉ ack.ctRec ∧ ρ.bit = some 1` is false, so the ciphertext is not decapsulated
again and no key is emitted. If A's requester epoch has advanced beyond
`ρ.tRes`, execution instead takes the earlier stale-message branch.

The game tests key uniqueness only when the receive emits `some (tI, key)`.
Emitting the epoch-`e` key twice would fail even if the two keys were identical,
because A's table already contains a key at `e`. Accepting the replay with no key
emission avoids that violation.

**Follow-up.** After the requester epoch advances, does execution reach the
ciphertext guard? What is the complete return value?

**Answer.** No. If `ρ.tRes < st.req.reqEpoch`, the result is:

```lean
some (none, ρ.sendingEpoch, { st with ack := ack })
```

Here `ack := recvAck role st.ack ρ` has already been computed. The stale branch
updates acknowledgements, skips payload processing and `recvFinish`, emits no
key, and reports the message's original sending epoch. For a replay of a previously
processed message, inserting its flags again is idempotent because acknowledgement
sets only grow. The stale replay therefore leaves the local state unchanged.
More generally, a receive emitting no key does not by itself imply an unchanged
local state: it can collect chunks, install a public key, or process new flags.

**Follow-up.** Why does the replay leave `tcurA` unchanged? What inequality is
needed, and why does the original delivery establish it?

**Answer.** The game sets:

```text
tcurA' = max tcurA trcv
trcv   = ρ.sendingEpoch
```

Unchanged progress requires `ρ.sendingEpoch ≤ tcurA`; using `max` alone
only proves that progress does not decrease. The original delivery made the game
epoch at least `ρ.sendingEpoch`. In a correct run later receives use `max`,
later accepted sends satisfy the monotonicity assertion, and the other operations
preserve A's game epoch. Hence the inequality still holds on replay.

**Follow-up.** Why does the stale branch report `ρ.sendingEpoch`? What could
break if it reported `st.req.reqEpoch.toNat` instead?

**Answer.** The game compares `trcv` with the sending epoch `tsnd` stored
with this particular message. `MessageInv.epoch` says that stored value equals
`ρ.sendingEpoch`. The current requester epoch describes A's local KEM progress
and can differ from the message's sending epoch. Returning it could violate
`trcv == tsnd`.

**Clarification.** Why require matching epochs at all?

**Answer.** The interface must identify the same epoch for a message on both
sides. Key consistency says that the parties agree on keys at a given epoch; it
does not say that they select the same epoch for a particular message. For example,
a messaging layer using the reported epoch to select key material would process a
delayed epoch-2 message with epoch-2 material even if the receiver had reached
epoch 5. Reporting 5 could select different material despite agreement between
the parties' tables at both epochs. This illustrates the purpose of the interface
guarantee; SCKA itself does not perform application-message encryption here.

**Follow-up.** If A has every key through epoch 5 but reports `trcv = 5` for
an epoch-2 message, why does known prefix still pass?

**Answer.** The check only asks whether keys exist at every positive epoch up to
`max tcurA trcv`. With `tcurA = 5` and all those keys present, it passes.
It does not examine the message's original epoch, so it cannot replace the matching
epoch assertion.

Sources: [recvSpec](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L46),
[recvAUpdate](../../SecureMessaging/SCKA/Correctness.lean#L74),
[MessageInv](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L101),
and [SCKA epoch notation](../SecureMessagingDocs/Chapters/SCKA/Defs.lean#L56).

### 2 Deriving equality of the parties' keys

**Question.** Suppose `s.keyA 2` and `s.keyB 2` both contain keys. How do
`key_req`, `key_res`, and the shared transcript prove that the keys are equal?

**Answer.** At epoch 2, A is the requester and B is the responder. B's
`key_res` gives:

```lean
s.keyB 2 = (T 2).key
```

A's `key_req` gives:

```lean
s.keyA 2 =
  if (2 : ℤ) ∈ s.stA.ack.ctRec then (T 2).key else none
```

If epoch 2 were absent from A's `ctRec`, A's entry would be `none`,
contradicting the premise that it contains a key. Therefore the first branch
applies, and A's entry also equals `(T 2).key`. Both party invariants use the
same `T`, so their entries are equal. Equality of the contained keys follows
from injectivity of `Option.some`.

**Follow-up.** Why is saying “once acknowledged” insufficient by itself?

**Answer.** It states a conditional consequence without establishing its
condition. The proof must derive acknowledgement from the premise that A's table
entry is present, by ruling out the `else none` branch.

**Clarification.** What is `(T 2).key), and why is A's table equal to it?

**Answer.** `EpochTranscript.key` is defined by:

```lean
def key (tr : EpochTranscript kem) : Option K := tr.enc.map Prod.snd
```

Thus `enc = some (c, k)` gives `key = some k`. This is the optional
encapsulated shared key, not the public key or secret key. A's equality follows
from `key_req` and acknowledgement, as above. It is a consequence of the
assumed invariant; the receive proof must establish that the invariant survives
decapsulation.

**Source clarification.** Where does “in A's invariant, `ownKey` is
`s.keyA`, and `st` is `s.stA`” come from?

**Answer.** The A clause of `GameInv` is:

```lean
PartyInv .A ecEk ecCt T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA
```

Match its arguments with the parameter order after `T` in `PartyInv`:

| Parameter | A's argument |
| --- | --- |
| `st` | `s.stA` |
| `peer` | `s.stB` |
| `ownMsgs` | `s.msgA` |
| `ownKey` | `s.keyA` |
| `peerKey` | `s.keyB` |
| `tcur` | `s.tcurA` |

Sources: [PartyInv parameters and fields](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L144),
[GameInv](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L277),
and [EpochTranscript.key](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L152).

### 3 Honest samples and KEM decapsulation

**Question.** With an imperfect KEM, do honestly sampled `(pk, sk)` and
`(c, k)`, together with deterministic decapsulation, guarantee recovery of
`k`? What extra fact does the receive proof need?

**Answer.** No. Support membership says that these values are possible outputs of
`keygen` and `encaps pk`. Those membership proofs alone do not certify
decapsulation correctness. Determinism means that a fixed `(sk, c)` has a fixed
outcome; that outcome can be `none` or `some k'` with `k' ≠ k`.

For a pending received epoch, the proof needs:

```lean
hDet.decapsDet sk c = some k
```

where `sk`, `c`, and `k` are the values recorded in the shared transcript.
The receive lemma takes this as `hdec`; `DecapsReady` supplies the corresponding
condition for all unacknowledged requester-parity epochs.

**Follow-up.** If erasure-code decoding succeeds but KEM decapsulation returns
a wrong `some k'`, does the receive emit it and insert `q` into `ctRec`?
Would `key_req` survive?

**Answer.** Yes, it emits the returned key and inserts `q`. The local `k`
bound by `let k ← hDet.decapsDet sk c` is whatever decapsulation returns;
`recv` has no transcript argument with which to compare it. The transition
also removes the secret key for `q` and clears the buffer.

The game records `some k'`, while the acknowledged branch of `key_req`
requires `(T q).key = some k`. With `k' ≠ k`, the invariant fails.
The peer has already emitted the encapsulated key, so the game's key-consistency
assertion fails as well.

**Clarification.** Shouldn't the code refuse to acknowledge a wrong key?

**Answer.** This code cannot identify a wrong successful output: the expected
shared key is known to the responder and to the proof transcript, not to the
requester before decapsulation. A returned `some` lets execution continue.
The correctness proof therefore excludes this case using `hdec` while it
preserves the invariant. With an imperfect KEM, such cases are possible and are
covered by the probabilistic failure bound.

Erasure-code decoding failure is a different case. It returns a successful receive
with no key, retaining the accumulated chunks. That branch does not insert `q`
as a completed local decapsulation; acknowledgement flags were nevertheless
processed earlier by `recvAck`. Also, `ctRec` stores epochs, not keys.

**Follow-up.** What if decapsulation returns `none` instead?

**Answer.** The `Option` bind propagates it to outer `none` for the entire
`recvSpec`. No successor state is returned. Since the correctness receive
oracle was delivering a recorded honest message, it retains the previous protocol
state and sets `correct := false`.

Sources: [EpochTranscript](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L73),
[decapsulation branch](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L67),
[partyInv_recv_step](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L975),
[DecapsReady](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L36),
and [oracleRecvA](../../SecureMessaging/SCKA/Defs.lean#L502).

### 4 Correctness and rejected sends

**Question.** Does probability-one success of the correctness game imply that
every send is accepted? What happens for a hypothetical scheme whose two send
algorithms always return `none`?

**Answer.** The game alone gives no such implication. A rejected send returns
`none` without changing the game state or `correct`. An always-rejecting
scheme with successful initialization records no messages or keys and can leave
`correct = true` throughout.

**Follow-up.** Can the adversary still issue receive queries when no messages
exist? Which `none` branch runs, and how does it differ from honest-message
rejection?

**Answer.** Receive queries remain allowed. If `state.msgB n = none`,
`RecvA n` returns `none` without modifying the state. It has no recorded
message to test. If a recorded message exists but `scka.recvA` returns
`none`, the oracle instead sets `correct := false`. Identical outward
responses therefore need not have identical effects on the correctness flag.

OppBiKEM separately proves `send_ne_none` on invariant states and lifts it to
reachable states with `sends_never_rejected_of_perfectKEM`, or to tracked states
whose failure flag is clear with `sends_never_rejected_of_noFailure`.

Sources: [oracleSendA](../../SecureMessaging/SCKA/Defs.lean#L279),
[oracleRecvA](../../SecureMessaging/SCKA/Defs.lean#L502),
and [send totality](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/SendTotal.lean#L32).

### 5 Ruling out a missing own public key

**Question.** Assume `PartyInv`, a positive current key epoch
`e = st.res.resEpoch + role.offset`, and no initial epoch advance in this call.
The public-key branch requires `e ∉ st.ack.ekRec`. Why can't its lookup of the
own public key return an error? Account for both alternatives in `ek_acked`.

**Answer.** Suppose `st.req.ek = none`. The field `ek_acked` gives:

```lean
(T e).keypair = none ∨ e ∈ st.ack.ekRec
```

The first alternative contradicts `keypair_current`, which gives
`(T e).keypair.isSome = true` because this current key epoch is positive.
The second contradicts the branch guard `e ∉ st.ack.ekRec`. Therefore the
own public key cannot be absent in this branch.

“It was never generated” and “it was removed after acknowledgement” can help
describe the protocol, but the proof uses these present-state conditions. In
particular, `keypair_current` guarantees existence at the positive current key
epoch, not at every positive epoch.

Sources: [sendWith](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L233)
and [ek_acked and keypair_current](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L187).

### 6 The bootstrap exception

**Question.** A initially has no public key and an empty `ekRec`. Why doesn't
its first send hit the missing-public-key error? Explain the initial advance guard,
the resulting responder and key epochs, and the purpose of `ctRec = {-1, 0}`.
Would `ctRec = ∅` work instead?

**Answer.** Initially A has `tRes = -1`, `role.offset = 1`, and `ek = none`.
The advance guard asks whether `ek` is absent and both `tRes` and
`tRes + offset` belong to `ctRec`. Those two epochs are `-1` and `0`,
so the bootstrap set makes the guard true.

The send samples a key pair, changes `tRes` to `1`, sets the new key epoch
to `1 + 1 = 2`, retains its secret key, and sets `ek := some newEk`.
The later public-key branch therefore finds a key and can send its chunk.
There is no emitted shared KEM key yet; generating a key pair is distinct from
encapsulating.

With `ctRec = ∅`, the advance guard would be false. The old key epoch
`0` would still be absent from the empty `ekRec`, so execution would reach
the public-key branch with `ek = none` and return an error.

For comparison, B starts at responder epoch `0` with offset `-1`. Its
bootstrap guard checks `0` and `-1`, advances to responder epoch `2`,
and generates its first key pair for epoch `1`.

Sources: [init](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L191),
[Role.offset](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L73),
and [advance guard](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L247).

## Continuation questions

The following sequence completes the study of the protocol invariants, the
erasure-code arguments, the quantitative proof, and the perfect-KEM theorem.
Answers are included so it can also serve as an open-book reference.

### 7 Roles and the different epochs

**Question.** What are `resEpoch`, `reqEpoch`, the current own key epoch, the
sending horizon, a message's sending epoch, and the game epoch? Why shouldn't they
be treated as one counter?

**Answer.** A requests even epochs and responds at odd ones; B does the reverse.
`resEpoch` identifies the party's current responder exchange, while `reqEpoch`
identifies its current requester exchange. The epoch of its current own key pair
is `resEpoch + role.offset`, with offset `1` for A and `-1` for B.
The sending horizon is computed from ciphertext acknowledgements. A message
records that horizon when sent. The game epoch records externally reported
progress: a send sets it to `tsnd`, and a receive takes `max tcur trcv`.
These quantities describe different exchanges, knowledge, or points in time.

Sources: [roles and offset](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L73),
[role parities](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L39),
and [epoch relationships](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L30).

### 8 Reading acknowledgements by parity

**Question.** Does membership in `ctRec` always mean “I decapsulated this
ciphertext”? What does membership in `ekRec` mean?

**Answer.** The interpretation depends on the party's role at that epoch.
At requester parity, `ctRec` records its own completed ciphertext receipt and
decapsulation; at responder parity, it records that the peer has received its
ciphertext. The invariant relates the latter to the peer's requester-parity
receipt. At responder parity, `ekRec` is backed by the locally decoded peer
public key. At requester parity, it is backed by the peer's decoded copy of the
party's own public key. The sets also contain or acquire entries through
acknowledgement flags, so their meaning comes from the invariant, not merely their
names. Bootstrap ciphertext entries are special placeholders.

Source: [acknowledgement fields of PartyInv](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L225).

### 9 The transcript and its updates

**Question.** Is the transcript protocol state? Why is it existential and shared?
Why can a send change it while a receive keeps it unchanged?

**Answer.** The transcript is a proof witness, not an argument passed to the
protocol's send and receive algorithms. `GameInv` requires one witness consistent
with both parties, rather than prescribing a fixed transcript for every execution.
A send can sample a new key pair or encapsulation and therefore extends the witness:
`ofKeypair` records a generated pair, and `setEnc` records an encapsulation.
A receive recovers material already generated by a send, so it preserves the same
transcript. Sharing the witness gives both parties a common reference for equality
of recovered payloads and emitted keys.

Sources: [EpochTranscript](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Transcript.lean#L73),
[GameInv](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L277),
[send step](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L931),
and [receive step](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L975).

### 10 The three kinds of send

**Question.** Which sends introduce new KEM samples? Could one invariant send
both advance with key generation and encapsulate?

**Answer.** A plain send retransmits or waits without changing the transcript.
An advancing send generates a key pair for the new own key epoch. An encapsulating
send samples a ciphertext and shared key at the current responder epoch.
On invariant states, one send cannot both advance and encapsulate. Encapsulation
requires acknowledgement of the sender's own public key; the just-generated public
key cannot already have been decoded by the peer. The proof rules this out using
the public-key acknowledgement fields, transcript consistency, and absence of
future key pairs. This separation also lets the quantitative proof charge fresh
key generation separately from completing an existing pending instance.

Sources: [sendWith](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L233),
[partyInv_send_step](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L931),
and [send classification in the tutorial](oppbikem-correctness-tutorial.md#8-the-send-step).

### 11 Why the decision tree needs an equivalence proof

**Question.** Why introduce `recvSpec` instead of proving everything directly
about `recv`? What prevents a proof of the wrong implementation?

**Answer.** The imperative-style `recv` uses mutable bindings and early returns,
which elaborate into a deeply nested term. `recvSpec` names intermediate updates
and presents the same choices as a decision tree. This makes subsequent proofs
follow named conditions rather than repeatedly splitting the elaborated implementation.
`recv_eq_recvSpec` establishes equality for every input, including arbitrary
states and messages. Thus facts proved through the decision tree apply to the
actual implementation; the equivalence itself does not assume the invariant.

Source: [recvSpec and recv_eq_recvSpec](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L9).

### 12 Local outcomes and game updates

**Question.** Why does the proof name pure updates such as `sendAUpdate` and
`recvAUpdate`? What cases must a receive oracle proof handle?

**Answer.** The pure updates isolate the game assertions and state changes from
`StateT` plumbing. Support lemmas characterize exactly which local outcomes can
produce which game successors. A receive has three cases: a missing recorded
message leaves the state unchanged; rejection of a recorded message changes only
`correct` to false; acceptance installs the local successor and applies the
receive update. A send has rejection with no state change, or acceptance followed
by its send update. Distribution equalities additionally retain the sampling
probabilities needed for expected-payoff proofs.

Source: [oracle updates and outcome lemmas](../../SecureMessaging/SCKA/Correctness.lean#L34).

### 13 The scope of erasure-code correctness

**Question.** Does `ec.Correct` say that any sufficiently large chunk set
decodes? Why must the buffer invariant establish honesty?

**Answer.** No. `Correct` applies to a set formed by encoding one message at
a set of positions `I`. It requires recovery of that message when
`nchunk ≤ I.card`, and `none` below threshold. It does not prescribe
behavior on arbitrary mixed or corrupted chunks, even if their positions are
distinct. The buffer proof must identify its contents as `payloadChunks` of
one transcript payload so that these correctness clauses apply.

Sources: [ErasureCode.Correct](../../SecureMessaging/ErasureCode/Defs.lean#L180)
and [BufferConsistent](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L68).

### 14 Distinct chunks and distinct positions

**Question.** Does using a `Finset` automatically prevent counting the same
position twice? What happens under exact replay or counter wraparound?

**Answer.** A finite set removes identical pairs. It can still contain
`(i, a)` and `(i, b)` with `a ≠ b`, which are different pairs at the same
position. `Decodable` therefore includes injectivity of the position projection.
An honest codeword has exactly one symbol at each position, so honest chunk sets
satisfy that requirement. Exact replay adds an already present pair and cannot
increase the number of positions. The encoding counter wraps modulo `N`;
for the same payload, wrapping repeats the same indexed symbol rather than
creating a new position. Equal symbols at different positions still count as
different chunks because their indices are retained.

Sources: [Decodable and encodeChunks](../../SecureMessaging/ErasureCode/Defs.lean#L122),
[counterIndex](../../SecureMessaging/ErasureCode/Defs.lean#L85),
and [insertChunkAndDecode](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L350).

### 15 Recovering a typed payload

**Question.** The erasure code decodes symbol blocks. How does the proof recover
a public key or ciphertext, and why can parsing not introduce another failure on
honest decoded blocks?

**Answer.** `ErasureCodePayload` supplies serialization and parsing with
`parse (serialize payload) = some payload`. Its decoder first checks the natural
indices are within range, converts them to bounded indices, invokes the code's
decoder, then parses the recovered block. Honest `payloadChunks` have valid
indices and convert back to the encoded serialized block. Above threshold,
code correctness returns that block and `parse_serialize` returns the original
typed payload. Below threshold, code correctness returns `none` before parsing.

Sources: [ErasureCodePayload](../../SecureMessaging/ErasureCode/Defs.lean#L67),
[payloadChunks_valid](../../SecureMessaging/ErasureCode/Payload.lean#L62),
[decode_payloadChunks](../../SecureMessaging/ErasureCode/Payload.lean#L103),
and [decode_payloadChunks_none](../../SecureMessaging/ErasureCode/Payload.lean#L120).

### 16 One buffer for two payload types

**Question.** How can one chunk buffer safely collect both public keys and
ciphertexts? Why does the invariant require it to remain below threshold?

**Answer.** `BufferConsistent` selects a stage from the receiver's state.
If the requester epoch is acknowledged in `ctRec`, the buffer is empty.
Otherwise, if the peer's key at `reqEpoch - offset` is missing, the buffer
holds honest chunks of that public key. Once that key is installed, the buffer
holds honest chunks of the ciphertext for `reqEpoch`. An as-yet ungenerated
payload has an empty buffer.

The collected position set is below the relevant threshold. Inserting another
honest chunk either leaves it below threshold, retaining the chunks, or allows
decoding. Installing a decoded public key clears the buffer before the ciphertext
stage; successful decapsulation clears it and acknowledges the requester epoch.
The below-threshold property is what makes each next decoding attempt predictable
from the erasure-code correctness clauses.

Sources: [BufferConsistent](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L68)
and [receive branches](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L57).

### 17 Catching up by exactly two

**Question.** `recvReq` only adds two when a message is ahead. Why is that enough
even though the adversary can delay and reorder messages arbitrarily?

**Answer.** For a recorded honest message, the sender's invariant bounds
`ρ.tRes ≤ stR.req.reqEpoch + 2`. Its responder parity is the receiver's
requester parity. A non-stale message also satisfies
`stR.req.reqEpoch ≤ ρ.tRes`. With matching parity, the only possibilities
are equality or a difference of two. Consequently `recvReq stR ρ = ρ.tRes`.
The argument relies on the parties' lockstep invariant, not on a restriction on
the delivery schedule.

Source: [recv_tRes_le and recvReq_eq_tRes](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L105).

### 18 The buffer when the requester epoch advances

**Question.** Why doesn't advancing the requester epoch carry old ciphertext
chunks into a new epoch's buffer?

**Answer.** `recv_advance_prev` proves that the old requester epoch is already
in the receiver's `ctRec` whenever an honest message advances it. The sender
could only have advanced after the corresponding prior exchanges were completed,
and the acknowledgement invariants transfer that fact to the receiver. The first
branch of `BufferConsistent` then says that the old buffer is empty. Thus the
algorithm can advance without mixing retained chunks from the previous epoch,
even though advancing `q` itself does not explicitly clear the buffer.

Sources: [recv_advance_prev](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L121)
and [BufferConsistent](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L68).

### 19 Finding the retained secret key

**Question.** After ciphertext reconstruction, why must secret-key lookup
succeed? Why is the key found the transcript's key, and why is removing it safe?

**Answer.** The transcript contains the requester's key pair for the received
ciphertext. `T_dk` requires that pair's secret key to remain in the list while
the epoch is unacknowledged. The list-shape invariant supports the required
lookup, and `dk_T` identifies a retained key with the transcript's secret key.
`hdec` then supplies correct decapsulation. The transition acknowledges the
epoch and removes its secret key; subsequent deliveries skip its decapsulation
because the epoch is acknowledged or the message is stale. The game key table
retains the emitted shared key independently of the protocol's secret-key list.

Sources: [dk_T, T_dk, and dk_shape](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L176)
and [ciphertext receive](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L73).

### 20 The sending horizon and known prefix

**Question.** Why define the sending horizon using two adjacent ciphertext
acknowledgements? How does it imply that every required game key is present?

**Answer.** The horizon is the maximum of `Int.toNat t` among acknowledged
`t` whose predecessor `t - 1` is also acknowledged, with default zero.
Those adjacent epochs cover both role parities. On invariant states, the
downward-closure fields for each parity give every positive acknowledgement
through that horizon. A single maximum acknowledgement would not by itself
establish the opposite parity's prefix.

The proof chain is `sendingHorizon_attained`, then `ctRec_prefix` and
`sendingHorizon_prefix`, then `keys_of_ctRec`, and finally
`knownPrefix_of_partyInv`. `keys_of_ctRec` uses both party invariants to
show that an acknowledged positive epoch has a key in both tables. The
`tcur_le` field places game progress within this horizon. Epoch zero is
explicitly exempted by the game and has no table key.

Sources: [sending horizon and prefix lemmas](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L299)
and [knownPrefix](../../SecureMessaging/SCKA/Correctness.lean#L36).

### 21 Preserving the horizon bound on receive

**Question.** A receive takes `max tcur trcv`. Why can't a high reported
message epoch move the receiver beyond its own sending horizon?

**Answer.** Message honesty says that the sender acknowledges every positive
epoch through the message's sending epoch. The parity-specific acknowledgement
relations and the incoming flags establish those acknowledgements at the receiver
after `recvAck`. Thus `recv_sendingEpoch_le` bounds the report by the new
local horizon. The old `tcur` was already bounded by the old horizon, and
acknowledgements grow, so it is bounded by the new one as well. Taking the maximum
preserves the bound. This is the content of `recv_tcur_le`.

Source: [recv_sendingEpoch_mem through recv_tcur_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L181).

### 22 Honesty of old messages

**Question.** Why must `MessageInv` relate recorded messages to the sender's
current state? Isn't honesty at creation time sufficient?

**Answer.** The adversary can deliver any recorded message much later. The
receive proof reads it through the sender's current `PartyInv.msgs`, so its
honesty must remain usable after the sender changes state and the transcript
extends. Payload identities and the recorded sending epoch stay fixed, while
bounds on carried epochs and acknowledgement backing must continue to hold.
`MessageInv.of_send` establishes honesty for the new message;
`MessageInv.transfer` maintains old messages after a send, and
`MessageInv.mono` maintains them after a receive.

Sources: [MessageInv](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L101),
[MessageInv.transfer](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L80),
and [MessageInv.mono](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L233).

### 23 The stale-message cleanup hazard

**Question.** A stale receive skips `recvFinish`. What would go wrong if it
newly acknowledged the receiver's current outgoing ciphertext? Which invariant
fields prevent that?

**Answer.** Normal cleanup clears an acknowledged outgoing ciphertext. A stale
receive updates flags but skips that cleanup. If it first acknowledged the current
responder epoch, the ciphertext could remain stored despite acknowledgement.
The next send could advance while retaining that ciphertext and then transmit it
under the new epoch, breaking transcript consistency.

`msgs_stale` prevents a stale message from introducing a new ciphertext
acknowledgement: its flagged epoch is already in the receiver's `ctRec`.
`msgs_flag_mono` relates flags in messages at different responder epochs and
helps preserve `msgs_stale` when the receiver advances. This is why historical
message facts are part of the main invariant rather than just payload correctness.

Sources: [message flag invariants](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L256),
[recv_stale_flag](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L175),
and [recvFinish](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L37).

### 24 Ruling out a missing peer public key

**Question.** How does send totality rule out the other error exit: trying to
encapsulate when `ekPeer tRes = none`?

**Answer.** The encapsulation branch requires `tRes ∈ ack.ekRec`.
The responder epoch has responder parity, so `ekRec_res` says the local decoded
peer key at that epoch is present. This contradicts the failed lookup. The same
argument applies to an epoch shifted by two, since the parity is unchanged.
Together with the missing-own-key argument and the bootstrap case, this excludes
both send errors on invariant states.

Sources: [encapsulation guard](../../SecureMessaging/SCKA/OppBiKEM/Construction.lean#L266),
[ekRec_res](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L242),
and [send_ne_none](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/SendTotal.lean#L32).

### 25 Discharging the game assertions

**Question.** How do the local invariant step lemmas establish the game's
Boolean assertions? Where does each receive-side assertion come from?

**Answer.** `partyInv_recv_step` proves successful reception, a matching
reported epoch, the post-state's known prefix, freshness and consistency of any
emitted key, and both updated party invariants. `gameInv_step_of` applies
these results to the pure game update and closes its Boolean conjunction.

| Receive assertion | Main supporting fact |
| --- | --- |
| Reception succeeds | `T_dk` supplies the secret key and `hdec` supplies successful decapsulation |
| Matching epoch | The report is `ρ.sendingEpoch`, and `MessageInv.epoch` identifies it with stored `tsnd` |
| Unique key epoch | `key_req` gives an empty local entry before unacknowledged decapsulation |
| Consistent key | The peer's `key_res` identifies its key with the transcript, and `hdec` identifies the received key |
| Known prefix | The post-state invariants and `knownPrefix_of_partyInv`, using the receive horizon bound |
| Nondecreasing game epoch | The update uses `max`; there is no separate receive monotonicity assertion |

For a send, `partyInv_send_step` supplies analogous key and prefix facts,
with `tcur_le` giving sending monotonicity. It also constructs the updated
shared transcript.

Sources: [partyInv_recv_step](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Recv.lean#L975),
[partyInv_send_step](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Send.lean#L931),
and [gameInv_step_of](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L50).

### 26 Initialisation and preservation without circular reasoning

**Question.** `GameInv` contains `correct = true`. Isn't using it to prove
correctness circular? How does a one-query result become a result for an adversary?

**Answer.** Defining an invariant to include the desired property is legitimate;
the work is to prove it initially and preserve it using explicit hypotheses.
`gameInv_init` constructs the empty shared transcript and checks both party
invariants. In particular, initial requester epochs 0 and -1 are already in the
bootstrap `ctRec`, so their buffers satisfy the empty-buffer branch.

The one-query theorem proves preservation by examining all supported oracle
outcomes, including refuting rejected honest receives under `hdec`.
When a perfect KEM supplies `DecapsReady` universally, the generic
`simulateQ_run_preservesInv` theorem lifts this to adaptive adversary
executions. With an imperfect KEM, the tracked proof instead preserves the
weaker flag-dependent invariant. Assuming the final `GameInv` without this
initialisation and preservation argument would leave the essential work undone.

Sources: [gameInv_init](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Init.lean#L27),
[gameInv_step_of](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant/Game.lean#L50),
and [simulateQ_gameInv](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L101).

### 27 Detecting a bad KEM instance before reception

**Question.** How can `kemFailure` become true before the requester receives
the ciphertext? Must the ordinary game's `correct` bit already be false?

**Answer.** The analysis reads both parties' state and the game key tables.
For the peer's current responder epoch, `kemFailureAt` checks that the requester
retains `sk`, the responder retains `c`, and the responder has recorded
`k`, then tests `decapsDet sk c ≠ some k`. These values are already present
after encapsulation; ciphertext delivery is unnecessary for this test.

The ordinary game can still have `correct = true`: the requester has not
emitted a conflicting key or rejected a delivery. The tracked analysis records
a bad KEM instance early enough to stop relying on `DecapsReady`. This is
global proof bookkeeping, not a check the requester performs during `recv`.

Source: [kemFailureAt and kemFailure](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L46).

### 28 Why the failure flag must be sticky

**Question.** Why retain a flag recording whether a bad instance ever occurred
instead of checking only the final `kemFailure` predicate?

**Answer.** `kemFailure` examines current retained material. That material
can disappear: for example, a wrong successful decapsulation removes the retained
secret key, after which the predicate's lookup can return `none` even though
the game has already failed. A final predicate alone could therefore miss the
earlier bad instance. The tracked handler updates:

```text
b' = b ∨ kemFailure s'
```

so the flag never clears. It preserves the history needed to bound failure over
the entire run. The handler performs the ordinary query and adds this bookkeeping;
forgetting the flag recovers the ordinary execution.

Sources: [tracked execution](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L46)
and [generic bad-flag handler](../../ToVCVio/OracleComp/SimSemantics/StateT/BadFlag.lean#L47).

### 29 The invariant while the flag is clear

**Question.** What does `J (s, b)` say, and how does “not bad” supply the
decapsulation hypothesis? Is `GameInv` alone enough?

**Answer.** The tracked invariant is:

```text
J (s, b) := b = true ∨ (GameInv s ∧ kemFailure s = false)
```

While the flag is false, it gives both the main invariant and absence of a bad
instance. The two party invariants identify the relevant retained secret key,
ciphertext, and responder key with the transcript. Their presence lets
`kemFailure = false` supply the required equality. The lemmas
`decaps_of_noFailure` and `decapsReady_of_noFailure` formalize this bridge.
Without the party invariants, a false predicate could merely mean some lookup
was missing.

`GameInv` alone does not require correctness of a pending decapsulation.
An imperfect KEM can have an honest, transcript-consistent encapsulation whose
eventual decapsulation is wrong. `DecapsReady` is therefore a separate
hypothesis of `gameInv_step_of`. Once the flag is set, `J` no longer
requires `GameInv`.

Sources: [tracked invariant](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L77),
[decaps_of_noFailure](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L300),
and [decapsReady_of_noFailure](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/RecvStep.lean#L311).

### 30 Average error and fixed-key error

**Question.** If the KEM's correctness error is `ε`, can the proof assume
every generated key pair has conditional failure probability at most `ε`?
Why does this matter against an adaptive adversary?

**Answer.** No. Define `φ(pk, sk)` as the probability that encapsulation to
`pk` produces a ciphertext and key that decapsulation with `sk` does not
match. The KEM's error is the average over generated key pairs:

```text
ε = Σ_(pk,sk) Pr[keygen = (pk,sk)] · φ(pk,sk)
```

Some supported pairs can have much larger error than the average. Conditioning
on an execution history can select such pairs, so a blanket “every future
encapsulation costs at most ε” assertion is unjustified. The proof charges
`φ` when the pair is generated, whose expected cost is bounded by `ε`,
and retains that particular pair's risk until encapsulation. Its per-state
bounds remain valid when later queries are chosen adaptively.

Sources: [keypairFailure](../../SecureMessaging/KEM/CorrectnessError.lean#L41)
and [correctnessError_eq_avg_keypair](../../SecureMessaging/KEM/CorrectnessError.lean#L59).

### 31 Locating the public key of a pending instance

**Question.** The pending potential uses a public key and a retained secret key.
Where does it find the public key after the requester has removed its own copy?
Why does the term become zero after encapsulation?

**Answer.** `pendingTerm` first checks whether the peer's key table has an
entry for the retained secret key's epoch. If not, it prefers the peer's decoded
public key and falls back to the requester's retained public key. Under the
invariant, `pendingKey_available` proves that an appropriate public key is
available and belongs to the same transcript pair as the secret key. When the
own public key is gone, `ek_acked` and the acknowledgement invariants provide
the peer's decoded copy.

A peer key-table entry means encapsulation has already occurred. Its risk is now
realized: the bad-instance flag records an inconsistent result, while a consistent
result needs no remaining encapsulation budget. The term is therefore zero even
if the requester still retains the secret key awaiting ciphertext delivery.

Sources: [pendingTerm](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L98)
and [pendingKey_available](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L239).

### 32 The potential and the tracked score

**Question.** How do `dk_shape`, the failure potential `V`, and the score
`S` fit together? Is `V` itself a probability that must be at most one?

**Answer.** `dk_shape` says a party retains either no secret key or a singleton
at its current own key epoch. Thus each party has at most one pending term, and
that term is a conditional error at most one. `V` adds the two parties'
pending potentials. It is a sum of risks, not a probability measure; the
per-party bounds give `V ≤ 2`, rather than a general normalization to one.

The tracked score is `S(s,b) = 1` if the flag is set and `V(s)` otherwise.
Therefore it is at least the flag's indicator, allowing expected score to bound
flag probability. Initially both secret-key lists are empty and the flag is
false, so the score is zero.

Sources: [dk_shape](../../SecureMessaging/SCKA/OppBiKEM/Correctness/MainInvariant.lean#L184),
[potential and score](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Core.lean#L109),
and [trackedScore_init](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L166).

### 33 A returned none and computation failure

**Question.** The quantitative proof uses `expectedPayoff`, which includes a
computation-failure term. Is a rejected send returning `pure none` that kind of
failure?

**Answer.** No. `none` is an ordinary value of the algorithm's result type.
`pure none` successfully returns that value. A receive whose local
`Option` result is `none` similarly causes the game oracle to return a
value and update its flag; it is not an intrinsic failure of the probabilistic
computation.

The generic expected payoff charges intrinsic computation failure with score one
and otherwise averages the scores of returned outcomes:

```text
E_X[f] = Pr[X fails intrinsically] + Σ_x Pr[X returns x] · f(x)
```

Here the proofs use `probFailure_eq_zero` for the `ProbComp` computations.
The important correctness failures are expressed by returned game states and their
`correct` or tracked flag fields.

Sources: [expected payoff notation](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L21),
[oracleSendA](../../SecureMessaging/SCKA/Defs.lean#L279),
and [oracleRecvA](../../SecureMessaging/SCKA/Defs.lean#L502).

### 34 Charging key generation and paying for encapsulation

**Question.** Why can key generation increase expected score by `ε`, while
encapsulation adds no further error budget? Show the accounting for one pending
instance.

**Answer.** A fresh generated pair adds `φ(pk, sk)` to the pending potential.
Averaging that addition over key generation gives `ε`, by the fixed-key
decomposition of KEM correctness error.

Before encapsulation, write the potential as `r + φ`, where `r` is the
other pending risk. The encapsulation is inconsistent with probability `φ`;
then the tracked flag is set and the score becomes one. Otherwise the completed
instance's term vanishes and the score is `r`. In ordinary probability
notation:

```text
E[score after encapsulation] = φ + (1 - φ) · r ≤ φ + r
```

Thus the risk was already paid for when the key pair was created. The formal
lemmas work in `ℝ≥0∞` and bound the corresponding sums directly. Plain sends
preserve this accounting.

Sources: [expectedPayoff_keygen_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean#L72),
[expectedPayoff_encaps_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean#L94),
and [send score cases](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean#L524).

### 35 Why receives cost no additional error

**Question.** Why don't many receives, including replays and chunk deliveries,
increase expected score? Could a receive reveal a fresh KEM failure while the
tracked flag is clear?

**Answer.** A receive introduces no fresh key-generation or encapsulation sample.
For invariant states that are not bad, `DecapsReady` supplies correct pending
decapsulation. The receive proofs establish that the resulting state is still
not bad and that its failure potential is unchanged. If decapsulation consumes a
secret key, its pending term was already zero because the peer had encapsulated
and recorded a key. Installing a public key changes where the matching public key
is available, not the fixed pair's conditional error.

Deterministic decapsulation makes repeated processing of the same pair a fixed
outcome rather than a new independent correctness trial. `Unif` may provide
randomness to the adversary but leaves the protocol game state unchanged.
`tracked_nonSend_score_le` packages these facts as a non-increase in expected
score.

Source: [receive score results and tracked_nonSend_score_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/RecvStep.lean#L430).

### 36 Counting sends under adaptive scheduling

**Question.** Why is the bound `q · ε` stated in terms of send queries rather
than all queries? What makes it valid for adaptive schedules without assuming
independence of the queries?

**Answer.** Only sends can generate fresh key pairs and add new conditional
risk. The one-step theorem bounds expected score by the previous score plus
`ε` for either send oracle and by the previous score for other queries.
Counting all sends is a convenient upper bound: even plain and encapsulating sends
are counted, though they need not add risk. A send cannot generate two fresh
instances in the classified invariant cases, so no factor of two is needed.

The per-query inequality holds at every tracked state satisfying `J`.
Consequently it still holds after conditioning on any possible response history.
The generic simulation theorem composes these conditional inequalities over the
adversary's oracle-computation tree, allowing later queries to depend on earlier
responses. With at most `q` sends and initial score zero, the final expected
score is at most `q · ε`. No separate receive-query budget is required.

Sources: [SendQueryBound](../../SecureMessaging/SCKA/Defs.lean#L714),
[tracked_step_score_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/SendStep.lean#L664),
and [tracked_bad_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L197).

### 37 Combining the tracked bound with game correctness

**Question.** How does a score bound become a bound on the ordinary game's
failure probability? Is a set tracked flag equivalent to `correct = false`?

**Answer.** Preservation of `J` implies that a clear flag gives
`GameInv`, hence `correct = true`. Therefore, on supported tracked outcomes,
`correct = false` implies a set flag. The reverse implication need not hold:
a bad instance may be flagged before the requester receives it, and the adversary
may stop before any game assertion fails.

Since `S ≥ 1` on flagged outcomes and is nonnegative elsewhere, flag
probability is at most expected score. Forgetting the bookkeeping flag recovers
the ordinary run, and `correctnessExp_eq_map` identifies the game's output
with its final `correct` bit. The inequalities are:

```text
Pr[G(Adv) = false] ≤ Pr[final flag = true] ≤ E[final score] ≤ q · ε
```

Sources: [trackedBiKem_preservesInv and tracked_bad_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness/Quantitative/Main.lean#L175),
[generic SCKA reduction](../../SecureMessaging/SCKA/Correctness/Tracked.lean#L83),
and [correctness_failure_le](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L84).

### 38 Reading the success bound

**Question.** Why does the failure bound imply
`Pr[G(Adv) = true] ≥ 1 - q · ε`? What happens when `q · ε > 1`?

**Answer.** The Boolean correctness experiment has no intrinsic computation
failure, so the probabilities of its two outcomes sum to one. Bounding the false
probability therefore gives the lower bound on the true probability.
The Lean statements use `ℝ≥0∞`, whose subtraction is truncated at zero.
If `q · ε > 1`, the success lower bound is zero and provides no positive
guarantee. The failure upper bound remains valid but is weaker than the universal
bound of one. Substituting `ε = 0` gives probability-one success for adversaries
satisfying the stated send-query bound.

Sources: [correctness_true_ge](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L107)
and [correctness_of_perfectKEM'](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L131).

### 39 Perfect correctness on support without a query bound

**Question.** How does probability-one KEM correctness become a pointwise
decapsulation equation on supported samples? Why does the unbounded-query theorem
need a separate argument from substituting `ε = 0`?

**Answer.** The support lemma for this probabilistic model gives
`support kem.CorrectExp = {true}` from probability-one success. If a supported
key pair and supported encapsulation violated the decapsulation equation, the
support-of-bind rules would put `false` in the correctness experiment's
support, a contradiction. This proves `DecapsCorrectOnSupport`; it is a
claim about honest supported samples, not arbitrary inputs.

The transcript's support fields then supply `DecapsReady` for both parties.
Every oracle preserves `GameInv`, and generic simulation preservation proves
it at every supported final state for every adversary represented by the model.
Mapping the final state to its `correct` bit proves probability-one success.
No flag, potential, or send-query-bound hypothesis is needed.

The primed theorem `correctness_of_perfectKEM'` substitutes zero into a theorem
that still requires `SendQueryBound adv q`. That substitution does not remove
the hypothesis. The unprimed theorem uses the direct invariant argument instead.

Sources: [DecapsCorrectOnSupport and its proof](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L37),
[gameInv_preserved and simulateQ_gameInv](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L79),
and [correctness_of_perfectKEM](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L151).

### 40 The scope of the correctness results

**Question.** What do the probability and send-totality theorems guarantee?
Do they establish confidentiality, successful handling of modified messages, or
eventual key advancement under every schedule?

**Answer.** The probability theorems bound violations of the correctness game's
assertions under its allowed oracle executions. Receive queries deliver recorded
honest messages; scheduling can delay, reorder, duplicate, or replay them but does
not replace them with arbitrary modified messages. Cryptographic security against
the security game's additional capabilities is a separate property.

Send totality establishes that sends are accepted on reachable perfect-KEM game
states, or on reachable tracked states with a clear failure flag. It does not
claim success from every arbitrarily constructed malformed state.
Accepted sends need not emit new keys. An adversary can withhold required distinct
chunks indefinitely, so these theorems do not force eventual key advancement
without delivery assumptions.

Sources: [correctness and security game definitions](../../SecureMessaging/SCKA/Defs.lean#L111),
[correctness results](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L84),
and [sends_never_rejected_of_perfectKEM](../../SecureMessaging/SCKA/OppBiKEM/Correctness/PerfectKEM.lean#L125).

### 41 Reading the Lean proof details

**Question.** Why do these proofs repeatedly split on the role, require positive
integer epochs before indexing natural-number tables, and split decidable
conditions explicitly?

**Answer.** Splitting on the role exposes concrete offsets and parity constants,
after which `omega` can discharge arithmetic and parity goals.
Local epochs are integers to support bootstrap values -1 and 0, while game-table
indices are natural numbers. `Int.toNat` maps negative values to zero, so
positivity or nonnegativity is needed when recovering the original integer and
preventing bootstrap values from being confused with positive key epochs.

An `if` with a propositional condition carries a `Decidable` instance that
depends on that condition. Explicit `by_cases` with `if_pos` or `if_neg`,
and `show` or `change` to align the goal, avoids problematic dependent
rewrites. Also check section variables: some receive lemmas get party and message
hypotheses through `include`, while `omit` marks hypotheses they do not use.

Source: [Lean idioms in the tutorial](oppbikem-correctness-tutorial.md#14-idioms-you-will-meet).

### 42 Auditing the theorem rather than only its explanation

**Question.** How would you check that the compiled Lean result has the intended
statement and no hidden unfinished proof dependencies?

**Answer.** Inspect the actual theorem declaration and its assumptions, including
deterministic decapsulation, code correctness, the perfect-KEM or query-bound
hypothesis, and the scope of reachable states. Build the relevant modules, and
use Lean's axiom inspection on the public theorems, for example:

```lean
import SecureMessaging.SCKA.OppBiKEM.Correctness

#print axioms oppBiKemCKA.correctness_failure_le
#print axioms oppBiKemCKA.correctness_of_perfectKEM
#print axioms oppBiKemCKA.sends_never_rejected_of_perfectKEM
```

An unexpected assumption or `sorryAx` dependency would need investigation.
`propext`, `Classical.choice`, and `Quot.sound` are standard logical
dependencies and do not by themselves indicate an unfinished proof. Reading the
implementation equivalence, invariant step statements, and reduction into the
game definition checks that the formally proved statement corresponds to the
protocol behavior under discussion.

Sources: [public theorem statements](../../SecureMessaging/SCKA/OppBiKEM/Correctness.lean#L84),
[receive implementation equivalence](../../SecureMessaging/SCKA/OppBiKEM/Correctness/RecvSpec.lean#L87),
and [results and recorded axiom dependencies](oppbikem-correctness-tutorial.md#12-the-results).
