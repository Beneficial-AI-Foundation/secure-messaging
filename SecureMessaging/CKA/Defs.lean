/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# Continuous Key Agreement (CKA)

A CKA is a two-party stateful protocol where two parties A and B take turns exchanging
protocol messages. Every send/receive pair yields a fresh shared epoch key.
Formally, a `CKAScheme` is a set of algorithms over

[SPACES]
- `IK`: initial shared key material,
- `St`: per-party local state.
- `I`: epoch-key space.
- `Rho`: protocol-message space.
- `Rand`: randomness space used by sending algorithms.

[ALGORITHMS]
- `initKeyGen : m IK`.
  Samples the initial key material `ik : IK` shared by A and B before the first protocol message.
- `initA : IK → m St`.
  Initializes A's local state `stA₀ : St` from the initial key `ik : IK`.
- `initB : IK → m St`.
  Initializes B's local state `stB₀ : St` from the initial key `ik : IK`.
- `sendA : St → m (Option (I × Rho × St))`.
  Generates new epoch key `kA : I`, message `ρA : Rho` from A to B, and new state `stA' : St`.
- `sendB : St → m (Option (I × Rho × St))`.
  Generates new epoch key `kB : I`, message `ρB : Rho` from B to A, and new state `stB' : St`.
- `sendA_rleak : St → m (Option (I × Rho × St × Rand))`.
  As `sendA`, but also returns the randomness used by A for that send.
- `sendB_rleak : St → m (Option (I × Rho × St × Rand))`.
  As `sendB`, but also returns the randomness used by B for that send.
- `recvA : St → Rho → Option (I × St)`.
  Processes incoming message `ρB`, derives matching epoch key `kB : I`, and new state `stB' : St`.
- `recvB : St → Rho → Option (I × St)`.
  Processes incoming message `ρA`, derives matching epoch key `kA : I`, and new state `stA' : St`.

[DIAGRAMS]
```text
Setup:

  initKeyGen() ──▶ ik
                   │
          ┌────────┴────────┐
          ▼                 ▼
      initA(ik)          initB(ik)
          │                 │
          ▼                 ▼
        stA₀              stB₀

Alternating protocol flow:

A                                          B
─────                                      ─────
stA                                        stB
Round 1 (A → B):

(kA, ρA, stA') ← sendA(stA)

         ─────────── ρA ───────────▶

                                           (kB, stB') ← recvB(stB, ρA)
[CORRECTNESS: kA =?= kB]

Round 2 (B → A):
                                           (kB', ρB, stB'') ← sendB(stB')
         ◀─────────── ρB ───────────

(kA', stA'') ← recvA(stA', ρB)

[CORRECTNESS: kA' =?= kB']
```

## Security model
The CKA security game is parameterized by:

- `challengeEpoch : ℕ`, where the adversary will attempt a challenge;
- `challengedParty ∈ {A, B}`, the party challenged by the adversary;
- `ΔFS : ℕ`, the forward-secrecy delay after which post-challenge state corruption
  is allowed;
- `ΔPCS : ℕ`, the post-compromise-security delay before the challenge during which
  state corruption is disallowed.

The adversary has access to send / receive oracles for each party, incrementing
per-party epoch counters `tA` and `tB`, respectively. In addition, there are
oracles for:

- **State corruption** (`O-Corrupt-A`, `O-Corrupt-B`): reveals a party's
  current local state. Permitted only outside the *challenge window* — either
  when both party counters are at least `ΔPCS` epochs before the challenge, or
  after the corrupted party's counter has advanced `ΔFS` epochs past
  `challengeEpoch`.

- **Send randomness leakage** (`O-Send-A-rleak`, `O-Send-B-rleak`): runs the
  regular send algorithm, updates the sender state, and returns the protocol
  message, epoch key, and randomness used for the send. Permitted only at least
  `ΔPCS` epochs before the challenge.

- **Challenge** (`O-Chall-A`, `O-Chall-B`): at epoch `challengeEpoch` on party
  `challengedParty`, runs the regular `sendP` algorithm but returns either
  the real epoch key `k` (if `b = 0`) or a freshly sampled uniform key
  (if `b = 1`).

These oracles define a game (security experiment) between a challenger and an
adversary. The adversary wins if it returns the bit `b` sampled by the
challenger. The adversary's *advantage* is `|Pr[Win] - 1/2|`.

## References

The CKA syntax, correctness and security definitions follow:

- [TripleRatchet]  Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf

For the security definition, we adopt Definition 2.12 and Figure 4 of [TripleRatchet],
with the following modelling differences:

1. **Two send oracles vs. one single oracle with a Boolean flag.**

  - The paper has a single `Send-P(rleak)` oracle parameterized by a flag `rleak ∈ {0,1}`.

  - We have separate oracles `O-Send-P` (no leakage) and `O-Send-P-rleak` (leakage).

2. **`Our CKA scheme has separate sendP and sendP_rleak algorithms.**

  - The paper has a single algorithm `CKA-Send-P` invoked in two modes by
  the game: with fresh internal randomness (`rleak = 0`), or with randomness
  sampled externally by the oracle and passed in as `CKA-Send-P(stP; rand)`
  (`rleak = 1`).

  - We have two separate algorithms, `sendP` and `sendP_rleak`,
  where `sendP_rleak` returns the used randomness alongside the normal output.

3. **The `challengedParty` field is explicit in `GameParams`.**

  - [TripleRatchet] and [ACD19] use per-party counters `tA, tB`, with `Chall-P` gated by
  `tP = t*`, where `t*` is the challenge epoch used as a game parameter.
  Under alternating communication (A first), both counters advance in lockstep,
  so for any single `t*` only one of `Chall-A` / `Chall-B` can fire:
  parity of `t*` determines the challenged party (odd ⇒ A sends, even ⇒ B sends).

  - We make this explicit by adding `challengedParty ∈ {A, B}` field to `GameParams`.

4. **Per-`GameParams` advantage with absolute value, instead of max over challenge epochs.**

  Let `t*` denote the `challengeEpoch`.

  - Definition 2.12 of [TripleRatchet] defines:
    `Adv^CKA_{𝒜, ΔFS, ΔPCS} := max_{t*} ( Pr[Game^CKA_{𝒜, ΔFS, ΔPCS, t*} = 1] − 1/2 )`,
  taking `Pr − 1/2` without an absolute value and folding the max over `t*` into the advantage.

  - Our `ckaGuessAdvantage` is instead defined as:
    `ckaGuessAdvantage(cka, 𝒜, gp) := | Pr[ securityExp(cka, 𝒜, gp) = 1 ] − 1/2 |`,
  where `gp = (t*, ΔFS, ΔPCS, challengedParty)`.

  *Note:*
  - **Absolute value is for free.** If an adversary `𝒜` wins with
    probability `1/2 − ε`, then `𝒜'` that runs `𝒜` and flips its output
    bit wins with probability `1/2 + ε`. So bounding `|Pr − 1/2| ≤ ε`
    is equivalent to bounding the signed `Pr − 1/2 ≤ ε` for every
    adversary in the same complexity class.
  - **Max becomes ∀-quantification in the theorem statement.** The
    paper includes `max_{t*}` into the advantage; we include `t*` (and the
    other parameters of `gp`) as inputs to `ckaGuessAdvantage` and move
    the quantification over `gp` into the security statement. The paper's
    `∀ ΔFS, ΔPCS, Adv^CKA_{𝒜, ΔFS, ΔPCS} ≤ ε` is equivalent to our
    `∀ gp, ckaGuessAdvantage(cka, 𝒜, gp) ≤ ε`.

5. **`req` failure encoded as oracle returning `none`, not as game abort.**
  The paper's `req ⟦…⟧` aborts the entire game on failure. In Lean, when an
  oracle's gate (PCS, FS, alternation, challenge-epoch) fails, it returns
  `none` and the game state is not updated.

Other references:

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf

- [SPQR] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols:
  A Quest for A More Efficient and Secure Post-Quantum Protocol.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf


-/

open OracleSpec OracleComp ENNReal

universe u v

/-- A continuous key agreement (CKA) protocol with initial-key space `IK`,
per-party state space `St`, epoch-key space `I`, protocol-message space `Rho`,
and send-randomness space `Rand`. -/
-- ANCHOR: CKAScheme
structure CKAScheme (m : Type → Type u) [Monad m] (IK St I Rho Rand : Type) where
  /-- samples initial shared key -/
  initKeyGen : m IK
  /-- initializes A's local state from the initial key -/
  initA : IK → m St
  /-- initializes B's local state from the initial key -/
  initB : IK → m St
  /-- Party A's send: returns the fresh epoch key, message sent to B, and A's next state. -/
  sendA : St → m (Option (I × Rho × St))
  /-- Party A's randomness-leaking send: also returns the randomness used for the send. -/
  sendA_rleak : St → m (Option (I × Rho × St × Rand))
  /-- Party A's receive: returns the derived epoch key and A's next state. -/
  recvA : St → Rho → Option (I × St)
  /-- Party B's send: returns the fresh epoch key, message sent to A, and B's next state. -/
  sendB : St → m (Option (I × Rho × St))
  /-- Party B's randomness-leaking send: also returns the randomness used for the send. -/
  sendB_rleak : St → m (Option (I × Rho × St × Rand))
  /-- Party B's receive: returns the derived epoch key and B's next state. -/
  recvB : St → Rho → Option (I × St)
-- ANCHOR_END: CKAScheme

namespace CKAScheme

/-! ## More Details on Security Model

As in [ACD19, TripleRatchet], we assume the following:

- **Alternating Communication**: parties A and B execute the sending and
receiving algorithms in an alternating order.

- **Fully Passive Adversary**: the adversary can neither modify nor reorder sent messages.

- **Static Challenge Epoch**: the security adversary can only challenge the key for one epoch,
which is fixed at the beginning of the security experiment.

Contrary to [ACD19], we don't consider oracles that allow to corrupt the randomness of a
sending party.
Instead, following the [TripleRatchet] paper, we include oracles that allow to leak it.

These assumptions are enforced by checks in the oracles defining the CKA security game.
The oracles are:
- **O-Send-A / O-Send-B**
  Trigger one party to send, return `(ρ, key)`, and update the sender state.
- **O-Recv-A / O-Recv-B**
  Deliver the latest message in that direction and update the receiver state.
  *Correctness assert*: the received key must match the sender's corresponding key.
- **O-Chall-A / O-Chall-B**
  Like send, but return real key (`b = 0`) or random key (`b = 1`).
- **O-Corrupt-A / O-Corrupt-B**
  Return the current state of party A (resp. B) and record the corruption epoch.
- **O-Send-A-rleak / O-Send-B-rleak**
  Like send, but also return the send randomness when the pre-challenge `ΔPCS`
  gate permits it.

We define two games:
- **Correctness game**: adversary wins if there is an epoch where the receiver
  and sender keys don't match.
- **Security game**: adversary wins if it can distinguish a real from a random
  key at the challenge epoch.

-/

section Games

variable {IK St I Rho Rand : Type}

/-- Trace of protocol actions observed in the CKA game. -/
inductive CKAAction where
  | sendA | recvA | sendB | recvB | challA | challB
  deriving DecidableEq, Repr

/-- The two parties in a CKA protocol. -/
inductive CKAParty where
  | A | B
  deriving DecidableEq, Repr

/-- The opposite party: `A.other = B` and `B.other = A`. -/
def CKAParty.other : CKAParty → CKAParty
  | .A => .B
  | .B => .A

/-- Predicate enforcing *Alternating Communication*.

The game is A-first and follows the cycle
`A-send/chall → B-recv → B-send/chall → A-recv → A-send/chall → ...`.
Challenge steps run the sending algorithm but return a real-or-random key to
the adversary. -/
def validStep (last : Option CKAAction) (next : CKAAction) : Bool :=
  match last, next with
  -- The first action must be an A-side send or challenge.
  | none, .sendA | none, .challA => true
  -- After A sends, B must receive A's message.
  | some .sendA, .recvB | some .challA, .recvB => true
  -- After B receives, B may send or challenge.
  | some .recvB, .sendB | some .recvB, .challB => true
  -- After B sends, A must receive B's message.
  | some .sendB, .recvA | some .challB, .recvA => true
  -- After A receives, the next round starts with an A-side send or challenge.
  | some .recvA, .sendA | some .recvA, .challA => true
  | _, _ => false

/-- Game parameters fixed at the start of the security experiment. -/
-- ANCHOR: GameParams
structure GameParams where
  /-- Epoch challenged by the adversary. -/
  challengeEpoch : ℕ
  /-- Forward-secrecy delay after which state corruption is allowed. -/
  ΔFS : ℕ
  /-- Post-compromise-security delay before the challenge during which corruption is disallowed. -/
  ΔPCS : ℕ
  /-- Party selected for the challenge oracle. -/
  challengedParty : CKAParty
-- ANCHOR_END: GameParams

/-- Internal state of the CKA game.
- `stA`, `stB`: per-party protocol state.
- `rhoA, rhoB`: undelivered messages sent by A or B.
- `keyA, keyB`: keys derived by A or B upon executing the send algorithm.
- `correct`: tracks whether A and B agree on derived keys at all epochs.
- `lastAction`: enforces alternating communication.
- `tA`, `tB`: per-party epoch counters. -/
-- ANCHOR: GameState
structure GameState (St I Rho : Type) where
  /-- Local protocol state for party A. -/
  stA : St
  /-- Local protocol state for party B. -/
  stB : St
  /-- Latest undelivered message sent from A to B. -/
  rhoA : Option Rho
  /-- Latest undelivered message sent from B to A. -/
  rhoB : Option Rho
  /-- Sender key corresponding to `rhoA`. -/
  keyA : Option I
  /-- Sender key corresponding to `rhoB`. -/
  keyB : Option I
  /-- Whether delivered epoch keys have agreed so far. -/
  correct : Bool
  /-- Last oracle action, used to enforce alternating communication. -/
  lastAction : Option CKAAction
  /-- Epoch counter for A, incremented on A-side send, challenge, or receive. -/
  tA : ℕ
  /-- Epoch counter for B, incremented on B-side send, challenge, or receive. -/
  tB : ℕ
-- ANCHOR_END: GameState

/-- Epoch counter for party `p`. -/
def GameState.tP (s : GameState St I Rho) : CKAParty → ℕ
  | .A => s.tA
  | .B => s.tB

/-- State of party `p`. -/
def GameState.stP (s : GameState St I Rho) : CKAParty → St
  | .A => s.stA
  | .B => s.stB

/-- Oracle spec for the CKA correctness game (send + recv only).
Defines the expected oracles types. -/
-- ANCHOR: ckaCorrectnessSpec
def ckaCorrectnessSpec (Rho I : Type) :=
  unifSpec                        -- Uniform randomness
  + (Unit →ₒ Option (Rho × I))   -- O-Send-A (outputs message and key)
  + (Unit →ₒ Unit)               -- O-Recv-A (no adversary I/O; delivers the pending sent message)
  + (Unit →ₒ Option (Rho × I))   -- O-Send-B (outputs message and key)
  + (Unit →ₒ Unit)               -- O-Recv-B (no adversary I/O; delivers the pending sent message)
-- ANCHOR_END: ckaCorrectnessSpec

namespace ckaCorrectnessSpec

variable {Rho I : Type}

/-! ### Named oracle indices

Aliases for the nested `.inl/.inr` paths into `(ckaCorrectnessSpec Rho I).Domain`.
Marked `@[match_pattern]` so they unfold transparently in `match` patterns. -/
@[match_pattern] abbrev OUnif (n : ℕ) : (ckaCorrectnessSpec Rho I).Domain :=
  .inl (.inl (.inl (.inl n)))
@[match_pattern] abbrev OSendA : (ckaCorrectnessSpec Rho I).Domain :=
  .inl (.inl (.inl (.inr ())))
@[match_pattern] abbrev ORecvA : (ckaCorrectnessSpec Rho I).Domain :=
  .inl (.inl (.inr ()))
@[match_pattern] abbrev OSendB : (ckaCorrectnessSpec Rho I).Domain :=
  .inl (.inr ())
@[match_pattern] abbrev ORecvB : (ckaCorrectnessSpec Rho I).Domain :=
  .inr ()

end ckaCorrectnessSpec

/-- Oracle spec for the CKA security game (send + recv + challenge + corrupt + rleak).
Defines the expected oracles types. -/
-- ANCHOR: ckaSecuritySpec
def ckaSecuritySpec (St Rho I Rand : Type) :=
  ckaCorrectnessSpec Rho I
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-A (outputs message and key)
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-B (outputs message and key)
  + (Unit →ₒ Option St)           -- O-Corrupt-A (outputs party state)
  + (Unit →ₒ Option St)           -- O-Corrupt-B (outputs party state)
  + (Unit →ₒ Option (Rho × I × Rand)) -- O-Send-A-rleak
  + (Unit →ₒ Option (Rho × I × Rand)) -- O-Send-B-rleak
-- ANCHOR_END: ckaSecuritySpec

namespace ckaSecuritySpec

variable {St Rho I Rand : Type}

/-! ### Named oracle indices

Aliases for the nested `.inl/.inr` paths into `(ckaSecuritySpec St Rho I Rand).Domain`.
Marked `@[match_pattern]` so they unfold transparently in `match` patterns. -/
@[match_pattern] abbrev OUnif (n : ℕ) : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl n)))))))))
@[match_pattern] abbrev OSendA : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ())))))))))
@[match_pattern] abbrev ORecvA : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ()))))))))
@[match_pattern] abbrev OSendB : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ())))))))
@[match_pattern] abbrev ORecvB : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inr ()))))))
@[match_pattern] abbrev OChallA : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inr ())))))
@[match_pattern] abbrev OChallB : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inl (.inr ()))))
@[match_pattern] abbrev OCorruptA : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inl (.inr ())))
@[match_pattern] abbrev OCorruptB : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inl (.inr ()))
@[match_pattern] abbrev OSendA_rleak : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inl (.inr ())
@[match_pattern] abbrev OSendB_rleak : (ckaSecuritySpec St Rho I Rand).Domain :=
  .inr ()

end ckaSecuritySpec

/-! ### Epoch predicates (used for restricting oracle calls, defining reductions, etc) -/

/-- Challenge allowed only when the challenged party's counter is at `challengeEpoch`. -/
-- ANCHOR: isChallengeEpoch
def isChallengeEpoch (gp : GameParams) (state : GameState St I Rho) : Bool :=
  state.tP gp.challengedParty == gp.challengeEpoch
-- ANCHOR_END: isChallengeEpoch

/-- The opposite party is sending in the epoch immediately before the challenge.

If `gp.challengedParty` is challenged at epoch `challengeEpoch`, this
predicate recognizes the send by the opposite party at preceding epoch. -/
def isOtherSendBeforeChall (gp : GameParams) (state : GameState St I Rho) : Bool :=
  state.tP gp.challengedParty.other == gp.challengeEpoch - 1

/-- Post-challenge FS gate for party `p`:
party `p` has advanced `ΔFS` epochs past the challenge. -/
-- ANCHOR: allowCorrFS
abbrev allowCorrFS (gp : GameParams) (state : GameState St I Rho) : CKAParty → Bool
  | .A => gp.challengeEpoch + gp.ΔFS ≤ state.tA
  | .B => gp.challengeEpoch + gp.ΔFS ≤ state.tB
-- ANCHOR_END: allowCorrFS

/-- Pre-challenge PCS gate:
`max(tA, tB) ≤ challengeEpoch - ΔPCS`, equivalently
`max(tA, tB) + ΔPCS ≤ challengeEpoch`. -/
-- ANCHOR: allowCorrPCS
def allowCorrPCS (gp : GameParams) (state : GameState St I Rho) : Bool :=
  (max state.tA state.tB) + gp.ΔPCS ≤ gp.challengeEpoch
-- ANCHOR_END: allowCorrPCS

/-- Corruption gate for party `p`. This is the disjunction of the two allowed
corruption windows: both party counters are `ΔPCS` epochs before the challenge,
or party `p` has advanced `ΔFS` epochs past the challenge. -/
-- ANCHOR: allowCorr
def allowCorr (gp : GameParams) (state : GameState St I Rho) : CKAParty → Bool
  | p => allowCorrPCS gp state || allowCorrFS gp state p
-- ANCHOR_END: allowCorr

/-! ### Send oracles -/

/-- **O-Send-A.**
Increment epoch counter, trigger send by A, return message and key.
`tA++; (key, ρ, stA') ← sendA(stA)`; return `(ρ, key)`. -/
-- ANCHOR: oracleSendA
def oracleSendA (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow A to send if it is A's turn in alternating communication.
    if validStep state.lastAction .sendA then
      -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
      -- Run A's send algorithm on the current A-state.
      match ← liftM (cka.sendA state.stA) with
      | none => pure none
      | some (key, ρ, stA') =>
        -- Update game state.
        set { state with
          stA := stA', rhoA := some ρ, keyA := some key,
          lastAction := some .sendA }
        -- Return the message and key to the adversary.
        return some (ρ, key)
    else pure none
-- ANCHOR_END: oracleSendA

/-- **O-Send-B.**
Increment epoch counter, trigger send by B, return message and key.
`tB++; (key, ρ, stB') ← sendB(stB)`; return `(ρ, key)`. -/
-- ANCHOR: oracleSendB
def oracleSendB (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow B to send if it is B's turn in alternating communication.
    if validStep state.lastAction .sendB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      -- Run B's send algorithm on the current B-state.
      match ← liftM (cka.sendB state.stB) with
      | none => pure none
      | some (key, ρ, stB') =>
        -- Update game state.
        set { state with
          stB := stB', rhoB := some ρ, keyB := some key,
          lastAction := some .sendB }
        -- Return the message and key to the adversary.
        return some (ρ, key)
    else pure none
-- ANCHOR_END: oracleSendB

/-! ### Randomness-leaking send oracles -/

/-- **O-Send-A-rleak.** Like `O-Send-A`, but returns the randomness used by
A's send when the post-increment epoch is before the `ΔPCS` challenge window. -/
-- ANCHOR: oracleSendA_rleak
def oracleSendA_rleak (gp : GameParams) (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I × Rand)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      let state := { state with tA := state.tA + 1 }
      if allowCorrPCS gp state then
        match ← liftM (cka.sendA_rleak state.stA) with
        | none => pure none
        | some (key, ρ, stA', rand) =>
          set { state with
            stA := stA', rhoA := some ρ, keyA := some key,
            lastAction := some .sendA }
          return some (ρ, key, rand)
      else pure none
    else pure none
-- ANCHOR_END: oracleSendA_rleak

/-- **O-Send-B-rleak.** Like `O-Send-B`, but returns the randomness used by
B's send when the post-increment epoch is before the `ΔPCS` challenge window. -/
-- ANCHOR: oracleSendB_rleak
def oracleSendB_rleak (gp : GameParams) (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I × Rand)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      let state := { state with tB := state.tB + 1 }
      if allowCorrPCS gp state then
        match ← liftM (cka.sendB_rleak state.stB) with
        | none => pure none
        | some (key, ρ, stB', rand) =>
          set { state with
            stB := stB', rhoB := some ρ, keyB := some key,
            lastAction := some .sendB }
          return some (ρ, key, rand)
      else pure none
    else pure none
-- ANCHOR_END: oracleSendB_rleak

/-! ### Receive oracles -/

/-- **O-Recv-A.**
Increment epoch counter, run A's receive on B's pending message, and update
the internal `correct` flag.
`tA++; (keyA, stA') ← recvA(stA, ρB); correct := correct ∧ (keyA == keyB)`. -/
-- ANCHOR: oracleRecvA
def oracleRecvA [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow A to receive if it is A's turn in alternating communication.
    if validStep state.lastAction .recvA then
      -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
      match state.rhoB with
      | none => pure () -- No pending message.
      | some ρ =>
        -- Run A's receive algorithm on the current A-state and B's message.
        match cka.recvA state.stA ρ with
        | none =>
          set { state with
            rhoB := none, keyB := none,
            correct := false, lastAction := some .recvA }
        | some (keyA, stA') =>
          let ok := state.keyB == some keyA
          set { state with
            -- Update game state.
            stA := stA', rhoB := none, keyB := none,
            -- Update correctness flag.
            correct := state.correct && ok, lastAction := some .recvA }
    else pure ()
-- ANCHOR_END: oracleRecvA

/-- **O-Recv-B.**
Increment epoch counter, run B's receive on A's pending message, and update
the internal `correct` flag.
`tB++; (keyB, stB') ← recvB(stB, ρA); correct := correct ∧ (keyB == keyA)`. -/
-- ANCHOR: oracleRecvB
def oracleRecvB [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow B to receive if it is B's turn in alternating communication.
    if validStep state.lastAction .recvB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      match state.rhoA with
      | none => pure () -- No pending message.
      | some ρ =>
        -- Run B's receive algorithm on the current B-state and A's message.
        match cka.recvB state.stB ρ with
        | none =>
          set { state with
            rhoA := none, keyA := none,
            correct := false, lastAction := some .recvB }
        | some (keyB, stB') =>
          let ok := state.keyA == some keyB
          set { state with
            -- Update game state.
            stB := stB', rhoA := none, keyA := none,
            -- Update correctness flag.
            correct := state.correct && ok, lastAction := some .recvB }
    else pure ()
-- ANCHOR_END: oracleRecvB

/-! ### Challenge oracles -/

/-- **O-Chall-A.**
Increment epoch counter, trigger send by A, return message and key.
Like `O-Send-A` but returns `b ? $ᵗ I : key` (real or
random key). Only fires when `challengedParty = A` and `tA = challengeEpoch`. -/
-- ANCHOR: oracleChallA
def oracleChallA (gp : GameParams) (isRandom : Bool) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA then
    -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
    -- Enforce correct challenge party and epoch.
      if gp.challengedParty == .A && isChallengeEpoch gp state then
        -- Run A's send algorithm on the current A-state.
        match ← liftM (cka.sendA state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          -- Real or random key for the adversary.
          let outKey ← if isRandom then liftM ($ᵗ I : ProbComp I) else pure key
          -- Update game state.
          set { state with
            stA := stA', rhoA := some ρ, keyA := some key,
            lastAction := some .challA }
          -- Return the message and key to the adversary.
          return some (ρ, outKey)
      else pure none
    else pure none
-- ANCHOR_END: oracleChallA

/-- **O-Chall-B.**
Increment epoch counter, trigger send by B, return message and key.
Like `O-Send-B` but returns `b ? $ᵗ I : key` (real or
random key). Only fires when `challengedParty = B` and `tB = challengeEpoch`. -/
-- ANCHOR: oracleChallB
def oracleChallB (gp : GameParams) (isRandom : Bool) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      -- Enforce correct challenge party and epoch.
      if gp.challengedParty == .B && isChallengeEpoch gp state then
        -- Run B's send algorithm on the current B-state.
        match ← liftM (cka.sendB state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          let outKey ← if isRandom then liftM ($ᵗ I : ProbComp I) else pure key
          -- Update game state.
          set { state with
            stB := stB', rhoB := some ρ, keyB := some key,
            lastAction := some .challB }
          -- Return the message and key to the adversary.
          return some (ρ, outKey)
      else pure none
    else pure none
-- ANCHOR_END: oracleChallB

/-! ### Corruption oracles

Corruption is allowed iff either
- `allowCorrPCS gp state`: both party counters are `ΔPCS` epochs before the challenge,
- or party `P` has advanced `ΔFS` epochs past the challenge.
-/

/-- **O-Corrupt-A.** Return `stA` if either the `ΔPCS` pre-challenge gate holds,
or A has advanced `ΔFS` epochs past the challenge. -/
-- ANCHOR: oracleCorruptA
def oracleCorruptA (gp : GameParams) (St I Rho : Type) :
    QueryImpl (Unit →ₒ Option St) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if allowCorr gp state .A then return some state.stA
    else return none
-- ANCHOR_END: oracleCorruptA

/-- **O-Corrupt-B.** Return `stB` if either the `ΔPCS` pre-challenge gate holds,
or B has advanced `ΔFS` epochs past the challenge. -/
-- ANCHOR: oracleCorruptB
def oracleCorruptB (gp : GameParams) (St I Rho : Type) :
    QueryImpl (Unit →ₒ Option St) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if allowCorr gp state .B then return some state.stB
    else return none
-- ANCHOR_END: oracleCorruptB

/-- Oracle for adversary randomness: forwards to `ProbComp`. -/
def oracleUnif (St I Rho : Type) :
    QueryImpl unifSpec (StateT (GameState St I Rho) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St I Rho) ProbComp)

/-- Oracle set for the correctness game. -/
-- ANCHOR: ckaCorrectnessImpl
def ckaCorrectnessImpl [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (ckaCorrectnessSpec Rho I) (StateT (GameState St I Rho) ProbComp) :=
  oracleUnif St I Rho
    + oracleSendA cka + oracleRecvA cka
    + oracleSendB cka + oracleRecvB cka
-- ANCHOR_END: ckaCorrectnessImpl

/-- Oracle set for the security game. -/
-- ANCHOR: ckaSecurityImpl
def ckaSecurityImpl (gp : GameParams) (isRandom : Bool) [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (ckaSecuritySpec St Rho I Rand) (StateT (GameState St I Rho) ProbComp) :=
  ckaCorrectnessImpl cka
    + oracleChallA gp isRandom cka + oracleChallB gp isRandom cka
    + oracleCorruptA gp St I Rho + oracleCorruptB gp St I Rho
    + oracleSendA_rleak gp cka + oracleSendB_rleak gp cka
-- ANCHOR_END: ckaSecurityImpl

/-- Correctness adversary: send + recv oracles only. -/
-- ANCHOR: CKACorrectnessAdversary
abbrev CKACorrectnessAdversary (Rho I : Type) := OracleComp (ckaCorrectnessSpec Rho I) Bool
-- ANCHOR_END: CKACorrectnessAdversary

/-- Security adversary: send + recv + challenge + corruption + rleak oracles. -/
-- ANCHOR: CKAAdversary
abbrev CKAAdversary (St Rho I Rand : Type) := OracleComp (ckaSecuritySpec St Rho I Rand) Bool
-- ANCHOR_END: CKAAdversary

/-! ### Correctness game -/

/-- Game state with initial `stA`, `stB`, initial epochs, and no pending keys or messages. -/
def initGameState (stA stB : St) : GameState St I Rho :=
  { stA, stB, rhoA := none, rhoB := none,
    keyA := none, keyB := none,
    correct := true, lastAction := none,
    tA := 0, tB := 0 }

/-- **Correctness experiment** `Expᶜᵒʳʳ(cka, 𝒜)`

Initialize both parties from common initial key material, then run the
adversary with access to the honest send/receive oracles. The experiment
returns whether all delivered epoch keys matched.

  `ik   ←$ cka.initKeyGen()`
  `stA  ← cka.initA(ik); stB ← cka.initB(ik)`
  `σ_0  := initGameState(stA, stB)`
  `(_,σ_f)  ← 𝒜^O(σ_0)`,        where `O = (O-Send-A, O-Recv-A, O-Send-B, O-Recv-B)`
  `output σ_f.correct` -/
-- ANCHOR: correctnessExp
def correctnessExp [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand)
    (adversary : CKACorrectnessAdversary Rho I) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let (_, state) ←
    (simulateQ (ckaCorrectnessImpl cka) adversary).run (initGameState stA stB)
  return state.correct
-- ANCHOR_END: correctnessExp

/-! ### Security game -/

/-- **Security experiment** `Expˢᵉᶜ(cka, 𝒜, gp)`.

Initialize both parties, sample a challenge bit, then run the adversary with
access to the send, receive, challenge, and corruption oracles. The experiment
returns whether the adversary guesses the challenge bit.

  `ik   ←$ KeyGen()`
  `stA  ← initA(ik); stB ← initB(ik)`
  `b    ←$ {0,1}`
  `σ_0  := initGameState(stA, stB)`
  `(b', σ_f) ← 𝒜^{O_b}(σ_0)`,
    where `O_b` is `ckaSecurityImpl gp b cka`
  `output (b = b')`

As in [ACD19, Def. 13, Fig. 3]. -/
-- ANCHOR: securityExp
def securityExp [SampleableType I] [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand)
  (adversary : CKAAdversary St Rho I Rand)
    (gp : GameParams) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (ckaSecurityImpl gp b cka) adversary).run (initGameState stA stB)
  return (b == b')
-- ANCHOR_END: securityExp

/-- CKA guess advantage: `|Pr[Win] - 1/2|`. -/
-- ANCHOR: ckaGuessAdvantage
noncomputable def ckaGuessAdvantage [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) (adversary : CKAAdversary St Rho I Rand)
    (gp : GameParams) : ℝ :=
  |(Pr[= true | securityExp cka adversary gp]).toReal - 1 / 2|
-- ANCHOR_END: ckaGuessAdvantage

/-! ### Useful security game decomposition -/

/-- Security experiment with a fixed challenge bit `b` (not sampled uniformly).
The branch `b = false` is `CKA_real`; the branch `b = true` is `CKA_rand`.
Returns the adversary's raw guess `b'` (not `b == b'`). -/
def securityExpFixedBit [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand)
    (adversary : CKAAdversary St Rho I Rand)
    (b : Bool) (gp : GameParams) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let (b', _) ← (simulateQ (ckaSecurityImpl gp b cka) adversary).run
    (initGameState stA stB)
  return b'

/-- CKA distinguishing advantage:
`|Pr[CKA_rand = 1] - Pr[CKA_real = 1]|`.

Here `CKA_real` is `securityExpFixedBit cka adversary false gp` and
`CKA_rand` is `securityExpFixedBit cka adversary true gp`. -/
noncomputable def ckaDistAdvantage [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand)
    (adversary : CKAAdversary St Rho I Rand)
    (gp : GameParams) : ℝ :=
  |(Pr[= true | securityExpFixedBit cka adversary true gp]).toReal -
   (Pr[= true | securityExpFixedBit cka adversary false gp]).toReal|

/-- The single-game CKA experiment can be decomposed as a uniform-bit branch over
the two fixed-bit experiments:

  `Pr[Expˢᵉᶜ(cka, 𝒜, gp) = 1]`
    `= Pr[b ←$ {0,1}; b' ← (if b then CKA_rand else CKA_real); output (b = b')]`.

Here `CKA_real` abbreviates `securityExpFixedBit cka adversary false gp`, and
`CKA_rand` abbreviates `securityExpFixedBit cka adversary true gp`; each branch
returns the adversary's raw guess `b'`. Proved by swapping `b ← $ᵗ Bool` past
the three initialization steps using `probEvent_bind_bind_swap`. -/
private lemma securityExp_probOutput_eq_branch [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand)
    (adversary : CKAAdversary St Rho I Rand) (gp : GameParams) :
    Pr[= true | securityExp cka adversary gp] =
    Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then securityExpFixedBit cka adversary true gp
               else securityExpFixedBit cka adversary false gp
      pure (b == z)] := by
  unfold securityExp
  simp only [← probEvent_eq_eq_probOutput]
  rw [probEvent_bind_congr fun ik _ =>
    probEvent_bind_congr fun stA _ =>
    probEvent_bind_bind_swap _ _ _ _]
  rw [probEvent_bind_congr fun ik _ =>
    probEvent_bind_bind_swap _ _ _ _]
  rw [probEvent_bind_bind_swap]
  simp only [probEvent_eq_eq_probOutput]
  refine probOutput_bind_congr' ($ᵗ Bool) true ?_
  intro b; cases b <;> simp [securityExpFixedBit]

/-- The centered success probability of the single-bit experiment decomposes
as the difference of the random-key and real-key fixed-bit branches:
`Pr[Expˢᵉᶜ = 1] - 1/2 =
  (Pr[CKA_rand = 1] - Pr[CKA_real = 1]) / 2`.
Here `CKA_rand` is `securityExpFixedBit cka adversary true gp`, and `CKA_real`
is `securityExpFixedBit cka adversary false gp`; both return the adversary's
raw guess. -/
lemma securityExp_toReal_sub_half [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand)
    (adversary : CKAAdversary St Rho I Rand) (gp : GameParams) :
    (Pr[= true | securityExp cka adversary gp]).toReal - 1 / 2 =
    ((Pr[= true | securityExpFixedBit cka adversary true gp]).toReal -
     (Pr[= true | securityExpFixedBit cka adversary false gp]).toReal) / 2 := by
  rw [show (Pr[= true | securityExp cka adversary gp]).toReal =
      (Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let z ← if b then securityExpFixedBit cka adversary true gp
                 else securityExpFixedBit cka adversary false gp
        pure (b == z)]).toReal from by
    congr 1; exact securityExp_probOutput_eq_branch cka adversary gp]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (securityExpFixedBit cka adversary true gp)
    (securityExpFixedBit cka adversary false gp)

/-- The CKA guess advantage equals half the distinguishing advantage:
`ckaGuessAdvantage = ckaDistAdvantage / 2`. -/
lemma ckaGuessAdvantage_eq_ckaDistAdvantage_div_two [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand)
    (adversary : CKAAdversary St Rho I Rand) (gp : GameParams) :
    ckaGuessAdvantage cka adversary gp = ckaDistAdvantage cka adversary gp / 2 := by
  simp only [ckaGuessAdvantage, ckaDistAdvantage]
  rw [securityExp_toReal_sub_half, abs_div]
  congr 1
  exact abs_of_pos two_pos

end Games

end CKAScheme
