/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import Mathlib.Data.Finset.Basic

/-!
# Sparse Continuous Key Agreement (SCKA)

Syntax and definitions from Section 3.1 of:

- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols:
  A Quest for A More Efficient and Secure Post-Quantum Protocol.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf


[SPACES]
- `IK`: initial shared key,
- `StA`: local state for party A.
- `StB`: local state for party B.
- `I`: epoch-key space.
- `Rho`: protocol-message space.
- `Rand`: randomness space used by sending algorithms.

[ALGORITHMS]
- `initKeyGen : m IK`.
  Produces the initial key `ik : IK` shared by A and B before the first protocol message.
- `initA : IK → m StA`.
  Initializes A's local state `stA₀ : StA` from the initial key `ik : IK`.
- `initB : IK → m StB`.
  Initializes B's local state `stB₀ : StB` from the initial key `ik : IK`.
- `sendA : StA → m (Option (Option (ℕ × I) × Rho × ℕ × StA))`.
  * May output an (epoch counter, epoch key) pair `(t_{I_A}, I_A) : ℕ × I`.
  * Outputs a message `ρA : Rho` from A to B, a sending epoch `t_A^snd : ℕ`, and a new state `stA'.
- `sendB : StB → m (Option (Option (ℕ × I) × Rho × ℕ × StB))`.
  * May output an (epoch counter, epoch key) pair `(t_{I_B}, I_B) : ℕ × I`.
  * Outputs a message `ρB : Rho` from B to A, a sending epoch `t_B^snd : ℕ`, and a new state `stB'.
- `sendArleak : StA → m (Option (Option (ℕ × I) × Rho × ℕ × StA × Rand))`.
  As `sendA`, but also returns the randomness used by A for that send.
- `sendBrleak : StB → m (Option (Option (ℕ × I) × Rho × ℕ × StB × Rand))`.
  As `sendB`, but also returns the randomness used by B for that send.
- `recvA : StA → Rho → Option (Option (ℕ × I) × ℕ × StA)`.
  * Processes incoming message `ρB`.
  * May output an (epoch counter, epoch key) pair `(t_{I_B}, I_B) : ℕ × I`.
  * Outputs a receiving epoch `t_A^rcv : ℕ`, and a new state `stA' : StA`.
- `recvB : StB → Rho → Option (Option (ℕ × I) × ℕ × StB)`.
  * Processes incoming message `ρA`.
  * May output an (epoch counter, epoch key) pair `(t_{I_A}, I_A) : ℕ × I`.
  * Outputs a receiving epoch `t_B^rcv : ℕ`, and a new state `stB' : StB`.

[EXECUTION MODEL]
Unlike CKA, SCKA does not assume the alternating ("ping-pong") A↔B pattern. Both parties may send
and receive messages at the same time. A send/receive may produce no key.
When a key is produced by a party P in {A, B}, we obtain (t_{I_P}, I_P), where
- t_{I_P} is an epoch counter,
- I_P is the key to be associated with that epoch.
-/

open OracleSpec OracleComp ENNReal

universe u

/-- A sparse continuous key agreement scheme.

- `IK`: initial shared key material,
- `StA`: local state for party A,
- `StB`: local state for party B,
- `I`: epoch-key space,
- `Rho`: protocol-message space,
- `Rand`: randomness space used by sending algorithms.
-/
-- ANCHOR: SCKAScheme
structure SCKAScheme (m : Type → Type u) [Monad m] (IK StA StB I Rho Rand : Type) where
  /-- Samples initial shared key material. -/
  initKeyGen : m IK
  /-- Initializes A's local state from the initial key. -/
  initA : IK → m StA
  /-- Initializes B's local state from the initial key. -/
  initB : IK → m StB
  /-- Party A's send: returns an optional (epoch,key) pair, the message sent to B,
  the sending epoch, and A's next state. -/
  sendA : StA → m (Option (Option (ℕ × I) × Rho × ℕ × StA))
  /-- Party A's randomness-leaking send: also returns the randomness used for the send. -/
  sendArleak : StA → m (Option (Option (ℕ × I) × Rho × ℕ × StA × Rand))
  /-- Party A's receive: returns the optional derived (epoch,key) pair, the receiving
  epoch, and A's next state. -/
  recvA : StA → Rho → Option (Option (ℕ × I) × ℕ × StA)
  /-- Party B's send: returns an optional (epoch,key) pair, the message sent to A,
  the sending epoch, and B's next state. -/
  sendB : StB → m (Option (Option (ℕ × I) × Rho × ℕ × StB))
  /-- Party B's randomness-leaking send: also returns the randomness used for the send. -/
  sendBrleak : StB → m (Option (Option (ℕ × I) × Rho × ℕ × StB × Rand))
  /-- Party B's receive: returns the optional derived (epoch,key) pair, the receiving
  epoch, and B's next state. -/
  recvB : StB → Rho → Option (Option (ℕ × I) × ℕ × StB)
-- ANCHOR_END: SCKAScheme

namespace SCKAScheme

variable {m : Type → Type u} [Monad m] {IK StA StB I Rho Rand : Type}

/-! ## Security and correctness games (Figure 1 and Appendix B.1 of [SCKA])

- the **correctness game** (`correctnessExp`) uses a restricted oracle
  set `sckaCorrectnessSpec` (uniform randomness + plain send + receive),
  and returns whether all correctness invariants hold (`state.correct`);

- the **security game** (`securityExp`) uses the full `sckaSecuritySpec` (the
  correctness oracles plus randomness-leaking send, challenge, and
  corruption oracles), and returns whether the adversary guessed the challenge bit.

**Modeling choices:**

- **Parties.** We write `P` for a party (`A` or `B`) and `P̄` for the *other* party,
  i.e. `P̄ := P.other`.
- **Message and key arrays**
  Each sent message is recorded in a per-party transit array `Msg[P, n]`,
  where `n` represents the index of the message in the sending sequence.
  The oracle `O-Recv-P n` delivers `Msg[P̄, n]` to `P`.
  The adversary may deliver messages for the other party in any order by
  supplying the desired indices to the `O-Recv-P n` oracle.

  Keys are stored in `Key[P, t]`, indexed by party `P` and epoch `t`.

- **Epochs.** A send by `P` outputs a *sending epoch* `t^snd_P` and a receive a
  *receiving epoch* `t^rcv_P`. The game additionally tracks `t^cur_P`, party `P`'s
  *current epoch*: the largest `t^snd_P` / `t^rcv_P` seen so far.

- **Correctness** (cf. Appendix B.1 of [SCKA]) states that the following assertions
  are always true:
  * `assertConsistentKeys`: `Key[A, t]` and `Key[B, t]` agree when both set;
  * `assertUniqueEpochs`: a party does not overwrite a key for an epoch;
  * `assertMonotonicity`: `t^snd_P ≥ t^cur_P`; a sending epoch never goes
    backwards — a party never reports a sending epoch behind one it already reached;
  * `assertKnownPrefix`: all epochs before `t^cur_P` have a recorded key; the
    sequence of a party's keys has no gaps up to its current epoch;
  * `assertMatchingEpoch`: `t^rcv_P = t^snd_P̄`; on delivery, the receiver
    recovers exactly the sending epoch its partner used to produce the message.

- **Vulnerable epochs.** A protocol state's *vulnerable epoch set* is modeled by functions
  `vulnA : StA → Finset ℕ` and `vulnB : StB → Finset ℕ` that determine
  the epochs that become vulnerable when that state is compromised.
  Revealing a state via `O-Corrupt-P` or `O-Send-P-rleak` adds its vulnerable epochs
  to the set of `Exposed` epochs.
  A challenge for epoch `t` requires `t ∉ Exposed ∪ Challenged`,
  and conversely a state compromise is refused if it would expose an already-`Challenged` epoch.

  This is analogous to the ΔPCS and ΔFS parameters in CKA, which also control the
  relation between state corruption and challenge epochs.

  Vulnerable epochs are protocol specific and have to be defined when proving security.
-/

section Games

variable {IK StA StB I Rho Rand : Type}

/-- The two parties in an SCKA protocol. -/
inductive SCKAParty where
  | A | B
  deriving DecidableEq, Repr

/-- The opposite party: `A.other = B` and `B.other = A`. -/
def SCKAParty.other : SCKAParty → SCKAParty
  | .A => .B
  | .B => .A

/-- Internal state of the SCKA game.

- `stA`, `stB`: per-party protocol state.
- `keyA`, `keyB`: tables with epoch keys derived by each party.
- `msgA`, `msgB`: arrays storing sent messages and their epochs.
- `nA`, `nB`: per-party send counters (number of messages sent so far).
- `tcurA`, `tcurB`: per-party current epoch (latest usable epoch).
- `exposed`: epochs exposed by corruption or randomness leakage.
- `challenged`: epochs the adversary has challenged.
- `correct`: whether all correctness properties have held so far. -/
-- ANCHOR: SCKAGameState
structure GameState (StA StB I Rho : Type) where
  /-- Local protocol state for party A. -/
  stA : StA
  /-- Local protocol state for party B. -/
  stB : StB
  /-- Key table for A: `Key[A, t]`. -/
  keyA : ℕ → Option I
  /-- Key table for B: `Key[B, t]`. -/
  keyB : ℕ → Option I
  /-- Transit array for A's messages: `Msg[A, n] = (ρ, t^snd)`. -/
  msgA : ℕ → Option (Rho × ℕ)
  /-- Transit array for B's messages: `Msg[B, n] = (ρ, t^snd)`. -/
  msgB : ℕ → Option (Rho × ℕ)
  /-- Number of messages A has sent. -/
  nA : ℕ
  /-- Number of messages B has sent. -/
  nB : ℕ
  /-- A's current epoch `t^cur_A`. -/
  tcurA : ℕ
  /-- B's current epoch `t^cur_B`. -/
  tcurB : ℕ
  /-- Epochs exposed through corruption or randomness leakage. -/
  exposed : Finset ℕ
  /-- Epochs already challenged. -/
  challenged : Finset ℕ
  /-- Whether all correctness asserts have held so far. -/
  correct : Bool
-- ANCHOR_END: SCKAGameState

/-- Initial game state. -/
def initGameState (stA : StA) (stB : StB) : GameState StA StB I Rho :=
  { stA, stB,
    keyA := fun _ => none, keyB := fun _ => none,
    msgA := fun _ => none, msgB := fun _ => none,
    nA := 0, nB := 0, tcurA := 0, tcurB := 0,
    exposed := ∅, challenged := ∅, correct := true }

/-! ### Oracle specifications -/

/-- Oracle spec for the SCKA correctness game: uniform randomness, send and receive oracles. -/
-- ANCHOR: sckaCorrectnessSpec
def sckaCorrectnessSpec (Rho : Type) :=
  unifSpec                                  -- Uniform randomness
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho))       -- O-Send-A
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho))       -- O-Send-B
  + (ℕ →ₒ Option (ℕ × Option ℕ))                -- O-Recv-A
  + (ℕ →ₒ Option (ℕ × Option ℕ))                -- O-Recv-B
-- ANCHOR_END: sckaCorrectnessSpec

/-- Oracle spec for the SCKA security game: the correctness spec extended with the
randomness-leaking send oracles, the challenge oracle, and the corruption oracles. -/
-- ANCHOR: sckaSecuritySpec
def sckaSecuritySpec (StA StB I Rho Rand : Type) :=
  sckaCorrectnessSpec Rho
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))    -- O-Send-A-rleak
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))    -- O-Send-B-rleak
  + (ℕ →ₒ Option I)                                  -- O-Chall t
  + (Unit →ₒ Option StA)                             -- O-Corrupt-A
  + (Unit →ₒ Option StB)                             -- O-Corrupt-B
-- ANCHOR_END: sckaSecuritySpec

/-! ### Send oracles -/

/-- **O-Send-A** (plain, `rleak = 0`).
```text
Send-A:
  ((tIA, IA), ρ, t^snd_A, stA) ←$ scka.sendA(stA)
  assert t^snd_A ≥ t^cur_A          -- monotonicity
  t^cur_A ← t^snd_A
  if (tIA, IA) ≠ (⊥, ⊥):            -- new key derived
     assert Key[A, tIA] = ⊥         -- unique epochs
     assert Key[B, tIA] ∈ {IA, ⊥}   -- consistent keys
     Key[A, tIA] ← IA
     assert ∀ t ≤ t^snd_A : Key[A, t] ≠ ⊥     -- known prefix
  Msg[A, ++nA] ← (ρ, t^snd_A)
  return (t^snd_A, tIA, ρ)
``` -/
-- ANCHOR: oracleSendA
def oracleSendA [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    match ← liftM (scka.sendA state.stA) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stA') =>
      let assertMonotonicity := state.tcurA ≤ tsnd
      let nA' := state.nA + 1
      let msgA' := Function.update state.msgA nA' (some (ρ, tsnd))
      match keyOpt with
      | none =>
        set { state with
          stA := stA', tcurA := tsnd, msgA := msgA', nA := nA',
          correct := state.correct && assertMonotonicity }
        return some (tsnd, none, ρ)
      | some (tI, key) =>
        let assertUniqueEpochs := (state.keyA tI).isNone
        let assertConsistentKeys := (state.keyB tI).isNone || state.keyB tI == some key
        let keyA' := Function.update state.keyA tI (some key)
        let assertKnownPrefix := (List.range (tsnd + 1)).all (fun t => (keyA' t).isSome)
        set { state with
          stA := stA', tcurA := tsnd, keyA := keyA', msgA := msgA', nA := nA',
          correct := state.correct
            && assertMonotonicity && assertUniqueEpochs
            && assertConsistentKeys && assertKnownPrefix }
        return some (tsnd, some tI, ρ)
-- ANCHOR_END: oracleSendA

/-- **O-Send-B** (plain, `rleak = 0`).
```text
Send-B:
  ((tIB, IB), ρ, t^snd_B, stB) ←$ scka.sendB(stB)
  assert t^snd_B ≥ t^cur_B                  -- monotonicity
  t^cur_B ← t^snd_B
  if (tIB, IB) ≠ (⊥, ⊥):                   -- new key derived
     assert Key[B, tIB] = ⊥               -- unique epochs
     assert Key[A, tIB] ∈ {IB, ⊥}         -- consistent keys
     Key[B, tIB] ← IB
     assert ∀ t ≤ t^snd_B : Key[B, t] ≠ ⊥    -- known prefix
  Msg[B, ++nB] ← (ρ, t^snd_B)
  return (t^snd_B, tIB, ρ)
``` -/
-- ANCHOR: oracleSendB
def oracleSendB [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    match ← liftM (scka.sendB state.stB) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stB') =>
      let assertMonotonicity := state.tcurB ≤ tsnd
      let nB' := state.nB + 1
      let msgB' := Function.update state.msgB nB' (some (ρ, tsnd))
      match keyOpt with
      | none =>
        set { state with
          stB := stB', tcurB := tsnd, msgB := msgB', nB := nB',
          correct := state.correct && assertMonotonicity }
        return some (tsnd, none, ρ)
      | some (tI, key) =>
        let assertUniqueEpochs := (state.keyB tI).isNone
        let assertConsistentKeys := (state.keyA tI).isNone || state.keyA tI == some key
        let keyB' := Function.update state.keyB tI (some key)
        let assertKnownPrefix := (List.range (tsnd + 1)).all (fun t => (keyB' t).isSome)
        set { state with
          stB := stB', tcurB := tsnd, keyB := keyB', msgB := msgB', nB := nB',
          correct := state.correct
            && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix }
        return some (tsnd, some tI, ρ)
-- ANCHOR_END: oracleSendB

/-- **O-Send-A-rleak** (`rleak = 1`).
Like `O-Send-A`, but uses `sendArleak`, computes the newly vulnerable epochs
`vuln' = vulnA stA' \ vulnA stA`, requires `vuln' ∩ Challenged = ∅`,
adds `vuln'` to `Exposed`, and also returns the randomness.

```text
Send-A-rleak:
  vuln ← stA.vuln
  ((tIA, IA), ρ, t^snd_A, stA) ←$ scka.sendArleak(stA)
  vuln' ← stA.vuln \ vuln                         -- newly vulnerable epochs
  req  vuln' ∩ Challenged = ∅
  Exposed = Exposed ∪ vuln'
  assert t^snd_A ≥ t^cur_A                -- monotonicity
  t^cur_A ← t^snd_A
  if (tIA, IA) ≠ (⊥, ⊥):
     assert Key[A, tIA] = ⊥               -- unique epochs
     assert Key[B, tIA] ∈ {IA, ⊥}         -- consistent keys
     Key[A, tIA] ← IA
     assert ∀ t ≤ t^snd_A : Key[A, t] ≠ ⊥    -- known prefix
  Msg[A, ++nA] ← (ρ, t^snd_A)
  return (t^snd_A, tIA, ρ, rand)
``` -/
-- ANCHOR: oracleSendArleak
def oracleSendArleak [DecidableEq I] (vulnA : StA → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vulnOld := vulnA state.stA
    match ← liftM (scka.sendArleak state.stA) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stA', rand) =>
      let vuln' := vulnA stA' \ vulnOld
      -- req vuln' ∩ Challenged = ∅
      if vuln' ∩ state.challenged ≠ ∅ then pure none
      else
        let exposed' := state.exposed ∪ vuln'
        let assertMonotonicity := state.tcurA ≤ tsnd
        let nA' := state.nA + 1
        let msgA' := Function.update state.msgA nA' (some (ρ, tsnd))
        match keyOpt with
        | none =>
          set { state with
            stA := stA', tcurA := tsnd, exposed := exposed',
            msgA := msgA', nA := nA', correct := state.correct && assertMonotonicity }
          return some (tsnd, none, ρ, rand)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyA tI).isNone
          let assertConsistentKeys := (state.keyB tI).isNone || state.keyB tI == some key
          let keyA' := Function.update state.keyA tI (some key)
          let assertKnownPrefix := (List.range (tsnd + 1)).all (fun t => (keyA' t).isSome)
          set { state with
            stA := stA', tcurA := tsnd, exposed := exposed', keyA := keyA',
            msgA := msgA', nA := nA',
            correct := state.correct
              && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix }
          return some (tsnd, some tI, ρ, rand)
-- ANCHOR_END: oracleSendArleak

/-- **O-Send-B-rleak** (`rleak = 1`).
Run B's randomness-leaking send, compute the newly vulnerable epochs
`vuln' = vulnB stB' \ vulnB stB`, require `vuln' ∩ Challenged = ∅`,
add `vuln'` to `Exposed`, and also return the randomness.

```text
Send-B-rleak:
  rand ←$ R
  vuln ← stB.vuln
  ((tIB, IB), ρ, t^snd_B, stB) ←$ CKA-Send-B(stB; rand)
  vuln' ← stB.vuln \ vuln                           -- newly vulnerable epochs
  req  vuln' ∩ Challenged = ∅
  Exposed = Exposed ∪ vuln'
  assert t^snd_B ≥ t^cur_B              -- monotonicity
  t^cur_B ← t^snd_B
  if (tIB, IB) ≠ (⊥, ⊥):
     assert Key[B, tIB] = ⊥              -- unique epochs
     assert Key[A, tIB] ∈ {IB, ⊥}        -- consistent keys
     Key[B, tIB] ← IB
     assert ∀ t ≤ t^snd_B : Key[B, t] ≠ ⊥   -- known prefix
  Msg[B, ++nB] ← (ρ, t^snd_B)
  return (t^snd_B, tIB, ρ, rand)
``` -/
-- ANCHOR: oracleSendBrleak
def oracleSendBrleak [DecidableEq I] (vulnB : StB → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vulnOld := vulnB state.stB
    match ← liftM (scka.sendBrleak state.stB) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stB', rand) =>
      let vuln' := vulnB stB' \ vulnOld
      if vuln' ∩ state.challenged ≠ ∅ then pure none
      else
        let exposed' := state.exposed ∪ vuln'
        let assertMonotonicity := state.tcurB ≤ tsnd
        let nB' := state.nB + 1
        let msgB' := Function.update state.msgB nB' (some (ρ, tsnd))
        match keyOpt with
        | none =>
          set { state with
            stB := stB', tcurB := tsnd, exposed := exposed',
            msgB := msgB', nB := nB', correct := state.correct && assertMonotonicity }
          return some (tsnd, none, ρ, rand)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyB tI).isNone
          let assertConsistentKeys := (state.keyA tI).isNone || state.keyA tI == some key
          let keyB' := Function.update state.keyB tI (some key)
          let assertKnownPrefix := (List.range (tsnd + 1)).all (fun t => (keyB' t).isSome)
          set { state with
            stB := stB', tcurB := tsnd, exposed := exposed', keyB := keyB',
            msgB := msgB', nB := nB',
            correct := state.correct
              && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix }
          return some (tsnd, some tI, ρ, rand)
-- ANCHOR_END: oracleSendBrleak

/-! ### Receive oracles -/

/-- **O-Recv-A n.**
Deliver `Msg[B, n]` to A (`req Msg[B, n] ≠ ⊥`), run A's receive, check the matching
epoch and key correctness asserts, and return `(t^rcv, t_I?)`.

```text
Receive-A(n):
 1  req Msg[B, n] ≠ ⊥
 2  (ρ, t^snd_B) ← Msg[B, n]
 3  ((tIB, IB), t^rcv_A, stA) ← scka.recvA(stA, ρ)
 4  assert t^rcv_A = t^snd_B        -- matching epoch
 5  t^cur_A ← max(t^cur_A, t^rcv_A)
 6  if (tIB, IB) ≠ (⊥, ⊥):          -- new key derived
 7     assert Key[A, tIB] = ⊥       -- unique epochs
 8     assert Key[B, tIB] ∈ {IB, ⊥}        -- consistent keys
 9     Key[A, tIB] ← IB
10     assert ∀ t ≤ t^cur_A : Key[A, t] ≠ ⊥   -- known prefix
11  return (t^rcv_A, tIB)
``` -/
-- ANCHOR: oracleRecvA
def oracleRecvA [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun (n : ℕ) => do
    let state ← get
    -- req Msg[B, n] ≠ ⊥
    match state.msgB n with
    | none => pure none
    | some (ρ, tsndB) =>
      match scka.recvA state.stA ρ with
      | none =>
        -- honest delivery should succeed; failure is a correctness violation.
        set { state with correct := false }
        return none
      | some (keyOpt, trcv, stA') =>
        let assertMatchingEpoch := trcv == tsndB
        let tcurA' := max state.tcurA trcv
        match keyOpt with
        | none =>
          set { state with
            stA := stA', tcurA := tcurA',
            correct := state.correct && assertMatchingEpoch }
          return some (trcv, none)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyA tI).isNone
          let assertConsistentKeys := (state.keyB tI).isNone || state.keyB tI == some key
          let keyA' := Function.update state.keyA tI (some key)
          let assertKnownPrefix := (List.range (tcurA' + 1)).all (fun t => (keyA' t).isSome)
          set { state with
            stA := stA', tcurA := tcurA', keyA := keyA',
            correct := state.correct
              && assertMatchingEpoch && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix }
          return some (trcv, some tI)
-- ANCHOR_END: oracleRecvA

/-- **O-Recv-B n.**
Deliver `Msg[A, n]` to B (`req Msg[A, n] ≠ ⊥`), run B's receive, check the matching
epoch and key correctness asserts, and return `(t^rcv, t_I?)`.

```text
Receive-B(n):
 1  req Msg[A, n] ≠ ⊥
 2  (ρ, t^snd_A) ← Msg[A, n]
 3  ((tIA, IA), t^rcv_B, stB) ← scka.recvB(stB, ρ)
 4  assert t^rcv_B = t^snd_A      -- matching epoch
 5  t^cur_B ← max(t^cur_B, t^rcv_B)
 6  if (tIA, IA) ≠ (⊥, ⊥):
 7     assert Key[B, tIA] = ⊥       -- unique epochs
 8     assert Key[A, tIA] ∈ {IA, ⊥}        -- consistent keys
 9     Key[B, tIA] ← IA
10     assert ∀ t ≤ t^cur_B : Key[B, t] ≠ ⊥   -- known prefix
11  return (t^rcv_B, tIA)
``` -/
-- ANCHOR: oracleRecvB
def oracleRecvB [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun (n : ℕ) => do
    let state ← get
    match state.msgA n with
    | none => pure none
    | some (ρ, tsndA) =>
      match scka.recvB state.stB ρ with
      | none =>
        set { state with correct := false }
        return none
      | some (keyOpt, trcv, stB') =>
        let assertMatchingEpoch := trcv == tsndA
        let tcurB' := max state.tcurB trcv
        match keyOpt with
        | none =>
          set { state with
            stB := stB', tcurB := tcurB',
            correct := state.correct && assertMatchingEpoch }
          return some (trcv, none)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyB tI).isNone
          let assertConsistentKeys := (state.keyA tI).isNone || state.keyA tI == some key
          let keyB' := Function.update state.keyB tI (some key)
          let assertKnownPrefix := (List.range (tcurB' + 1)).all (fun t => (keyB' t).isSome)
          set { state with
            stB := stB', tcurB := tcurB', keyB := keyB',
            correct := state.correct
              && assertMatchingEpoch && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix }
          return some (trcv, some tI)
-- ANCHOR_END: oracleRecvB

/-! ### Challenge oracle -/

/-- **O-Chall t.**
`req t ∉ Exposed ∪ Challenged`; take the recorded key for epoch `t`;
return the real key (`isRandom = false`) or a
freshly sampled uniform key (`isRandom = true`); record `t` as challenged.

```text
Chall(t):
 1  req t ∉ Exposed ∪ Challenged
 2  if Key[A, t] ≠ ⊥:  K ← Key[A, t]
 4  else            :  K ← Key[B, t]
 5  req K ≠ ⊥
 6  if b = 1:  K ←$ I                               // replace with random key
 8  Challenged = Challenged ∪ {t}
 9  return K
``` -/
-- ANCHOR: oracleChall
def oracleChall (isRandom : Bool) (StA StB I Rho : Type) [SampleableType I] :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun (t : ℕ) => do
    let state ← get
    -- req t ∉ Exposed ∪ Challenged
    if t ∈ state.exposed ∨ t ∈ state.challenged then pure none
    else
      let key? := match state.keyA t with
        | some k => some k
        | none => state.keyB t
      match key? with
      | none => pure none -- req K ≠ ⊥
      | some k =>
        let outK ← if isRandom then liftM ($ᵗ I : ProbComp I) else pure k
        set { state with challenged := insert t state.challenged }
        return some outK
-- ANCHOR_END: oracleChall

/-! ### Corruption oracles -/

/-- **O-Corrupt-A.**
`req stA.vuln ∩ Challenged = ∅`; expose `stA.vuln`; return A's state.

```text
Corr-A():
 1  req stA.vuln ∩ Challenged = ∅                    // no challenge of a vulnerable epoch
 2  Exposed = Exposed ∪ stA.vuln
 3  return stA
``` -/
-- ANCHOR: oracleCorruptA
def oracleCorruptA (vulnA : StA → Finset ℕ) (StB I Rho : Type) :
    QueryImpl (Unit →ₒ Option StA) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vuln := vulnA state.stA
    if vuln ∩ state.challenged ≠ ∅ then pure none
    else
      set { state with exposed := state.exposed ∪ vuln }
      return some state.stA
-- ANCHOR_END: oracleCorruptA

/-- **O-Corrupt-B.**
`req stB.vuln ∩ Challenged = ∅`; expose `stB.vuln`; return B's state.

```text
Corr-B():
 1  req stB.vuln ∩ Challenged = ∅                    // no challenge of a vulnerable epoch
 2  Exposed = Exposed ∪ stB.vuln
 3  return stB
``` -/
-- ANCHOR: oracleCorruptB
def oracleCorruptB (vulnB : StB → Finset ℕ) (StA I Rho : Type) :
    QueryImpl (Unit →ₒ Option StB) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vuln := vulnB state.stB
    if vuln ∩ state.challenged ≠ ∅ then pure none
    else
      set { state with exposed := state.exposed ∪ vuln }
      return some state.stB
-- ANCHOR_END: oracleCorruptB

/-- Oracle for adversary randomness: forwards to `ProbComp`. -/
def oracleUnif (StA StB I Rho : Type) :
    QueryImpl unifSpec (StateT (GameState StA StB I Rho) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState StA StB I Rho) ProbComp)

/-- Oracle set for the SCKA correctness game: uniform randomness, plain send oracles,
and receive oracles. -/
-- ANCHOR: sckaCorrectnessImpl
def sckaCorrectnessImpl [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaCorrectnessSpec Rho)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  oracleUnif StA StB I Rho
    + oracleSendA scka + oracleSendB scka
    + oracleRecvA scka + oracleRecvB scka
-- ANCHOR_END: sckaCorrectnessImpl

/-- Oracle set for the SCKA security game (Fig. 1): the correctness oracles
extended with randomness-leaking sends, challenge, and corruption. -/
-- ANCHOR: sckaSecurityImpl
def sckaSecurityImpl (isRandom : Bool) (vulnA : StA → Finset ℕ) (vulnB : StB → Finset ℕ)
    [SampleableType I] [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  sckaCorrectnessImpl scka
    + oracleSendArleak vulnA scka + oracleSendBrleak vulnB scka
    + oracleChall isRandom StA StB I Rho
    + oracleCorruptA vulnA StB I Rho + oracleCorruptB vulnB StA I Rho
-- ANCHOR_END: sckaSecurityImpl

/-- SCKA correctness adversary: access to the restricted send/receive oracles. -/
-- ANCHOR: SCKACorrectnessAdversary
abbrev SCKACorrectnessAdversary (Rho : Type) :=
  OracleComp (sckaCorrectnessSpec Rho) Bool
-- ANCHOR_END: SCKACorrectnessAdversary

/-- SCKA security adversary: access to all oracles of `sckaSecuritySpec`. -/
-- ANCHOR: SCKAAdversary
abbrev SCKAAdversary (StA StB I Rho Rand : Type) :=
  OracleComp (sckaSecuritySpec StA StB I Rho Rand) Bool
-- ANCHOR_END: SCKAAdversary

/-! ### Experiments -/

/-- **Correctness experiment** (§3.1 of [SCKA]).
Run the adversary against the restricted send/receive oracles and return whether
all correctness invariants (Monotonicity, Matching epoch, Unique epochs,
Consistent keys, Known prefix) held throughout. -/
-- ANCHOR: correctnessExp
def correctnessExp [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKACorrectnessAdversary Rho) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let (_, state) ← (simulateQ (sckaCorrectnessImpl scka) adversary).run
    (initGameState stA stB)
  return state.correct
-- ANCHOR_END: correctnessExp

/-- **Security experiment** (Fig. 1).
Initialize both parties, sample a challenge bit, run the adversary with the full
game oracles, and return whether it guessed the bit. -/
-- ANCHOR: securityExp
def securityExp [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (vulnA : StA → Finset ℕ) (vulnB : StB → Finset ℕ) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (sckaSecurityImpl b vulnA vulnB scka) adversary).run
    (initGameState stA stB)
  return (b == b')
-- ANCHOR_END: securityExp

/-- SCKA guess advantage: `|Pr[Win] - 1/2|`. -/
-- ANCHOR: sckaGuessAdvantage
noncomputable def sckaGuessAdvantage [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (vulnA : StA → Finset ℕ) (vulnB : StB → Finset ℕ) : ℝ :=
  |(Pr[= true | securityExp scka adversary vulnA vulnB]).toReal - 1 / 2|
-- ANCHOR_END: sckaGuessAdvantage

end Games

end SCKAScheme
