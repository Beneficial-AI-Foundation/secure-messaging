/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.Control

/-!
# Joint states of the two parties

`AllowedStatePair gen enc` lists the pairs of a key-generating state `gen` and an encapsulating
state `enc` that occur at the same epoch. For states `st` and `peer` of the two parties,
`PairInv st peer` requires:

1. if the epochs are equal and `st` is key-generating, then `AllowedStatePair st peer`;
2. if `peer.epoch = st.epoch + 1`, then `st` is in `ct2Sampled` and `peer` in `noHeaderReceived`.

`StatePairInv` requires `PairInv` in both directions. Every oracle of the correctness game
preserves `ControlInv ∧ StatePairInv` (`correctnessImpl_preserves_controlInv_statePairInv`).
-/

open OracleSpec OracleComp
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

/-- The pairs of a key generator's state and an encapsulator's state that occur at the same
epoch. -/
def AllowedStatePair {P : Parameters ProbComp} {AuthState : Type} :
    State P AuthState → State P AuthState → Prop
  | .keysUnsampled .., .noHeaderReceived .. => True
  | .keysSampled .., .noHeaderReceived .. => True
  | .keysSampled .., .headerReceived .. => True
  | .keysSampled .., .ct1Sampled .. => True
  | .headerSent .., .ct1Sampled .. => True
  | .headerSent .., .ekReceivedCt1Sampled .. => True
  | .ct1Received .., .ct1Sampled .. => True
  | .ct1Received .., .ekReceivedCt1Sampled .. => True
  | .ct1Received .., .ct1Acknowledged .. => True
  | .ct1Received .., .ct2Sampled .. => True
  | .ekSentCt1Received .., .ct2Sampled .. => True
  | _, _ => False

/-- `PairInv st peer` holds if, at equal epochs, a key-generating `st` forms an `AllowedStatePair`
with `peer`, and, if `peer` is one epoch ahead, `st` is in `ct2Sampled` and `peer` in
`noHeaderReceived`. -/
def PairInv {P : Parameters ProbComp} {AuthState : Type} (st peer : State P AuthState) : Prop :=
  (st.epoch = peer.epoch → st.controlPosition.isGenerator = true → AllowedStatePair st peer) ∧
    (peer.epoch = st.epoch + 1 →
      st.controlPosition = ⟨false, 4⟩ ∧ peer.controlPosition = ⟨false, 0⟩)

/-- `PairInv` holds for A's state against B's and for B's state against A's. -/
def StatePairInv {P : Parameters ProbComp} {AuthState : Type} (s : GameState P AuthState) : Prop :=
  PairInv s.stA s.stB ∧ PairInv s.stB s.stA

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- Each party's state satisfies `PairInv` against its peer's state. -/
theorem StatePairInv.pair {s : GameState P AuthState} (hs : StatePairInv s) (party : Bool) :
    PairInv (s.stateAt party) (s.stateAt (!party)) := by
  cases party; exacts [hs.2, hs.1]

/-- A send from `st` preserves `PairInv` between `st` and `peer` in both directions. -/
theorem PairInv.send {st peer : State P AuthState} {r : SendResult P AuthState}
    (hedge : SendEdge auth st r) (h : PairInv st peer) (h' : PairInv peer st) :
    PairInv r.state peer ∧ PairInv peer r.state := by
  cases hedge <;> cases peer <;>
    simp_all [PairInv, AllowedStatePair, State.controlPosition, State.epoch]

/-- A receive by `st` of a message recorded by `peer` preserves `PairInv` between `st` and `peer`
in both directions. -/
theorem PairInv.receive [DecidableEq P.Sym] {st peer : State P AuthState} {msg : Message P.Sym}
    {r : RecvResult P AuthState} (hedge : ReceiveEdge auth st msg r)
    (hpos : 0 < st.epoch) (hposP : 0 < peer.epoch)
    (hcross : st.epoch ≤ peer.completedEpoch + 1) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    (hroles : st.epoch = peer.epoch →
      st.controlPosition.isGenerator = (!peer.controlPosition.isGenerator))
    (hle : msg.epoch ≤ peer.epoch)
    (hstep : msg.epoch = peer.epoch → msg.type.sendStep ≤ peer.controlPosition.step)
    (h : PairInv st peer) (h' : PairInv peer st) :
    PairInv r.state peer ∧ PairInv peer r.state := by
  -- One goal per edge and peer state; `simp` evaluates the roles, steps and allowed pairs of the
  -- two constructors, and `omega` decides the epoch arithmetic.
  cases hedge
  case ignore => exact ⟨h, h'⟩
  all_goals cases peer <;>
    simp only [PairInv, AllowedStatePair, State.controlPosition, State.epoch,
      State.completedEpoch, MessageType.sendStep, ControlPosition.mk.injEq, Bool.true_eq_false,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, and_true, true_and, and_false, false_and,
      imp_false, and_self, implies_true, not_true_eq_false, not_false_eq_true] at * <;>
    omega

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

omit [DecidableEq P.EpochKey] [DecidableEq P.Sym] in
/-- At equal epochs the two parties have opposite roles. -/
theorem roles_opposite {s : GameState P AuthState} (hs : ControlInv s)
    (heq : s.stA.epoch = s.stB.epoch) :
    s.stA.controlPosition.isGenerator = (!s.stB.controlPosition.isGenerator) := by
  have hA := (hs.roles true).1
  have hB := (hs.roles false).1
  simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hA hB
  rw [hA, hB, heq]
  rcases Nat.mod_two_eq_zero_or_one s.stB.epoch with h | h <;> simp [h]

/-- Every oracle of the correctness game preserves `ControlInv` together with `StatePairInv`. -/
theorem correctnessImpl_preserves_controlInv_statePairInv :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey))
      (fun s => ControlInv s ∧ StatePairInv s) := by
  refine SCKAScheme.sckaCorrectnessImpl_preservesInv _ ?_ ?_ ?_ ?_
  · intro t s hs z hz
    cases t
    refine ⟨oracleSend_preserves_controlInv auth irl sampleInitKey true () s hs.1 z hz, ?_⟩
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendA_run_iff auth irl sampleInitKey s z).mp hz
    have hpair := PairInv.send auth ((mem_support_send_iff auth).mp hr) hs.2.1 hs.2.2
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> exact hpair
  · intro t s hs z hz
    cases t
    refine ⟨oracleSend_preserves_controlInv auth irl sampleInitKey false () s hs.1 z hz, ?_⟩
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendB_run_iff auth irl sampleInitKey s z).mp hz
    have hpair := PairInv.send auth ((mem_support_send_iff auth).mp hr) hs.2.2 hs.2.1
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> exact ⟨hpair.2, hpair.1⟩
  · intro n s hs z hz
    refine ⟨oracleRecv_preserves_controlInv auth irl sampleInitKey true n s hs.1 z hz, ?_⟩
    rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hs.2
    · exact hs.2
    have hB := hs.1.roles false
    simp only [PartyControl, Bool.false_eq_true, ↓reduceIte] at hB
    obtain ⟨-, hle, hstep, -⟩ := hB.2.2 n msg tsnd hentry
    have hpair := PairInv.receive auth (ReceiveEdge.of_eq_ok auth hraw)
      hs.1.epochKnowledge.keyPrefix.posA hs.1.epochKnowledge.keyPrefix.posB
      hs.1.epochKnowledge.epochA_le hs.1.epochKnowledge.epochB_le (roles_opposite hs.1) hle hstep
      hs.2.1 hs.2.2
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> exact hpair
  · intro n s hs z hz
    refine ⟨oracleRecv_preserves_controlInv auth irl sampleInitKey false n s hs.1 z hz, ?_⟩
    rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hs.2
    · exact hs.2
    have hA := hs.1.roles true
    simp only [PartyControl, ↓reduceIte] at hA
    obtain ⟨-, hle, hstep, -⟩ := hA.2.2 n msg tsnd hentry
    have hroles : s.stB.epoch = s.stA.epoch →
        s.stB.controlPosition.isGenerator = (!s.stA.controlPosition.isGenerator) := by
      intro heq
      rw [roles_opposite hs.1 heq.symm, Bool.not_not]
    have hpair := PairInv.receive auth (ReceiveEdge.of_eq_ok auth hraw)
      hs.1.epochKnowledge.keyPrefix.posB hs.1.epochKnowledge.keyPrefix.posA
      hs.1.epochKnowledge.epochB_le hs.1.epochKnowledge.epochA_le hroles hle hstep
      hs.2.2 hs.2.1
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> exact ⟨hpair.2, hpair.1⟩

end MLKEMBraid
