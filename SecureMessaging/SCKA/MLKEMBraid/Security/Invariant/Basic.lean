/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Games
import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant

/-!
# The repaired transcript invariant

`RepairInv` records control, payload and output-key consistency without assuming actual
agreement of retained decapsulations. `DecapsGood` supplies precisely that missing condition.
The frame and peer facts here depend on neither sampling nor analytical bad-event bounds.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- `TranscriptConsistent` for the unit authenticator without the generator's actual
decapsulation agreement. -/
structure RepairInv (hMac : P.Mac = Unit) (T : ℕ → EpochTranscript P)
    (s : MLKEMBraid.GameState P Unit) : Prop where
  /-- The correctness flag is true. -/
  correct : s.correct = true
  /-- The control invariant holds. -/
  control : ControlInv s
  /-- The state-pair invariant holds. -/
  statePair : StatePairInv s
  /-- Epoch `0` has no key pair. -/
  keypair_zero : (T 0).keypair = none
  /-- Epoch `0` has no encapsulation. -/
  encaps_zero : (T 0).encaps1 = none
  /-- A recorded key pair belongs to a positive epoch its generator has reached. -/
  keypair : ∀ e pk sk, (T e).keypair = some (pk, sk) →
    0 < e ∧ e ≤ (if e % 2 = 1 then s.stA else s.stB).epoch
  /-- A recorded encapsulation belongs to a positive epoch its encapsulator has completed and
  that has a recorded key pair. -/
  encaps : ∀ e encapsState ct1 key,
    (T e).encaps1 = some (encapsState, ct1, key) →
    0 < e ∧ e ≤ (if e % 2 = 1 then s.stB else s.stA).completedEpoch ∧
      ∃ pk sk, (T e).keypair = some (pk, sk)
  /-- A's state agrees with the transcript. -/
  localA : LocalPayloadInv (auth P hMac) () T s.stA
  /-- B's state agrees with the transcript. -/
  localB : LocalPayloadInv (auth P hMac) () T s.stB
  /-- Every recorded message agrees with the transcript. -/
  messages : ∀ (party : Bool) n msg tsnd,
    (if party then s.msgA else s.msgB) n = some (msg, tsnd) →
      MessagePayloadInv (auth P hMac) () T msg
  /-- Each party's output keys are the transcript keys of its completed epochs. -/
  keys : ∀ (party : Bool) e,
    (if party then s.keyA else s.keyB) e =
      if 0 < e ∧ e ≤ (if party then s.stA else s.stB).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e)
      else none

/-- Actual decapsulation of every recorded first-stage encapsulation gives its derived key. -/
def DecapsGood (T : ℕ → EpochTranscript P) : Prop :=
  ∀ e pk sk encapsState ct1 key, (T e).keypair = some (pk, sk) →
    (T e).encaps1 = some (encapsState, ct1, key) →
    decapsEpochKey e pk sk encapsState ct1 = some (P.kdfOK key e)

namespace RepairInv

variable {hMac : P.Mac = Unit} {T : ℕ → EpochTranscript P} {s : MLKEMBraid.GameState P Unit}

/-- Transcript consistency implies the repaired invariant. -/
theorem of_transcriptConsistent (h : TranscriptConsistent (auth P hMac) () T s) :
    RepairInv hMac T s :=
  ⟨h.correct, h.control, h.statePair, h.keypair_zero, h.encaps_zero, h.keypair,
    fun e es ct1 key hc => by
      obtain ⟨h0, hle, pk, sk, hkp, -⟩ := h.encaps e es ct1 key hc
      exact ⟨h0, hle, pk, sk, hkp⟩,
    h.localA, h.localB, h.messages, h.keys⟩

/-- With decapsulation agreement the repaired invariant is transcript consistency. -/
theorem transcriptConsistent (h : RepairInv hMac T s) (hgood : DecapsGood T) :
    TranscriptConsistent (auth P hMac) () T s :=
  ⟨h.correct, h.control, h.statePair, h.keypair_zero, h.encaps_zero, h.keypair,
    fun e es ct1 key hc => by
      obtain ⟨h0, hle, pk, sk, hkp⟩ := h.encaps e es ct1 key hc
      exact ⟨h0, hle, pk, sk, hkp, fun _ => hgood e pk sk es ct1 key hkp hc⟩,
    h.localA, h.localB, h.messages, h.keys⟩

/-- The state of either party agrees with the transcript. -/
theorem «local» (h : RepairInv hMac T s) (party : Bool) :
    LocalPayloadInv (auth P hMac) () T (s.stateAt party) := by
  cases party; exacts [h.localB, h.localA]

/-- The invariant reads neither the exposed nor the challenged epochs. -/
theorem setFlags (h : RepairInv hMac T s) (X Y : Finset ℕ) :
    RepairInv hMac T { s with exposed := X, challenged := Y } :=
  have hC := h.control
  have hE := hC.epochKnowledge
  ⟨h.correct,
    ⟨⟨⟨hE.keyPrefix.posA, hE.keyPrefix.posB, hE.keyPrefix.prefixA, hE.keyPrefix.prefixB⟩,
        hE.epochA_le, hE.epochB_le, hE.tcurA_le, hE.tcurB_le, hE.msgA, hE.msgB⟩,
      ⟨hC.recordedReport.msgA, hC.recordedReport.msgB⟩, hC.tcurA_le_sub_one,
      hC.tcurB_le_sub_one, hC.roles⟩,
    h.statePair, h.keypair_zero, h.encaps_zero, h.keypair, h.encaps, h.localA, h.localB,
    h.messages, h.keys⟩

/-- Build the invariant for the same transcript at a state with larger epochs and completed
epochs whose local states, messages and keys agree with the transcript. -/
theorem of_le (h : RepairInv hMac T s) {s' : MLKEMBraid.GameState P Unit}
    (hc : s'.correct = true) (hC : ControlInv s') (hP : StatePairInv s')
    (he : ∀ party, (s.stateAt party).epoch ≤ (s'.stateAt party).epoch)
    (hcomp : ∀ party, (s.stateAt party).completedEpoch ≤ (s'.stateAt party).completedEpoch)
    (hLocal : ∀ party, LocalPayloadInv (auth P hMac) () T (s'.stateAt party))
    (hMessages : ∀ party n msg tsnd, s'.messagesAt party n = some (msg, tsnd) →
      MessagePayloadInv (auth P hMac) () T msg)
    (hKeys : ∀ party e, s'.keysAt party e =
      if 0 < e ∧ e ≤ (s'.stateAt party).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e) else none) :
    RepairInv hMac T s' := by
  refine ⟨hc, hC, hP, h.keypair_zero, h.encaps_zero, ?_, ?_, hLocal true, hLocal false,
    hMessages, hKeys⟩
  · intro e pk sk hk
    obtain ⟨h0, hle⟩ := h.keypair e pk sk hk
    refine ⟨h0, ?_⟩
    rw [← GameState.stateAt_generator] at hle ⊢
    exact hle.trans (he _)
  · intro e es ct1 key hc'
    obtain ⟨h0, hle, hkp⟩ := h.encaps e es ct1 key hc'
    refine ⟨h0, ?_, hkp⟩
    rw [← GameState.stateAt_encapsulator] at hle ⊢
    exact hle.trans (hcomp _)

/-- The pair and epoch bounds of the two parties. -/
theorem pairBounds (h : RepairInv hMac T s) (party : Bool) :
    let st := s.stateAt party
    let peer := s.stateAt (!party)
    PairInv st peer ∧ PairInv peer st ∧ 0 < st.epoch ∧ 0 < peer.epoch ∧
      st.epoch ≤ peer.completedEpoch + 1 ∧ peer.epoch ≤ st.completedEpoch + 1 ∧
      (st.epoch = peer.epoch →
        st.controlPosition.isGenerator = (!peer.controlPosition.isGenerator)) := by
  have hE := h.control.epochKnowledge
  refine ⟨h.statePair.pair party, by simpa using h.statePair.pair (!party),
    hE.keyPrefix.pos party, hE.keyPrefix.pos (!party), hE.epoch_le party,
    by simpa using hE.epoch_le (!party), ?_⟩
  cases party
  · intro heq
    simpa only [GameState.stateAt, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Bool.not_not] using (congrArg Bool.not (roles_opposite h.control heq.symm)).symm
  · exact roles_opposite h.control

/-- The peer of a key generator in `keysUnsampled` waits for the header of the same epoch. -/
theorem peer_of_keysUnsampled (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    (hst : s.stateAt party = .keysUnsampled e a) :
    ∃ b dec, s.stateAt (!party) = .noHeaderReceived e b dec := by
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds party
  exact PairInv.peer_of_keysUnsampled h1 h2 hpos hposP hcross hcrossP hst

/-- The peer of an encapsulator in `headerReceived` holds the recorded key pair of the epoch. -/
theorem peer_of_headerReceived (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.stateAt party = .headerReceived e a hdr dec) :
    ∃ pk sk b enc,
      (T e).keypair = some (pk, sk) ∧
      s.stateAt (!party) = .keysSampled e b sk (P.inc.toVector pk) enc ∧
      hdr = P.inc.toHeader pk := by
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, hroles⟩ := h.pairBounds party
  obtain ⟨b, sk', vec, enc, hpeer⟩ :=
    PairInv.peer_of_headerReceived h1 h2 hpos hposP hcross hcrossP hroles hst
  have hLs := h.local party
  have hLp := h.local (!party)
  rw [hst] at hLs
  rw [hpeer] at hLp
  obtain ⟨-, -, pk, sk, hkp, hhdr, -⟩ := hLs
  obtain ⟨-, pk', hkp', hvec, -⟩ := hLp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hkp.symm.trans hkp'))
  exact ⟨pk, sk, b, enc, hkp, by rw [hpeer, hvec], hhdr⟩

end RepairInv

/-- At equal epochs a generator waiting for `ct₂` is paired with `ct2Sampled`. -/
theorem PairInv.peer_of_ekSentCt1Received {st peer : State P Unit}
    (h : PairInv st peer) (h' : PairInv peer st)
    (hpos : 0 < st.epoch) (hposP : 0 < peer.epoch)
    (hcross : st.epoch ≤ peer.completedEpoch + 1) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    {e : ℕ} {a : Unit} {sk : P.SK} {ct1 : P.inc.C₁}
    {dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym}
    (hst : st = .ekSentCt1Received e a sk ct1 dec) :
    ∃ b enc, peer = .ct2Sampled e b enc := by
  subst hst
  cases peer <;>
    simp [PairInv, AllowedStatePair, State.controlPosition, State.epoch,
      State.completedEpoch] at * <;>
    omega

end MLKEMBraid.NoAuth
