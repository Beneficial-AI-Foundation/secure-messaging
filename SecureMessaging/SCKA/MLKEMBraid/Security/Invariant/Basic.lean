/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Games
public import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant

/-!
# The repaired transcript invariant

`RepairInv` is `TranscriptInv` with no condition on decapsulation: the control states, the
payloads and the output keys agree with the transcript. `DecapsGood` is the extra condition that
decapsulation of every recorded encapsulation gives its key. Like every `TranscriptInv`,
`RepairInv` ignores the exposed and challenged epochs (`TranscriptInv.setFlags`).
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace Braid.NoAuth

variable {P : Parameters ProbComp}

/-- `TranscriptInv` for the unit authenticator with no condition on decapsulation. -/
abbrev RepairInv (hMac : P.Mac = Unit) (T : ℕ → EpochTranscript P)
    (s : Braid.GameState P Unit) : Prop :=
  TranscriptInv (auth P hMac) (fun _ _ _ _ _ _ => True) () T s

/-- Actual decapsulation of every recorded first-stage encapsulation gives its derived key. -/
def DecapsGood (T : ℕ → EpochTranscript P) : Prop :=
  ∀ e pk sk encapsState ct1 key, (T e).keypair = some (pk, sk) →
    (T e).encaps1 = some (encapsState, ct1, key) →
    decapsEpochKey e pk sk encapsState ct1 = some (P.kdfOK key e)

namespace RepairInv

variable {hMac : P.Mac = Unit} {T : ℕ → EpochTranscript P} {s : Braid.GameState P Unit}

/-- Transcript consistency implies the repaired invariant. -/
theorem of_transcriptConsistent (h : TranscriptConsistent (auth P hMac) () T s) :
    RepairInv hMac T s :=
  h.mono _ _ fun _ _ _ _ _ _ _ _ _ => trivial

/-- Build the invariant for the same transcript at a state with larger epochs and completed
epochs whose local states, messages and keys agree with the transcript. -/
theorem of_le (h : RepairInv hMac T s) {s' : Braid.GameState P Unit}
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
    obtain ⟨h0, hle, pk, sk, hkp, -⟩ := h.encaps e es ct1 key hc'
    refine ⟨h0, ?_, pk, sk, hkp, fun _ => trivial⟩
    rw [← GameState.stateAt_encapsulator] at hle ⊢
    exact hle.trans (hcomp _)

end RepairInv

/-- At equal epochs a generator waiting for `ct₂` is paired with `ct2Sampled`. -/
theorem PairInv.peer_of_ekSentCt1Received {st peer : State P Unit}
    (h : PairInv st peer) (h' : PairInv peer st)
    (hpos : 0 < st.epoch) (hposP : 0 < peer.epoch)
    (hcross : st.epoch ≤ peer.completedEpoch + 1) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    {e : ℕ} {a : Unit} {sk : P.SK} {ct1 : P.inc.C₁}
    {dec : P.decCt2.D}
    (hst : st = .ekSentCt1Received e a sk ct1 dec) :
    ∃ b enc, peer = .ct2Sampled e b enc := by
  subst hst
  cases peer <;>
    simp [PairInv, AllowedStatePair, State.controlPosition, State.epoch,
      State.completedEpoch] at * <;>
    omega

end Braid.NoAuth
