/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant

/-!
# Payload preservation for sends without sampling

A send outside the key-generation and first-encapsulation branches preserves its local
payload invariant and epochs, outputs no key, and emits an honestly encoded payload. These
facts require only the local invariant, so they also apply to repaired security executions.
-/

open ErasureCodePayload.Streaming

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- The states whose send samples nothing: all but `keysUnsampled` and `headerReceived`. -/
def State.SendsNoSample : State P AuthState → Prop
  | .keysUnsampled .. => False
  | .headerReceived .. => False
  | _ => True

/-- A send without sampling preserves epochs and `LocalPayloadInv`, outputs no key, and emits a
message satisfying `MessagePayloadInv`. -/
theorem send_steady_step {ik : InitKey} {T : ℕ → EpochTranscript P}
    {st : State P AuthState} {r : SendResult P AuthState} (hedge : SendEdge auth st r)
    (hsteady : st.SendsNoSample) (hLocal : LocalPayloadInv auth ik T st) :
    r.outputKey = none ∧ r.state.epoch = st.epoch ∧ r.state.completedEpoch = st.completedEpoch ∧
      LocalPayloadInv auth ik T r.state ∧ MessagePayloadInv auth ik T r.msg := by
  cases hedge
  case keygen => exact False.elim hsteady
  case encaps1 => exact False.elim hsteady
  case hdrChunk _ _ sk _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, hkp, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, enc.nextIndex, hkp, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case ekChunk _ _ sk _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, _, _, _, hkp, -, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, enc.nextIndex, hkp, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case ackChunk _ _ sk _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, _, _, hkp, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, enc.nextIndex, hkp, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case idleEkSent => exact ⟨rfl, rfl, rfl, hLocal, rfl⟩
  case idleNoHeader => exact ⟨rfl, rfl, rfl, hLocal, rfl⟩
  case ct1Chunk _ _ _ es ct1 enc _ =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, _, _, key, -, hc, -, ⟨hecp, hpay⟩, -⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, es, ct1, key, enc.nextIndex, hc, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case ct1ChunkVec _ _ es ct1 _ _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, _, _, key, -, hc, -, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, es, ct1, key, enc.nextIndex, hc, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case idleAcknowledged => exact ⟨rfl, rfl, rfl, hLocal, rfl⟩
  case ct2Chunk _ _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, sk, es, ct1, key, hkp, hc, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, es, ct1, key, enc.nextIndex, hkp, hc, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]

end MLKEMBraid
