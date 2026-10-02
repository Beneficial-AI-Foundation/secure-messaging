/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.PublicKeyReconstruction

/-!
# Same-epoch public-key buffer provenance

For a successful receive of a recorded public-key message (bit `0`) whose responder epoch
equals the receiver's requester epoch, the requester chunk buffer is updated exactly as on
the public-key path of `recv`, and `RecordedPublicKeyChunks` is preserved.
Stale and advancing epochs are not covered here.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- On a same-epoch public-key message, the receive buffer is either unchanged (peer key
already installed), the buffer after inserting the incoming chunk (no decode yet), or
cleared (successful decode). -/
theorem recv_same_epoch_publicKey_receivedChunks [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ)
    (st' : State PK SK C Sym)
    (hsame : ρ.tRes = st.req.reqEpoch)
    (hbit : ρ.bit = some 0)
    (hout :
      recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
    st'.req.receivedChunks =
      if (st.res.ekPeer (st.req.reqEpoch - role.offset)).isNone then
        match (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 with
        | none => (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).1
        | some _ => ∅
      else st.req.receivedChunks := by
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      out.2.2.req.receivedChunks) hout
  simp only [Option.map_some] at hproj
  rw [recv] at hproj
  dsimp only at hproj
  have hstale : ¬ ρ.tRes < st.req.reqEpoch := by omega
  have hadvance : ¬ st.req.reqEpoch < ρ.tRes := by omega
  have hbit1 : ¬ (some (0 : Bit) = some 1) := by decide
  by_cases hctRec : ρ.ack.ctRec = true <;>
    simp only [hctRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    simp only [hstale, hadvance, hbit, if_false, and_true] at hproj
  all_goals
    by_cases hpk : (st.res.ekPeer (st.req.reqEpoch - role.offset)).isNone = true
    · simp only [hpk, if_true] at hproj ⊢
      cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
        simp only [hdecode] at hproj ⊢
      all_goals
        repeat' split at hproj
        all_goals simp only [Option.pure_def, Option.map_some] at hproj
        all_goals exact (Option.some.inj hproj).symm
    · simp only [hpk, hbit1, Bool.false_eq_true, if_false, and_false] at hproj ⊢
      repeat' split at hproj
      all_goals simp only [Option.pure_def, Option.map_some] at hproj
      all_goals exact (Option.some.inj hproj).symm

/-- A successful same-epoch receive of a recorded public-key message preserves
`RecordedPublicKeyChunks` for the requester buffer: the inserted chunk is witnessed by the
recorded message itself, retained chunks by the input buffer, and a cleared buffer is vacuous. -/
theorem recv_same_epoch_preserves_recordedPublicKeyChunks
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (msgs : ℕ → Option (Message Sym × ℕ))
    (st : State PK SK C Sym) (ρ : Message Sym)
    (n tsnd : ℕ)
    (key? : Option (ℕ × K)) (trcv : ℕ)
    (st' : State PK SK C Sym)
    (hrecord : msgs n = some (ρ, tsnd))
    (hsame : ρ.tRes = st.req.reqEpoch)
    (hbit : ρ.bit = some 0)
    (hchunks :
      RecordedPublicKeyChunks msgs st.req.reqEpoch st.req.receivedChunks)
    (hout :
      recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
    RecordedPublicKeyChunks msgs st'.req.reqEpoch st'.req.receivedChunks := by
  have hepoch :=
    (recv_success_state_facts role kem hDet ecEk ecCt st ρ key? trcv st' hout).2.2.2.1
  have hadvance : ¬ st.req.reqEpoch < ρ.tRes := by omega
  rw [if_neg hadvance] at hepoch
  rw [hepoch, recv_same_epoch_publicKey_receivedChunks role kem hDet ecEk ecCt st ρ
    key? trcv st' hsame hbit hout]
  by_cases hpk : (st.res.ekPeer (st.req.reqEpoch - role.offset)).isNone = true
  · rw [if_pos hpk]
    cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 with
    | some _ =>
        intro chunk hmem
        simp only [Finset.notMem_empty] at hmem
    | none =>
        change RecordedPublicKeyChunks msgs st.req.reqEpoch
          (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).1
        cases hch : ρ.ch with
        | none => exact hchunks
        | some ch =>
            intro chunk hmem
            simp only [insertChunkAndDecode, Finset.mem_insert] at hmem
            rcases hmem with rfl | hmem
            · exact ⟨n, ρ, tsnd, hrecord, hsame, hbit, hch⟩
            · exact hchunks chunk hmem
  · rw [if_neg hpk]
    exact hchunks

end oppBiKemCKA
