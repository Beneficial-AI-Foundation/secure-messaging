/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Ideal

/-!
# Epoch and send-count invariants of the auxiliary game

Let `Π` be Opp-UniKEM, let `mode : ℕ → Bool` be a challenge mode, and let
`idealSecurityImpl mode` be the auxiliary oracle implementation.
For a game state `s`, let `n := s.nA` count successful sends by A.

Every auxiliary query preserves `sendEpochInv` and, with correct erasure codes,
`reachableInv`. Both predicates hold initially. Each query increases `n` by at most one
if it is one of the four sends, and by zero otherwise.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

omit [SampleableType K] in
/-- Every auxiliary correctness query preserves `sendEpochInv`. -/
theorem idealCorrectnessImpl_preserves_sendEpochInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      sendEpochInv := by
  intro t s hs z hz
  rcases t with ((((n | u) | u) | n) | n)
  · rw [SCKAScheme.mem_support_oracleUnif_run n s z hz]; exact hs
  · exact oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
  · exact oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
  · exact oracleRecvAIdeal_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1
      leak n s hs z hz
  · exact oracleRecvB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs z hz

/-- Every auxiliary query preserves `sendEpochInv`, for every challenge mode. -/
theorem idealSecurityImpl_preserves_sendEpochInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      sendEpochInv :=
  SCKAScheme.securityImplOf_preservesInv_of_book _ _ _ _ _ sendEpochInv (fun _ _ _ h => h)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)
    (idealCorrectnessImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)

/-- An auxiliary query increases A's send counter by at most one if it is one of the four send
queries and not otherwise. -/
theorem idealSecurityImpl_sendCounter_step
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode t).run s)) :
    z.2.nA ≤ s.nA + if SCKAScheme.sckaSecuritySpec.isSendQuery t then 1 else 0 :=
  SCKAScheme.securityImplOf_nA_step _ _ _ _ _
    (idealCorrectnessImpl_nA_step kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _) t s z hz

/-- With correct erasure codes, every auxiliary query preserves `reachableInv`, for every
challenge mode. -/
theorem idealSecurityImpl_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) :=
  SCKAScheme.securityImplOf_preservesInv_of_book _ _ _ _ _ _
    (fun _ E C h => reachableInv_with_security_bookkeeping h E C)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)
    (idealCorrectnessImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak)
    (oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak ecEk.ec.nchunk_pos)
    (oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak)

end oppUniKemCKA.Security
