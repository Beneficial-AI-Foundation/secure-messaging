/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints

/-!
# Send and epoch accounting in the ideal game

Let `idealSecurityImpl … mode` be the oracles of the ideal game, in which A uses B's recorded key
in place of decapsulation and `mode : ℕ → Bool` selects the epochs with uniform challenge keys.
For every `mode`, every query preserves `sendEpochInv` and, with correct erasure codes,
`reachableInv`. Every possible successor `s'` of a query from `s` satisfies
`s'.nA ≤ s.nA + 1` for the four send queries and `s'.nA ≤ s.nA` for all other queries.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

omit [SampleableType K] in
/-- Every correctness query of the ideal game preserves `sendEpochInv`. -/
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

/-- For every challenge mode, every query of the ideal game preserves `sendEpochInv`. -/
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

/-- For every challenge mode, query `t`, and possible successor `z.2` of `t` from `s`,
`z.2.nA ≤ s.nA + 1` if `t` is one of the four send queries and `z.2.nA ≤ s.nA` otherwise. -/
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

/-- With correct erasure codes, for every challenge mode, every query of the ideal game
preserves `reachableInv`. -/
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
