/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OracleLeakage
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OracleReceive
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Corruption
import SecureMessaging.SCKA.Security.Bookkeeping
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Per-query comparison of the reduction and the honest intermediate game

**Statement.** Fix selected material `m`, epoch `e`, and challenge key
`kStar`. For every transcript-consistent state `s` with `e ∉ s.exposed`
and every security query, the reduction from `markState e s` has the same
joint response/state distribution as the stopped honest intermediate game
from `s`, followed by marking the successor.

**Proof.** Ordinary sends and receives use their complete game-state
relations. Challenges preserve honest key tables. Exposure guards agree;
successful revelation fails exactly on the paths stopped by the honest
game. Uniform queries return the same sample and retain the state.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- For every transcript-consistent state and correctness-interface query,
the symbolic query's joint distribution is the honest pinned query's joint
distribution followed by successor marking. -/
theorem correctnessOracle_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) :
    𝒟[(SCKAScheme.sckaCorrectnessImpl
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) t).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s] := by
  rcases t with ((((n | u) | u) | n) | n)
  · simp [SCKAScheme.sckaCorrectnessImpl, SCKAScheme.oracleUnif,
      Prod.map, markState, markA, markB]
  · cases u
    exact oracleSendA_mark base onoff ecEk ecCt0 ecCt1 leak m e s
  · cases u
    exact oracleSendB_mark base onoff ecEk ecCt0 ecCt1 leak m e s hs
  · exact congrArg evalDist (oracleRecvA_mark base onoff ecEk ecCt0 ecCt1 leak m e n s)
  · exact congrArg evalDist (oracleRecvB_mark base onoff ecEk ecCt0 ecCt1 leak m e n s)

/-- For every selected material value, epoch, supplied challenge key,
transcript-consistent unexposed state, and security query, the reduction's
joint optional-response/state distribution equals the stopped honest
intermediate query followed by marking the successor. -/
theorem oracle_mark [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (he : e ∉ s.exposed) :
    𝒟[((oracle base onoff ecEk ecCt0 ecCt1 leak e m.keygen.1.1 m.ciphertext kStar t).run).run
      (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      ((honestStopped base onoff ecEk ecCt0 ecCt1 leak m e kStar t).run).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · apply evalDist_lift_eq_stopOnState_map
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s))
      (SCKAScheme.sckaCorrectnessImpl (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s))
      (markState e) (fun u => decide (e ∈ u.exposed)) t s
      (correctnessOracle_mark base onoff ecEk ecCt0 ecCt1 leak m e t s hs)
    intro z hz
    have h := (SCKAScheme.correctnessImpl_securitySets_eq _ t s z hz).1
    simp [h, he]
  · cases u
    exact oracleSendArleak_mark base onoff ecEk ecCt0 ecCt1 leak m e s he
  · cases u
    exact oracleSendBrleak_mark base onoff ecEk ecCt0 ecCt1 leak m e s he hs
  · apply evalDist_lift_eq_stopOnState_map
      (pinnedChallenge onoff e kStar) (challenge onoff e kStar)
      (markState e) (fun u => decide (e ∈ u.exposed)) t s
      (congrArg evalDist (challenge_mark onoff e kStar t s))
    intro z hz
    simp [pinnedChallenge_exposed_eq onoff e kStar t s z hz, he]
  · cases u
    exact congrArg evalDist (corruptA_mark base onoff e s he)
  · cases u
    exact congrArg evalDist (corruptB_mark base onoff e s he)

end oppUniKemCKA.Security.Embedding
