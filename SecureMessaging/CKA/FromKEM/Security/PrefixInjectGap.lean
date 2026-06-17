/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectSplit
import ToVCVio.OracleComp.EvalDist

/-!
# CKA from KEM — Prefix Injection Gap

This file performs the final branch-level assembly that ties the injected
challenge-key fixed branch to the raw IND-CPA reduction branch.  The prepared
challenge and post-challenge simulations already live in `ChallengeBridge` and
`HiddenStateSim`; the hidden-state move that brings the reduction's sampled key
pair to the honest generation point lives in `PrefixInjectSim`/`PrefixInjectSplit`.

What remains here is to split the injected honest branch at the paused challenge,
couple it against the raw reduction prefix, and read off the per-bit output
equality (with the bit reversed across the two games) up to the prepared
challenge bridges.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## Projection helpers for the post-challenge continuation

Once the paused challenge has been reached, the injected honest continuation has
to be rewritten into the honest `securityImpl … false` continuation that the
prepared challenge bridges consume.  Two collapses are involved: dropping the
installed challenge key pair (valid once `injectionPassed` holds at the
continuation state) and erasing the fixed bit (valid once `challengePassed`
holds).  Both are stated on `.run'`, the projection the bridges use. -/

/-- The honest implementation keeps `challengePassed` true on every reachable
post-state, because no oracle step lowers the epoch counters. -/
private lemma securityImpl_preservesInv_challengePassed [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    QueryImpl.PreservesInv (securityImpl kem hDet leak gp isRandom)
      (challengePassed (K := K) (PK := PK) (SK := SK) (C := C) gp) := by
  intro t σ0 h z hz
  have hmono := securityImpl_run_counters_mono kem hDet leak gp isRandom t σ0 z hz
  cases hcp : gp.challengedParty <;>
    simp only [challengePassed, hcp] at h ⊢ <;> omega

/-- Past the injection epoch, `securityImplWithChallengeKeyPair` and the honest
`securityImpl` give the same simulated output distribution after `.run'`. -/
lemma probOutput_simulateQ_wck_run'_eq_of_injectionPassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    (adv : OracleComp (securitySpec leak) Bool)
    (s : SecurityState K PK SK C)
    (hs : injectionPassed gp s) :
    Pr[= true |
        (simulateQ
          (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar)
          adv).run' s] =
      Pr[= true |
        (simulateQ (securityImpl kem hDet leak gp isRandom) adv).run' s] :=
  probOutput_run'_true_eq_of_run_probOutput_eq s fun z =>
    probOutput_simulateQ_securityImplWithChallengeKeyPair_run_eq_of_injectionPassed
      kem hDet leak gp isRandom pkStar skStar adv s hs z

/-- Past the challenge epoch, the fixed-bit honest implementations give the same
simulated output distribution after `.run'`. -/
lemma probOutput_simulateQ_true_false_run'_eq_of_challengePassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (adv : OracleComp (securitySpec leak) Bool)
    (s : SecurityState K PK SK C)
    (hs : challengePassed gp s) :
    Pr[= true |
        (simulateQ (securityImpl kem hDet leak gp true) adv).run' s] =
      Pr[= true |
        (simulateQ (securityImpl kem hDet leak gp false) adv).run' s] :=
  probOutput_run'_true_eq_of_run_probOutput_eq s fun z =>
    probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
      (securityImpl kem hDet leak gp true)
      (securityImpl kem hDet leak gp false)
      (challengePassed gp) adv
      (securityImpl_true_false_run_eq_of_challengePassed kem hDet leak gp)
      (securityImpl_preservesInv_challengePassed kem hDet leak gp false)
      s hs z

end kemCKA
