/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixSim

/-!
# CKA from KEM — Challenge-Step Probability Bridges

This file exposes the prepared challenge-step simulations from `PrefixSim` as
plain output-probability equalities.  The relational lemmas carry the real
hidden-state work; these wrappers are the shape needed by the top-level branch
gap proof.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-- Probability form of `challA_sampled_reduction_cont_run'_relTriple`: the
prepared real-key A-challenge step and the reduction's challenge step output
`true` with equal probability. -/
lemma challA_sampled_reduction_cont_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true |
      (((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)] =
    Pr[= true |
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey
            (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preAToBReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey)
          (cont q.1)).run' q.2)] := by
  exact probOutput_true_eq_of_relTriple_eqRel
    (challA_sampled_reduction_cont_run'_relTriple
      kem hDet hkem leak gp hgp σ hInv hWill hks cont)

/-- Probability form of
`challA_sampled_reduction_random_cont_run'_relTriple`, the random-key
case. -/
lemma challA_sampled_reduction_random_cont_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true |
      (((securityImpl kem hDet leak gp true
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)] =
    Pr[= true |
      (do
        let (cStar, _realKey) ← kem.encaps pkStar
        let kRand ← ($ᵗ K : ProbComp K)
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand
            (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preAToBReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand)
          (cont q.1)).run' q.2)] := by
  exact probOutput_true_eq_of_relTriple_eqRel
    (challA_sampled_reduction_random_cont_run'_relTriple
      kem hDet hkem leak gp hgp σ hInv hWill hks cont)

/-- Probability form of `challB_sampled_reduction_cont_run'_relTriple`, the
B-side real-key case. -/
lemma challB_sampled_reduction_cont_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true |
      (((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)] =
    Pr[= true |
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey
            (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preBToAReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey)
          (cont q.1)).run' q.2)] := by
  exact probOutput_true_eq_of_relTriple_eqRel
    (challB_sampled_reduction_cont_run'_relTriple
      kem hDet hkem leak gp hgp σ hInv hWill hks cont)

/-- Probability form of
`challB_sampled_reduction_random_cont_run'_relTriple`, the B-side random-key
case. -/
lemma challB_sampled_reduction_random_cont_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true |
      (((securityImpl kem hDet leak gp true
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)] =
    Pr[= true |
      (do
        let (cStar, _realKey) ← kem.encaps pkStar
        let kRand ← ($ᵗ K : ProbComp K)
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand
            (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preBToAReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand)
          (cont q.1)).run' q.2)] := by
  exact probOutput_true_eq_of_relTriple_eqRel
    (challB_sampled_reduction_random_cont_run'_relTriple
      kem hDet hkem leak gp hgp σ hInv hWill hks cont)

end kemCKA
