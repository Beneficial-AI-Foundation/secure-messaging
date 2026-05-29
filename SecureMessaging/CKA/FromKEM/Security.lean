/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import SecureMessaging.CKA.FromKEM.Security.PrefixInjectSim

/-!
# CKA from KEM — Security Statements

This file states the security property for the generic CKA-from-KEM construction
of [ACD19, Section 4.1.2].

The paper's Theorem 2 says that the generic KEM-based construction has
`Delta_CKA = 0` and reduces CKA security to KEM security.
-/

open OracleSpec OracleComp ENNReal

namespace kemCKA

variable {K PK SK C : Type}

private lemma abs_half_gap_le_abs (x : ℝ) : |x / 2| ≤ |x| := by
  grind

private lemma cka_securityAdvantage_le_ind_cpa_of_fixed_gap
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (red : kem.IND_CPA_Adversary)
    (hGap :
      |(Pr[= true |
          CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
        (Pr[= true |
          CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
      |(Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red true]).toReal -
        (Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red false]).toReal|) :
    CKAScheme.securityAdvantage (SecurityCKA kem hDet leak) adv gp ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp red := by
  rw [kem_ind_cpa_advantage_eq_fixed_branch_dist]
  unfold CKAScheme.securityAdvantage
  rw [CKAScheme.securityExp_toReal_sub_half]
  exact le_trans (abs_half_gap_le_abs _) hGap

private lemma cka_fixed_gap_le_normalized_reduction_raw_gap_pure
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (guess : Bool) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak)
          (pure guess : OracleComp (SecuritySpec leak) Bool) true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak)
          (pure guess : OracleComp (SecuritySpec leak) Bool) false gp]).toReal| ≤
    |(Pr[= true |
        ckaReductionINDCPABranchRaw kem hDet leak
          (pure guess : OracleComp (SecuritySpec leak) Bool) gp true]).toReal -
      (Pr[= true |
        ckaReductionINDCPABranchRaw kem hDet leak
          (pure guess : OracleComp (SecuritySpec leak) Bool) gp false]).toReal| := by
  simp [CKAScheme.securityExpFixedBit, ckaReductionINDCPABranchRaw,
    SecurityCKA, schemeWithLeak, finishChallengeStepRaw]

private lemma cka_fixed_gap_le_normalized_reduction_raw_gap
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (_hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (_hgp : AdmissibleParams gp) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
    |(Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp false]).toReal| := by
  rw [securityExpFixedBit_eq_ckaSecurityFixedBranch]
  rw [securityExpFixedBit_eq_ckaSecurityFixedBranch]
  rw [ckaSecurityFixedBranch_challenge_key_gap_eq]
  rw [ckaReductionINDCPABranchRaw_keygen_swapped_gap_eq]
  /- Remaining semantic obligation: the paper's hidden-state simulation.

     The reduction may install `pkStar` while the corresponding secret key is
     unknown and represented by unrelated hidden state. Admissibility prevents
     corruption/rleak from exposing that state before the challenge, and
     `_hkem` justifies that the matching receive deletes the hidden decapsulation
     key and reaches the same public next state. The proof cannot be the stronger
     per-branch equality without this correctness argument. -/
  sorry

private lemma cka_fixed_gap_le_normalized_reduction_gap
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
    |(Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp false]).toReal| := by
  rw [ckaReductionINDCPABranch_gap_eq_raw_gap]
  exact cka_fixed_gap_le_normalized_reduction_raw_gap kem hDet hkem leak adv gp hgp

private lemma ckaToINDCPAReduction_fixed_gap_dominates
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (_hgp : AdmissibleParams gp) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
    |(Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp) true]).toReal -
      (Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp) false]).toReal| := by
  rw [ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch
    kem hDet leak adv gp true]
  rw [ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch
    kem hDet leak adv gp false]
  exact cka_fixed_gap_le_normalized_reduction_gap kem hDet hkem leak adv gp _hgp

/-- Existential security-reduction statement for CKA from a KEM.

For every perfectly correct input KEM, every CKA adversary, and every admissible
challenge parameter set, there exists an IND-CPA adversary against the input KEM
whose advantage upper-bounds the CKA security advantage of the constructed
protocol.

The statement is intentionally existential: this specification PR records the
proof obligation. A later proof PR should refine the existential witness to a
named concrete reduction.
-/
theorem security_reduces_to_ind_cpa_exists [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    ∃ red : INDCPAReduction kem leak adv gp,
      CKAScheme.securityAdvantage (schemeWithLeak kem hDet leak) adv gp ≤
        kem.IND_CPA_Advantage ProbCompRuntime.probComp red := by
  refine ⟨ckaToINDCPAReduction kem hDet leak adv gp, ?_⟩
  exact cka_securityAdvantage_le_ind_cpa_of_fixed_gap
    kem hDet leak adv gp (ckaToINDCPAReduction kem hDet leak adv gp)
    (ckaToINDCPAReduction_fixed_gap_dominates kem hDet hkem leak adv gp hgp)

end kemCKA
