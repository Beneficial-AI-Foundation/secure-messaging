/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectCoupling

/-!
# CKA from KEM — Security Statements

This file states and proves the security property for the generic CKA-from-KEM
construction of [ACD19, Section 4.1.2].

The paper's Theorem 2 says that the generic KEM-based construction has
`Delta_CKA = 0` and reduces CKA security to KEM security. The paper's proof is
constructive: it builds an explicit IND-CPA adversary from the CKA adversary.
The primary theorem `security` follows that proof: it bounds the CKA
distinguishing advantage by the IND-CPA advantage of the concrete reduction
`ckaToINDCPAReduction kem hDet leak adv gp`, in fact with equality, chaining the
gap equalities proved in the `Security/` modules. `security_exists` repackages
it in the paper-style existential form.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

variable {K PK SK C : Type}

/-- Security reduction for CKA from a KEM.

For every perfectly correct KEM, CKA adversary, and admissible challenge
parameters, the IND-CPA advantage of the concrete reduction
`ckaToINDCPAReduction kem hDet leak adv gp` upper-bounds the CKA distinguishing
advantage of the constructed protocol — in fact the two advantages are equal,
so the stated bound holds with equality.

The bound compares like with like: `CKAScheme.ckaDistAdvantage` is the gap
between the real-key and random-key branches of the CKA game (twice
`CKAScheme.ckaGuessAdvantage`), and `KEMScheme.IND_CPA_Advantage` is the
Boolean bias `|Pr[true] - Pr[false]|` of the single IND-CPA game.

N.B. ACD19's sampled-bit guessing advantage is half of `ckaDistAdvantage`
(`CKAScheme.ckaGuessAdvantage_eq_ckaDistAdvantage_div_two`); the paper's no-leak
construction is the instance `RandLeak.noLeak kem`.
-/
-- ANCHOR: security
theorem security [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    CKAScheme.ckaDistAdvantage (scheme kem hDet leak) adv gp ≤
      KEMScheme.IND_CPA_Advantage (kem := kem) ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp)
-- ANCHOR_END: security
    := by
  refine le_of_eq ?_
  rw [kem_ind_cpa_advantage_eq_fixed_branch_dist,
    ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch kem hDet leak adv gp true,
    ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch kem hDet leak adv gp false,
    ckaReductionINDCPABranch_gap_eq_raw_gap,
    ckaReductionINDCPABranchRaw_keygen_swapped_gap_eq]
  unfold CKAScheme.ckaDistAdvantage
  rw [securityExpFixedBit_eq_ckaSecurityFixedBranch kem hDet leak adv gp true,
    securityExpFixedBit_eq_ckaSecurityFixedBranch kem hDet leak adv gp false,
    ckaSecurityFixedBranch_challenge_key_gap_eq,
    ckaSecurityFixedBranchWithChallengeKey_injected_gap_eq]
  exact cka_injected_honest_gap_eq_keygen_swapped_raw_gap kem hDet hkem leak adv gp hgp

/-- Existential repackaging of `security`: there exists an IND-CPA adversary
against the KEM whose advantage upper-bounds the CKA distinguishing advantage.
The witness is the concrete reduction `ckaToINDCPAReduction kem hDet leak adv gp`. -/
theorem security_exists [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    ∃ red : KEMScheme.IND_CPA_Adversary kem,
      CKAScheme.ckaDistAdvantage (scheme kem hDet leak) adv gp ≤
        KEMScheme.IND_CPA_Advantage (kem := kem) ProbCompRuntime.probComp red :=
  ⟨ckaToINDCPAReduction kem hDet leak adv gp,
    security kem hDet hkem leak adv gp hgp⟩

end kemCKA
