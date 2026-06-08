/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PostChallenge

/-!
# CKA from KEM — Security Statements

This file states the security property for the generic CKA-from-KEM construction
of [ACD19, Section 4.1.2].

The paper's Theorem 2 says that the generic KEM-based construction has
`Delta_CKA = 0` and reduces CKA security to KEM security. The paper's proof is
constructive: it builds an explicit IND-CPA adversary from the CKA adversary.
The statement below is an existential placeholder for that theorem; the proof
PR for issue #5 will replace it with a statement about a concrete reduction,
an explicitly constructed IND-CPA adversary proved to satisfy the bound.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

variable {K PK SK C : Type}

/-- Existential security-reduction statement for CKA from a KEM.

For every perfectly correct KEM, CKA adversary, and admissible challenge
parameters, there exists an IND-CPA adversary against the KEM whose advantage
upper-bounds the CKA distinguishing advantage of the constructed protocol.
The bound compares like with like: `CKAScheme.ckaDistAdvantage` is the gap
between the real-key and random-key branches of the CKA game (twice
`CKAScheme.ckaGuessAdvantage`), and `KEMScheme.IND_CPA_Advantage` is the
Boolean bias `|Pr[true] - Pr[false]|` of the single IND-CPA game.

N.B. ACD19's sampled-bit guessing advantage is half of `ckaDistAdvantage`
(`CKAScheme.ckaGuessAdvantage_eq_ckaDistAdvantage_div_two`); the paper's no-leak
construction is the instance `RandLeak.noLeak kem`.

The statement is an existential placeholder, not the final form of [ACD19,
Theorem 2], whose proof is constructive. The proof PR for issue #5 will
replace the existential with a concrete reduction — an explicitly constructed
IND-CPA adversary — and prove this bound for it.
-/
theorem security_reduces_to_ind_cpa_exists [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    ∃ red : KEMScheme.IND_CPA_Adversary kem,
      CKAScheme.ckaDistAdvantage (scheme kem hDet leak) adv gp ≤
        KEMScheme.IND_CPA_Advantage (kem := kem) ProbCompRuntime.probComp red := by
  sorry

end kemCKA
