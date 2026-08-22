/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Projection
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# Opp-UniKEM-CKA Adversary Composition

This module extends the one-query bounds of `Reduction.OneStep` to complete
adaptive executions of the tracked game.

For an execution of the tracked game against an adversary `adv`, let:

* `(s_f, b_f)` denote the final tracked state: ordinary game state `s_f` and
  failure flag `b_f`;
* `V(s) := currentFailurePotential s` (`Reduction.Core`), the conditional
  failure probability of the KEM epoch in progress;
* `S(s, b) := trackedFailureScore (s, b)` (`Reduction.Core`), equal to `1`
  when `b = true` and to `V(s)` otherwise;
* `E[S(s_f, b_f)]` denote `expectedPayoff` of the final score, which assigns
  score `1` to computation failure.

For every tracked execution,

```text
Pr[b_f = true] ≤ E[S(s_f, b_f)].
```

that is, the probability that the failure flag is set is at most the expected
tracked failure score.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

open SCKAScheme.sckaCorrectnessSpec
open Reduction.Internal

/-- Syntactic bound on the total number of send queries.  Both send oracles
count: either party may draw the first sample of a fresh epoch. -/
def SendQueryBound (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) : Prop :=
  adv.IsQueryBoundP (IsSendQuery (Sym := Sym)) q

namespace Reduction.Internal

omit [DecidableEq Sym] in
/-- The probability that the failure flag is set is at most the expected
tracked failure score. -/
lemma tracked_bad_probability_le_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (oa : ProbComp
      (Bool ×
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) ×
          Bool))) :
    Pr[fun z => z.2.2 = true | oa] ≤
      expectedPayoff oa (fun z => trackedFailureScore kem onoff z.2) := by
  classical
  unfold expectedPayoff
  calc
    Pr[fun z => z.2.2 = true | oa] ≤
        ∑' z, Pr[= z | oa] * trackedFailureScore kem onoff z.2 := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro z hz
      simp [trackedFailureScore, hz]
    _ ≤ Pr[⊥ | oa] +
        ∑' z, Pr[= z | oa] * trackedFailureScore kem onoff z.2 :=
      le_add_left le_rfl

end Reduction.Internal

end oppUniKemCKA
