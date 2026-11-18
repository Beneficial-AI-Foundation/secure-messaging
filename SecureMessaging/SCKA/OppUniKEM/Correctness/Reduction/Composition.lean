/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Core

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
* `E[S(s_f, b_f)]` denote `wp` of the final score.

For every tracked execution,

```text
Pr[b_f = true] ≤ E[S(s_f, b_f)].
```

that is, the probability that the failure flag is set is at most the expected
tracked failure score. This is `OracleComp.tracked_bad_probability_le_score`
(`ToVCVio.OracleComp.SimSemantics.StateT.BadFlag`) with `S`, since `S(s, true) = 1`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

open SCKAScheme.sckaCorrectnessSpec
open Reduction.Internal

/-- A bound on total send queries to both parties (`SCKAScheme.SendQueryBound`). -/
abbrev SendQueryBound (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) : Prop :=
  SCKAScheme.SendQueryBound adv q

end oppUniKemCKA
