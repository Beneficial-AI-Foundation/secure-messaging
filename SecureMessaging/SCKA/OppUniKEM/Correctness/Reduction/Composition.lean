/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Core

/-!
# Opp-UniKEM-CKA send-query bound

This module defines `SendQueryBound adv q`: the adversary `adv` makes at most `q` `SendA` and
`SendB` queries in total. It is the query bound of `correctness_failure_le_reduction`
(`Correctness.Reduction`), which takes the bound on executions of the tracked game from
`SCKAScheme.tracked_bad_le_of_score_step`.
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
