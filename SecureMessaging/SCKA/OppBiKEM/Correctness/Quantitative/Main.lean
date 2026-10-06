/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.SendStep
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.SendTotal

/-!
# Opp-BiKEM — correctness with an imperfect KEM

The quantitative correctness theorem. The tracked game runs the correctness game alongside
the flag `kemFailure`, which is raised exactly when a party holds a decapsulation key, the peer
holds a ciphertext for it, and the two disagree on the key. While the flag is down the main
invariant holds, so the game is correct (`gameInv_step_of_noFailure`); the probability that
the flag is ever raised is bounded by `q · ε` through the potential `trackedScore`
(`tracked_step_score_le`). The two facts combine through the generic tracked layer in
`SCKA.Correctness.Tracked`.

Endpoints:

* `correctness_failure_le`: the game fails with probability at most `q · ε`;
* `correctness_true_ge`: the game succeeds with probability at least `1 - q · ε`;
* `correctness_of_perfectKEM'`: for a perfectly correct KEM the game succeeds with probability
  one, obtained from the bound with `ε = 0` (the direct proof is
  `MainInvariant.Game.correctness_of_perfectKEM`);
* `sends_never_rejected_of_noFailure`: while the failure flag is down, neither party's send is
  rejected (the perfect-KEM version is `sends_never_rejected_of_perfectKEM`).
-/

open OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)

/-- The initial game state of the Opp-BiKEM correctness game. -/
abbrev initState : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) :=
  SCKAScheme.initGameState (initialState .A) (initialState .B)

omit [DecidableEq Sym] in
/-- No party holds a decapsulation key initially, so the flag is down. -/
theorem kemFailure_init : kemFailure hDet (initState (PK := PK) (SK := SK) (C := C) (Sym := Sym)
    (K := K)) = false := by
  rw [kemFailure, Bool.or_eq_false_iff]
  constructor <;> exact kemFailureAt_eq_false_of hDet (Or.inl rfl)

omit [DecidableEq Sym] in
/-- No party holds a decapsulation key initially, so the potential is `0`. -/
theorem trackedScore_init :
    trackedScore hDet (initState (PK := PK) (SK := SK) (C := C) (Sym := Sym) (K := K), false)
      = 0 := by
  rw [trackedScore_false, failurePotential, pendingPotential_nil hDet rfl,
    pendingPotential_nil hDet rfl, add_zero]

include hEk hCt in
/-- The tracked game preserves the tracked invariant: the flag is up, or the main invariant
holds and the flag is down. -/
theorem trackedBiKem_preservesInv :
    QueryImpl.PreservesInv (trackedBiKem kem hDet ecEk ecCt leak)
      (trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)) :=
  trackedImpl_preserves _ _ _ (gameInv_step_of_noFailure kem hDet ecEk ecCt hEk hCt leak)

omit [DecidableEq Sym] in
/-- The initial game state satisfies the main invariant with the flag down. -/
theorem trackedInv_init :
    trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)
      (initState (PK := PK) (SK := SK) (C := C) (Sym := Sym) (K := K), false) :=
  Or.inr ⟨gameInv_init kem ecEk ecCt _ _ (by simp [initA, init, initialState])
    (by simp [initB, init, initialState]), kemFailure_init kem hDet⟩

include hEk hCt in
/-- The flag is raised with probability at most `q · ε` for an adversary making at most `q`
send queries. -/
theorem tracked_bad_le (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[ fun z => z.2.2 = true |
        (simulateQ (trackedBiKem kem hDet ecEk ecCt leak) adv).run (initState, false)] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp :=
  SCKAScheme.tracked_bad_le_of_score_step (scheme kem hDet ecEk ecCt leak) (kemFailure hDet)
    (GameInv kem ecEk ecCt) (fun z => trackedScore hDet z)
    (kem.correctnessError ProbCompRuntime.probComp)
    (fun p hp => one_le_trackedScore_of_flag hDet p hp)
    (trackedBiKem_preservesInv kem hDet ecEk ecCt hEk hCt leak)
    (tracked_step_score_le kem hDet ecEk ecCt leak hEk hCt)
    adv q hq _ (trackedInv_init kem hDet ecEk ecCt) (trackedScore_init kem hDet)

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game fails with probability at most
`q · kem.correctnessError`. -/
theorem correctness_failure_le (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= false | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp :=
  SCKAScheme.correctness_failure_le_of_tracked_bad (scheme kem hDet ecEk ecCt leak)
    (kemFailure hDet) (GameInv kem ecEk ecCt) (fun _ hs => hs.1)
    (trackedBiKem_preservesInv kem hDet ecEk ecCt hEk hCt leak) adv _
    (trackedInv_init kem hDet ecEk ecCt) (correctnessExp_eq_map kem hDet ecEk ecCt leak adv) _
    (tracked_bad_le kem hDet ecEk ecCt hEk hCt leak adv q hq)

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game succeeds with probability at least
`1 - q · kem.correctnessError`. -/
theorem correctness_true_ge (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  have h := correctness_failure_le kem hDet ecEk ecCt hEk hCt leak adv q hq
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero, tsub_le_iff_right] at h
  rw [ge_iff_le, tsub_le_iff_right]
  rwa [add_comm]

include hEk hCt in
/-- For a perfectly correct KEM the correctness game succeeds with probability one, for every
adversary with a send-query bound: the `ε = 0` instance of `correctness_true_ge`. The direct
proof without a query bound is `correctness_of_perfectKEM`. -/
theorem correctness_of_perfectKEM' (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] = 1 := by
  have h := correctness_true_ge kem hDet ecEk ecCt hEk hCt leak adv q hq
  rw [(KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr
    hkem, mul_zero, tsub_zero] at h
  exact le_antisymm probOutput_le_one h

include hEk hCt in
/-- At every reachable state of the tracked game at which the failure flag is down, neither
party's send is rejected. Together with `tracked_bad_le`, send rejection therefore happens with
probability at most `q · ε`. -/
theorem sends_never_rejected_of_noFailure
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (z : Bool × (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool))
    (hz : z ∈ support ((simulateQ (trackedBiKem kem hDet ecEk ecCt leak) adv).run
      (initState, false)))
    (hflag : z.2.2 = false) :
    none ∉ support (sendA kem ecEk ecCt z.2.1.stA) ∧
      none ∉ support (sendB kem ecEk ecCt z.2.1.stB) := by
  have hinv := simulateQ_run_preservesInv _ _
    (trackedBiKem_preservesInv kem hDet ecEk ecCt hEk hCt leak) adv _
    (trackedInv_init kem hDet ecEk ecCt) z hz
  rcases hinv with h | ⟨hs, -⟩
  · rw [hflag] at h; cases h
  · exact ⟨sendA_ne_none kem ecEk ecCt _ hs, sendB_ne_none kem ecEk ecCt _ hs⟩

end oppBiKemCKA
