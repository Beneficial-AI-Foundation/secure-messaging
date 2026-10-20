/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineDeferral
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OfflineDeferral
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.KeygenDeferral
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SamplingStages
import SecureMessaging.SCKA.OppUniKEM.Security.IdealStopping

/-!
# Adjacent ideal hybrids from the KEM branches

**Setting.** Let `base` be a KEM with deterministic decapsulation, and assume correct erasure
codes. Let `adv` be a security adversary and `H_i := idealEpochHybridExp adv i` the ideal
hybrids. For a selected epoch `e` and a challenge mode `μ`, let `I_e[μ]` be the ideal game with
mode `μ`, run from the initial state and stopped at the first query whose successor state exposes
`e`. As in `Material`, the *real-minus-random acceptance gap* of Boolean computations `G_b` is
`Pr[G_true = true] - Pr[G_false = true]`.

**Results.**

- `fixedBranch_eq_ideal`: for `e > 0` and every IND-CPA branch `b`,
  `Pr[fixedBranch adv e b = true] = Pr[I_e[adjacentMode e (!b)] = true]`.
- `fixedBranch_signed_gap_eq`: `Pr[fixedBranch adv (i+1) true = true] -
  Pr[fixedBranch adv (i+1) false = true] = Pr[H_i = true] - Pr[H_{i+1} = true]`.
- `hybrid_gap_eq_query_factor`: for every `q`,
  `|Pr[H_0 = true] - Pr[H_q = true]| = q · Adv_IND-CPA(base, securityReduction adv q)`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For all reference material `m₀`, drawing `m ← sampleMaterial leak` and running the stopped
pinned hybrid `hybridStopped m e b` from the initial state returns `true` with the probability
of `stopped .fresh m₀ e b` from the initial state. The stage `fresh` reads no stored output. -/
theorem pinnedHybrid_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m₀ : Material leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | do
      let m ← sampleMaterial leak
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] =
    Pr[= true | optionRun
      (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak .fresh m₀ e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  trans Pr[= true | do
    let kg ← leak.keygenRleak
    let off ← leak.encapsOffRleak
    optionRun (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m₀ with keygen := kg, off := off } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]
  · simp only [sampleMaterial, bind_assoc, pure_bind]
    apply probOutput_bind_congr
    intro kg hkg
    apply probOutput_bind_congr
    intro off hoff
    obtain ⟨online, hon⟩ : (support (leak.encapsOnRleak off.1.1 kg.1.1)).Nonempty := by
      simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
    let m : Material leak := ⟨kg, off, online⟩
    have hm : m ∈ support (sampleMaterial leak) := by
      simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨kg, hkg, off, hoff, online, hon, rfl⟩
    exact hybridStopped_online_deferred base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak m hm e b adv _
      (reachableInv_init base onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
      (pinnedSources_initial base onoff leak m e)
  trans Pr[= true | do
    let kg ← leak.keygenRleak
    optionRun (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { m₀ with keygen := kg } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]
  · apply probOutput_bind_congr
    intro kg _
    exact Sampling.stopped_offline_deferred base onoff ecEk ecCt0 ecCt1 leak
      { m₀ with keygen := kg } e b adv _
  · exact Sampling.stopped_keygen_deferred base onoff ecEk ecCt0 ecCt1 leak m₀ e b adv _

/-- Drawing `m ← sampleMaterial leak` and running the stopped pinned hybrid
`hybridStopped m e b` from the initial state returns `true` with the probability of
`I_e[adjacentMode e b]`. -/
theorem pinnedHybrid_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | do
      let m ← sampleMaterial leak
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] =
    Pr[= true | optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b))
        (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  obtain ⟨m₀, _⟩ : (support (sampleMaterial leak)).Nonempty := by
    simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
  rw [pinnedHybrid_eq_fresh base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak m₀ e b adv]
  unfold Sampling.stopped
  rw [Sampling.oracle_fresh_eq_ideal base onoff hDet ecEk ecCt0 ecCt1 leak m₀ e b]

/-- For every `e > 0` and IND-CPA branch `b`,
`Pr[fixedBranch adv e b = true] = Pr[I_e[adjacentMode e (!b)] = true]`. The negation converts
the KEM convention (`true` for the real key) to the mode convention (`true` for a uniform
key). -/
theorem fixedBranch_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (e : ℕ) (he : 0 < e)
    (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] =
    Pr[= true | optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak
        (adjacentMode e (!b))) (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  rw [fixedBranch_eq_pinnedHybrid base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak adv e he b]
  exact pinnedHybrid_eq_ideal base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak e (!b) adv

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- `adjacentMode (i + 1) false` randomizes exactly the epochs `1, …, i`. -/
theorem adjacentMode_succ_false (i : ℕ) :
    adjacentMode (i + 1) false = fun t => decide (0 < t ∧ t ≤ i) := by
  funext t
  simp only [adjacentMode, Bool.false_eq_true, false_and, or_false]
  congr 1
  apply propext
  omega

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- `adjacentMode (i + 1) true` randomizes exactly the epochs `1, …, i + 1`. -/
theorem adjacentMode_succ_true (i : ℕ) :
    adjacentMode (i + 1) true = fun t => decide (0 < t ∧ t ≤ i + 1) := by
  funext t
  simp only [adjacentMode, true_and]
  congr 1
  apply propext
  omega

/-- For every adversary and index `i`, the real-minus-random acceptance gap of
`fixedBranch adv (i + 1)` is `Pr[H_i = true] - Pr[H_{i+1} = true]`. -/
-- ANCHOR: fixedBranch_signed_gap_eq
theorem fixedBranch_signed_gap_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (adv : SecurityAdversary leak Sym) (i : ℕ) :
    (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv (i + 1) true]).toReal -
      (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv (i + 1) false]).toReal =
    (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv i]).toReal -
      (Pr[= true | idealEpochHybridExp
        base onoff hDet ecEk ecCt0 ecCt1 leak adv (i + 1)]).toReal
-- ANCHOR_END: fixedBranch_signed_gap_eq
    := by
  rw [fixedBranch_eq_ideal base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak (i + 1) (Nat.succ_pos i) true adv,
    fixedBranch_eq_ideal base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak (i + 1) (Nat.succ_pos i) false adv]
  simp only [Bool.not_true, Bool.not_false, adjacentMode_succ_false, adjacentMode_succ_true]
  have hstop := idealEpochHybrid_signed_gap_stop_eq base onoff hDet ecEk ecCt0 ecCt1
    leak i adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)
    (by simp [oppUniKemCKA.Reduction.Internal.initialGame, SCKAScheme.initGameState])
  change
    (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv (i + 1)]).toReal -
      (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv i]).toReal = _
    at hstop
  change
    (Pr[= true | stoppedRun (idealEpochHybridImpl base onoff hDet ecEk ecCt0 ecCt1 leak i)
      (fun s => decide (i + 1 ∈ s.exposed)) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]).toReal -
    (Pr[= true | stoppedRun (idealEpochHybridImpl base onoff hDet ecEk ecCt0 ecCt1 leak (i + 1))
      (fun s => decide (i + 1 ∈ s.exposed)) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]).toReal = _
  linarith only [hstop]

/-- For every adversary and `q > 0`, the real-minus-random acceptance gap of
`securityReduction adv q` in the IND-CPA experiment is
`(Pr[H_0 = true] - Pr[H_q = true]) / q`. -/
theorem securityReduction_signed_gap_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (adv : SecurityAdversary leak Sym)
    (q : ℕ) (hq : q ≠ 0) :
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) true]).toReal -
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) false]).toReal =
    (q : ℝ)⁻¹ *
      ((Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv 0]).toReal -
       (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv q]).toReal) := by
  rw [securityReduction_signed_gap_average base onoff ecEk ecCt0 ecCt1 leak adv q hq]
  simp_rw [fixedBranch_signed_gap_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv i]).toReal -
    (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv (i + 1)]).toReal) q,
    Finset.sum_range_sub']

/-- For every adversary and every `q`,
`|Pr[H_0 = true] - Pr[H_q = true]| = q · Adv_IND-CPA(base, securityReduction adv q)`, where the
IND-CPA advantage is the full gap between the real and random branches. For `q = 0` both sides
vanish. -/
-- ANCHOR: hybrid_gap_eq_query_factor
theorem hybrid_gap_eq_query_factor
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (adv : SecurityAdversary leak Sym) (q : ℕ) :
    |(Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv 0]).toReal -
      (Pr[= true | idealEpochHybridExp base onoff hDet ecEk ecCt0 ecCt1 leak adv q]).toReal| =
    (q : ℝ) * base.IND_CPA_Advantage ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q)
-- ANCHOR_END: hybrid_gap_eq_query_factor
    := by
  rcases Nat.eq_zero_or_pos q with rfl | hpos
  · simp
  have hq : q ≠ 0 := hpos.ne'
  rw [KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist,
    securityReduction_signed_gap_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak adv q hq, abs_mul, abs_inv,
    abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q),
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hq), one_mul]

end oppUniKemCKA.Security.Embedding
