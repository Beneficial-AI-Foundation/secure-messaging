/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineDeferral
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceDeferral
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.Security

/-!
# Opp-UniKEM SCKA security

**Setting.**

- `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak`: Opp-UniKEM over a KEM `kem` with
  deterministic decapsulation `hDet`, on/off factorization `onoff`, leakage witness `leak`, and
  correct erasure codes `ecEk`, `ecCt0`, `ecCt1`.
- `adv : SecurityAdversary leak Sym` with `SecuritySendQueryBound adv q`: at most `q` ordinary
  and leaking sends on every oracle-response path.
- The SCKA security game uses the exposure policies `exposureA`, `exposureB`. A challenge at `t`
  is *eligible* if `t` is unexposed, unchallenged, and has a recorded key.

**Advantages.**

- `G_b`: eligible challenges get recorded keys if `b = false` and independent uniform keys if
  `b = true`.
- `AdvGuess_SCKA(Π, adv) := |Pr[b' = b] - 1/2| = |Pr[G_true = true] - Pr[G_false = true]| / 2`.
- `AdvINDCPA_KEM(kem, B) = |Pr[B_real = true] - Pr[B_random = true]|`, where `B` receives the
  encapsulated key or an independent uniform key (`IND_CPA_Advantage_eq_fixed_branch_dist`).
- `ε`: the probability that decapsulating an honest encapsulation does not return its key.

**Theorem** (`security`). For every `q : ℕ` and `B := Security.Embedding.securityReduction … adv q`,

`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, B) + q · ε`.

`security_perfectKEM` drops `q · ε` for a perfectly correct KEM.

## Proof map

Paths are relative to `OppUniKEM/Security/`. Let `p_i := Pr[H_i = true]` for the ideal hybrids
`H_i` (`IdealHybrids`): the ideal game, in which A outputs B's recorded key instead of
decapsulating (`Endpoints`), with uniform challenge keys exactly at epochs `1, …, i`.

1. `Endpoints`, `IdealHybrids`: `security_guess_le_hybrid_gap`,
   `AdvGuess_SCKA(Π, adv) ≤ |p_0 - p_q| / 2 + q · ε`.
2. `Reduction/Simulator`: `securityReduction`, its fixed branches `fixedBranch adv e b`, complete
   material, and pinned sampling phases.
3. `Reduction/{Relation,Game,Oracle,Simulation}`: `fixedBranch_eq_honestStopped`, each branch as
   the honest intermediate game stopped at the exposure of `e`.
4. `Reduction/{HybridGame,SourceUse,OnlineDeferral,SourceDeferral}`: `fixedBranch_eq_pinnedHybrid`
   and the deferral of the three stored samples to their protocol calls.
5. This module: `fixedBranch_signed_gap_eq`, the real-minus-random gap of
   `fixedBranch adv (i + 1)` is `p_i - p_{i+1}`; `hybrid_gap_eq_query_factor`,
   `|p_0 - p_q| = q · AdvINDCPA_KEM(kem, B)`; and `security`.

Supporting modules: `Basic` (interface, send budget), `Invariant` (transcript and epoch
invariants), `SCKA.Security` (generic guards), ToVCVio (sampling and stopping).
-/

/-! ## Adjacent hybrids from the fixed branches

`I_e[μ]` is the ideal game `idealSecurityImpl μ` (`Endpoints`) stopped at the first query whose
successor state exposes `e`; `adjacentMode e b` (`HybridGame`) randomizes the epochs
`1, …, e - 1`, and `e` if `b`. The real-minus-random gap of `G_b` is
`Pr[G_true = true] - Pr[G_false = true]`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For all material `m₀`, `Pr[m ← sampleMaterial leak; hybridStopped m e b = true]` equals
`Pr[stopped .fresh m₀ e b = true]`, both from the initial state; `fresh` reads no stored output. -/
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

/-- `Pr[m ← sampleMaterial leak; hybridStopped m e b = true] = Pr[I_e[adjacentMode e b] = true]`,
from the initial state. -/
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

/-- For `e > 0`, `Pr[fixedBranch adv e b = true] = Pr[I_e[adjacentMode e (!b)] = true]`; the
negation maps the KEM bit (`true`: real key) to the mode bit (`true`: uniform key). -/
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

/-- The real-minus-random gap of `fixedBranch adv (i + 1)` is
`Pr[H_i = true] - Pr[H_{i+1} = true]`. -/
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

/-- For `q > 0`, the real-minus-random gap of `securityReduction adv q` in the IND-CPA experiment
is `(Pr[H_0 = true] - Pr[H_q = true]) / q`. -/
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

/-- For every `q`, `|Pr[H_0 = true] - Pr[H_q = true]| = q · AdvINDCPA_KEM(base, B)` with
`B := securityReduction adv q`; both sides vanish at `q = 0`. -/
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

/-! ## The security theorem -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- If `SecuritySendQueryBound adv q` and `B := securityReduction … adv q`, then
`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, B) + q · ε`. -/
-- ANCHOR: security
theorem security
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    ((q : ℝ) / 2) * kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) +
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal
-- ANCHOR_END: security
    := by
  have h := Security.security_guess_le_hybrid_gap kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
  have hgap := Security.Embedding.hybrid_gap_eq_query_factor kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q
  linarith

/-- `security` for a perfectly correct KEM:
`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, B)`. -/
-- ANCHOR: security_perfectKEM
theorem security_perfectKEM
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    ((q : ℝ) / 2) * kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q)
-- ANCHOR_END: security_perfectKEM
    := by
  have herror := (KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect
    kem ProbCompRuntime.probComp).2 hkem
  simpa only [herror, ENNReal.toReal_zero, mul_zero, add_zero] using
    security kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq

end oppUniKemCKA
