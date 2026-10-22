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
- `𝓑 := Security.Embedding.securityReduction … adv q`: the IND-CPA adversary against `kem`
  constructed from `adv`. It draws a *challenge epoch* `e` uniformly from `1, …, q`, embeds the
  KEM challenge in the key generation and encapsulation of epoch `e`, and runs `adv`.

**Security game and adversary advantage functions.**

Let:
- `G_b` be the SCKA security game of `Π` with its challenge bit fixed to `b`
  (`securityExpFixedBit`);
- `AdvGuess_SCKA(Π, adv) := |Pr[b' = b] - 1/2| = |Pr[G_true = true] - Pr[G_false = true]| / 2`
  be the advantage of `adv` in guessing the challenge bit;
- `AdvINDCPA_KEM(kem, 𝓑) := |2 Pr[b' = b] - 1| = |Pr[𝓑_real = true] - Pr[𝓑_random = true]|` be
  the advantage of `𝓑` in the IND-CPA game (`IND_CPA_Advantage_eq_fixed_branch_dist`);
- `ε` be the KEM correctness error (`kem.correctnessError`): the probability that an honest
  encapsulation `(ct, k) ← Encaps(pk)` under `(pk, sk) ← KeyGen` does not decapsulate to `k`.

**Theorem** (`security`). For every `q : ℕ`,

`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, 𝓑) + q · ε`.

`security_perfectKEM` drops `q · ε` for a perfectly correct KEM.

## Proof structure

Paths are relative to `OppUniKEM/Security/`.

**Notation.**

- `I_b := idealSecurityExp (fun _ => b) adv` (`Endpoints`): the *ideal game*, defined as
  `G_b` in which party A, on completing an online ciphertext, outputs party B's recorded key for
  that epoch instead of decapsulating.
- `H_i := idealEpochHybridExp adv i` (`IdealHybrids`): the *ideal hybrid* `i`, the ideal game
  whose challenges at epochs `1, …, i` return uniform keys (as in `I_true`) and all others
  recorded keys (as in `I_false`).
  Let `p_i := Pr[H_i = true]`. Then `H_0 = I_false`, and `p_q = Pr[I_true = true]` under the
  send bound.
- Epoch `e` is *exposed* once a permitted corruption or leaking send reveals its secrets
  (`exposureA`, `exposureB`); the game then records `e` in `exposed` and rejects challenges
  at `e`.

**Proof steps.**

1. *Correctness error* (`Endpoints`, `IdealHybrids`).
   - Bound the distance between the acceptance probabilities of the real game `G_b` and the
     ideal game `I_b`:
     `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`, where `q · ε` bounds the probability of a KEM
     failure within `q` sends (`security_correctness_endpoint_le`).
   - Hence `AdvGuess_SCKA(Π, adv) ≤ |p_0 - p_q| / 2 + q · ε` (`security_guess_le_hybrid_gap`).

2. *Reduction and simulation* (`Reduction/{Simulator,Relation,Game,Oracle,Simulation,HybridGame}`).
   - On public key `pk*` and challenge `(ct*, k*)`, the *reduction* `𝓑` runs `adv` against
     the oracles of the ideal game (`oracle`):
     - key generation at epoch `e` returns `pk*` and encapsulation at `e` returns `ct*`, with
       *hidden* secret key, offline state, shared key, and coins; other epochs sample honestly;
     - a challenge at `t` returns a uniform key if `t < e`, `k*` if `t = e`, and the recorded
       key if `t > e`;
     - a permitted corruption or leaking send that would reveal a hidden value stops the run
       with output `false`.
   - Define `𝓑_e^b := fixedBranch adv e b` (`Reduction/Simulator`): `𝓑` with its drawn challenge
     epoch fixed to `e` and the IND-CPA bit fixed to `b` (`true`: the encapsulated key).
   - Let `i_b := if b then e - 1 else e`.
    Define the *pinned hybrid* `P_e^b` (`hybridStopped`): `H_{i_b}` with the samples of
    epoch `e` drawn in advance, stopped at the first exposure of `e`.

   Main result: `Pr[𝓑_e^b = true] = Pr[P_e^b = true]` (`fixedBranch_eq_pinnedHybrid`).

3. *Deferred sampling* (`Reduction/{SourceUse,OnlineDeferral,SourceDeferral}`).
   - Define `S_e^b`: `H_{i_b}` stopped at the first exposure of `e`.
   - In `P_e^b`, each pre-drawn sample of epoch `e` (key generation, offline and online
     encapsulation) is used by at most one query: the protocol call that draws it in `S_e^b`
     (`SourceUse`). For a value used at most once, drawing it in advance or at that query gives
     the same acceptance probability (`stoppedRun_sample_once_eq`).

   Main result: `Pr[P_e^b = true] = Pr[S_e^b = true]` (`pinnedHybrid_eq_ideal`).

4. *Exposure cancellation* (`IdealHybrids`, this module).
   - Prove `Pr[S_e^true = true] - Pr[S_e^false = true] = p_{e-1} - p_e`
     (`idealEpochHybrid_signed_gap_stop_eq`): `H_{e-1}` and `H_e` differ only at a challenge of
     `e`, which is rejected once `e` is exposed.
   - Hence `Pr[𝓑_e^true = true] - Pr[𝓑_e^false = true] = p_{e-1} - p_e`
     (`fixedBranch_signed_gap_eq`).

5. *Averaging* (this module).
   - For `q > 0`, `𝓑` draws `e` uniformly from `1, …, q`, so

     ```text
     AdvINDCPA_KEM(kem, 𝓑)
       = |Pr[𝓑_real = true] - Pr[𝓑_random = true]|
       = |q⁻¹ · ∑_{e=1}^{q} (Pr[𝓑_e^true = true] - Pr[𝓑_e^false = true])|   (e uniform)
       = |q⁻¹ · ∑_{e=1}^{q} (p_{e-1} - p_e)|                                (step 4)
       = |p_0 - p_q| / q                                                     (telescoping)
     ```

   - Hence `|p_0 - p_q| = q · AdvINDCPA_KEM(kem, 𝓑)` (`hybrid_gap_eq_query_factor`).
   - Substituting into the bound of step 1, `AdvGuess_SCKA(Π, adv) ≤ |p_0 - p_q| / 2 + q · ε`,
     gives `security`:

     ```text
     AdvGuess_SCKA(Π, adv) ≤ |p_0 - p_q| / 2 + q · ε = (q / 2) · AdvINDCPA_KEM(kem, 𝓑) + q · ε
     ```

Supporting modules: `Basic` (interface, send budget), `Invariant` (transcript and epoch
invariants), `SCKA.Security` (generic guards), ToVCVio (sampling and stopping).
-/

/-! ## Steps 3–5: from the fixed branches to the ideal hybrids

In the notation of the proof structure, `S_e^b` is `idealSecurityImpl (adjacentMode e (!b))`
stopped at the first exposure of `e`, where the function `adjacentMode e b : ℕ → Bool`
(`HybridGame`) is `true` exactly at the epochs `1, …, e - 1`, and at `e` if `b`, whose
challenges get uniform keys.
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

/-- Step 3: `Pr[m ← sampleMaterial leak; hybridStopped m e b = true]` equals the acceptance
probability of `idealSecurityImpl (adjacentMode e b)` stopped at the first exposure of `e`. -/
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

/-- Steps 2 and 3: for `e > 0`, `Pr[𝓑_e^b = true] = Pr[S_e^b = true]`. -/
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

/-- Step 4: `Pr[𝓑_{i+1}^true = true] - Pr[𝓑_{i+1}^false = true] = p_i - p_{i+1}`. -/
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

/-- Step 5: for `q > 0`, `Pr[𝓑_real = true] - Pr[𝓑_random = true] = (p_0 - p_q) / q`. -/
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

/-- Step 5: for every `q`, `|p_0 - p_q| = q · AdvINDCPA_KEM(base, 𝓑)`. -/
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

/-- If `SecuritySendQueryBound adv q` and `𝓑 := securityReduction … adv q`, then
`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, 𝓑) + q · ε`. -/
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
`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, 𝓑)`. -/
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
