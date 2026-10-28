/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Simulation
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# Opp-BiKEM — Security

The SCKA guess advantage of an adversary against Opp-BiKEM is bounded by `q · ε_cor` for the
KEM's correctness error, plus half the sum over target epochs `t ≤ 2q` of the IND-CPA advantage
of the reduction `reduction adv t` against the KEM (`security`); the sharper form over the
positive targets only is `security_positive`. When every reduction at a positive target has
advantage at most `δ`, the bound is `q · ε_cor + q · δ` (`security_uniform`).

The hop at a positive target is exact (`hybrid_hop_eq_reduction`): the distance between the
adjacent hybrids `t` and `t + 1` of the challenge-answer chain is the reduction's IND-CPA
advantage. It is assembled from the cancellation of exposed paths (`hybridExp_sub_eq_stopped_sub`),
the eager sampling of the target's values (`probOutput_stoppedHybridExp_eq_eager`), the
simulation by the reduction (`probOutput_stoppedEagerExp_eq_reductionRun`), and the fixed-branch
form of the IND-CPA advantage. The real-key branch of the KEM experiment is the hybrid `t`, the
random-key branch the hybrid `t + 1`.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)

include hEk hCt in
/-- The fixed-bit IND-CPA experiment of the reduction at target `t` accepts with the probability
of the eager hybrid of the opposite bit, averaged over the target's values: the real key is
hybrid `t`, the random key hybrid `t + 1`. -/
lemma probOutput_indCPAExpProb_reduction_eq (adv : SecurityAdversary leak Sym) (t : ℕ)
    (ht : 0 < t) (bb : Bool) :
    Pr[= true | indCPAExpProb kem (reduction kem hDet ecEk ecCt leak adv t) bb] =
      Pr[= true | kem.keygen >>= fun x => kem.encaps x.1 >>= fun y => ($ᵗ K : ProbComp K) >>=
        fun r => stoppedEagerExp kem hDet ecEk ecCt leak t (!bb) x.1 x.2 y.1 y.2 r adv] := by
  simp only [indCPAExpProb, indCPAPrefix, reduction_preChallenge, bind_assoc]
  refine probOutput_bind_congr (mx := kem.keygen) ?_
  rintro ⟨pk, sk⟩ hx
  change Pr[= true | (do
      let st ← (pure pk : ProbComp PK)
      let y ← kem.encaps pk
      let r ← ($ᵗ K : ProbComp K)
      pure (⟨st, y.1, y.2, r⟩ : INDCPAPrefixState kem (reduction kem hDet ecEk ecCt leak adv t)))
      >>= fun p => reductionRun kem hDet ecEk ecCt leak adv t p.st p.cStar
        (if bb then p.kReal else p.kRand)] = _
  simp only [bind_assoc, pure_bind]
  refine probOutput_bind_congr (mx := kem.encaps pk) ?_
  rintro ⟨c, kReal⟩ hy
  refine probOutput_bind_congr (mx := ($ᵗ K : ProbComp K)) ?_
  intro r _
  dsimp only
  unfold reductionRun
  trans Pr[= true | kem.keygen >>= fun _ =>
    stoppedEagerExp kem hDet ecEk ecCt leak t (!bb) pk sk c kReal r adv]
  · refine probOutput_bind_congr ?_
    rintro ⟨_, dummy⟩ _
    rw [probOutput_stoppedEagerExp_eq_reductionRun kem hDet ecEk ecCt hEk hCt leak t ht pk sk
      dummy c kReal r (!bb) adv hx hy]
    cases bb <;> rfl
  · exact probOutput_congr rfl (evalDist_bind_const_probComp _ _)

include hEk hCt in
/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `0 < t`.

Then the distance between the adjacent hybrids `t + 1` and `t` is the IND-CPA advantage of the
reduction at target `t`. -/
theorem hybrid_hop_eq_reduction (adv : SecurityAdversary leak Sym) (t : ℕ) (ht : 0 < t) :
    |(Pr[= true | hybridExp kem hDet ecEk ecCt leak (t + 1) adv]).toReal -
        (Pr[= true | hybridExp kem hDet ecEk ecCt leak t adv]).toReal| =
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (reduction kem hDet ecEk ecCt leak adv t) := by
  rw [IND_CPA_Advantage_eq_fixed_branch_dist, ← indCPAExpProb_probOutput_true_eq,
    ← indCPAExpProb_probOutput_true_eq, hybridExp_sub_eq_stopped_sub]
  have h1 := probOutput_stoppedHybridExp_eq_eager kem hDet ecEk ecCt hEk hCt leak adv t ht true
  have h0 := probOutput_stoppedHybridExp_eq_eager kem hDet ecEk ecCt hEk hCt leak adv t ht false
  simp only [Bool.toNat_true, Bool.toNat_false, add_zero] at h1 h0
  rw [h1, h0, probOutput_indCPAExpProb_reduction_eq kem hDet ecEk ecCt hEk hCt leak adv t ht,
    probOutput_indCPAExpProb_reduction_eq kem hDet ecEk ecCt hEk hCt leak adv t ht,
    Bool.not_true, Bool.not_false, abs_sub_comm]

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then the SCKA guess advantage of `adv` against Opp-BiKEM is at most `q · ε_cor`, for the
correctness error `ε_cor` of `kem`, plus half the sum over the positive targets `1 ≤ t ≤ 2q` of
the IND-CPA advantage of `reduction adv t` against `kem`. -/
theorem security_positive (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) * ∑ i ∈ Finset.range (2 * q), kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv (i + 1)) := by
  set δ' : ℕ → ℝ := fun t => if t = 0 then 0 else
    kem.IND_CPA_Advantage ProbCompRuntime.probComp (reduction kem hDet ecEk ecCt leak adv t)
    with hδ'
  have hbound := sckaGuessAdvantage_le_of_hop_bound kem hDet ecEk ecCt leak hEk hCt adv q hq δ'
    (fun t => by
      simp only [hδ']
      split_ifs
      · exact le_rfl
      · rw [IND_CPA_Advantage_eq_fixed_branch_dist]
        exact abs_nonneg _)
    (fun t ht _ => by
      simp only [hδ', if_neg (Nat.pos_iff_ne_zero.mp ht)]
      exact le_of_eq (hybrid_hop_eq_reduction kem hDet ecEk ecCt hEk hCt leak adv t ht))
  have hsum : ∑ t ∈ Finset.range (2 * q + 1), δ' t = ∑ i ∈ Finset.range (2 * q),
      kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv (i + 1)) := by
    rw [Finset.sum_range_succ']
    simp [hδ']
  rwa [hsum] at hbound

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then the SCKA guess advantage of `adv` against Opp-BiKEM is at most `q · ε_cor`, for the
correctness error `ε_cor` of `kem`, plus half the sum over targets `t ≤ 2q` of the IND-CPA
advantage of `reduction adv t` against `kem`. The summand at `t = 0` only adds its
non-negativity to `security_positive`. -/
theorem security (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) * ∑ t ∈ Finset.range (2 * q + 1),
        kem.IND_CPA_Advantage ProbCompRuntime.probComp
          (reduction kem hDet ecEk ecCt leak adv t) := by
  refine (security_positive kem hDet ecEk ecCt hEk hCt leak adv q hq).trans ?_
  have h0 : 0 ≤ kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (reduction kem hDet ecEk ecCt leak adv 0) := by
    rw [IND_CPA_Advantage_eq_fixed_branch_dist]
    exact abs_nonneg _
  rw [Finset.sum_range_succ']
  linarith

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends;
* every reduction `reduction adv t` at a positive target `t ≤ 2q` has IND-CPA advantage at
  most `δ`.

Then the SCKA guess advantage of `adv` against Opp-BiKEM is at most `q · ε_cor + q · δ`. -/
theorem security_uniform (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) (δ : ℝ)
    (hδ : ∀ t, 0 < t → t ≤ 2 * q →
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (reduction kem hDet ecEk ecCt leak adv t) ≤
        δ) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal + (q : ℝ) * δ := by
  refine (security_positive kem hDet ecEk ecCt hEk hCt leak adv q hq).trans ?_
  have hsum : ∑ i ∈ Finset.range (2 * q), kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (reduction kem hDet ecEk ecCt leak adv (i + 1)) ≤ 2 * (q : ℝ) * δ := by
    calc ∑ i ∈ Finset.range (2 * q), kem.IND_CPA_Advantage ProbCompRuntime.probComp
          (reduction kem hDet ecEk ecCt leak adv (i + 1))
        ≤ ∑ _i ∈ Finset.range (2 * q), δ :=
          Finset.sum_le_sum fun i hi => hδ (i + 1) (Nat.succ_pos i)
            (by have := Finset.mem_range.1 hi; omega)
      _ = 2 * (q : ℝ) * δ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  linarith

end oppBiKemCKA
