/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.ExperimentLaw
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Challenge.Model
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Challenge.Arithmetic
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Packing
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Radix
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Numerical certificate for the Frodo Challenge entry ramp

This file connects the downward-rounded counting measure from `ChallengeCertificateModel`
to the kernel-checked endpoint from `ChallengeCertificateArithmetic`. The packed recurrence
is an exact base-`2^145` implementation of the same natural-number recurrence. Together they
enclose the expected modular reconciliation ramp for the exact D1 noise distribution.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

set_option Elab.async false in
section

open ChallengeCertificateModel

private def packedIterate (step : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => packedIterate step n (step x)

private theorem packedIterate_succ_right
    (step : Nat → Nat) (n x : Nat) :
    packedIterate step (n + 1) x =
      step (packedIterate step n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change packedIterate step (n + 1) (step x) =
        step (packedIterate step n (step x))
      exact ih (step x)

private def repunit : Nat :=
  (List.range 769).foldl (fun acc _ => acc * radix + 1) 0

private def roundingMask : Nat := (2 ^ 129 - 1) * repunit

private def packedStep (x : Nat) : Nat :=
  ((x * productPack) >>> (9 * 145 + 16)) &&& roundingMask

private def packedRun (n x : Nat) : Nat :=
  packedIterate packedStep n x

private def reversedWeightPack : Nat :=
  (List.range 775).foldl
    (fun acc i => acc * radix +
      ((if i ≤ 387 then 387 - i else i - 387) - 256)) 0

private def certificateValues : Nat × Nat :=
  let x := packedRun 704 (scale * radix ^ 384)
  ((((x * extraPack * reversedWeightPack) >>> (145 * 774)) % radix),
    scale - x % (radix - 1))

private theorem measurePack_lowerCounts_zero :
    MLKEM.measurePack radix (-384) (lowerCounts 0) = scale * radix ^ 384 := by
  rw [lowerCounts, MLKEM.measurePack_single]
  rw [show ((0 : ℤ) - -384).toNat = 384 from rfl]

private theorem measurePack_lowerCounts_mod_pred :
    MLKEM.measurePack radix (-384) (lowerCounts 704) % (radix - 1) =
      ToVCVio.totalMass (lowerCounts 704) := by
  apply ChallengeCertificatePacking.measurePack_mod_pred_eq_totalMass (n := 769)
  · convert measureWindow_lowerCounts 704 using 1
    norm_num only
  · norm_num [radix]
  · calc
    ToVCVio.totalMass (lowerCounts 704) ≤ scale := totalMass_lowerCounts_le 704
    _ < radix - 1 := by norm_num [scale, radix]

private theorem repunit_eq_sum :
    repunit = ∑ i ∈ Finset.range 769, radix ^ i := by
  unfold repunit
  exact ChallengeCertificatePacking.foldl_range_mul_add_one_eq_pack radix 769

private theorem roundingMask_eq_sum :
    roundingMask =
      (2 ^ (145 - 16) - 1) * ∑ i ∈ Finset.range 769, (2 ^ 145) ^ i := by
  rw [roundingMask, repunit_eq_sum]
  simp only [radix, show (145 - 16 : Nat) = 129 from rfl]

private theorem measureWindow_lowerCounts_product (n : Nat) :
    ToVCVio.MeasureWindow (lowerCounts n * productCounts) (-393) 393 := by
  have h := ToVCVio.measureWindow_mul
    (measureWindow_lowerCounts n) measureWindow_productCounts
  convert h using 1 <;> norm_num

private theorem measurePack_lowerCounts_succ_sum (n : Nat) :
    MLKEM.measurePack radix (-384) (lowerCounts (n + 1)) =
      ∑ i ∈ Finset.range 769,
        ((lowerCounts n * productCounts) ((-384 : ℤ) + i) / 65536) *
          radix ^ i := by
  rw [MLKEM.measurePack_eq_range_sum
    (show ToVCVio.MeasureWindow (lowerCounts (n + 1))
        (-384) (-384 + (769 : ℤ) - 1) by
      norm_num
      exact measureWindow_lowerCounts (n + 1))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [lowerCounts_succ_apply, if_pos]
  simpa only [Finset.mem_Icc] using
    (show (-384 : ℤ) ≤ -384 + (i : ℤ) ∧ -384 + (i : ℤ) ≤ 384 by
      have := Finset.mem_range.mp hi
      omega)

private theorem measurePack_lowerCounts_product_sum (n : Nat) :
    MLKEM.measurePack radix (-393) (lowerCounts n * productCounts) =
      ∑ i ∈ Finset.range 787,
        (lowerCounts n * productCounts) ((-393 : ℤ) + i) * radix ^ i := by
  exact MLKEM.measurePack_eq_range_sum
    (show ToVCVio.MeasureWindow (lowerCounts n * productCounts)
        (-393) (-393 + (787 : ℤ) - 1) by
      norm_num
      exact measureWindow_lowerCounts_product n)

private theorem measurePack_lowerCounts_product_mul (n : Nat) :
    MLKEM.measurePack radix (-393) (lowerCounts n * productCounts) =
      MLKEM.measurePack radix (-384) (lowerCounts n) * productPack := by
  calc
    MLKEM.measurePack radix (-393) (lowerCounts n * productCounts) =
        MLKEM.measurePack radix (-384) (lowerCounts n) *
          MLKEM.measurePack radix (-9) productCounts := by
      convert MLKEM.measurePack_mul (R := radix)
        (measureWindow_lowerCounts n) measureWindow_productCounts using 1
      norm_num
    _ = MLKEM.measurePack radix (-384) (lowerCounts n) * productPack := by
      rw [productPack_eq_measurePack]

private theorem packed_crop_step (f : Nat → Nat) (hf : ∀ i < 787, f i < radix) :
    (((∑ i ∈ Finset.range 787, f i * radix ^ i) >>> (9 * 145 + 16)) &&&
      roundingMask) = ∑ i ∈ Finset.range 769, (f (9 + i) / 65536) * radix ^ i := by
  have h := ChallengeCertificatePacking.packed_bitSlice
    (b := 145) (k := 9) (t := 16) (n := 769) (m := 787)
    (by norm_num) (by norm_num) (by norm_num) f hf
  simpa only [radix, roundingMask_eq_sum,
    show (2 ^ 16 : Nat) = 65536 from rfl,
    show (145 * 9 + 16 : Nat) = 9 * 145 + 16 from rfl] using h

private theorem measurePack_lowerCounts_succ (n : Nat) :
    MLKEM.measurePack radix (-384) (lowerCounts (n + 1)) =
      packedStep (MLKEM.measurePack radix (-384) (lowerCounts n)) := by
  have h := packed_crop_step
    (fun i => (lowerCounts n * productCounts) ((-393 : ℤ) + i))
    (fun i _ => convolutionCoefficient_lt_radix n ((-393 : ℤ) + i))
  have hindex (i : Nat) :
      (-393 : ℤ) + (9 + i : Nat) = -384 + (i : ℤ) := by
    push_cast
    omega
  simp_rw [hindex] at h
  have hp := (measurePack_lowerCounts_product_sum n).symm.trans
    (measurePack_lowerCounts_product_mul n)
  calc
    MLKEM.measurePack radix (-384) (lowerCounts (n + 1)) =
        ∑ i ∈ Finset.range 769,
          ((lowerCounts n * productCounts) ((-384 : ℤ) + i) / 65536) * radix ^ i :=
      measurePack_lowerCounts_succ_sum n
    _ = (((∑ i ∈ Finset.range 787,
        (lowerCounts n * productCounts) ((-393 : ℤ) + i) * radix ^ i) >>>
          (9 * 145 + 16)) &&& roundingMask) := h.symm
    _ = packedStep (MLKEM.measurePack radix (-384) (lowerCounts n)) :=
      congrArg (fun x : Nat => (x >>> (9 * 145 + 16)) &&& roundingMask) hp

private theorem packedRun_succ_right (n x : Nat) :
    packedRun (n + 1) x = packedStep (packedRun n x) := by
  exact packedIterate_succ_right packedStep n x

private theorem measurePack_lowerCounts_run (n : Nat) :
    MLKEM.measurePack radix (-384) (lowerCounts n) =
      packedRun n (scale * radix ^ 384) := by
  induction n with
  | zero => exact measurePack_lowerCounts_zero
  | succ n ih =>
      rw [measurePack_lowerCounts_succ, ih, ← packedRun_succ_right]

private theorem indexWeight_eq (i : Nat) :
    ((-387 : ℤ) + (i : ℤ)).natAbs - 256 =
      (if i ≤ 387 then 387 - i else i - 387) - 256 := by
  rw [show (-387 : ℤ) + (i : ℤ) = (i : ℤ) - (387 : ℤ) by ring]
  by_cases hi : i ≤ 387
  · have h := Int.natAbs_natCast_sub_natCast_of_le hi
    norm_num only [Nat.cast_ofNat] at h
    rw [h, if_pos hi]
  · have h := Int.natAbs_natCast_sub_natCast_of_ge (a := i) (b := 387) (by omega)
    norm_num only [Nat.cast_ofNat] at h
    rw [h, if_neg hi]

private theorem indexedWeight_le_131 (i : Nat) (hi : i < 775) :
    ((-387 : ℤ) + (i : ℤ)).natAbs - 256 ≤ 131 := by
  rw [indexWeight_eq]
  split_ifs <;> omega

private theorem reversedWeightPack_eq_sum :
    reversedWeightPack =
      ∑ i ∈ Finset.range 775,
        (((-387 : ℤ) + ((775 - 1 - i : Nat) : ℤ)).natAbs - 256) * radix ^ i := by
  rw [reversedWeightPack, ChallengeCertificatePacking.foldl_range_mul_add_eq_reversePack]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [indexWeight_eq]

private theorem totalMass_approxCounts_le :
    ToVCVio.totalMass (lowerCounts 704 * d1Counts) ≤ 256 * scale := by
  rw [totalMass_approxCounts]
  exact Nat.mul_le_mul_left 256 (totalMass_lowerCounts_le 704)

private theorem weightedMass_eq_packExtract :
    Finsupp.sum (lowerCounts 704 * d1Counts)
        (fun (z : ℤ) (a : Nat) => a * (z.natAbs - 256)) =
      MLKEM.measurePack radix (-387) (lowerCounts 704 * d1Counts) *
          reversedWeightPack / radix ^ 774 % radix := by
  let A := lowerCounts 704 * d1Counts
  have hwindow : ToVCVio.MeasureWindow A (-387) (-387 + (775 : ℤ) - 1) := by
    convert measureWindow_approxCounts using 1
    norm_num only
  have hsum :
      ∑ i ∈ Finset.range 775, A ((-387 : ℤ) + i) =
        ToVCVio.totalMass A :=
    (MLKEM.totalMass_eq_range_sum hwindow).symm
  have hcarry :
      131 * ∑ i ∈ Finset.range 775, A ((-387 : ℤ) + i) < radix := by
    rw [hsum]
    calc
      131 * ToVCVio.totalMass A ≤ 131 * (256 * scale) :=
        Nat.mul_le_mul_left 131 totalMass_approxCounts_le
      _ < radix := by norm_num [scale, radix]
  have hdot := ChallengeCertificatePacking.dot_eq_pack_extract_bound
    (R := radix) (q := 775) (B := 131) (by norm_num)
    (fun i => A ((-387 : ℤ) + i))
    (fun i => ((-387 : ℤ) + (i : ℤ)).natAbs - 256)
    indexedWeight_le_131 hcarry
  rw [← MLKEM.measurePack_eq_range_sum hwindow,
    ← reversedWeightPack_eq_sum] at hdot
  rw [ChallengeCertificatePacking.finsuppWeightedSum_eq_range_sum A (-387) 775
    (fun z => z.natAbs - 256) hwindow]
  simpa only [show 775 - 1 = 774 by norm_num] using hdot

private theorem packedIterate_eq_arithmetic
    (step : Nat → Nat) (n x : Nat) :
    packedIterate step n x =
      ChallengeCertificateArithmetic.packedIterate step n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change packedIterate step n (step x) =
        ChallengeCertificateArithmetic.packedIterate step n (step x)
      exact ih _

private theorem radix_eq_arithmetic :
    radix = ChallengeCertificateArithmetic.radix := by
  rfl

private theorem repunit_eq_arithmetic :
    repunit = ChallengeCertificateArithmetic.repunit := by
  rw [repunit, ChallengeCertificateArithmetic.repunit,
    radix_eq_arithmetic]

private theorem roundingMask_eq_arithmetic :
    roundingMask = ChallengeCertificateArithmetic.roundingMask := by
  rw [roundingMask, ChallengeCertificateArithmetic.roundingMask,
    repunit_eq_arithmetic]

private theorem productPack_eq_arithmetic :
    productPack = ChallengeCertificateArithmetic.productPack := by
  rw [productPack, ChallengeCertificateArithmetic.productPack,
    radix_eq_arithmetic]

private theorem packedStep_eq_arithmetic :
    packedStep = ChallengeCertificateArithmetic.packedStep := by
  funext x
  rw [packedStep, ChallengeCertificateArithmetic.packedStep,
    productPack_eq_arithmetic, roundingMask_eq_arithmetic]

private theorem packedRun_eq_arithmetic (n x : Nat) :
    packedRun n x = ChallengeCertificateArithmetic.packedRun n x := by
  change packedIterate packedStep n x =
    ChallengeCertificateArithmetic.packedIterate
      ChallengeCertificateArithmetic.packedStep n x
  rw [packedIterate_eq_arithmetic, packedStep_eq_arithmetic]

private theorem scale_eq_arithmetic :
    scale = ChallengeCertificateArithmetic.scale := by
  rfl

private theorem extraPack_eq_arithmetic :
    extraPack = ChallengeCertificateArithmetic.extraPack := by
  rw [extraPack, ChallengeCertificateArithmetic.extraPack,
    radix_eq_arithmetic]

private theorem reversedWeightPack_eq_arithmetic :
    reversedWeightPack =
      ChallengeCertificateArithmetic.reversedWeightPack := by
  rw [reversedWeightPack,
    ChallengeCertificateArithmetic.reversedWeightPack,
    radix_eq_arithmetic]

private theorem endpoint_congr
    (run run' : Nat → Nat → Nat) (s s' r r' e e' w w' : Nat)
    (hrun : run = run') (hs : s = s') (hr : r = r')
    (he : e = e') (hw : w = w') :
    (let x := run 704 (s * r ^ 384)
     ((((x * e * w) >>> (145 * 774)) % r), s - x % (r - 1))) =
      (let x := run' 704 (s' * r' ^ 384)
       ((((x * e' * w') >>> (145 * 774)) % r'),
        s' - x % (r' - 1))) := by
  subst run'
  subst s'
  subst r'
  subst e'
  subst w'
  rfl

set_option maxRecDepth 65536 in
private theorem certificateValues_eq :
    @Eq (Nat × Nat) certificateValues
      (182190504909736707587867345424, 4538522943514) := by
  change
    (let x := packedRun 704 (scale * radix ^ 384)
     ((((x * extraPack * reversedWeightPack) >>> (145 * 774)) % radix),
      scale - x % (radix - 1))) =
      (182190504909736707587867345424, 4538522943514)
  have hrun : packedRun = ChallengeCertificateArithmetic.packedRun := by
    funext n x
    exact packedRun_eq_arithmetic n x
  exact (endpoint_congr packedRun ChallengeCertificateArithmetic.packedRun
    scale ChallengeCertificateArithmetic.scale radix
    ChallengeCertificateArithmetic.radix extraPack
    ChallengeCertificateArithmetic.extraPack reversedWeightPack
    ChallengeCertificateArithmetic.reversedWeightPack hrun
    scale_eq_arithmetic radix_eq_arithmetic extraPack_eq_arithmetic
    reversedWeightPack_eq_arithmetic).trans
      ChallengeCertificateArithmetic.certificateValues_eq

private theorem shift_extract_eq_div
    (x e w r k n : Nat) (hr : r = 2 ^ k) :
    ((x * e * w) >>> (k * n)) % r =
      (x * e * w / r ^ n) % r := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul, ← hr]

private theorem weightedMass_eq_certificateValue :
    Finsupp.sum (lowerCounts 704 * d1Counts)
        (fun (z : ℤ) (a : Nat) => a * (z.natAbs - 256)) =
      182190504909736707587867345424 := by
  have hcert := congrArg Prod.fst certificateValues_eq
  dsimp only [certificateValues] at hcert
  rw [shift_extract_eq_div _ _ _ radix 145 774 (by rfl)] at hcert
  change
      (packedRun 704 (scale * radix ^ 384) * extraPack * reversedWeightPack /
          radix ^ 774) % radix = 182190504909736707587867345424 at hcert
  rw [weightedMass_eq_packExtract, measurePack_approxCounts,
    measurePack_lowerCounts_run]
  exact hcert

private theorem add_eq_of_sub_eq {a b c : Nat}
    (hle : b ≤ a) (hsub : a - b = c) :
    b + c = a := by
  omega

private theorem lowerCounts_mass_add_certificateValue :
    ToVCVio.totalMass (lowerCounts 704) + 4538522943514 = scale := by
  have hcert := congrArg Prod.snd certificateValues_eq
  dsimp only [certificateValues] at hcert
  rw [← measurePack_lowerCounts_run,
    measurePack_lowerCounts_mod_pred] at hcert
  have hle := totalMass_lowerCounts_le 704
  exact add_eq_of_sub_eq hle hcert

private theorem mul_sub_mul_eq_of_add_eq
    (k a b c : Nat) (hadd : b + c = a) :
    k * a - k * b = k * c := by
  rw [← hadd, Nat.mul_add, Nat.add_sub_cancel_left]

private theorem approxCounts_missingMass_eq_certificateValue :
    256 * scale - ToVCVio.totalMass (lowerCounts 704 * d1Counts) =
      256 * 4538522943514 := by
  rw [totalMass_approxCounts]
  have h := lowerCounts_mass_add_certificateValue
  exact mul_sub_mul_eq_of_add_eq 256 scale
    (ToVCVio.totalMass (lowerCounts 704)) 4538522943514 h

private theorem weightedSum_union_support_right
    (F A : ToVCVio.IntMeasure) (w : ℤ → Nat) :
    ∑ z ∈ F.coeff.support ∪ A.coeff.support, A z * w z =
      Finsupp.sum A (fun z a => a * w z) := by
  change (∑ z ∈ F.coeff.support ∪ A.coeff.support, A z * w z) =
    ∑ z ∈ A.coeff.support, A z * w z
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro z hz hz'
  have hnot : z ∉ A.coeff.support := hz'
  rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]

private theorem approximatingRampTerm_eq_certificateValue :
    let F := (productCounts ^ 704) * d1Counts
    let A := lowerCounts 704 * d1Counts
    let s := F.coeff.support ∪ A.coeff.support
    (∑ z ∈ s,
        ((A z * (z.natAbs - 256) : Nat) : ℝ≥0∞) /
          ((256 * scale) * 512)) =
      (182190504909736707587867345424 : ℝ≥0∞) /
        ((256 * scale) * 512) := by
  dsimp only
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum,
    weightedSum_union_support_right, weightedMass_eq_certificateValue]
  norm_num only [Nat.cast_ofNat]

private theorem challenge_main_scale_cancel (N S : ℝ≥0∞) :
    64 * (N / ((256 * S) * 512)) = N / (2048 * S) := by
  have hden : (256 * S) * 512 = 64 * (2048 * S) := by
    calc
      (256 * S) * 512 = (256 * 512) * S := by ac_rfl
      _ = (64 * 2048) * S := by norm_num
      _ = 64 * (2048 * S) := by rw [mul_assoc]
  rw [hden, ← mul_div_assoc]
  exact ENNReal.mul_div_mul_left N (2048 * S) (by norm_num) (by norm_num)

private theorem challenge_missing_scale_cancel (d S : ℝ≥0∞) :
    (256 * d) / (256 * S) = d / S :=
  ENNReal.mul_div_mul_left d S (by norm_num) (by norm_num)

/-- Certified bounds on 64 times the modular-ramp expectation for the exact Challenge D1 noise law.
`ChallengeCorrectness` relates this expectation to first-exchange failure with a uniform public
matrix, including the exceptional-secret-vector and pairwise-overlap allowances. -/
theorem challengeEntryRamp_bounds :
    (182190504909736707587867345424 : ℝ≥0∞) / 2 ^ 139 ≤
      64 * OracleComp.EvalDist.expectedValue
        challengeEntryNoiseIntExp challengeFailureRamp ∧
    64 * OracleComp.EvalDist.expectedValue
        challengeEntryNoiseIntExp challengeFailureRamp ≤
      (182190504909736707587867345424 : ℝ≥0∞) / 2 ^ 139 +
        64 * (4538522943514 : ℝ≥0∞) / 2 ^ 128 := by
  classical
  have hbounds := challengeEntryRamp_missingMass_bounds
  dsimp only at hbounds
  rw [approximatingRampTerm_eq_certificateValue,
    approxCounts_missingMass_eq_certificateValue] at hbounds
  have hscale : (scale : ℝ≥0∞) = 2 ^ 128 := by
    simp only [scale, Nat.cast_pow, Nat.cast_ofNat]
  have hden : (2048 : ℝ≥0∞) * scale = 2 ^ 139 := by
    calc
      (2048 : ℝ≥0∞) * scale = 2 ^ 11 * 2 ^ 128 := by
        rw [hscale]
        congr 1
        norm_num
      _ = 2 ^ (11 + 128) := (pow_add 2 11 128).symm
      _ = 2 ^ 139 := by rw [show 11 + 128 = 139 by norm_num]
  have hmain :
      (182190504909736707587867345424 : ℝ≥0∞) / 2 ^ 139 =
        64 * ((182190504909736707587867345424 : ℝ≥0∞) /
          ((256 * scale) * 512)) := by
    rw [← hden]
    exact (challenge_main_scale_cancel _ _).symm
  have hmissing :
      (((256 * 4538522943514 : Nat) : ℝ≥0∞) /
          (256 * (scale : ℝ≥0∞))) =
        (4538522943514 : ℝ≥0∞) / scale := by
    rw [Nat.cast_mul]
    exact challenge_missing_scale_cancel _ _
  constructor
  · calc
      (182190504909736707587867345424 : ℝ≥0∞) / 2 ^ 139 =
          64 * ((182190504909736707587867345424 : ℝ≥0∞) /
            ((256 * scale) * 512)) := hmain
      _ ≤ 64 * OracleComp.EvalDist.expectedValue
          challengeEntryNoiseIntExp challengeFailureRamp :=
        by simpa only [mul_comm] using mul_le_mul_left hbounds.1 64
  · calc
      64 * OracleComp.EvalDist.expectedValue
          challengeEntryNoiseIntExp challengeFailureRamp ≤
          64 * ((182190504909736707587867345424 : ℝ≥0∞) /
              ((256 * scale) * 512) +
            ((256 * 4538522943514 : Nat) : ℝ≥0∞) /
              (256 * scale)) :=
        by simpa only [mul_comm] using mul_le_mul_left hbounds.2 64
      _ = (182190504909736707587867345424 : ℝ≥0∞) / 2 ^ 139 +
          64 * (4538522943514 : ℝ≥0∞) / 2 ^ 128 := by
        rw [mul_add, ← hmain, hmissing, ← mul_div_assoc, hscale]

end

end lweCKA
