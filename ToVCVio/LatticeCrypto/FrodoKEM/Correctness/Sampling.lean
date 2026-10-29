/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Basic
import ToVCVio.Probability.MatrixSampling
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.Constructions.UniformFinMeasure
import VCVio.OracleComp.EvalDist.Sum
import VCVio.EvalDist.IndepProductMeasure

/-!
# FrodoKEM sampling laws

This module proves the exact scalar probability mass function of FrodoKEM's error sampler and the
joint law of its matrix sampler. The matrix theorem transports a uniform bit string through the
block-packing equivalence, so it also covers matrices with a zero dimension.
-/

namespace FrodoKEM

open OracleComp ToVCVio

/-- Apply the Frodo error sampler to one uniformly sampled sixteen-bit string. -/
def sampleError (ps : ParameterSet) : ProbComp ℤ :=
  Sample ps.errorTable <$> ($ᵗ (Bits lenChi))

/-- Number of sixteen-bit sampler inputs producing an integer error value. -/
def noiseCount (ps : ParameterSet) (z : ℤ) : ℕ :=
  if h : z.natAbs ≤ ps.errorTable.d then
    ps.errorProbNumerators[z.natAbs]'(Nat.lt_succ_of_le h)
  else 0

theorem noiseCount_neg (ps : ParameterSet) (z : ℤ) :
    noiseCount ps (-z) = noiseCount ps z := by
  simp only [noiseCount, Int.natAbs_neg]

private def sampleMagnitude (table : ErrorTable) (t : ℕ) : ℕ :=
  (List.finRange table.d).countP fun i =>
    decide (table.thresholds[i.castSucc] < t)

private def sampleSeedParts (r : Bits lenChi) : Bool × Fin (2 ^ (lenChi - 1)) :=
  (r[0]'(by decide),
    ⟨Nat.ofBits fun i : Fin (lenChi - 1) => r[i.val + 1]'(by omega),
      Nat.ofBits_lt_two_pow _⟩)

private def sampleSeedOfParts (p : Bool × Fin (2 ^ (lenChi - 1))) : Bits lenChi :=
  Vector.ofFn fun i => if _h : i.val = 0 then p.1 else p.2.val.testBit (i.val - 1)

private theorem sampleSeedParts_leftInverse :
    Function.LeftInverse sampleSeedParts sampleSeedOfParts := by
  intro p
  apply Prod.ext
  · simp [sampleSeedParts, sampleSeedOfParts]
  · apply Fin.ext
    simp only [sampleSeedParts, sampleSeedOfParts, Vector.getElem_ofFn]
    have hfun : (fun i : Fin (lenChi - 1) =>
        if _h : i.val + 1 = 0 then p.1 else p.2.val.testBit (i.val + 1 - 1)) =
        fun i : Fin (lenChi - 1) => p.2.val.testBit i.val := by
      funext i
      rw [dite_eq_right (by omega), Nat.add_sub_cancel]
    rw [hfun]
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt p.2.isLt]

private theorem sampleSeedParts_rightInverse :
    Function.RightInverse sampleSeedParts sampleSeedOfParts := by
  intro r
  apply Vector.ext
  intro i hi
  simp only [sampleSeedOfParts, Vector.getElem_ofFn]
  by_cases hzero : i = 0
  · subst i
    simp [sampleSeedParts]
  · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
    simp only [hzero, ↓reduceDIte, sampleSeedParts]
    rw [Nat.testBit_ofBits]
    simp only [lenChi] at hi ⊢
    simp only [Nat.sub_add_cancel hpos]
    rw [dite_eq_left (by omega)]

private def sampleSeedEquiv : Bits lenChi ≃ Bool × Fin (2 ^ (lenChi - 1)) where
  toFun := sampleSeedParts
  invFun := sampleSeedOfParts
  left_inv := sampleSeedParts_rightInverse
  right_inv := sampleSeedParts_leftInverse

private theorem Sample_sampleSeedOfParts (table : ErrorTable)
    (p : Bool × Fin (2 ^ (lenChi - 1))) :
    Sample table (sampleSeedOfParts p) =
      if p.1 then -(sampleMagnitude table p.2.val : ℤ)
      else (sampleMagnitude table p.2.val : ℤ) := by
  have hbits : Nat.ofBits (fun i : Fin (lenChi - 1) => p.2.val.testBit i.val) = p.2.val := by
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt p.2.isLt]
  simp [Sample, sampleSeedOfParts, sampleMagnitude, hbits]

private theorem sampleMagnitude_eq_card (table : ErrorTable) (t : ℕ) :
    sampleMagnitude table t =
      ((Finset.univ.filter fun i : Fin table.d =>
        table.thresholds[i.castSucc] < t).card) := by
  rw [sampleMagnitude, ← (List.nodup_finRange table.d).card_eq_countP,
    List.toFinset_finRange]

private theorem threshold_monotone (table : ErrorTable)
    {probs : Vector ℕ (table.d + 1)} (hw : table.WellFormed probs) :
    Monotone (fun i : Fin table.d =>
      table.thresholds[i.castSucc]) := by
  intro i j hij
  exact hw.strictMono.monotone (by simpa using hij)

private theorem threshold_lt_iff_lt_sampleMagnitude (table : ErrorTable)
    {probs : Vector ℕ (table.d + 1)} (hw : table.WellFormed probs)
    (t : ℕ) (i : Fin table.d) :
    table.thresholds[i.castSucc] < t ↔
      i.val < sampleMagnitude table t := by
  rw [sampleMagnitude_eq_card]
  exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone
    (threshold_monotone table hw)).symm

private theorem sampleMagnitude_le (table : ErrorTable) (t : ℕ) :
    sampleMagnitude table t ≤ table.d := by
  rw [sampleMagnitude]
  exact List.countP_le_length.trans_eq (List.length_finRange ..)

private theorem sampleMagnitude_eq_zero_iff (table : ErrorTable)
    {probs : Vector ℕ (table.d + 1)} (hw : table.WellFormed probs)
    (hd : 0 < table.d) (t : ℕ) :
    sampleMagnitude table t = 0 ↔ t ≤ table.thresholds[0] := by
  have hfirst := threshold_lt_iff_lt_sampleMagnitude table hw t ⟨0, hd⟩
  change table.thresholds[0] < t ↔ 0 < sampleMagnitude table t at hfirst
  omega

private theorem sampleMagnitude_eq_iff (table : ErrorTable)
    {probs : Vector ℕ (table.d + 1)} (hw : table.WellFormed probs)
    (t : ℕ) (ht : t < 2 ^ (lenChi - 1)) (k : ℕ)
    (hk0 : 0 < k) (hkd : k ≤ table.d) :
    sampleMagnitude table t = k ↔
      table.thresholds[k - 1]'(by omega) < t ∧
        t ≤ table.thresholds[k]'(by omega) := by
  have hbefore : table.thresholds[k - 1]'(by omega) < t ↔ k - 1 < sampleMagnitude table t := by
    simpa using threshold_lt_iff_lt_sampleMagnitude table hw t ⟨k - 1, by omega⟩
  by_cases hk : k < table.d
  · have hat : table.thresholds[k]'(by omega) < t ↔ k < sampleMagnitude table t := by
      simpa using threshold_lt_iff_lt_sampleMagnitude table hw t ⟨k, hk⟩
    omega
  · obtain rfl : k = table.d := by omega
    have hlast := hw.last_eq
    have := sampleMagnitude_le table t
    omega

private theorem prEvent_uniformFin_Icc {N a b : ℕ} [NeZero N]
    (ha : a < N) (hb : b < N) :
    Pr{let t ← ($ᵗ (Fin N) : ProbComp (Fin N))}[a ≤ t.val ∧ t.val ≤ b] =
      (↑(b + 1 - a) : ENNReal) / N := by
  rw [SampleableType.prEvent_uniformSample]
  have hfilter :
      (Finset.univ.filter fun t : Fin N => a ≤ t.val ∧ t.val ≤ b) =
        Finset.Icc (⟨a, ha⟩ : Fin N) ⟨b, hb⟩ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc,
      Fin.le_iff_val_le_val]
  rw [hfilter, Fin.card_Icc]
  simp

private theorem prEvent_uniformFin_Ioc {N a b : ℕ} [NeZero N]
    (ha : a < N) (hb : b < N) :
    Pr{let t ← ($ᵗ (Fin N) : ProbComp (Fin N))}[a < t.val ∧ t.val ≤ b] =
      (↑(b - a) : ENNReal) / N := by
  rw [SampleableType.prEvent_uniformSample]
  have hfilter :
      (Finset.univ.filter fun t : Fin N => a < t.val ∧ t.val ≤ b) =
        Finset.Ioc (⟨a, ha⟩ : Fin N) ⟨b, hb⟩ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc,
      Fin.le_iff_val_le_val, Fin.lt_def]
  rw [hfilter, Fin.card_Ioc]
  simp

private theorem prEvent_uniformBool_fin {N : ℕ} [NeZero N]
    (p : Bool → Fin N → Prop) :
    Pr{let x ← ($ᵗ (Bool × Fin N) : ProbComp (Bool × Fin N))}[p x.1 x.2] =
      (Pr{let t ← ($ᵗ (Fin N) : ProbComp (Fin N))}[p false t] +
        Pr{let t ← ($ᵗ (Fin N) : ProbComp (Fin N))}[p true t]) / 2 := by
  classical
  rw [SampleableType.prEvent_uniformSample_prod]
  rw [OracleComp.prEvent_bind_eq_tsum_prEvent, tsum_fintype, Fintype.sum_bool]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool,
    prEvent_norm]
  simp only [div_eq_mul_inv, mul_comm]
  rw [← mul_add, add_comm]
  norm_num

private theorem prSample_eq_parts (table : ErrorTable) (z : ℤ) :
    Pr{let r ← ($ᵗ (Bits lenChi) : ProbComp (Bits lenChi))}[Sample table r = z] =
      Pr{let p ← ($ᵗ (Bool × Fin (2 ^ (lenChi - 1))) :
        ProbComp (Bool × Fin (2 ^ (lenChi - 1))))}[
          (if p.1 then -(sampleMagnitude table p.2.val : ℤ)
            else (sampleMagnitude table p.2.val : ℤ)) = z] := by
  calc
    _ = Pr{let r ← ($ᵗ (Bits lenChi) : ProbComp (Bits lenChi))}[
          Sample table (sampleSeedOfParts (sampleSeedParts r)) = z] := by
      apply prEvent_congr
      intro r
      rw [sampleSeedParts_rightInverse r]
    _ = Pr{let p ← ($ᵗ (Bool × Fin (2 ^ (lenChi - 1))) :
          ProbComp (Bool × Fin (2 ^ (lenChi - 1))))}[
            Sample table (sampleSeedOfParts p) = z] := by
      exact SampleableType.prEvent_uniformSample_equiv sampleSeedEquiv
        (fun p => Sample table (sampleSeedOfParts p) = z)
    _ = _ := by
      apply prEvent_congr
      intro p
      rw [Sample_sampleSeedOfParts]

private theorem threshold_lt_seedSpace (table : ErrorTable)
    {probs : Vector ℕ (table.d + 1)} (hw : table.WellFormed probs)
    (k : ℕ) (hk : k ≤ table.d) :
    table.thresholds[k]'(Nat.lt_succ_of_le hk) < 2 ^ (lenChi - 1) := by
  have hle : table.thresholds[k]'(Nat.lt_succ_of_le hk) ≤
      table.thresholds[table.d] := by
    have hfin : (⟨k, by omega⟩ : Fin (table.d + 1)) ≤
        (⟨table.d, by omega⟩ : Fin (table.d + 1)) :=
      Fin.le_iff_val_le_val.mpr hk
    simpa using hw.strictMono.monotone hfin
  rw [hw.last_eq] at hle
  simp only [lenChi] at hle ⊢
  omega

private theorem prSampleMagnitude_zero (ps : ParameterSet) :
    Pr{let t ← ($ᵗ (Fin (2 ^ (lenChi - 1))) :
      ProbComp (Fin (2 ^ (lenChi - 1))))}[
        sampleMagnitude ps.errorTable t.val = 0] =
      (↑(ps.errorTable.thresholds[0] + 1) : ENNReal) / 2 ^ (lenChi - 1) := by
  have hw := ps.errorTable_wellFormed
  have hd : 0 < ps.errorTable.d := by cases ps <;> decide
  have htop : ps.errorTable.thresholds[0] < 2 ^ (lenChi - 1) :=
    threshold_lt_seedSpace ps.errorTable hw 0 (Nat.zero_le _)
  calc
    _ = Pr{let t ← ($ᵗ (Fin (2 ^ (lenChi - 1))) :
          ProbComp (Fin (2 ^ (lenChi - 1))))}[
            0 ≤ t.val ∧ t.val ≤ ps.errorTable.thresholds[0]] := by
      apply prEvent_congr
      intro t
      rw [sampleMagnitude_eq_zero_iff ps.errorTable hw hd]
      simp
    _ = _ := by
      have h := prEvent_uniformFin_Icc (a := 0) (b := ps.errorTable.thresholds[0])
        (by positivity : 0 < 2 ^ (lenChi - 1)) htop
      convert h using 1
      all_goals norm_num [lenChi]

private theorem prSampleMagnitude_pos (ps : ParameterSet) (k : ℕ)
    (hk0 : 0 < k) (hkd : k ≤ ps.errorTable.d) :
    Pr{let t ← ($ᵗ (Fin (2 ^ (lenChi - 1))) :
      ProbComp (Fin (2 ^ (lenChi - 1))))}[
        sampleMagnitude ps.errorTable t.val = k] =
      (↑(ps.errorTable.thresholds[k]'(by omega) -
        ps.errorTable.thresholds[k - 1]'(by omega)) : ENNReal) /
          2 ^ (lenChi - 1) := by
  have hw := ps.errorTable_wellFormed
  have hlow : ps.errorTable.thresholds[k - 1]'(by omega) < 2 ^ (lenChi - 1) :=
    threshold_lt_seedSpace ps.errorTable hw (k - 1) (by omega)
  have hupp : ps.errorTable.thresholds[k]'(by omega) < 2 ^ (lenChi - 1) :=
    threshold_lt_seedSpace ps.errorTable hw k hkd
  calc
    _ = Pr{let t ← ($ᵗ (Fin (2 ^ (lenChi - 1))) :
          ProbComp (Fin (2 ^ (lenChi - 1))))}[
            ps.errorTable.thresholds[k - 1]'(by omega) < t.val ∧
              t.val ≤ ps.errorTable.thresholds[k]'(by omega)] := by
      apply prEvent_congr
      intro t
      exact sampleMagnitude_eq_iff ps.errorTable hw t.val t.isLt k hk0 hkd
    _ = _ := by
      have h := prEvent_uniformFin_Ioc
        (a := ps.errorTable.thresholds[k - 1]'(by omega))
        (b := ps.errorTable.thresholds[k]'(by omega)) hlow hupp
      convert h using 1
      all_goals norm_num [lenChi]

private theorem threshold_diff_eq_noiseCount (ps : ParameterSet) (k : ℕ)
    (hk0 : 0 < k) (hkd : k ≤ ps.errorTable.d) :
    ps.errorTable.thresholds[k]'(by omega) -
        ps.errorTable.thresholds[k - 1]'(by omega) =
      noiseCount ps (k : ℤ) := by
  cases ps <;> simp only [ParameterSet.errorTable] at hkd ⊢
  all_goals interval_cases k <;>
    norm_num [noiseCount, ParameterSet.errorTable, ParameterSet.errorProbNumerators]
  all_goals rfl

private theorem div_seedHalf_two (x : ENNReal) :
    x / 2 ^ (lenChi - 1) / 2 = x / 2 ^ lenChi := by
  norm_num [lenChi]
  simp only [div_eq_mul_inv, mul_assoc]
  rw [← ENNReal.mul_inv (a := 32768) (b := 2) (by simp) (by simp)]
  norm_num

private theorem probSample_zero (ps : ParameterSet) :
    Pr{let r ← ($ᵗ (Bits lenChi) : ProbComp (Bits lenChi))}[
      Sample ps.errorTable r = 0] = (noiseCount ps 0 : ENNReal) / 2 ^ lenChi := by
  rw [prSample_eq_parts]
  rw [prEvent_uniformBool_fin (p := fun b t =>
    (if b then -(sampleMagnitude ps.errorTable t.val : ℤ)
      else (sampleMagnitude ps.errorTable t.val : ℤ)) = 0)]
  simp only [Bool.false_eq_true, ↓reduceIte, neg_eq_zero,
    Int.ofNat_eq_zero]
  rw [prSampleMagnitude_zero]
  have hzero : noiseCount ps 0 = 2 * (ps.errorTable.thresholds[0] + 1) := by
    simpa [noiseCount] using ps.errorTable_wellFormed.zero_eq.symm
  rw [hzero]
  push_cast
  rw [← two_mul, mul_div_assoc, mul_div_assoc, div_seedHalf_two, ← mul_div_assoc]

private theorem probSample_pos (ps : ParameterSet) (k : ℕ)
    (hk0 : 0 < k) (hkd : k ≤ ps.errorTable.d) :
    Pr{let r ← ($ᵗ (Bits lenChi) : ProbComp (Bits lenChi))}[
      Sample ps.errorTable r = (k : ℤ)] =
        (noiseCount ps (k : ℤ) : ENNReal) / 2 ^ lenChi := by
  rw [prSample_eq_parts]
  rw [prEvent_uniformBool_fin (p := fun b t =>
    (if b then -(sampleMagnitude ps.errorTable t.val : ℤ)
      else (sampleMagnitude ps.errorTable t.val : ℤ)) = (k : ℤ))]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_inj]
  have hneg : Pr{let t ← ($ᵗ (Fin (2 ^ (lenChi - 1))) :
      ProbComp (Fin (2 ^ (lenChi - 1))))}[
        -(sampleMagnitude ps.errorTable t.val : ℤ) = (k : ℤ)] = 0 := by
    apply prEvent_eq_zero_of_forall_not
    intro t ht
    have hkz : (0 : ℤ) < k := by exact_mod_cast hk0
    omega
  rw [prSampleMagnitude_pos ps k hk0 hkd, hneg]
  simp only [add_zero, threshold_diff_eq_noiseCount ps k hk0 hkd]
  exact div_seedHalf_two _

private theorem probSample_neg (ps : ParameterSet) (k : ℕ)
    (hk0 : 0 < k) (hkd : k ≤ ps.errorTable.d) :
    Pr{let r ← ($ᵗ (Bits lenChi) : ProbComp (Bits lenChi))}[
      Sample ps.errorTable r = -(k : ℤ)] =
        (noiseCount ps (-(k : ℤ)) : ENNReal) / 2 ^ lenChi := by
  rw [prSample_eq_parts]
  rw [prEvent_uniformBool_fin (p := fun b t =>
    (if b then -(sampleMagnitude ps.errorTable t.val : ℤ)
      else (sampleMagnitude ps.errorTable t.val : ℤ)) = -(k : ℤ))]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hpos : Pr{let t ← ($ᵗ (Fin (2 ^ (lenChi - 1))) :
      ProbComp (Fin (2 ^ (lenChi - 1))))}[
        (sampleMagnitude ps.errorTable t.val : ℤ) = -(k : ℤ)] = 0 := by
    apply prEvent_eq_zero_of_forall_not
    intro t ht
    have hkz : (0 : ℤ) < k := by exact_mod_cast hk0
    omega
  rw [hpos]
  simp only [neg_inj, Nat.cast_inj]
  rw [prSampleMagnitude_pos ps k hk0 hkd]
  simp only [zero_add, noiseCount_neg ps (k : ℤ)]
  rw [threshold_diff_eq_noiseCount ps k hk0 hkd]
  exact div_seedHalf_two _

theorem probOutput_sampleError (ps : ParameterSet) (z : ℤ) :
    Pr{let x ← sampleError ps}[x = z] =
      (noiseCount ps z : ENNReal) / 2 ^ lenChi := by
  rw [sampleError, prEvent_map]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · by_cases hn0 : n = 0
    · subst n
      exact probSample_zero ps
    · by_cases hnd : n ≤ ps.errorTable.d
      · exact probSample_pos ps n (Nat.pos_of_ne_zero hn0) hnd
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun r _ hr => by
          have := Sample_bounds ps.errorTable r; omega]
        simp [noiseCount, hnd]
  · by_cases hn0 : n = 0
    · subst n
      simpa using probSample_zero ps
    · by_cases hnd : n ≤ ps.errorTable.d
      · exact probSample_neg ps n (Nat.pos_of_ne_zero hn0) hnd
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun r _ hr => by
          have := Sample_bounds ps.errorTable r; omega]
        simp [noiseCount, hnd]

private def blockEquiv (rows cols width : ℕ) :
    Bits (rows * cols * width) ≃ Matrix (Fin rows) (Fin cols) (Bits width) where
  toFun := bitsToMatrixWith id rows cols
  invFun := matrixToBitsWith id
  left_inv := matrixToBitsWith_bitsToMatrixWith (fun _ => rfl) rows cols
  right_inv := bitsToMatrixWith_matrixToBitsWith (fun _ => rfl)

private theorem sampleIID_uniform {α : Type} [SampleableType α] (n : ℕ) :
    finiteLaw (ProbComp.sampleIID n ($ᵗ α)) = finiteLaw ($ᵗ (Fin n → α)) := by
  let : MeasurableSpace α := ⊤
  have h := evalDist_mOfFn_const_uniform n ($ᵗ α : ProbComp α)
    SampleableType.evalDist_uniformSample
  have he := EvalDistEq.of_evalDist_eq
    (h.trans (SampleableType.evalDist_uniformSample (β := Fin n → α)).symm)
  let : MeasurableSpace (Fin n → α) := ⊤
  exact he.evalDist_eq

private theorem sampleMatrix_uniform {α : Type} [SampleableType α] (rows cols : ℕ) :
    finiteLaw (ToVCVio.sampleMatrix rows cols ($ᵗ α)) =
      finiteLaw ($ᵗ (Matrix (Fin rows) (Fin cols) α)) := by
  let : MeasurableSpace (Fin cols → α) := ⊤
  let : MeasurableSpace (Matrix (Fin rows) (Fin cols) α) := MeasurableSpace.pi
  let : MeasurableSingletonClass (Matrix (Fin rows) (Fin cols) α) :=
    Pi.instMeasurableSingletonClass
  have h := evalDist_mOfFn_const_uniform rows (ProbComp.sampleIID cols ($ᵗ α))
    ((sampleIID_uniform (α := α) cols).trans SampleableType.evalDist_uniformSample)
  have he := EvalDistEq.of_evalDist_eq
    (h.trans (SampleableType.evalDist_uniformSample
      (β := Matrix (Fin rows) (Fin cols) α)).symm)
  let : MeasurableSpace (Matrix (Fin rows) (Fin cols) α) := ⊤
  let : MeasurableSpace (Fin rows → Fin cols → α) := ⊤
  exact he.evalDist_eq

theorem finiteLaw_SampleMatrix (ps : ParameterSet) (rows cols : ℕ) :
    finiteLaw
      (SampleMatrix ps.errorTable rows cols <$>
        ($ᵗ (Bits (rows * cols * lenChi)))) =
      finiteLaw (ToVCVio.sampleMatrix rows cols (sampleError ps)) := by
  let : MeasurableSpace (Matrix (Fin rows) (Fin cols) (Bits lenChi)) := ⊤
  have hb : finiteLaw
      ((blockEquiv rows cols lenChi) <$> ($ᵗ Bits (rows * cols * lenChi))) =
        finiteLaw ($ᵗ Matrix (Fin rows) (Fin cols) (Bits lenChi)) :=
    (SampleableType.map_uniformSample_evalDistEq_of_bijective
      (blockEquiv rows cols lenChi).bijective).evalDist_eq
  have hu := sampleMatrix_uniform (α := Bits lenChi) rows cols
  have hm := finiteLaw_map_congr (hb.trans hu.symm)
    (fun M : Matrix (Fin rows) (Fin cols) (Bits lenChi) =>
      M.map (Sample ps.errorTable))
  rw [Functor.map_map] at hm
  exact hm.trans
    (finiteLaw_sampleMatrix_map rows cols ($ᵗ (Bits lenChi)) (Sample ps.errorTable))

end FrodoKEM
