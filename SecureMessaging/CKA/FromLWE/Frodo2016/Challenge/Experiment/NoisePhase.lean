/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.ExperimentLaw

/-!
# The historical Challenge experiment

This file completes the comparison between one actual Challenge entry-mismatch
probability and the exact modular phase ramp.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA

theorem Frodo2016.Challenge.Experiment.Internal.challengeFailureRamp_le_one (z : ℤ) :
    challengeFailureRamp z ≤ 1 := by
  unfold challengeFailureRamp
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
  simpa only [one_mul] using
    (min_le_left (512 : ℝ≥0∞)
      ((modularDistance challengeParams (z : Scalar challengeParams) 0 : ℝ≥0∞) - 256))

open Frodo2016.Challenge.Experiment.Internal

theorem Frodo2016.Challenge.Experiment.Internal.cast_challengeEntryNoiseInt
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    (challengeEntryNoiseInt c t : Scalar challengeParams) =
      (t.2.secret * t.1.error - t.2.error * t.1.secret + t.2.extra) c.1 c.2 := by
  simp only [challengeEntryNoiseInt, Int.cast_add, Int.cast_sub, Int.cast_sum,
    Int.cast_mul, ZMod.coe_valMinAbs, Matrix.add_apply, Matrix.sub_apply,
    Matrix.mul_apply]

private theorem entryMismatch_imp_large_int_of_cast
    (p : Params) (hp : p.WellFormed)
    (ik : InitKey p) (r : SendACoins p)
    (c : Fin p.nbar × Fin p.nbar) (z : ℤ)
    (hz :
      (z : Scalar p) =
        (r.secret * ik.error - r.error * ik.secret + r.extra) c.1 c.2)
    (hmismatch :
      reconcileScalar p
          (((r.secret * ik.baseMatrix + r.error) * ik.secret) c.1 c.2)
          (hintScalar p
            ((r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)
              c.1 c.2)) ≠
        extractScalar p
          ((r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)
            c.1 c.2)) :
    2 ^ (p.discardBits - 2) ≤ z.natAbs := by
  let v := r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra
  let w := (r.secret * ik.baseMatrix + r.error) * ik.secret
  have hlarge :
      2 ^ (p.discardBits - 2) ≤ modularDistance p (w c.1 c.2) (v c.1 c.2) := by
    by_contra hclose
    apply hmismatch
    apply reconcileScalar_eq_extractScalar_of_modularDistance_lt
      p hp
    exact lt_of_not_ge hclose
  have hvalue := congrArg (fun m => m c.1 c.2)
    (firstExchangeValue_sub_eq_noise p ik r)
  simp only [Matrix.sub_apply] at hvalue
  have hnoise : v c.1 c.2 - w c.1 c.2 = (z : Scalar p) :=
    hvalue.trans hz.symm
  have hdistance :
      modularDistance p (w c.1 c.2) (v c.1 c.2) =
        modularDistance p (z : Scalar p) 0 := by
    calc
      modularDistance p (w c.1 c.2) (v c.1 c.2) =
          modularDistance p (v c.1 c.2 - w c.1 c.2) 0 := by
        unfold modularDistance
        simp only [sub_zero, zero_sub, neg_sub]
        rw [min_comm]
      _ = _ := by rw [hnoise]
  rw [hdistance] at hlarge
  exact le_trans hlarge
    (modularDistance_intCast_zero_le_natAbs p z)

/-- Every actual Challenge entry mismatch has centered integer magnitude at least `256`. -/
theorem challengeEntryMismatch_imp_large_int
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    challengeEntryMismatch c t →
      256 ≤ (challengeEntryNoiseInt c t).natAbs := by
  intro hmismatch
  have hmismatch' :
      reconcileScalar challengeParams
          (((t.2.secret * t.1.baseMatrix + t.2.error) * t.1.secret) c.1 c.2)
          (hintScalar challengeParams
            ((t.2.secret * (t.1.baseMatrix * t.1.secret + t.1.error) + t.2.extra)
              c.1 c.2)) ≠
        extractScalar challengeParams
          ((t.2.secret * (t.1.baseMatrix * t.1.secret + t.1.error) + t.2.extra)
            c.1 c.2) := by
    exact hmismatch
  have hlarge := entryMismatch_imp_large_int_of_cast
    challengeParams challengeParams_wellFormed t.1 t.2 c
    (challengeEntryNoiseInt c t) (cast_challengeEntryNoiseInt c t) hmismatch'
  norm_num [challengeParams, Params.discardBits] at hlarge
  exact hlarge

/-- Samples the Challenge secret and error matrices with a zero public base matrix. -/
def Frodo2016.Challenge.Experiment.Internal.challengeNoiseCoinsExp :
    ProbComp (InitKey challengeParams × SendACoins challengeParams) := do
  let s0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let e0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let s1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let e1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let extra ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
  pure (({ baseMatrix := 0, secret := s0, error := e0 } : InitKey challengeParams),
    ({ secret := s1, error := e1, extra := extra } : SendACoins challengeParams))

/-- Installs a public base matrix into sampled Challenge noise coins. -/
def Frodo2016.Challenge.Experiment.Internal.challengeWithBase
    (a : BaseMatrix challengeParams)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    InitKey challengeParams × SendACoins challengeParams :=
  ({ t.1 with baseMatrix := a }, t.2)

/-- The all-even secret-row or secret-column exception at a Challenge coordinate. -/
def Frodo2016.Challenge.Experiment.Internal.challengeEntryBad
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) : Prop :=
  (∀ k : Fin challengeParams.n, Even (t.2.secret c.1 k).val) ∨
  (∀ k : Fin challengeParams.n, Even (t.1.secret k c.2).val)

theorem Frodo2016.Challenge.Experiment.Internal.evalDist_challengeCoinsExp_noiseFirst :
    finiteLaw challengeCoinsExp =
      finiteLaw
        (do
          let t ← challengeNoiseCoinsExp
          let a ← ($ᵗ (BaseMatrix challengeParams) :
            ProbComp (BaseMatrix challengeParams))
          return challengeWithBase a t) := by
  simp only [challengeCoinsExp, challengeNoiseCoinsExp, challengeWithBase, initKeyGen,
    sampleSendACoins, bind_assoc, pure_bind]
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar)]
  refine evalDist_bind_congr'
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar)]
  refine evalDist_bind_congr'
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
    (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n)]
  refine evalDist_bind_congr'
    (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
    (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n)]
  refine evalDist_bind_congr'
    (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
    (sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar)]

private theorem even_val_intCast_iff_of_mem_d1_support
    (z : ℤ) (hz : z ∈ support d1IntSampler) :
    Even ((z : Scalar challengeParams).val) ↔ Even z := by
  rw [support_d1IntSampler] at hz
  simp only [Set.mem_Icc] at hz
  have hlo : (-3 : ℤ) ≤ z := hz.1
  have hhi : z ≤ 3 := hz.2
  change Even ((z : ZMod 2048).val) ↔ Even z
  interval_cases z <;> decide

private theorem probEvent_even_d1Sampler :
    Pr{let x ← d1Sampler}[Even x.val] =
      1 / (2 : ℝ≥0∞) := by
  rw [d1Sampler, prEvent_map]
  calc
    Pr{let z ← d1IntSampler}[Even ((z : Scalar challengeParams).val)] =
        Pr{let z ← d1IntSampler}[Even z] := by
      apply probEvent_congr'
      · exact fun z hz => even_val_intCast_iff_of_mem_d1_support z hz
      · rfl
    _ = 1 / (2 : ℝ≥0∞) := by
      rw [OracleComp.prEvent_eq_tsum_ite, tsum_eq_sum (s := Finset.Icc (-3 : ℤ) 3)]
      · have hIcc : Finset.Icc (-3 : ℤ) 3 = {-3, -2, -1, 0, 1, 2, 3} := by
          ext z
          simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
          omega
        rw [hIcc]
        have hodd : ¬Even (3 : ℤ) := by decide
        norm_num [hodd, probOutput_d1IntSampler, d1Weight]
        rw [← ENNReal.add_div, ← ENNReal.add_div]
        rw [← one_div]
        apply (ENNReal.div_eq_div_iff (a := 2) (b := 256)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
        norm_num
      · intro z hz
        have hz' : z ∉ support d1IntSampler := by
          rw [support_d1IntSampler]
          simpa [Set.mem_Icc] using hz
        rw [(prEvent_eq_zero_of_not_mem_support _) hz']
        split <;> simp

private theorem probEvent_d1_vector_all_even (n : ℕ) :
    Pr{let v ← ProbComp.sampleIID n d1Sampler}[∀ k, Even (v k).val] =
        (1 / (2 : ℝ≥0∞)) ^ n := by
  change Pr{let v ← Fin.mOfFn n fun _ => d1Sampler}[∀ k, Even (v k).val] = _
  calc
    Pr{let v ← Fin.mOfFn n fun _ => d1Sampler}[∀ k, Even (v k).val] =
        ∏ _ : Fin n, Pr{let x ← d1Sampler}[Even x.val] :=
      prEvent_forall_coord_mOfFn n (fun _ => d1Sampler)
        (fun _ x => Even x.val)
    _ = (1 / (2 : ℝ≥0∞)) ^ n := by
      simp only [probEvent_even_d1Sampler, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]

private theorem evalDist_challengeMatrix_col
    (j : Fin challengeParams.nbar) :
    finiteLaw
        (do
          let m ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
          pure fun k => m k j) =
      finiteLaw (ProbComp.sampleIID challengeParams.n d1Sampler) :=
  ChallengeExperimentLaw.evalDist_sampleMatrix_col_bind d1Sampler probFailure_eq_zero
    challengeParams.n challengeParams.nbar j

private theorem evalDist_challengeMatrix_row
    (i : Fin challengeParams.nbar) :
    finiteLaw
        (do
          let m ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
          pure (m i)) =
      finiteLaw (ProbComp.sampleIID challengeParams.n d1Sampler) :=
  ChallengeExperimentLaw.evalDist_sampleMatrix_row_bind d1Sampler probFailure_eq_zero
    challengeParams.nbar challengeParams.n i

private theorem evalDist_noiseCoins_initSecretCol
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    finiteLaw
        ((fun t : InitKey challengeParams × SendACoins challengeParams =>
          fun k => t.1.secret k c.2) <$> challengeNoiseCoinsExp) =
      finiteLaw (ProbComp.sampleIID challengeParams.n d1Sampler) := by
  simp only [challengeNoiseCoinsExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    finiteLaw
          (do
            let s0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
            let _ ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
            pure fun k => s0 k c.2) =
        finiteLaw
          (do
            let s0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
            pure fun k => s0 k c.2) := by
      refine evalDist_bind_congr'
        (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) fun _ => ?_
      rw [lweCKA.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) probFailure_eq_zero]
      rw [lweCKA.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) probFailure_eq_zero]
      rw [lweCKA.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) probFailure_eq_zero]
      rw [lweCKA.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar) probFailure_eq_zero]
    _ = finiteLaw (ProbComp.sampleIID challengeParams.n d1Sampler) := by
      exact evalDist_challengeMatrix_col c.2

private theorem evalDist_noiseCoins_sendSecretRow
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    finiteLaw
        ((fun t : InitKey challengeParams × SendACoins challengeParams =>
          t.2.secret c.1) <$> challengeNoiseCoinsExp) =
      finiteLaw (ProbComp.sampleIID challengeParams.n d1Sampler) := by
  simp only [challengeNoiseCoinsExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  rw [lweCKA.evalDist_bind_const_neverFails
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) probFailure_eq_zero]
  rw [lweCKA.evalDist_bind_const_neverFails
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) probFailure_eq_zero]
  calc
    finiteLaw
          (do
            let s1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
            pure (s1 c.1)) =
        finiteLaw
          (do
            let s1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            pure (s1 c.1)) := by
      refine evalDist_bind_congr'
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) fun _ => ?_
      rw [lweCKA.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) probFailure_eq_zero]
      rw [lweCKA.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar) probFailure_eq_zero]
    _ = finiteLaw (ProbComp.sampleIID challengeParams.n d1Sampler) := by
      exact evalDist_challengeMatrix_row c.1

theorem Frodo2016.Challenge.Experiment.Internal.probEvent_challengeEntryBad_le
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    Pr{let x ← challengeNoiseCoinsExp}[(challengeEntryBad c) x] ≤
      1 / (2 : ℝ≥0∞) ^ 351 := by
  let p := fun t : InitKey challengeParams × SendACoins challengeParams =>
    ∀ k : Fin challengeParams.n, Even (t.2.secret c.1 k).val
  let q := fun t : InitKey challengeParams × SendACoins challengeParams =>
    ∀ k : Fin challengeParams.n, Even (t.1.secret k c.2).val
  have hp : Pr{let x ← challengeNoiseCoinsExp}[p x] = (1 / (2 : ℝ≥0∞)) ^ 352 := by
    calc
      Pr{let x ← challengeNoiseCoinsExp}[p x] =
          Pr{let v ← ((fun t : InitKey challengeParams × SendACoins challengeParams =>
              t.2.secret c.1) <$> challengeNoiseCoinsExp)}[∀ k, Even (v k).val] := by
        rw [prEvent_map]
      _ = Pr{let v ← ProbComp.sampleIID challengeParams.n d1Sampler}[∀ k, Even (v k).val] := by
        simp only [probEvent_def, evalDist_noiseCoins_sendSecretRow c]
      _ = (1 / (2 : ℝ≥0∞)) ^ 352 := by
        simpa only [challengeParams] using probEvent_d1_vector_all_even 352
  have hq : Pr{let x ← challengeNoiseCoinsExp}[q x] = (1 / (2 : ℝ≥0∞)) ^ 352 := by
    calc
      Pr{let x ← challengeNoiseCoinsExp}[q x] =
          Pr{let v ← ((fun t : InitKey challengeParams × SendACoins challengeParams =>
              fun k => t.1.secret k c.2) <$> challengeNoiseCoinsExp)}[∀ k, Even (v k).val] := by
        rw [prEvent_map]
      _ = Pr{let v ← ProbComp.sampleIID challengeParams.n d1Sampler}[∀ k, Even (v k).val] := by
        simp only [probEvent_def, evalDist_noiseCoins_initSecretCol c]
      _ = (1 / (2 : ℝ≥0∞)) ^ 352 := by
        simpa only [challengeParams] using probEvent_d1_vector_all_even 352
  change Pr{let t ← challengeNoiseCoinsExp}[p t ∨ q t] ≤ _
  calc
    Pr{let t ← challengeNoiseCoinsExp}[p t ∨ q t] ≤
        Pr{let x ← challengeNoiseCoinsExp}[p x] + Pr{let x ← challengeNoiseCoinsExp}[q x] :=
      prEvent_or_le challengeNoiseCoinsExp p q
    _ = (1 / (2 : ℝ≥0∞)) ^ 352 + (1 / (2 : ℝ≥0∞)) ^ 352 := by rw [hp, hq]
    _ = 1 / (2 : ℝ≥0∞) ^ 351 := by
      simp only [one_div, ENNReal.inv_pow]
      rw [show 352 = 351 + 1 by norm_num, pow_succ]
      calc
        (2 : ℝ≥0∞)⁻¹ ^ 351 * 2⁻¹ + (2 : ℝ≥0∞)⁻¹ ^ 351 * 2⁻¹ =
          (2 : ℝ≥0∞)⁻¹ ^ 351 * (2⁻¹ + 2⁻¹) := by rw [mul_add]
        _ = (2 : ℝ≥0∞)⁻¹ ^ 351 := by
          rw [ENNReal.inv_two_add_inv_two, mul_one]

private def challengeScalarPhaseEquiv :
    Scalar challengeParams ≃ Fin 512 × Fin 4 := by
  change ZMod 2048 ≃ Fin 512 × Fin 4
  exact (ZMod.finEquiv 2048).toEquiv.symm |>.trans
    ((finProdFinEquiv : Fin 4 × Fin 512 ≃ Fin 2048).symm |>.trans
      (Equiv.prodComm (Fin 4) (Fin 512)))

private theorem challengeScalarPhaseEquiv_fst
    (v : Scalar challengeParams) :
    (challengeScalarPhaseEquiv v).1.val = v.val % 512 := by
  rfl

private theorem evalDist_uniform_challengePhase :
    finiteLaw
        ((fun v : Scalar challengeParams => (challengeScalarPhaseEquiv v).1) <$>
          ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))) =
      finiteLaw ($ᵗ (Fin 512) : ProbComp (Fin 512)) := by
  calc
    finiteLaw
          ((fun v : Scalar challengeParams => (challengeScalarPhaseEquiv v).1) <$>
            ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))) =
        finiteLaw
          (Prod.fst <$>
            (challengeScalarPhaseEquiv <$>
              ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)))) := by
      rw [Functor.map_map]
    _ = finiteLaw
          (Prod.fst <$> ($ᵗ (Fin 512 × Fin 4) : ProbComp (Fin 512 × Fin 4))) := by
      exact finiteLaw_map_congr
        (evalDist_map_bijective_uniform_cross
          (α := Scalar challengeParams) challengeScalarPhaseEquiv
          challengeScalarPhaseEquiv.bijective) Prod.fst
    _ = finiteLaw ($ᵗ (Fin 512) : ProbComp (Fin 512)) :=
      evalDist_map_fst_uniformSample_prod

theorem
    Frodo2016.Challenge.Experiment.Internal.probEvent_uniform_phase_eq_challengeFailureRamp
    (z : ℤ) :
    Pr{let v ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))}[1024 ≤
        ((((v.val % 512 + 256 : ℕ) : Scalar challengeParams) -
          (z : Scalar challengeParams)).val)] =
        challengeFailureRamp z := by
  let phaseBad := fun u : ℕ =>
    1024 ≤
      ((((u + 256 : ℕ) : Scalar challengeParams) -
        (z : Scalar challengeParams)).val)
  have hcard :
      ((Finset.univ : Finset (Fin 512)).filter fun u => phaseBad u.val).card =
        ((Finset.range 512).filter phaseBad).card := by
    apply Finset.card_bij (fun u _ => u.val)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 u.isLt, hu⟩
    · intro u₁ _ u₂ _ huv
      exact Fin.ext huv
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      exact ⟨⟨x, hx.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ,
        true_and, hx.2], rfl⟩
  have hphaseCount :
      ((Finset.range 512).filter phaseBad).card =
        min 512
          (modularDistance challengeParams (z : Scalar challengeParams) 0 - 256) := by
    dsimp only [phaseBad]
    convert card_reconciliationFailurePhases challengeParams
      challengeParams_wellFormed (z : Scalar challengeParams) using 1 <;>
        norm_num [challengeParams, Params.halfWidth, Params.blockWidth,
          Params.discardBits]
  calc
    Pr{let v ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))}[phaseBad (v.val
        % 512)] =
        Pr{let u ← ((fun v : Scalar challengeParams => (challengeScalarPhaseEquiv v).1) <$>
            ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)))}[phaseBad u.val] :=
                by
      rw [prEvent_map]
      apply probEvent_congr'
      · intro v _
        rw [challengeScalarPhaseEquiv_fst]
      · rfl
    _ = Pr{let u ← ($ᵗ (Fin 512) : ProbComp (Fin 512))}[phaseBad u.val] := by
      simp only [probEvent_def, evalDist_uniform_challengePhase]
    _ = (((Finset.univ : Finset (Fin 512)).filter fun u => phaseBad u.val).card :
          ℝ≥0∞) / 512 := by
      rw [SampleableType.prEvent_uniformSample]
      change (((Finset.univ : Finset (Fin 512)).filter fun u => phaseBad u.val).card :
        ℝ≥0∞) / 512 = _
      rfl
    _ = challengeFailureRamp z := by
      rw [hcard, hphaseCount]
      unfold challengeFailureRamp
      let d := modularDistance challengeParams (z : Scalar challengeParams) 0
      change ((min 512 (d - 256) : ℕ) : ℝ≥0∞) / 512 =
        min (512 : ℝ≥0∞) ((d : ℝ≥0∞) - 256) / 512
      apply congrArg (fun x : ℝ≥0∞ => x / 512)
      calc
        ((min 512 (d - 256) : ℕ) : ℝ≥0∞) =
            min (512 : ℝ≥0∞) ((d - 256 : ℕ) : ℝ≥0∞) :=
          Monotone.map_min Nat.mono_cast
        _ = min (512 : ℝ≥0∞) ((d : ℝ≥0∞) - 256) := by
          rw [ENNReal.natCast_sub]
          norm_num

end lweCKA
