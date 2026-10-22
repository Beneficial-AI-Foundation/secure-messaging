/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ChallengeExperimentLaw
import SecureMessaging.CKA.FromLWE.ConcreteCorrectness
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# The historical Challenge experiment

This file completes the comparison between one actual Challenge entry-mismatch
probability and the exact modular phase ramp.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

private theorem challengeFailureRamp_le_one (z : ℤ) :
    challengeFailureRamp z ≤ 1 := by
  unfold challengeFailureRamp
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
  simpa only [one_mul] using
    (min_le_left (512 : ℝ≥0∞)
      ((modularDistance challengeParams (z : Scalar challengeParams) 0 : ℝ≥0∞) - 256))

private theorem cast_challengeEntryNoiseInt
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

private def challengeNoiseCoinsExp :
    ProbComp (InitKey challengeParams × SendACoins challengeParams) := do
  let s0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let e0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let s1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let e1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let extra ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
  pure (({ baseMatrix := 0, secret := s0, error := e0 } : InitKey challengeParams),
    ({ secret := s1, error := e1, extra := extra } : SendACoins challengeParams))

private def challengeWithBase
    (a : BaseMatrix challengeParams)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    InitKey challengeParams × SendACoins challengeParams :=
  ({ t.1 with baseMatrix := a }, t.2)

private def challengeEntryBad
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) : Prop :=
  (∀ k : Fin challengeParams.n, Even (t.2.secret c.1 k).val) ∨
  (∀ k : Fin challengeParams.n, Even (t.1.secret k c.2).val)

private theorem evalDist_challengeCoinsExp_noiseFirst :
    evalDist challengeCoinsExp =
      evalDist
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
    Pr[fun x : Scalar challengeParams => Even x.val | d1Sampler] =
      1 / (2 : ℝ≥0∞) := by
  rw [d1Sampler, probEvent_map]
  calc
    Pr[fun z : ℤ => Even ((z : Scalar challengeParams).val) | d1IntSampler] =
        Pr[fun z : ℤ => Even z | d1IntSampler] := by
      apply probEvent_congr'
      · exact fun z hz => even_val_intCast_iff_of_mem_d1_support z hz
      · rfl
    _ = 1 / (2 : ℝ≥0∞) := by
      rw [probEvent_eq_tsum_ite, tsum_eq_sum (s := Finset.Icc (-3 : ℤ) 3)]
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
        rw [probOutput_eq_zero_of_not_mem_support hz']
        split <;> simp

private theorem probEvent_d1_vector_all_even (n : ℕ) :
    Pr[fun v : Fin n → Scalar challengeParams =>
      ∀ k, Even (v k).val | ProbComp.sampleIID n d1Sampler] =
        (1 / (2 : ℝ≥0∞)) ^ n := by
  change Pr[fun v : Fin n → Scalar challengeParams =>
      ∀ k, Even (v k).val | Fin.mOfFn n fun _ => d1Sampler] = _
  calc
    Pr[fun v : Fin n → Scalar challengeParams => ∀ k, Even (v k).val |
        Fin.mOfFn n fun _ => d1Sampler] =
        ∏ _ : Fin n, Pr[fun x : Scalar challengeParams => Even x.val | d1Sampler] :=
      probEvent_forall_coord_mOfFn n (fun _ => d1Sampler)
        (fun _ x => Even x.val)
    _ = (1 / (2 : ℝ≥0∞)) ^ n := by
      simp only [probEvent_even_d1Sampler, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]

private theorem evalDist_challengeMatrix_col
    (j : Fin challengeParams.nbar) :
    evalDist
        (do
          let m ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
          pure fun k => m k j) =
      evalDist (ProbComp.sampleIID challengeParams.n d1Sampler) :=
  ChallengeExperimentLaw.evalDist_sampleMatrix_col_bind d1Sampler probFailure_eq_zero
    challengeParams.n challengeParams.nbar j

private theorem evalDist_challengeMatrix_row
    (i : Fin challengeParams.nbar) :
    evalDist
        (do
          let m ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
          pure (m i)) =
      evalDist (ProbComp.sampleIID challengeParams.n d1Sampler) :=
  ChallengeExperimentLaw.evalDist_sampleMatrix_row_bind d1Sampler probFailure_eq_zero
    challengeParams.nbar challengeParams.n i

private theorem evalDist_noiseCoins_initSecretCol
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    evalDist
        ((fun t : InitKey challengeParams × SendACoins challengeParams =>
          fun k => t.1.secret k c.2) <$> challengeNoiseCoinsExp) =
      evalDist (ProbComp.sampleIID challengeParams.n d1Sampler) := by
  simp only [challengeNoiseCoinsExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    evalDist
          (do
            let s0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
            let _ ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
            pure fun k => s0 k c.2) =
        evalDist
          (do
            let s0 ← sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
            pure fun k => s0 k c.2) := by
      refine evalDist_bind_congr'
        (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) fun _ => ?_
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) probFailure_eq_zero]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) probFailure_eq_zero]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) probFailure_eq_zero]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar) probFailure_eq_zero]
    _ = evalDist (ProbComp.sampleIID challengeParams.n d1Sampler) := by
      exact evalDist_challengeMatrix_col c.2

private theorem evalDist_noiseCoins_sendSecretRow
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    evalDist
        ((fun t : InitKey challengeParams × SendACoins challengeParams =>
          t.2.secret c.1) <$> challengeNoiseCoinsExp) =
      evalDist (ProbComp.sampleIID challengeParams.n d1Sampler) := by
  simp only [challengeNoiseCoinsExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) probFailure_eq_zero]
  rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    (sampleMatrix d1Sampler challengeParams.n challengeParams.nbar) probFailure_eq_zero]
  calc
    evalDist
          (do
            let s1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            let _ ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
            pure (s1 c.1)) =
        evalDist
          (do
            let s1 ← sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
            pure (s1 c.1)) := by
      refine evalDist_bind_congr'
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) fun _ => ?_
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.n) probFailure_eq_zero]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar) probFailure_eq_zero]
    _ = evalDist (ProbComp.sampleIID challengeParams.n d1Sampler) := by
      exact evalDist_challengeMatrix_row c.1

private theorem probEvent_challengeEntryBad_le
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    Pr[challengeEntryBad c | challengeNoiseCoinsExp] ≤
      1 / (2 : ℝ≥0∞) ^ 351 := by
  let p := fun t : InitKey challengeParams × SendACoins challengeParams =>
    ∀ k : Fin challengeParams.n, Even (t.2.secret c.1 k).val
  let q := fun t : InitKey challengeParams × SendACoins challengeParams =>
    ∀ k : Fin challengeParams.n, Even (t.1.secret k c.2).val
  have hp : Pr[p | challengeNoiseCoinsExp] = (1 / (2 : ℝ≥0∞)) ^ 352 := by
    calc
      Pr[p | challengeNoiseCoinsExp] =
          Pr[fun v : Fin challengeParams.n → Scalar challengeParams =>
              ∀ k, Even (v k).val |
            (fun t : InitKey challengeParams × SendACoins challengeParams =>
              t.2.secret c.1) <$> challengeNoiseCoinsExp] := by
        rw [probEvent_map]
        rfl
      _ = Pr[fun v : Fin challengeParams.n → Scalar challengeParams =>
              ∀ k, Even (v k).val |
            ProbComp.sampleIID challengeParams.n d1Sampler] := by
        simp only [probEvent_def, evalDist_noiseCoins_sendSecretRow c]
      _ = (1 / (2 : ℝ≥0∞)) ^ 352 := by
        simpa only [challengeParams] using probEvent_d1_vector_all_even 352
  have hq : Pr[q | challengeNoiseCoinsExp] = (1 / (2 : ℝ≥0∞)) ^ 352 := by
    calc
      Pr[q | challengeNoiseCoinsExp] =
          Pr[fun v : Fin challengeParams.n → Scalar challengeParams =>
              ∀ k, Even (v k).val |
            (fun t : InitKey challengeParams × SendACoins challengeParams =>
              fun k => t.1.secret k c.2) <$> challengeNoiseCoinsExp] := by
        rw [probEvent_map]
        rfl
      _ = Pr[fun v : Fin challengeParams.n → Scalar challengeParams =>
              ∀ k, Even (v k).val |
            ProbComp.sampleIID challengeParams.n d1Sampler] := by
        simp only [probEvent_def, evalDist_noiseCoins_initSecretCol c]
      _ = (1 / (2 : ℝ≥0∞)) ^ 352 := by
        simpa only [challengeParams] using probEvent_d1_vector_all_even 352
  change Pr[fun t => p t ∨ q t | challengeNoiseCoinsExp] ≤ _
  calc
    Pr[fun t => p t ∨ q t | challengeNoiseCoinsExp] ≤
        Pr[p | challengeNoiseCoinsExp] + Pr[q | challengeNoiseCoinsExp] :=
      probEvent_or_le challengeNoiseCoinsExp p q
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
    evalDist
        ((fun v : Scalar challengeParams => (challengeScalarPhaseEquiv v).1) <$>
          ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))) =
      evalDist ($ᵗ (Fin 512) : ProbComp (Fin 512)) := by
  calc
    evalDist
          ((fun v : Scalar challengeParams => (challengeScalarPhaseEquiv v).1) <$>
            ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))) =
        evalDist
          (Prod.fst <$>
            (challengeScalarPhaseEquiv <$>
              ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)))) := by
      rw [Functor.map_map]
    _ = evalDist
          (Prod.fst <$> ($ᵗ (Fin 512 × Fin 4) : ProbComp (Fin 512 × Fin 4))) := by
      exact evalDist_map_eq_of_evalDist_eq
        (evalDist_map_bijective_uniform_cross
          (α := Scalar challengeParams) challengeScalarPhaseEquiv
          challengeScalarPhaseEquiv.bijective) Prod.fst
    _ = evalDist ($ᵗ (Fin 512) : ProbComp (Fin 512)) :=
      evalDist_map_fst_uniformSample_prod

private theorem probEvent_uniform_phase_eq_challengeFailureRamp (z : ℤ) :
    Pr[fun v : Scalar challengeParams =>
      1024 ≤
        ((((v.val % 512 + 256 : ℕ) : Scalar challengeParams) -
          (z : Scalar challengeParams)).val) |
      ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))] =
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
    Pr[fun v : Scalar challengeParams => phaseBad (v.val % 512) |
        ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))] =
        Pr[fun u : Fin 512 => phaseBad u.val |
          (fun v : Scalar challengeParams => (challengeScalarPhaseEquiv v).1) <$>
            ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))] := by
      rw [probEvent_map]
      apply probEvent_congr'
      · intro v _
        simp only [Function.comp_apply]
        rw [challengeScalarPhaseEquiv_fst]
      · rfl
    _ = Pr[fun u : Fin 512 => phaseBad u.val |
          ($ᵗ (Fin 512) : ProbComp (Fin 512))] := by
      simp only [probEvent_def, evalDist_uniform_challengePhase]
    _ = (((Finset.univ : Finset (Fin 512)).filter fun u => phaseBad u.val).card :
          ℝ≥0∞) / 512 := by
      rw [probEvent_uniformSample]
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

private def challengeSenderScalar
    (p : Params)
    (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p)
    (a : BaseMatrix p) : Scalar p :=
  (t.2.secret * (a * t.1.secret + t.1.error) + t.2.extra) c.1 c.2

private def challengeBaseReplace
    (p : Params) (a : BaseMatrix p) (k l : Fin p.n)
    (r : Fin p.n → Scalar p) (x : Scalar p) : BaseMatrix p :=
  Function.update a k (Function.update r l x)

private theorem sum_update_mul
    {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r s : ι → R) (l : ι) (x : R) :
    (∑ j : ι, Function.update r l x j * s j) =
      (∑ j ∈ (Finset.univ : Finset ι).erase l, r j * s j) + x * s l := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ l)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]
  · rw [Function.update_self]

private theorem double_sum_update_affine
    {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    (left right err : ι → R) (a : ι → ι → R) (k l : ι)
    (r : ι → R) (x : R) :
    (∑ i : ι, left i *
      ((∑ j : ι, Function.update a k (Function.update r l x) i j * right j) +
        err i)) =
      (left k * right l) * x +
        ∑ i : ι, left i *
          ((∑ j : ι,
            Function.update a k (Function.update r l 0) i j * right j) + err i) := by
  let rest := ∑ i ∈ (Finset.univ : Finset ι).erase k,
    left i * ((∑ j : ι, a i j * right j) + err i)
  have houter (y : R) :
      (∑ i : ι, left i *
        ((∑ j : ι, Function.update a k (Function.update r l y) i j * right j) +
          err i)) =
        rest + left k *
          ((∑ j : ι, Function.update r l y j * right j) + err k) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Function.update_apply, if_neg (Finset.ne_of_mem_erase hi)]
    · simp only [Function.update_self]
  rw [houter x, houter 0, sum_update_mul r right l x,
    sum_update_mul r right l 0]
  ring

private theorem challengeSenderScalar_replace_affine
    (p : Params)
    (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p)
    (a : BaseMatrix p) (k l : Fin p.n)
    (r : Fin p.n → Scalar p) (x : Scalar p) :
    challengeSenderScalar p c t (challengeBaseReplace p a k l r x) =
      (t.2.secret c.1 k * t.1.secret l c.2) * x +
        challengeSenderScalar p c t (challengeBaseReplace p a k l r 0) := by
  classical
  change
    (∑ i : Fin p.n, t.2.secret c.1 i *
      ((∑ j : Fin p.n,
        Function.update a k (Function.update r l x) i j * t.1.secret j c.2) +
          t.1.error i c.2)) + t.2.extra c.1 c.2 =
      (t.2.secret c.1 k * t.1.secret l c.2) * x +
        ((∑ i : Fin p.n, t.2.secret c.1 i *
          ((∑ j : Fin p.n,
            Function.update a k (Function.update r l 0) i j * t.1.secret j c.2) +
              t.1.error i c.2)) + t.2.extra c.1 c.2)
  rw [double_sum_update_affine
    (fun i => t.2.secret c.1 i) (fun j => t.1.secret j c.2)
    (fun i => t.1.error i c.2) a k l r x]
  rw [add_assoc]

private theorem isUnit_of_not_even_val
    (x : Scalar challengeParams) (hx : ¬Even x.val) : IsUnit x := by
  rw [← ZMod.natCast_zmod_val x]
  change IsUnit ((x.val : ℕ) : ZMod (2 ^ 11))
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by norm_num)).2
  simpa only [even_iff_two_dvd] using hx

private theorem evalDist_uniform_update_map
    {D R α : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) (ψ : (D → R) → α) :
    evalDist
        (do
          let u ← ($ᵗ R : ProbComp R)
          let g ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (ψ (Function.update g t u))) =
      evalDist (ψ <$> ($ᵗ (D → R) : ProbComp (D → R))) := by
  rw [map_eq_bind_pure_comp]
  exact OracleComp.evalDist_uniformSample_bind_update_map t ψ

private theorem evalDist_uniform_update_nested_map
    {D E R α : Type} [Finite D] [DecidableEq D] [Finite (E → R)]
    [Nonempty (E → R)] [SampleableType (E → R)] [SampleableType (D → E → R)]
    (t : D) (ψ : (D → E → R) → α) :
    evalDist
        (do
          let u ← ($ᵗ (E → R) : ProbComp (E → R))
          let g ← ($ᵗ (D → E → R) : ProbComp (D → E → R))
          pure (ψ (Function.update g t u))) =
      evalDist (ψ <$> ($ᵗ (D → E → R) : ProbComp (D → E → R))) := by
  exact evalDist_uniform_update_map (D := D) (R := E → R) (α := α) t ψ

private theorem evalDist_uniform_update_bind
    {D R α : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) (ψ : (D → R) → α) :
    evalDist
        (do
          let u ← ($ᵗ R : ProbComp R)
          let g ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (ψ (Function.update g t u))) =
      evalDist
        (do
          let g ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (ψ g)) := by
  exact OracleComp.evalDist_uniformSample_bind_update_map t ψ

private theorem evalDist_challengeBase_update_row
    {α : Type} (k : Fin challengeParams.n)
    (ψ : BaseMatrix challengeParams → α) :
    evalDist
        (do
          let r ← ($ᵗ (Fin challengeParams.n → Scalar challengeParams) :
            ProbComp (Fin challengeParams.n → Scalar challengeParams))
          let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
          pure (ψ (Function.update a k r))) =
      evalDist
        (ψ <$> ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))) := by
  exact @evalDist_uniform_update_nested_map
    (Fin challengeParams.n)
    (Fin challengeParams.n)
    (Scalar challengeParams)
    α
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (inferInstanceAs
      (SampleableType (Fin challengeParams.n → Scalar challengeParams)))
    (inferInstanceAs (SampleableType (BaseMatrix challengeParams)))
    k ψ

private theorem evalDist_challengeRow_update_cell
    {α : Type} (l : Fin challengeParams.n)
    (ψ : (Fin challengeParams.n → Scalar challengeParams) → α) :
    evalDist
        (do
          let x ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
          let r ← ($ᵗ (Fin challengeParams.n → Scalar challengeParams) :
            ProbComp (Fin challengeParams.n → Scalar challengeParams))
          pure (ψ (Function.update r l x))) =
      evalDist
        (do
          let r ← ($ᵗ (Fin challengeParams.n → Scalar challengeParams) :
            ProbComp (Fin challengeParams.n → Scalar challengeParams))
          pure (ψ r)) := by
  exact evalDist_uniform_update_bind
    (D := Fin challengeParams.n)
    (R := Scalar challengeParams)
    (α := α) l ψ

private theorem evalDist_bind_pure_of_map
    {α β : Type} (oa : ProbComp α) (f : α → β) (ob : ProbComp β)
    (h : evalDist (f <$> oa) = evalDist ob) :
    evalDist (oa >>= fun x => pure (f x)) = evalDist ob := by
  rw [show (oa >>= fun x => pure (f x)) = f <$> oa from
    (map_eq_bind_pure_comp ProbComp f oa).symm]
  exact h

private theorem evalDist_challengeSender_cell_uniform
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams)
    (k l : Fin challengeParams.n)
    (hcoeff : IsUnit (t.2.secret c.1 k * t.1.secret l c.2))
    (a : BaseMatrix challengeParams)
    (r : Fin challengeParams.n → Scalar challengeParams) :
    evalDist
        ((fun x : Scalar challengeParams =>
          challengeSenderScalar challengeParams c t
            (challengeBaseReplace challengeParams a k l r x)) <$>
          ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))) =
      evalDist ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)) := by
  classical
  let coeff := t.2.secret c.1 k * t.1.secret l c.2
  have hmul : Function.Bijective (coeff * ·) :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp hcoeff
  let b := challengeSenderScalar challengeParams c t
    (challengeBaseReplace challengeParams a k l r 0)
  have haffine : Function.Bijective (fun x : Scalar challengeParams => coeff * x + b) := by
    constructor
    · intro x y hxy
      apply hmul.1
      exact add_right_cancel hxy
    · intro y
      obtain ⟨x, hx⟩ := hmul.2 (y - b)
      refine ⟨x, ?_⟩
      change coeff * x + b = y
      change coeff * x = y - b at hx
      rw [hx, sub_add_cancel]
  have hfun :
      (fun x : Scalar challengeParams =>
        challengeSenderScalar challengeParams c t
          (challengeBaseReplace challengeParams a k l r x)) =
        fun x => coeff * x + b := by
    funext x
    exact challengeSenderScalar_replace_affine challengeParams c t a k l r x
  rw [hfun]
  exact evalDist_map_bijective_uniform_cross
    (α := Scalar challengeParams) (fun x => coeff * x + b) haffine

private theorem evalDist_challengeSender_uniform_of_not_bad
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams)
    (hgood : ¬challengeEntryBad c t) :
    evalDist
        ((fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a) <$>
          ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))) =
      evalDist
        ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)) := by
  classical
  simp only [challengeEntryBad, not_or, not_forall] at hgood
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hgood
  have hcoeff : IsUnit (t.2.secret c.1 k * t.1.secret l c.2) :=
    (isUnit_of_not_even_val _ hk).mul (isUnit_of_not_even_val _ hl)
  let rowType := Fin challengeParams.n → Scalar challengeParams
  let rowSample : ProbComp rowType := $ᵗ rowType
  let baseSample : ProbComp (BaseMatrix challengeParams) := $ᵗ (BaseMatrix challengeParams)
  calc
    evalDist
          ((fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a) <$>
            baseSample) =
        evalDist
          (do
            let r ← rowSample
            let a ← baseSample
            return challengeSenderScalar challengeParams c t (Function.update a k r)) := by
      exact (evalDist_challengeBase_update_row k
        (fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a)).symm
    _ = evalDist
          (do
            let a ← baseSample
            let r ← rowSample
            return challengeSenderScalar challengeParams c t (Function.update a k r)) :=
      evalDist_bind_bind_swap rowSample baseSample _
    _ = evalDist
          (do
            let a ← baseSample
            let x ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
            let r ← rowSample
            return challengeSenderScalar challengeParams c t
              (challengeBaseReplace challengeParams a k l r x)) := by
      refine evalDist_bind_congr' baseSample fun a => ?_
      exact (evalDist_challengeRow_update_cell l
        (fun r : rowType => challengeSenderScalar challengeParams c t (Function.update a k r))).symm
    _ = evalDist
          (do
            let a ← baseSample
            let r ← rowSample
            let x ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
            return challengeSenderScalar challengeParams c t
              (challengeBaseReplace challengeParams a k l r x)) := by
      refine evalDist_bind_congr' baseSample fun a => ?_
      exact evalDist_bind_bind_swap
        ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)) rowSample _
    _ = evalDist
          (do
            let a ← baseSample
            let r ← rowSample
            ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))) := by
      refine evalDist_bind_congr' baseSample fun a => ?_
      refine evalDist_bind_congr' rowSample fun r => ?_
      exact evalDist_bind_pure_of_map
        ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
        (fun x : Scalar challengeParams =>
          challengeSenderScalar challengeParams c t
            (challengeBaseReplace challengeParams a k l r x))
        ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
        (evalDist_challengeSender_cell_uniform c t k l hcoeff a r)
    _ = evalDist
          ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)) := by
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        baseSample probFailure_eq_zero]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        rowSample probFailure_eq_zero]

private theorem entryMismatch_iff_phase_of_cast
    (p : Params) (hp : p.WellFormed)
    (ik : InitKey p) (r : SendACoins p)
    (c : Fin p.nbar × Fin p.nbar) (z : ℤ)
    (hz :
      (z : Scalar p) =
        (r.secret * ik.error - r.error * ik.secret + r.extra) c.1 c.2) :
    reconcileScalar p
          (((r.secret * ik.baseMatrix + r.error) * ik.secret) c.1 c.2)
          (hintScalar p
            ((r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)
              c.1 c.2)) ≠
        extractScalar p
          ((r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)
            c.1 c.2) ↔
      p.blockWidth ≤
        ((((((r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)
          c.1 c.2).val % p.halfWidth + 2 ^ (p.discardBits - 2) : ℕ) :
            Scalar p) - (z : Scalar p)).val) := by
  let v := r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra
  let w := (r.secret * ik.baseMatrix + r.error) * ik.secret
  have hvalue := congrArg (fun m => m c.1 c.2)
    (firstExchangeValue_sub_eq_noise p ik r)
  simp only [Matrix.sub_apply] at hvalue
  have hdiff : v c.1 c.2 - w c.1 c.2 = (z : Scalar p) :=
    hvalue.trans hz.symm
  have hphase := reconcileScalar_eq_extractScalar_iff_phase
    p hp (w c.1 c.2) (v c.1 c.2)
  constructor
  · intro hne
    have hnlt :
        ¬ (((((v c.1 c.2).val % p.halfWidth +
              2 ^ (p.discardBits - 2) : ℕ) : Scalar p) -
            (v c.1 c.2 - w c.1 c.2)).val < p.blockWidth) :=
      fun hlt => hne (hphase.mpr hlt)
    rw [hdiff] at hnlt
    exact not_lt.mp hnlt
  · intro hlarge heq
    have hlt := hphase.mp heq
    rw [hdiff] at hlt
    exact (not_lt_of_ge hlarge) hlt

private theorem challengeEntryMismatch_withBase_iff_phase
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams)
    (a : BaseMatrix challengeParams) :
    challengeEntryMismatch c (challengeWithBase a t) ↔
      1024 ≤
        ((((challengeSenderScalar challengeParams c t a).val % 512 + 256 : ℕ) :
            Scalar challengeParams) -
          (challengeEntryNoiseInt c t : Scalar challengeParams)).val := by
  let tb := challengeWithBase a t
  have hnoiseSame : challengeEntryNoiseInt c tb = challengeEntryNoiseInt c t := by
    rfl
  have hz :
      (challengeEntryNoiseInt c t : Scalar challengeParams) =
        (tb.2.secret * tb.1.error - tb.2.error * tb.1.secret + tb.2.extra)
          c.1 c.2 := by
    exact (congrArg (fun z : ℤ => (z : Scalar challengeParams))
      hnoiseSame).symm.trans (cast_challengeEntryNoiseInt c tb)
  have hphase := entryMismatch_iff_phase_of_cast
    challengeParams challengeParams_wellFormed tb.1 tb.2 c
      (challengeEntryNoiseInt c t) hz
  have hhalf : challengeParams.halfWidth = 512 := by
    norm_num [challengeParams, Params.halfWidth, Params.discardBits]
  have hwidth : challengeParams.blockWidth = 1024 := by
    norm_num [challengeParams, Params.blockWidth, Params.discardBits]
  have hradius : 2 ^ (challengeParams.discardBits - 2) = 256 := by
    norm_num [challengeParams, Params.discardBits]
  dsimp only [tb, challengeWithBase] at hphase
  rw [hhalf, hwidth, hradius] at hphase
  simpa only [challengeEntryMismatch, challengeWithBase,
    challengeSenderScalar] using hphase

private theorem probEvent_challengeEntryMismatch_withBase
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams)
    (hgood : ¬challengeEntryBad c t) :
    Pr[fun a : BaseMatrix challengeParams =>
      challengeEntryMismatch c (challengeWithBase a t) |
        ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))] =
      challengeFailureRamp (challengeEntryNoiseInt c t) := by
  let phaseBad := fun v : Scalar challengeParams =>
    1024 ≤
      ((((v.val % 512 + 256 : ℕ) : Scalar challengeParams) -
        (challengeEntryNoiseInt c t : Scalar challengeParams)).val)
  calc
    Pr[fun a : BaseMatrix challengeParams =>
        challengeEntryMismatch c (challengeWithBase a t) |
          ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))] =
        Pr[phaseBad |
          (fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a) <$>
            ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))] := by
      rw [probEvent_map]
      apply probEvent_congr'
      · intro a _
        exact challengeEntryMismatch_withBase_iff_phase c t a
      · rfl
    _ = Pr[phaseBad |
          ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))] := by
      simp only [probEvent_def, evalDist_challengeSender_uniform_of_not_bad c t hgood]
    _ = challengeFailureRamp (challengeEntryNoiseInt c t) :=
      probEvent_uniform_phase_eq_challengeFailureRamp (challengeEntryNoiseInt c t)

private noncomputable def challengeFixedFailure
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) : ℝ≥0∞ :=
  Pr[fun a : BaseMatrix challengeParams =>
    challengeEntryMismatch c (challengeWithBase a t) |
      ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))]

private noncomputable local instance challengeEntryBadDecidable
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    Decidable (challengeEntryBad c t) :=
  Classical.propDecidable _

private theorem evalDist_challengeEntryNoiseInt_noiseCoins
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    evalDist ((fun t => challengeEntryNoiseInt c t) <$> challengeNoiseCoinsExp) =
      evalDist challengeEntryNoiseIntExp := by
  let withBaseExp : ProbComp (InitKey challengeParams × SendACoins challengeParams) := do
    let t ← challengeNoiseCoinsExp
    let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
    return challengeWithBase a t
  have hdrop :
      evalDist ((fun t => challengeEntryNoiseInt c t) <$> withBaseExp) =
        evalDist ((fun t => challengeEntryNoiseInt c t) <$> challengeNoiseCoinsExp) := by
    simp only [withBaseExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    refine evalDist_bind_congr' challengeNoiseCoinsExp fun t => ?_
    convert OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams)))
      probFailure_eq_zero (pure (challengeEntryNoiseInt c t)) using 1 <;>
        rfl
  have hmap := evalDist_map_eq_of_evalDist_eq evalDist_challengeCoinsExp_noiseFirst
    (fun t => challengeEntryNoiseInt c t)
  exact hdrop.symm.trans (hmap.symm.trans (evalDist_challengeEntryNoiseInt c))

private theorem probEvent_bind_pure_map
    {α β : Type} (mx : ProbComp α) (f : α → β) (q : β → Prop) :
    Pr[q | mx >>= fun x => pure (f x)] = Pr[fun x => q (f x) | mx] := by
  rw [show (fun x => pure (f x)) = pure ∘ f from rfl,
    probEvent_bind_pure_comp]
  rfl

private theorem probEvent_challengeEntryMismatch_eq_expectedFixed
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    Pr[challengeEntryMismatch c | challengeCoinsExp] =
      expectedValue challengeNoiseCoinsExp (challengeFixedFailure c) := by
  have hprob := probEvent_congr'
    (p := challengeEntryMismatch c)
    (q := challengeEntryMismatch c)
    (oa := challengeCoinsExp)
    (oa' := do
      let t ← challengeNoiseCoinsExp
      let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
      return challengeWithBase a t)
    (fun _ _ => Iff.rfl) evalDist_challengeCoinsExp_noiseFirst
  rw [hprob, probEvent_bind_eq_tsum]
  unfold expectedValue challengeFixedFailure
  apply tsum_congr
  intro t
  apply congrArg (fun q : ℝ≥0∞ => Pr[= t | challengeNoiseCoinsExp] * q)
  exact probEvent_bind_pure_map
    (($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams)))
    (fun a => challengeWithBase a t) (challengeEntryMismatch c)

private theorem expectedValue_noiseCoins_ramp
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    expectedValue challengeNoiseCoinsExp
        (fun t => challengeFailureRamp (challengeEntryNoiseInt c t)) =
      expectedValue challengeEntryNoiseIntExp challengeFailureRamp := by
  rw [← expectedValue_map]
  apply expectedValue_congr
  exact evalDist_ext_iff.mp (evalDist_challengeEntryNoiseInt_noiseCoins c)

private theorem expectedValue_noiseCoins_badIndicator
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    expectedValue challengeNoiseCoinsExp
        (fun t => if challengeEntryBad c t then 1 else 0) =
      Pr[challengeEntryBad c | challengeNoiseCoinsExp] := by
  classical
  rw [expectedValue, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro t
  by_cases hbad : challengeEntryBad c t <;> simp only [hbad, if_true, if_false,
    mul_one, mul_zero]

private theorem challengeFixedFailure_le_ramp_add_bad
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    challengeFixedFailure c t ≤
      challengeFailureRamp (challengeEntryNoiseInt c t) +
        if challengeEntryBad c t then 1 else 0 := by
  classical
  by_cases hbad : challengeEntryBad c t
  · simp only [hbad, if_true]
    exact probEvent_le_one.trans (le_add_left le_rfl)
  · unfold challengeFixedFailure
    rw [probEvent_challengeEntryMismatch_withBase c t hbad]
    simp only [hbad, if_false, add_zero]
    exact le_rfl

private theorem challengeRamp_le_fixedFailure_add_bad
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    challengeFailureRamp (challengeEntryNoiseInt c t) ≤
      challengeFixedFailure c t + if challengeEntryBad c t then 1 else 0 := by
  classical
  by_cases hbad : challengeEntryBad c t
  · simp only [hbad, if_true]
    exact (challengeFailureRamp_le_one _).trans (le_add_left le_rfl)
  · unfold challengeFixedFailure
    rw [probEvent_challengeEntryMismatch_withBase c t hbad]
    simp only [hbad, if_false, add_zero]
    exact le_rfl

/-- The actual entry probability and exact modular-ramp expectation differ by at most `2^-351`. -/
theorem probEvent_challengeEntryMismatch_ramp_bounds
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    (Pr[challengeEntryMismatch c | challengeCoinsExp] ≤
      expectedValue challengeEntryNoiseIntExp challengeFailureRamp +
        1 / (2 : ℝ≥0∞) ^ 351) ∧
    (expectedValue challengeEntryNoiseIntExp challengeFailureRamp ≤
      Pr[challengeEntryMismatch c | challengeCoinsExp] +
        1 / (2 : ℝ≥0∞) ^ 351) := by
  classical
  constructor
  · rw [probEvent_challengeEntryMismatch_eq_expectedFixed c]
    calc
      expectedValue challengeNoiseCoinsExp (challengeFixedFailure c) ≤
          expectedValue challengeNoiseCoinsExp
            (fun t => challengeFailureRamp (challengeEntryNoiseInt c t) +
              if challengeEntryBad c t then 1 else 0) :=
        expectedValue_mono challengeNoiseCoinsExp
          (challengeFixedFailure_le_ramp_add_bad c)
      _ = expectedValue challengeEntryNoiseIntExp challengeFailureRamp +
          Pr[challengeEntryBad c | challengeNoiseCoinsExp] := by
        rw [expectedValue_add, expectedValue_noiseCoins_ramp c,
          expectedValue_noiseCoins_badIndicator c]
      _ ≤ expectedValue challengeEntryNoiseIntExp challengeFailureRamp +
          1 / (2 : ℝ≥0∞) ^ 351 :=
        add_le_add_right (probEvent_challengeEntryBad_le c) _
  · rw [← expectedValue_noiseCoins_ramp c,
      probEvent_challengeEntryMismatch_eq_expectedFixed c]
    calc
      expectedValue challengeNoiseCoinsExp
          (fun t => challengeFailureRamp (challengeEntryNoiseInt c t)) ≤
          expectedValue challengeNoiseCoinsExp
            (fun t => challengeFixedFailure c t +
              if challengeEntryBad c t then 1 else 0) :=
        expectedValue_mono challengeNoiseCoinsExp
          (challengeRamp_le_fixedFailure_add_bad c)
      _ = expectedValue challengeNoiseCoinsExp (challengeFixedFailure c) +
          Pr[challengeEntryBad c | challengeNoiseCoinsExp] := by
        rw [expectedValue_add, expectedValue_noiseCoins_badIndicator c]
      _ ≤ expectedValue challengeNoiseCoinsExp (challengeFixedFailure c) +
          1 / (2 : ℝ≥0∞) ^ 351 :=
        add_le_add_right (probEvent_challengeEntryBad_le c) _

end lweCKA
