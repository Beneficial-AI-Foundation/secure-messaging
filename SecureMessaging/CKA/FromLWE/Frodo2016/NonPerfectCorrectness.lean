/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Correctness
import SecureMessaging.CKA.FromLWE.Frodo2016.Sampling
import SecureMessaging.CKA.FromLWE.ReconciliationCorrectness

/-!
# Non-perfect correctness of three historical Frodo instantiations

The exact D1, D2, and D4 samplers each support a first-exchange execution in which the sender and
receiver derive different keys. Consequently, the historical Challenge, Classical, and Paranoid
instantiations have strictly positive first-exchange failure probability.

These are support-witness proofs. They do not formalize the numerical failure estimates or security
estimates in the original Frodo paper.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace lweCKA

private def witnessInitKey (p : Params) (errorValue : Scalar p) : InitKey p :=
  { baseMatrix := 0
    secret := 0
    error := fun _ _ => errorValue }

private def witnessSendACoins (p : Params) (secretValue : Scalar p) : SendACoins p :=
  { secret := fun _ _ => secretValue
    error := 0
    extra := 0 }

private def witnessSenderValue
    (p : Params) (errorValue secretValue : Scalar p) : SharedMatrix p :=
  let ik := witnessInitKey p errorValue
  let r := witnessSendACoins p secretValue
  r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra

private def witnessReceiverValue
    (p : Params) (errorValue secretValue : Scalar p) : SharedMatrix p :=
  let ik := witnessInitKey p errorValue
  let r := witnessSendACoins p secretValue
  (r.secret * ik.baseMatrix + r.error) * ik.secret

private theorem d1_cast_mem_support (z : ℤ) (hz : z ∈ Set.Icc (-3 : ℤ) 3) :
    (z : Scalar challengeParams) ∈ support d1Sampler := by
  rw [d1Sampler, support_map]
  exact ⟨z, support_d1IntSampler ▸ hz, rfl⟩

private theorem d2_cast_mem_support (z : ℤ) (hz : z ∈ Set.Icc (-4 : ℤ) 4) :
    (z : Scalar classicalParams) ∈ support d2Sampler := by
  rw [d2Sampler, support_map]
  exact ⟨z, support_d2IntSampler ▸ hz, rfl⟩

private theorem d4_cast_mem_support (z : ℤ) (hz : z ∈ Set.Icc (-6 : ℤ) 6) :
    (z : Scalar paranoidParams) ∈ support d4Sampler := by
  rw [d4Sampler, support_map]
  exact ⟨z, support_d4IntSampler ▸ hz, rfl⟩

private theorem mem_support_bind_intro
    {α β : Type} {mx : ProbComp α} {f : α → ProbComp β} {a : α} {b : β}
    (ha : a ∈ support mx) (hb : b ∈ support (f a)) :
    b ∈ support (mx >>= f) := by
  rw [support_bind]
  simp only [Set.mem_iUnion]
  exact ⟨a, ha, hb⟩

private theorem constMatrix_mem_support
    {p : Params} (χ : ProbComp (Scalar p))
    (rows cols : ℕ) (x : Scalar p) (hx : x ∈ support χ) :
    (fun _ : Fin rows => fun _ : Fin cols => x) ∈ support (sampleMatrix χ rows cols) := by
  apply mem_support_of_probOutput_pos
  rw [sampleMatrix, ProbComp.sampleIID, probOutput_mOfFn]
  rw [pos_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [ProbComp.sampleIID, probOutput_mOfFn]
  apply Finset.prod_ne_zero_iff.mpr
  exact fun _ _ => ne_of_gt (probOutput_pos χ x hx)

private theorem witnessInitKey_prob_pos
    {p : Params} (χ : ProbComp (Scalar p)) (errorValue : Scalar p)
    (hzero : (0 : Scalar p) ∈ support χ) (herror : errorValue ∈ support χ) :
    0 < Pr[= witnessInitKey p errorValue | initKeyGen p χ] := by
  rw [probOutput_pos_iff]
  let base : BaseMatrix p := 0
  let afterError (baseMatrix : BaseMatrix p) (secret error : RightMatrix p) :
      ProbComp (InitKey p) :=
    pure { baseMatrix := baseMatrix, secret := secret, error := error }
  let afterSecret (baseMatrix : BaseMatrix p) (secret : RightMatrix p) :
      ProbComp (InitKey p) :=
    sampleMatrix χ p.n p.nbar >>= fun error => afterError baseMatrix secret error
  let afterBase (baseMatrix : BaseMatrix p) : ProbComp (InitKey p) :=
    sampleMatrix χ p.n p.nbar >>= fun secret => afterSecret baseMatrix secret
  let secret : RightMatrix p := 0
  let error : RightMatrix p := fun _ _ => errorValue
  have hsecret : secret ∈ support (sampleMatrix χ p.n p.nbar) :=
    constMatrix_mem_support χ _ _ 0 hzero
  have herrorMatrix : error ∈ support (sampleMatrix χ p.n p.nbar) :=
    constMatrix_mem_support χ _ _ errorValue herror
  have hpure : witnessInitKey p errorValue ∈ support (afterError base secret error) := by
    simp [afterError, base, secret, error, witnessInitKey]
  have hafterSecret : witnessInitKey p errorValue ∈ support (afterSecret base secret) := by
    change witnessInitKey p errorValue ∈
      support (sampleMatrix χ p.n p.nbar >>= afterError base secret)
    exact mem_support_bind_intro herrorMatrix hpure
  have hafterBase : witnessInitKey p errorValue ∈ support (afterBase base) := by
    change witnessInitKey p errorValue ∈
      support (sampleMatrix χ p.n p.nbar >>= afterSecret base)
    exact mem_support_bind_intro hsecret hafterSecret
  change witnessInitKey p errorValue ∈ support (($ᵗ (BaseMatrix p)) >>= afterBase)
  rw [support_bind, support_uniformSample]
  simp only [Set.mem_univ, Set.iUnion_true]
  exact Set.mem_iUnion_of_mem base hafterBase

private theorem witnessSendACoins_mem_support
    {p : Params} (χ : ProbComp (Scalar p)) (secretValue : Scalar p)
    (hzero : (0 : Scalar p) ∈ support χ) (hsecret : secretValue ∈ support χ) :
    witnessSendACoins p secretValue ∈ support (sampleSendACoins p χ) := by
  rw [sampleSendACoins]
  apply mem_support_bind_intro
    (a := (fun _ _ => secretValue : LeftMatrix p))
    (constMatrix_mem_support χ _ _ secretValue hsecret)
  apply mem_support_bind_intro (a := (0 : LeftMatrix p))
    (constMatrix_mem_support χ _ _ 0 hzero)
  apply mem_support_bind_intro (a := (0 : SharedMatrix p))
    (constMatrix_mem_support χ _ _ 0 hzero)
  rw [support_pure]
  simp only [Set.mem_singleton_iff]
  unfold witnessSendACoins
  congr 1

private theorem witnessSenderValue_entry
    (p : Params) (errorValue secretValue : Scalar p) (i j : Fin p.nbar) :
    witnessSenderValue p errorValue secretValue i j =
      ∑ _ : Fin p.n, secretValue * errorValue := by
  have hpublic :
      (witnessInitKey p errorValue).baseMatrix * (witnessInitKey p errorValue).secret +
          (witnessInitKey p errorValue).error =
        (witnessInitKey p errorValue).error := by
    ext x y
    rw [Matrix.add_apply, Matrix.mul_apply]
    simp [witnessInitKey]
  rw [witnessSenderValue, Matrix.add_apply, hpublic, Matrix.mul_apply]
  simp only [witnessSendACoins, witnessInitKey, Matrix.zero_apply, add_zero]

private theorem witnessReceiverValue_entry
    (p : Params) (errorValue secretValue : Scalar p) (i j : Fin p.nbar) :
    witnessReceiverValue p errorValue secretValue i j = 0 := by
  simp [witnessReceiverValue, witnessSendACoins, witnessInitKey]

private theorem reconcileScalar_zero (p : Params) (hp : p.WellFormed) :
    reconcileScalar p 0 (hintScalar p 0) = extractScalar p 0 := by
  apply reconcileScalar_eq_extractScalar_of_modularDistance_lt p hp
  simp [modularDistance]

private theorem witnessFailure_true
    (p : Params) (hp : p.WellFormed) (errorValue secretValue value : Scalar p)
    (hsender : ∀ i j, witnessSenderValue p errorValue secretValue i j = value)
    (hhint : hintScalar p value = hintScalar p 0)
    (hextract : extractScalar p value ≠ extractScalar p 0) :
    decide
      (reconcile p (witnessReceiverValue p errorValue secretValue)
          (makeHint p (witnessSenderValue p errorValue secretValue)) ≠
        extract p (witnessSenderValue p errorValue secretValue)) = true := by
  apply decide_eq_true
  intro hkeys
  let i : Fin p.nbar := ⟨0, hp.nbar_pos⟩
  have hentry := congrFun (congrFun hkeys i) i
  change reconcileScalar p (witnessReceiverValue p errorValue secretValue i i)
      (hintScalar p (witnessSenderValue p errorValue secretValue i i)) =
    extractScalar p (witnessSenderValue p errorValue secretValue i i) at hentry
  rw [witnessReceiverValue_entry, hsender i i, hhint, reconcileScalar_zero p hp] at hentry
  exact hextract hentry.symm

private theorem firstExchangeFailureProb_pos_of_witness
    (p : Params) (χ : ProbComp (Scalar p)) (errorValue secretValue : Scalar p)
    (hinit : 0 < Pr[= witnessInitKey p errorValue | initKeyGen p χ])
    (hsend : witnessSendACoins p secretValue ∈ support (sampleSendACoins p χ))
    (hfailure :
      decide
        (reconcile p (witnessReceiverValue p errorValue secretValue)
            (makeHint p (witnessSenderValue p errorValue secretValue)) ≠
          extract p (witnessSenderValue p errorValue secretValue)) = true) :
    0 < firstExchangeFailureProb p χ := by
  rw [firstExchangeFailureProb]
  let afterCoins (ik : InitKey p) (r : SendACoins p) : ProbComp Bool :=
    pure (decide
      (reconcile p
          ((r.secret * ik.baseMatrix + r.error) * ik.secret)
          (makeHint p
            (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) ≠
        extract p
          (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)))
  let afterInit (ik : InitKey p) : ProbComp Bool :=
    sampleSendACoins p χ >>= afterCoins ik
  have hout : true ∈
      support (afterCoins (witnessInitKey p errorValue) (witnessSendACoins p secretValue)) := by
    change true ∈ support (pure (decide
      (reconcile p (witnessReceiverValue p errorValue secretValue)
          (makeHint p (witnessSenderValue p errorValue secretValue)) ≠
        extract p (witnessSenderValue p errorValue secretValue))) : ProbComp Bool)
    rw [hfailure]
    simp
  have hafterInit : true ∈ support (afterInit (witnessInitKey p errorValue)) := by
    change true ∈ support
      (sampleSendACoins p χ >>= afterCoins (witnessInitKey p errorValue))
    exact mem_support_bind_intro hsend hout
  change 0 < Pr[= true | initKeyGen p χ >>= afterInit]
  rw [probOutput_bind_eq_tsum]
  have hterm :
      0 < Pr[= witnessInitKey p errorValue | initKeyGen p χ] *
        Pr[= true | afterInit (witnessInitKey p errorValue)] :=
    ENNReal.mul_pos (ne_of_gt hinit) (ne_of_gt (probOutput_pos _ _ hafterInit))
  exact lt_of_lt_of_le hterm (ENNReal.le_tsum (witnessInitKey p errorValue))

private theorem challengeWitnessSenderValue_entry
    (i j : Fin challengeParams.nbar) :
    witnessSenderValue challengeParams 2 2 i j = (1408 : Scalar challengeParams) := by
  rw [witnessSenderValue_entry]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num [challengeParams]

private theorem challengeWitnessHint :
    hintScalar challengeParams (1408 : Scalar challengeParams) =
      hintScalar challengeParams 0 := by
  have hval : (1408 : Scalar challengeParams).val = 1408 := by
    apply ZMod.val_natCast_of_lt
    norm_num [challengeParams, Params.q]
  simp only [hintScalar]
  rw [hval]
  norm_num [challengeParams, Params.halfWidth, Params.discardBits]
  exact ZMod.natCast_self 2

private theorem challengeWitnessExtract :
    extractScalar challengeParams (1408 : Scalar challengeParams) ≠
      extractScalar challengeParams 0 := by
  have hval : (1408 : Scalar challengeParams).val = 1408 := by
    apply ZMod.val_natCast_of_lt
    norm_num [challengeParams, Params.q]
  have hvalue : extractScalar challengeParams (1408 : Scalar challengeParams) = 1 := by
    rw [extractScalar, hval]
    norm_num [challengeParams, Params.halfWidth, Params.blockWidth, Params.discardBits]
  have hzero : extractScalar challengeParams 0 = 0 := by
    norm_num [extractScalar, challengeParams, Params.halfWidth, Params.blockWidth,
      Params.discardBits]
  rw [hvalue, hzero]
  intro h
  have hvals := congrArg ZMod.val h
  rw [ZMod.val_one'' (by norm_num [challengeParams]), ZMod.val_zero] at hvals
  omega

private theorem challengeWitnessFailure_true :
    decide
      (reconcile challengeParams (witnessReceiverValue challengeParams 2 2)
          (makeHint challengeParams (witnessSenderValue challengeParams 2 2)) ≠
        extract challengeParams (witnessSenderValue challengeParams 2 2)) = true := by
  exact witnessFailure_true challengeParams challengeParams_wellFormed 2 2 1408
    challengeWitnessSenderValue_entry challengeWitnessHint challengeWitnessExtract

/-- The historical Challenge parameters with exact D1 sampling have positive first-exchange
failure probability. -/
theorem firstExchangeFailureProb_challenge_pos :
    0 < firstExchangeFailureProb challengeParams d1Sampler := by
  apply firstExchangeFailureProb_pos_of_witness challengeParams d1Sampler 2 2
  · apply witnessInitKey_prob_pos
    · exact d1_cast_mem_support 0 (by norm_num)
    · exact d1_cast_mem_support 2 (by norm_num)
  · apply witnessSendACoins_mem_support
    · exact d1_cast_mem_support 0 (by norm_num)
    · exact d1_cast_mem_support 2 (by norm_num)
  · exact challengeWitnessFailure_true

private theorem classicalWitnessSenderValue_entry
    (i j : Fin classicalParams.nbar) :
    witnessSenderValue classicalParams 2 2 i j = (2368 : Scalar classicalParams) := by
  rw [witnessSenderValue_entry]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num [classicalParams]

private theorem classicalWitnessHint :
    hintScalar classicalParams (2368 : Scalar classicalParams) =
      hintScalar classicalParams 0 := by
  have hval : (2368 : Scalar classicalParams).val = 2368 := by
    apply ZMod.val_natCast_of_lt
    norm_num [classicalParams, Params.q]
  simp only [hintScalar]
  rw [hval]
  norm_num [classicalParams, Params.halfWidth, Params.discardBits]
  exact ZMod.natCast_self 2

private theorem classicalWitnessExtract :
    extractScalar classicalParams (2368 : Scalar classicalParams) ≠
      extractScalar classicalParams 0 := by
  have hval : (2368 : Scalar classicalParams).val = 2368 := by
    apply ZMod.val_natCast_of_lt
    norm_num [classicalParams, Params.q]
  have hvalue : extractScalar classicalParams (2368 : Scalar classicalParams) = 2 := by
    rw [extractScalar, hval]
    norm_num [classicalParams, Params.halfWidth, Params.blockWidth, Params.discardBits]
  have hzero : extractScalar classicalParams 0 = 0 := by
    norm_num [extractScalar, classicalParams, Params.halfWidth, Params.blockWidth,
      Params.discardBits]
  rw [hvalue, hzero]
  intro h
  have hvals := congrArg ZMod.val h
  have htwo : ((2 : KeyScalar classicalParams)).val = 2 := by
    apply ZMod.val_natCast_of_lt
    norm_num [classicalParams]
  rw [htwo, ZMod.val_zero] at hvals
  omega

private theorem classicalWitnessFailure_true :
    decide
      (reconcile classicalParams (witnessReceiverValue classicalParams 2 2)
          (makeHint classicalParams (witnessSenderValue classicalParams 2 2)) ≠
        extract classicalParams (witnessSenderValue classicalParams 2 2)) = true := by
  exact witnessFailure_true classicalParams classicalParams_wellFormed 2 2 2368
    classicalWitnessSenderValue_entry classicalWitnessHint classicalWitnessExtract

/-- The historical Classical parameters with exact D2 sampling have positive first-exchange
failure probability. -/
theorem firstExchangeFailureProb_classical_pos :
    0 < firstExchangeFailureProb classicalParams d2Sampler := by
  apply firstExchangeFailureProb_pos_of_witness classicalParams d2Sampler 2 2
  · apply witnessInitKey_prob_pos
    · exact d2_cast_mem_support 0 (by norm_num)
    · exact d2_cast_mem_support 2 (by norm_num)
  · apply witnessSendACoins_mem_support
    · exact d2_cast_mem_support 0 (by norm_num)
    · exact d2_cast_mem_support 2 (by norm_num)
  · exact classicalWitnessFailure_true

private theorem paranoidWitnessSenderValue_entry
    (i j : Fin paranoidParams.nbar) :
    witnessSenderValue paranoidParams 2 4 i j = (6912 : Scalar paranoidParams) := by
  rw [witnessSenderValue_entry]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num [paranoidParams]

private theorem paranoidWitnessHint :
    hintScalar paranoidParams (6912 : Scalar paranoidParams) =
      hintScalar paranoidParams 0 := by
  have hval : (6912 : Scalar paranoidParams).val = 6912 := by
    apply ZMod.val_natCast_of_lt
    norm_num [paranoidParams, Params.q]
  simp only [hintScalar]
  rw [hval]
  norm_num [paranoidParams, Params.halfWidth, Params.discardBits]
  exact ZMod.natCast_self 2

private theorem paranoidWitnessExtract :
    extractScalar paranoidParams (6912 : Scalar paranoidParams) ≠
      extractScalar paranoidParams 0 := by
  have hval : (6912 : Scalar paranoidParams).val = 6912 := by
    apply ZMod.val_natCast_of_lt
    norm_num [paranoidParams, Params.q]
  have hvalue : extractScalar paranoidParams (6912 : Scalar paranoidParams) = 3 := by
    rw [extractScalar, hval]
    norm_num [paranoidParams, Params.halfWidth, Params.blockWidth, Params.discardBits]
  have hzero : extractScalar paranoidParams 0 = 0 := by
    norm_num [extractScalar, paranoidParams, Params.halfWidth, Params.blockWidth,
      Params.discardBits]
  rw [hvalue, hzero]
  intro h
  have hvals := congrArg ZMod.val h
  have hthree : ((3 : KeyScalar paranoidParams)).val = 3 := by
    apply ZMod.val_natCast_of_lt
    norm_num [paranoidParams]
  rw [hthree, ZMod.val_zero] at hvals
  omega

private theorem paranoidWitnessFailure_true :
    decide
      (reconcile paranoidParams (witnessReceiverValue paranoidParams 2 4)
          (makeHint paranoidParams (witnessSenderValue paranoidParams 2 4)) ≠
        extract paranoidParams (witnessSenderValue paranoidParams 2 4)) = true := by
  exact witnessFailure_true paranoidParams paranoidParams_wellFormed 2 4 6912
    paranoidWitnessSenderValue_entry paranoidWitnessHint paranoidWitnessExtract

/-- The historical Paranoid parameters with exact D4 sampling have positive first-exchange
failure probability. -/
theorem firstExchangeFailureProb_paranoid_pos :
    0 < firstExchangeFailureProb paranoidParams d4Sampler := by
  apply firstExchangeFailureProb_pos_of_witness paranoidParams d4Sampler 2 4
  · apply witnessInitKey_prob_pos
    · exact d4_cast_mem_support 0 (by norm_num)
    · exact d4_cast_mem_support 2 (by norm_num)
  · apply witnessSendACoins_mem_support
    · exact d4_cast_mem_support 0 (by norm_num)
    · exact d4_cast_mem_support 4 (by norm_num)
  · exact paranoidWitnessFailure_true

end lweCKA
