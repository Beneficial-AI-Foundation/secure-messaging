/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ConcreteSampling
import SecureMessaging.CKA.FromLWE.Correctness
import SecureMessaging.CKA.FromLWE.ReconciliationCorrectness

/-!
# Non-perfect correctness of the recommended LWE instantiation

The exact D3 sampler supports a first-exchange execution in which the sender and receiver derive
different keys. Consequently, the recommended instantiation has strictly positive first-exchange
failure probability.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace lweCKA

private def failureInitKey : InitKey recommendedParams :=
  { baseMatrix := 0
    secret := 0
    error := fun _ _ => 2 }

private def failureSendACoins : SendACoins recommendedParams :=
  { secret := fun _ _ => 2
    error := 0
    extra := 0 }

private def failureSenderValue : SharedMatrix recommendedParams :=
  failureSendACoins.secret *
      (failureInitKey.baseMatrix * failureInitKey.secret + failureInitKey.error) +
    failureSendACoins.extra

private def failureReceiverValue : SharedMatrix recommendedParams :=
  (failureSendACoins.secret * failureInitKey.baseMatrix + failureSendACoins.error) *
    failureInitKey.secret

private theorem d3_cast_mem_support (z : ℤ) (hz : z ∈ Set.Icc (-5 : ℤ) 5) :
    (z : Scalar recommendedParams) ∈ support d3Sampler := by
  rw [d3Sampler, support_map]
  exact ⟨z, support_d3IntSampler ▸ hz, rfl⟩

private theorem mem_support_bind_intro
    {α β : Type} {mx : ProbComp α} {f : α → ProbComp β} {a : α} {b : β}
    (ha : a ∈ support mx) (hb : b ∈ support (f a)) :
    b ∈ support (mx >>= f) := by
  rw [support_bind]
  simp only [Set.mem_iUnion]
  exact ⟨a, ha, hb⟩

private theorem constMatrix_mem_support
    (rows cols : ℕ) (x : Scalar recommendedParams) (hx : x ∈ support d3Sampler) :
    (fun _ : Fin rows => fun _ : Fin cols => x) ∈
      support (sampleMatrix d3Sampler rows cols) := by
  apply mem_support_of_probOutput_pos
  rw [sampleMatrix, ProbComp.sampleIID, probOutput_mOfFn]
  rw [pos_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [ProbComp.sampleIID, probOutput_mOfFn]
  apply Finset.prod_ne_zero_iff.mpr
  exact fun _ _ => ne_of_gt (probOutput_pos d3Sampler x hx)

private theorem failureInitKey_prob_pos :
    0 < Pr[= failureInitKey | initKeyGen recommendedParams d3Sampler] := by
  rw [probOutput_pos_iff]
  let base : BaseMatrix recommendedParams := 0
  let afterError (baseMatrix : BaseMatrix recommendedParams)
      (secret error : RightMatrix recommendedParams) : ProbComp (InitKey recommendedParams) :=
    pure { baseMatrix := baseMatrix, secret := secret, error := error }
  let afterSecret (baseMatrix : BaseMatrix recommendedParams)
      (secret : RightMatrix recommendedParams) : ProbComp (InitKey recommendedParams) :=
    sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar >>= fun error =>
      afterError baseMatrix secret error
  let afterBase (baseMatrix : BaseMatrix recommendedParams) :
      ProbComp (InitKey recommendedParams) :=
    sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar >>= fun secret =>
      afterSecret baseMatrix secret
  let secret : RightMatrix recommendedParams := 0
  let error : RightMatrix recommendedParams := fun _ _ => 2
  have hsecret : secret ∈
      support (sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar) :=
    constMatrix_mem_support _ _ 0 (d3_cast_mem_support 0 (by norm_num))
  have herror : error ∈
      support (sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar) :=
    constMatrix_mem_support _ _ 2 (d3_cast_mem_support 2 (by norm_num))
  have hpure : failureInitKey ∈ support (afterError base secret error) := by
    simp [afterError, base, secret, error, failureInitKey]
  have hafterSecret : failureInitKey ∈ support (afterSecret base secret) := by
    change failureInitKey ∈ support
      (sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar >>=
        afterError base secret)
    exact mem_support_bind_intro herror hpure
  have hafterBase : failureInitKey ∈ support (afterBase base) := by
    change failureInitKey ∈ support
      (sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar >>=
        afterSecret base)
    exact mem_support_bind_intro hsecret hafterSecret
  change failureInitKey ∈ support (($ᵗ (BaseMatrix recommendedParams)) >>= afterBase)
  rw [support_bind, support_uniformSample]
  simp only [Set.mem_univ, Set.iUnion_true]
  exact Set.mem_iUnion_of_mem base hafterBase

private theorem failureSendACoins_mem_support :
    failureSendACoins ∈ support (sampleSendACoins recommendedParams d3Sampler) := by
  rw [sampleSendACoins]
  apply mem_support_bind_intro
    (a := (fun _ _ => 2 : LeftMatrix recommendedParams))
    (constMatrix_mem_support _ _ 2 (d3_cast_mem_support 2 (by norm_num)))
  apply mem_support_bind_intro (a := (0 : LeftMatrix recommendedParams))
    (constMatrix_mem_support _ _ 0 (d3_cast_mem_support 0 (by norm_num)))
  apply mem_support_bind_intro (a := (0 : SharedMatrix recommendedParams))
    (constMatrix_mem_support _ _ 0 (d3_cast_mem_support 0 (by norm_num)))
  rw [support_pure]
  simp only [Set.mem_singleton_iff]
  unfold failureSendACoins
  congr 1

private theorem failureSenderValue_entry :
    failureSenderValue
        ⟨0, by norm_num [recommendedParams]⟩ ⟨0, by norm_num [recommendedParams]⟩ =
      (3008 : Scalar recommendedParams) := by
  have hpublic :
      failureInitKey.baseMatrix * failureInitKey.secret + failureInitKey.error =
        failureInitKey.error := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply]
    simp [failureInitKey]
  rw [failureSenderValue, Matrix.add_apply, hpublic, Matrix.mul_apply]
  simp only [failureSendACoins, failureInitKey, Matrix.zero_apply, add_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num [recommendedParams]

private theorem failureReceiverValue_entry :
    failureReceiverValue
        ⟨0, by norm_num [recommendedParams]⟩ ⟨0, by norm_num [recommendedParams]⟩ = 0 := by
  simp [failureReceiverValue, failureSendACoins, failureInitKey, Matrix.mul_apply]

private theorem failureWitness_true :
    decide
      (reconcile recommendedParams failureReceiverValue
          (makeHint recommendedParams failureSenderValue) ≠
        extract recommendedParams failureSenderValue) = true := by
  apply decide_eq_true
  intro hkeys
  let i : Fin recommendedParams.nbar := ⟨0, by norm_num [recommendedParams]⟩
  have hentry := congrFun (congrFun hkeys i) i
  change reconcileScalar recommendedParams (failureReceiverValue i i)
      (hintScalar recommendedParams (failureSenderValue i i)) =
    extractScalar recommendedParams (failureSenderValue i i) at hentry
  rw [failureReceiverValue_entry, failureSenderValue_entry] at hentry
  have hzero :
      reconcileScalar recommendedParams 0 (hintScalar recommendedParams 0) =
        extractScalar recommendedParams 0 := by
    apply reconcileScalar_eq_extractScalar_of_modularDistance_lt
      recommendedParams recommendedParams_wellFormed
    norm_num [modularDistance, recommendedParams, Params.discardBits]
  have hhint :
      hintScalar recommendedParams (3008 : Scalar recommendedParams) =
        hintScalar recommendedParams 0 := by
    have hval : (3008 : Scalar recommendedParams).val = 3008 := by
      apply ZMod.val_natCast_of_lt
      norm_num [recommendedParams, Params.q]
    simp only [hintScalar]
    rw [hval]
    norm_num [recommendedParams, Params.halfWidth, Params.discardBits]
    exact ZMod.natCast_self 2
  rw [hhint, hzero] at hentry
  have hextractZero : extractScalar recommendedParams 0 = 0 := by
    norm_num [extractScalar, recommendedParams, Params.halfWidth, Params.blockWidth,
      Params.discardBits]
  have hextractValue :
      extractScalar recommendedParams (3008 : Scalar recommendedParams) = 1 := by
    have hval : (3008 : Scalar recommendedParams).val = 3008 := by
      apply ZMod.val_natCast_of_lt
      norm_num [recommendedParams, Params.q]
    rw [extractScalar, hval]
    change (((3008 + 1024) / 2048 : ℕ) : ZMod 16) = 1
    norm_num
  rw [hextractZero, hextractValue] at hentry
  have hneq : (0 : KeyScalar recommendedParams) ≠ 1 := by
    intro h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_one'' (by norm_num [recommendedParams])] at hval
    omega
  exact hneq hentry

/-- The recommended parameters with exact D3 sampling have positive first-exchange failure
probability. -/
theorem firstExchangeFailureProb_recommended_pos :
    0 < firstExchangeFailureProb recommendedParams d3Sampler := by
  rw [firstExchangeFailureProb]
  let afterCoins (ik : InitKey recommendedParams) (r : SendACoins recommendedParams) :
      ProbComp Bool :=
    pure (decide
      (reconcile recommendedParams
          ((r.secret * ik.baseMatrix + r.error) * ik.secret)
          (makeHint recommendedParams
            (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) ≠
        extract recommendedParams
          (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)))
  let afterInit (ik : InitKey recommendedParams) : ProbComp Bool :=
    sampleSendACoins recommendedParams d3Sampler >>= afterCoins ik
  have hout : true ∈ support (afterCoins failureInitKey failureSendACoins) := by
    change true ∈ support (pure (decide
      (reconcile recommendedParams failureReceiverValue
          (makeHint recommendedParams failureSenderValue) ≠
        extract recommendedParams failureSenderValue)) : ProbComp Bool)
    rw [failureWitness_true]
    simp
  have hafterInit : true ∈ support (afterInit failureInitKey) := by
    change true ∈ support
      (sampleSendACoins recommendedParams d3Sampler >>= afterCoins failureInitKey)
    exact mem_support_bind_intro failureSendACoins_mem_support hout
  change 0 < Pr[= true | initKeyGen recommendedParams d3Sampler >>= afterInit]
  rw [probOutput_bind_eq_tsum]
  have hterm :
      0 < Pr[= failureInitKey | initKeyGen recommendedParams d3Sampler] *
        Pr[= true | afterInit failureInitKey] :=
    ENNReal.mul_pos
      (ne_of_gt failureInitKey_prob_pos)
      (ne_of_gt (probOutput_pos _ _ hafterInit))
  exact lt_of_lt_of_le hterm (ENNReal.le_tsum failureInitKey)

end lweCKA
