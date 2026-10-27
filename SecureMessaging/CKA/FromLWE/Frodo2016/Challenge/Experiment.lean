/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.Experiment.NoisePhase
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# The historical Challenge experiment

This file completes the comparison between one actual Challenge entry-mismatch
probability and the exact modular phase ramp.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA

open Frodo2016.Challenge.Experiment.Internal

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
    {D R α : Type} [Finite D] [DecidableEq D] [Finite R]
    [SampleableType R] [SampleableType (D → R)] (t : D) (ψ : (D → R) → α) :
    finiteLaw
        (do
          let u ← ($ᵗ R : ProbComp R)
          let g ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (ψ (Function.update g t u))) =
      finiteLaw (ψ <$> ($ᵗ (D → R) : ProbComp (D → R))) := by
  rw [map_eq_bind_pure_comp]
  letI : MeasurableSpace R := ⊤
  letI : MeasurableSpace α := ⊤
  exact OracleComp.evalDist_uniformSample_bind_update_map
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample t ψ

private theorem evalDist_uniform_update_nested_map
    {D E R α : Type} [Finite D] [DecidableEq D] [Finite (E → R)]
    [SampleableType (E → R)] [SampleableType (D → E → R)]
    (t : D) (ψ : (D → E → R) → α) :
    finiteLaw
        (do
          let u ← ($ᵗ (E → R) : ProbComp (E → R))
          let g ← ($ᵗ (D → E → R) : ProbComp (D → E → R))
          pure (ψ (Function.update g t u))) =
      finiteLaw (ψ <$> ($ᵗ (D → E → R) : ProbComp (D → E → R))) := by
  exact evalDist_uniform_update_map (D := D) (R := E → R) (α := α) t ψ

private theorem evalDist_uniform_update_bind
    {D R α : Type} [Finite D] [DecidableEq D] [Finite R]
    [SampleableType R] [SampleableType (D → R)] (t : D) (ψ : (D → R) → α) :
    finiteLaw
        (do
          let u ← ($ᵗ R : ProbComp R)
          let g ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (ψ (Function.update g t u))) =
      finiteLaw
        (do
          let g ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (ψ g)) := by
  letI : MeasurableSpace R := ⊤
  letI : MeasurableSpace α := ⊤
  exact OracleComp.evalDist_uniformSample_bind_update_map
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample t ψ

private theorem evalDist_challengeBase_update_row
    {α : Type} (k : Fin challengeParams.n)
    (ψ : BaseMatrix challengeParams → α) :
    finiteLaw
        (do
          let r ← ($ᵗ (Fin challengeParams.n → Scalar challengeParams) :
            ProbComp (Fin challengeParams.n → Scalar challengeParams))
          let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
          pure (ψ (Function.update a k r))) =
      finiteLaw
        (ψ <$> ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))) := by
  exact @evalDist_uniform_update_nested_map
    (Fin challengeParams.n)
    (Fin challengeParams.n)
    (Scalar challengeParams)
    α
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
    finiteLaw
        (do
          let x ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
          let r ← ($ᵗ (Fin challengeParams.n → Scalar challengeParams) :
            ProbComp (Fin challengeParams.n → Scalar challengeParams))
          pure (ψ (Function.update r l x))) =
      finiteLaw
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
    (h : finiteLaw (f <$> oa) = finiteLaw ob) :
    finiteLaw (oa >>= fun x => pure (f x)) = finiteLaw ob := by
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
    finiteLaw
        ((fun x : Scalar challengeParams =>
          challengeSenderScalar challengeParams c t
            (challengeBaseReplace challengeParams a k l r x)) <$>
          ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))) =
      finiteLaw ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)) := by
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
    finiteLaw
        ((fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a) <$>
          ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))) =
      finiteLaw
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
    finiteLaw
          ((fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a) <$>
            baseSample) =
        finiteLaw
          (do
            let r ← rowSample
            let a ← baseSample
            return challengeSenderScalar challengeParams c t (Function.update a k r)) := by
      exact (evalDist_challengeBase_update_row k
        (fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a)).symm
    _ = finiteLaw
          (do
            let a ← baseSample
            let r ← rowSample
            return challengeSenderScalar challengeParams c t (Function.update a k r)) :=
      evalDist_bind_bind_swap rowSample baseSample _
    _ = finiteLaw
          (do
            let a ← baseSample
            let x ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
            let r ← rowSample
            return challengeSenderScalar challengeParams c t
              (challengeBaseReplace challengeParams a k l r x)) := by
      refine evalDist_bind_congr' baseSample fun a => ?_
      exact (evalDist_challengeRow_update_cell l
        (fun r : rowType => challengeSenderScalar challengeParams c t (Function.update a k r))).symm
    _ = finiteLaw
          (do
            let a ← baseSample
            let r ← rowSample
            let x ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))
            return challengeSenderScalar challengeParams c t
              (challengeBaseReplace challengeParams a k l r x)) := by
      refine evalDist_bind_congr' baseSample fun a => ?_
      exact evalDist_bind_bind_swap
        ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)) rowSample _
    _ = finiteLaw
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
    _ = finiteLaw
          ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams)) := by
      rw [lweCKA.evalDist_bind_const_neverFails
        baseSample probFailure_eq_zero]
      rw [lweCKA.evalDist_bind_const_neverFails
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
    Pr{let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))}[challengeEntryMismatch c (challengeWithBase a t)] =
      challengeFailureRamp (challengeEntryNoiseInt c t) := by
  let phaseBad := fun v : Scalar challengeParams =>
    1024 ≤
      ((((v.val % 512 + 256 : ℕ) : Scalar challengeParams) -
        (challengeEntryNoiseInt c t : Scalar challengeParams)).val)
  calc
    Pr{let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))}[challengeEntryMismatch c (challengeWithBase a t)] =
        Pr{let x ← ((fun a : BaseMatrix challengeParams => challengeSenderScalar challengeParams c t a) <$>
            ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams)))}[phaseBad x] := by
      rw [prEvent_map]
      apply probEvent_congr'
      · intro a _
        exact challengeEntryMismatch_withBase_iff_phase c t a
      · rfl
    _ = Pr{let x ← ($ᵗ (Scalar challengeParams) : ProbComp (Scalar challengeParams))}[phaseBad x] := by
      simp only [probEvent_def, evalDist_challengeSender_uniform_of_not_bad c t hgood]
    _ = challengeFailureRamp (challengeEntryNoiseInt c t) :=
      probEvent_uniform_phase_eq_challengeFailureRamp (challengeEntryNoiseInt c t)

private noncomputable def challengeFixedFailure
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) : ℝ≥0∞ :=
  Pr{let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))}[challengeEntryMismatch c (challengeWithBase a t)]

private noncomputable local instance challengeEntryBadDecidable
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    Decidable (challengeEntryBad c t) :=
  Classical.propDecidable _

private theorem evalDist_challengeEntryNoiseInt_noiseCoins
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    finiteLaw ((fun t => challengeEntryNoiseInt c t) <$> challengeNoiseCoinsExp) =
      finiteLaw challengeEntryNoiseIntExp := by
  let withBaseExp : ProbComp (InitKey challengeParams × SendACoins challengeParams) := do
    let t ← challengeNoiseCoinsExp
    let a ← ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))
    return challengeWithBase a t
  have hdrop :
      finiteLaw ((fun t => challengeEntryNoiseInt c t) <$> withBaseExp) =
        finiteLaw ((fun t => challengeEntryNoiseInt c t) <$> challengeNoiseCoinsExp) := by
    simp only [withBaseExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    refine evalDist_bind_congr' challengeNoiseCoinsExp fun t => ?_
    convert lweCKA.evalDist_bind_const_neverFails
      (($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams)))
      probFailure_eq_zero (pure (challengeEntryNoiseInt c t)) using 1 <;>
        rfl
  have hmap := finiteLaw_map_congr evalDist_challengeCoinsExp_noiseFirst
    (fun t => challengeEntryNoiseInt c t)
  exact hdrop.symm.trans (hmap.symm.trans (evalDist_challengeEntryNoiseInt c))

private theorem probEvent_bind_pure_map
    {α β : Type} (mx : ProbComp α) (f : α → β) (q : β → Prop) :
    Pr{let y ← mx >>= fun x => pure (f x)}[q y] = Pr{let x ← mx}[q (f x)] := by
  simpa only [bind_pure_comp] using prEvent_map mx f q

private theorem probEvent_challengeEntryMismatch_eq_expectedFixed
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    Pr{let x ← challengeCoinsExp}[(challengeEntryMismatch c) x] =
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
  rw [hprob, OracleComp.prEvent_bind_eq_tsum]
  rw [expectedValue_def]
  unfold challengeFixedFailure
  apply tsum_congr
  intro t
  apply congrArg (fun q : ℝ≥0∞ => Pr{let x ← challengeNoiseCoinsExp}[x = t] * q)
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
      Pr{let x ← challengeNoiseCoinsExp}[(challengeEntryBad c) x] := by
  classical
  rw [expectedValue_def, OracleComp.prEvent_eq_tsum_ite]
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
    exact (prEvent_le_one _).trans (le_add_left le_rfl)
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
    (Pr{let x ← challengeCoinsExp}[(challengeEntryMismatch c) x] ≤
      expectedValue challengeEntryNoiseIntExp challengeFailureRamp +
        1 / (2 : ℝ≥0∞) ^ 351) ∧
    (expectedValue challengeEntryNoiseIntExp challengeFailureRamp ≤
      Pr{let x ← challengeCoinsExp}[(challengeEntryMismatch c) x] +
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
          Pr{let x ← challengeNoiseCoinsExp}[(challengeEntryBad c) x] := by
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
          Pr{let x ← challengeNoiseCoinsExp}[(challengeEntryBad c) x] := by
        rw [expectedValue_add, expectedValue_noiseCoins_badIndicator c]
      _ ≤ expectedValue challengeNoiseCoinsExp (challengeFixedFailure c) +
          1 / (2 : ℝ≥0∞) ^ 351 :=
        add_le_add_right (probEvent_challengeEntryBad_le c) _

end lweCKA
