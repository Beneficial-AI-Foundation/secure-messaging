/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Sampling
import SecureMessaging.CKA.FromLWE.NoiseCorrectness
import VCVio.EvalDist.IndepProduct
import VCVio.EvalDist.Monad.Map
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Entrywise first-exchange noise

This file identifies the distribution of each entry of the concrete first-exchange noise matrix
with the cast of an integer experiment that samples the same five independent D3 components.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA

/-- The integer noise in one entry of the first exchange. -/
def firstExchangeEntryNoiseIntExp : ProbComp ℤ := do
  let s0 ← ProbComp.sampleIID recommendedParams.n d3IntSampler
  let e0 ← ProbComp.sampleIID recommendedParams.n d3IntSampler
  let s1 ← ProbComp.sampleIID recommendedParams.n d3IntSampler
  let e1 ← ProbComp.sampleIID recommendedParams.n d3IntSampler
  let extra ← d3IntSampler
  return (∑ k : Fin recommendedParams.n, s1 k * e0 k) -
      (∑ k : Fin recommendedParams.n, e1 k * s0 k) + extra

private theorem evalDist_sampleIID_map
    {α β : Type} (n : ℕ) (χ : ProbComp α) (f : α → β) :
    finiteLaw
        ((fun xs : Fin n → α => fun k => f (xs k)) <$>
          ProbComp.sampleIID n χ) =
      finiteLaw (ProbComp.sampleIID n (f <$> χ)) := by
  induction n with
  | zero =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_pure]
      congr 2
      funext k
      exact k.elim0
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
      refine evalDist_bind_congr' χ fun a => ?_
      have htail := finiteLaw_map_congr ih
        (fun rest : Fin n → β => @Fin.cons n (fun _ => β) (f a) rest)
      convert htail using 1
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => χ) fun rest => ?_
        congr 2
        funext k
        exact Fin.cases (by simp) (fun l => by simp) k
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, Function.comp_def]

private theorem evalDist_sampleMatrix_row
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : prFail χ = 0) (rows cols : ℕ) (i : Fin rows) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m i) <$>
          sampleMatrix χ rows cols) =
      finiteLaw (ProbComp.sampleIID cols χ) := by
  apply evalDist_ext
  intro y
  rw [prEvent_map]
  unfold sampleMatrix ProbComp.sampleIID
  change
    Pr{let m ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[m i = y] =
      Pr{let x ← Fin.mOfFn cols fun _ => χ}[x = y]
  simpa only [Function.comp_apply] using
    probEvent_coord_mOfFn rows (fun _ => Fin.mOfFn cols fun _ => χ)
      (fun _ => probFailure_mOfFn cols (fun _ => χ) fun _ => hχ) i (· = y)

private theorem evalDist_sampleMatrix_col
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : prFail χ = 0) (rows cols : ℕ) (j : Fin cols) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) =>
            fun k => m k j) <$>
          sampleMatrix χ rows cols) =
      finiteLaw (ProbComp.sampleIID rows χ) := by
  calc
    finiteLaw
          ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => fun k => m k j) <$>
            sampleMatrix χ rows cols) =
        finiteLaw
          ((fun m : Matrix (Fin cols) (Fin rows) (Scalar p) => m j) <$>
            ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m.transpose) <$>
              sampleMatrix χ rows cols)) := by
          rw [Functor.map_map]
          congr 2
    _ = finiteLaw
          ((fun m : Matrix (Fin cols) (Fin rows) (Scalar p) => m j) <$>
            sampleMatrix χ cols rows) :=
        finiteLaw_map_congr
          (evalDist_sampleMatrix_transpose χ rows cols) (fun m => m j)
    _ = finiteLaw (ProbComp.sampleIID rows χ) :=
      evalDist_sampleMatrix_row χ hχ cols rows j

private theorem evalDist_sampleMatrix_entry
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : prFail χ = 0) (rows cols : ℕ)
    (i : Fin rows) (j : Fin cols) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m i j) <$>
          sampleMatrix χ rows cols) =
      finiteLaw χ := by
  apply evalDist_ext
  intro y
  rw [prEvent_map]
  unfold sampleMatrix ProbComp.sampleIID
  change
    Pr{let m ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[m i j = y] = Pr{let x ← χ}[x = y]
  calc
    Pr{let m ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[m i j = y] =
        Pr{let row ← Fin.mOfFn cols fun _ => χ}[row j = y] :=
      probEvent_coord_mOfFn rows (fun _ => Fin.mOfFn cols fun _ => χ)
        (fun _ => probFailure_mOfFn cols (fun _ => χ) fun _ => hχ) i
        (fun row : Fin cols → Scalar p => row j = y)
    _ = Pr{let x ← χ}[x = y] :=
      probEvent_coord_mOfFn cols (fun _ => χ) (fun _ => hχ) j (· = y)
    _ = Pr{let x ← χ}[x = y] := rfl

/-- Each entry of the matrix noise has the cast distribution of the integer entry experiment. -/
theorem evalDist_firstExchangeNoise_entry_eq_cast
    (i j : Fin recommendedParams.nbar) :
    finiteLaw
        ((fun z : ℤ => (z : Scalar recommendedParams)) <$>
          firstExchangeEntryNoiseIntExp) =
      finiteLaw
        ((fun delta : SharedMatrix recommendedParams => delta i j) <$>
          firstExchangeNoiseExp recommendedParams d3Sampler) := by
  let matrixProjectedExp : ProbComp (Scalar recommendedParams) := do
    let s0 ←
      (fun m : Matrix (Fin recommendedParams.n) (Fin recommendedParams.nbar)
          (Scalar recommendedParams) => fun k => m k j) <$>
        sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar
    let e0 ←
      (fun m : Matrix (Fin recommendedParams.n) (Fin recommendedParams.nbar)
          (Scalar recommendedParams) => fun k => m k j) <$>
        sampleMatrix d3Sampler recommendedParams.n recommendedParams.nbar
    let s1 ←
      (fun m : Matrix (Fin recommendedParams.nbar) (Fin recommendedParams.n)
          (Scalar recommendedParams) => m i) <$>
        sampleMatrix d3Sampler recommendedParams.nbar recommendedParams.n
    let e1 ←
      (fun m : Matrix (Fin recommendedParams.nbar) (Fin recommendedParams.n)
          (Scalar recommendedParams) => m i) <$>
        sampleMatrix d3Sampler recommendedParams.nbar recommendedParams.n
    let extra ←
      (fun m : SharedMatrix recommendedParams => m i j) <$>
        sampleMatrix d3Sampler recommendedParams.nbar recommendedParams.nbar
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  let scalarExp : ProbComp (Scalar recommendedParams) := do
    let s0 ← ProbComp.sampleIID recommendedParams.n d3Sampler
    let e0 ← ProbComp.sampleIID recommendedParams.n d3Sampler
    let s1 ← ProbComp.sampleIID recommendedParams.n d3Sampler
    let e1 ← ProbComp.sampleIID recommendedParams.n d3Sampler
    let extra ← d3Sampler
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  let mappedIntExp : ProbComp (Scalar recommendedParams) := do
    let s0 ←
      (fun xs : Fin recommendedParams.n → ℤ => fun k => (xs k : Scalar recommendedParams)) <$>
        ProbComp.sampleIID recommendedParams.n d3IntSampler
    let e0 ←
      (fun xs : Fin recommendedParams.n → ℤ => fun k => (xs k : Scalar recommendedParams)) <$>
        ProbComp.sampleIID recommendedParams.n d3IntSampler
    let s1 ←
      (fun xs : Fin recommendedParams.n → ℤ => fun k => (xs k : Scalar recommendedParams)) <$>
        ProbComp.sampleIID recommendedParams.n d3IntSampler
    let e1 ←
      (fun xs : Fin recommendedParams.n → ℤ => fun k => (xs k : Scalar recommendedParams)) <$>
        ProbComp.sampleIID recommendedParams.n d3IntSampler
    let extra ← (fun z : ℤ => (z : Scalar recommendedParams)) <$> d3IntSampler
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  have hActual :
      finiteLaw
          ((fun delta : SharedMatrix recommendedParams => delta i j) <$>
            firstExchangeNoiseExp recommendedParams d3Sampler) =
        finiteLaw matrixProjectedExp := by
    simp only [matrixProjectedExp, firstExchangeNoiseExp, initKeyGen, sampleSendACoins,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.mul_apply]
    exact lweCKA.evalDist_bind_const_neverFails
      (($ᵗ (BaseMatrix recommendedParams) : ProbComp (BaseMatrix recommendedParams)))
      (probFailure_eq_zero
        (mx := ($ᵗ (BaseMatrix recommendedParams) : ProbComp (BaseMatrix recommendedParams))))
      _
  have hHead {A B : Type} {mx my : ProbComp A}
      (h : finiteLaw mx = finiteLaw my) (k : A → ProbComp B) :
      finiteLaw (mx >>= k) = finiteLaw (my >>= k) := by
    simp only [evalDist_bind, h]
  have hMatrix : finiteLaw matrixProjectedExp = finiteLaw scalarExp := by
    simp only [matrixProjectedExp, scalarExp]
    refine (hHead (evalDist_sampleMatrix_col d3Sampler probFailure_eq_zero _ _ j) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_col d3Sampler probFailure_eq_zero _ _ j) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_row d3Sampler probFailure_eq_zero _ _ i) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_row d3Sampler probFailure_eq_zero _ _ i) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    exact hHead
      (evalDist_sampleMatrix_entry d3Sampler probFailure_eq_zero _ _ i j) _
  have hMapped : finiteLaw mappedIntExp = finiteLaw scalarExp := by
    simp only [mappedIntExp, scalarExp, d3Sampler]
    refine (hHead (evalDist_sampleIID_map recommendedParams.n d3IntSampler
      (fun z : ℤ => (z : Scalar recommendedParams))) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleIID_map recommendedParams.n d3IntSampler
      (fun z : ℤ => (z : Scalar recommendedParams))) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleIID_map recommendedParams.n d3IntSampler
      (fun z : ℤ => (z : Scalar recommendedParams))) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleIID_map recommendedParams.n d3IntSampler
      (fun z : ℤ => (z : Scalar recommendedParams))) _).trans ?_
    rfl
  have hCast :
      finiteLaw
          ((fun z : ℤ => (z : Scalar recommendedParams)) <$>
            firstExchangeEntryNoiseIntExp) = finiteLaw mappedIntExp := by
    simp only [firstExchangeEntryNoiseIntExp, mappedIntExp, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_apply]
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    simp only [Int.cast_add, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  calc
    finiteLaw
          ((fun z : ℤ => (z : Scalar recommendedParams)) <$>
            firstExchangeEntryNoiseIntExp) = finiteLaw scalarExp := hCast.trans hMapped
    _ = finiteLaw
          ((fun delta : SharedMatrix recommendedParams => delta i j) <$>
            firstExchangeNoiseExp recommendedParams d3Sampler) :=
      hMatrix.symm.trans hActual.symm

end lweCKA
