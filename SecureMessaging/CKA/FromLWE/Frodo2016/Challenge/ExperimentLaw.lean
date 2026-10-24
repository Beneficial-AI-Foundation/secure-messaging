/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Sampling
import SecureMessaging.CKA.FromLWE.NoiseCorrectness
import SecureMessaging.CKA.FromLWE.ReconciliationPhase
import VCVio.EvalDist.IndepProduct
import VCVio.EvalDist.Monad.Map
import VCVio.EvalDist.Expectation
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Challenge entry-noise law

This file defines the Challenge-parameter first exchange with a uniformly sampled public matrix
and the exact D1 sampler. It relates entry noise to its centered integer law and defines the
modular phase ramp. `ChallengeExperiment` compares entry-mismatch probability with this ramp,
allowing the mass where at least one relevant secret vector has no odd entry.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

/-- The common coins of the actual Challenge-parameter first exchange. -/
def challengeCoinsExp :
    ProbComp (InitKey challengeParams × SendACoins challengeParams) := do
  let ik ← initKeyGen challengeParams d1Sampler
  let r ← sampleSendACoins challengeParams d1Sampler
  return (ik, r)

/-- The event that one Challenge key entry differs after reconciliation. -/
def challengeEntryMismatch
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) : Prop :=
  let v := t.2.secret * (t.1.baseMatrix * t.1.secret + t.1.error) + t.2.extra
  let w := (t.2.secret * t.1.baseMatrix + t.2.error) * t.1.secret
  reconcileScalar challengeParams (w c.1 c.2)
      (hintScalar challengeParams (v c.1 c.2)) ≠
    extractScalar challengeParams (v c.1 c.2)

/-- The centered integer sender-minus-receiver noise in one Challenge entry. -/
def challengeEntryNoiseInt
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) : ℤ :=
  (∑ k : Fin challengeParams.n,
    (t.2.secret c.1 k).valMinAbs * (t.1.error k c.2).valMinAbs) -
  (∑ k : Fin challengeParams.n,
    (t.2.error c.1 k).valMinAbs * (t.1.secret k c.2).valMinAbs) +
  (t.2.extra c.1 c.2).valMinAbs

/-- The independent integer experiment giving one Challenge entry's centered noise law. -/
def challengeEntryNoiseIntExp : ProbComp ℤ := do
  let s0 ← ProbComp.sampleIID challengeParams.n d1IntSampler
  let e0 ← ProbComp.sampleIID challengeParams.n d1IntSampler
  let s1 ← ProbComp.sampleIID challengeParams.n d1IntSampler
  let e1 ← ProbComp.sampleIID challengeParams.n d1IntSampler
  let extra ← d1IntSampler
  return (∑ k : Fin challengeParams.n, s1 k * e0 k) -
    (∑ k : Fin challengeParams.n, e1 k * s0 k) + extra

/-- The exact fraction of sender phases that fail for a fixed centered integer noise. -/
noncomputable def challengeFailureRamp (z : ℤ) : ℝ≥0∞ :=
  (min 512
    (modularDistance challengeParams (z : Scalar challengeParams) 0 - 256) :
      ℝ≥0∞) / 512

private theorem matrix_ne_iff_exists_entry_ne
    {m n α : Type}
    (x y : Matrix m n α) :
    x ≠ y ↔ ∃ c : m × n, x c.1 c.2 ≠ y c.1 c.2 := by
  constructor
  · intro hxy
    by_contra h
    push Not at h
    apply hxy
    ext i j
    exact h (i, j)
  · rintro ⟨c, hc⟩ hxy
    exact hc (congrFun (congrFun hxy c.1) c.2)

/-- Whole-key failure is exactly the union of the 64 entry-mismatch events. -/
theorem firstExchangeFailureProb_challenge_eq_entry_union :
    firstExchangeFailureProb challengeParams d1Sampler =
      Pr[fun t =>
        ∃ c : Fin challengeParams.nbar × Fin challengeParams.nbar,
          challengeEntryMismatch c t | challengeCoinsExp] := by
  classical
  rw [firstExchangeFailureProb, ← probEvent_eq_eq_probOutput]
  simp only [firstExchangeFailureExp, challengeCoinsExp, probEvent_bind_eq_tsum,
    probEvent_pure]
  apply tsum_congr
  intro ik
  congr 1
  apply tsum_congr
  intro r
  congr 1
  have hentries := matrix_ne_iff_exists_entry_ne
    (reconcile challengeParams
      ((r.secret * ik.baseMatrix + r.error) * ik.secret)
      (makeHint challengeParams
        (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)))
    (extract challengeParams
      (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra))
  have hevents :
      (reconcile challengeParams
          ((r.secret * ik.baseMatrix + r.error) * ik.secret)
          (makeHint challengeParams
            (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) ≠
        extract challengeParams
          (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) ↔
        ∃ c, challengeEntryMismatch c (ik, r) := by
    rw [hentries]
    rfl
  simp only [decide_eq_true_eq, hevents]

private theorem valMinAbs_intCast_eq_of_mem_d1_support
    (z : ℤ) (hz : z ∈ support d1IntSampler) :
    ((z : Scalar challengeParams).valMinAbs) = z := by
  apply (ZMod.valMinAbs_spec (z : Scalar challengeParams) z).2
  constructor
  · rfl
  · rw [support_d1IntSampler] at hz
    simp only [Set.mem_Icc] at hz
    change z * 2 ∈ Set.Ioc (-(challengeParams.q : ℤ)) challengeParams.q
    simp only [Set.mem_Ioc, challengeParams, Params.q]
    omega

/-- Taking the centered representative of a modular D1 draw recovers the signed D1 law. -/
theorem evalDist_valMinAbs_d1Sampler :
    evalDist
        ((fun x : Scalar challengeParams => x.valMinAbs) <$> d1Sampler) =
      evalDist d1IntSampler := by
  simp only [d1Sampler, map_eq_bind_pure_comp]
  calc
    evalDist
          (d1IntSampler >>= fun z =>
            pure ((z : Scalar challengeParams).valMinAbs)) =
        evalDist (d1IntSampler >>= fun z => pure z) := by
      apply evalDist_bind_congr
      intro z hz
      rw [valMinAbs_intCast_eq_of_mem_d1_support z hz]
    _ = evalDist d1IntSampler := by rw [bind_pure]

private theorem evalDist_sampleIID_map
    {α β : Type} (n : ℕ) (χ : ProbComp α) (f : α → β) :
    evalDist
        ((fun xs : Fin n → α => fun k => f (xs k)) <$>
          ProbComp.sampleIID n χ) =
      evalDist (ProbComp.sampleIID n (f <$> χ)) := by
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
      have htail := evalDist_map_eq_of_evalDist_eq ih
        (fun rest : Fin n → β => @Fin.cons n (fun _ => β) (f a) rest)
      convert htail using 1
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => χ) fun rest => ?_
        congr 2
        funext k
        exact Fin.cases (by simp) (fun l => by simp) k
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, Function.comp_def]

private theorem evalDist_sampleIID_congr
    {α : Type} (n : ℕ) (χ ψ : ProbComp α)
    (hχψ : evalDist χ = evalDist ψ) :
    evalDist (ProbComp.sampleIID n χ) =
    evalDist (ProbComp.sampleIID n ψ) := by
  apply evalDist_ext
  intro v
  simp only [ProbComp.sampleIID, probOutput_mOfFn]
  apply Finset.prod_congr rfl
  intro i _
  exact evalDist_ext_iff.mp hχψ (v i)

private theorem evalDist_sampleMatrix_row
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ) (i : Fin rows) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m i) <$>
          sampleMatrix χ rows cols) =
      evalDist (ProbComp.sampleIID cols χ) := by
  apply evalDist_ext
  intro y
  rw [probOutput_map]
  unfold sampleMatrix ProbComp.sampleIID
  change
    Pr[fun m : Fin rows → Fin cols → Scalar p => m i = y |
      Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ] =
      Pr[= y | Fin.mOfFn cols fun _ => χ]
  simpa only [Function.comp_apply, probEvent_eq_eq_probOutput] using
    probEvent_coord_mOfFn rows (fun _ => Fin.mOfFn cols fun _ => χ)
      (fun _ => probFailure_mOfFn cols (fun _ => χ) fun _ => hχ) i (· = y)

private theorem evalDist_sampleMatrix_col
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ) (j : Fin cols) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) =>
            fun k => m k j) <$>
          sampleMatrix χ rows cols) =
      evalDist (ProbComp.sampleIID rows χ) := by
  calc
    evalDist
          ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => fun k => m k j) <$>
            sampleMatrix χ rows cols) =
        evalDist
          ((fun m : Matrix (Fin cols) (Fin rows) (Scalar p) => m j) <$>
            ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m.transpose) <$>
              sampleMatrix χ rows cols)) := by
          rw [Functor.map_map]
          congr 2
    _ = evalDist
          ((fun m : Matrix (Fin cols) (Fin rows) (Scalar p) => m j) <$>
            sampleMatrix χ cols rows) :=
        evalDist_map_eq_of_evalDist_eq
          (evalDist_sampleMatrix_transpose χ rows cols) (fun m => m j)
    _ = evalDist (ProbComp.sampleIID rows χ) :=
      evalDist_sampleMatrix_row χ hχ cols rows j

/-- Evaluation law for binding a sampled matrix to one selected row. -/
theorem ChallengeExperimentLaw.evalDist_sampleMatrix_row_bind
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ) (i : Fin rows) :
    evalDist
        (sampleMatrix χ rows cols >>= fun m => pure (m i)) =
      evalDist (ProbComp.sampleIID cols χ) := by
  rw [show
    (sampleMatrix χ rows cols >>= fun m => pure (m i)) =
      ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m i) <$>
        sampleMatrix χ rows cols) from
    (map_eq_bind_pure_comp ProbComp _ _).symm]
  exact evalDist_sampleMatrix_row χ hχ rows cols i

/-- Evaluation law for binding a sampled matrix to one selected column. -/
theorem ChallengeExperimentLaw.evalDist_sampleMatrix_col_bind
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ) (j : Fin cols) :
    evalDist
        (sampleMatrix χ rows cols >>= fun m => pure (fun k => m k j)) =
      evalDist (ProbComp.sampleIID rows χ) := by
  rw [show
    (sampleMatrix χ rows cols >>= fun m => pure (fun k => m k j)) =
      ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => fun k => m k j) <$>
        sampleMatrix χ rows cols) from
    (map_eq_bind_pure_comp ProbComp _ _).symm]
  exact evalDist_sampleMatrix_col χ hχ rows cols j

private theorem evalDist_sampleMatrix_entry
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ)
    (i : Fin rows) (j : Fin cols) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m i j) <$>
          sampleMatrix χ rows cols) =
      evalDist χ := by
  apply evalDist_ext
  intro y
  rw [probOutput_map]
  unfold sampleMatrix ProbComp.sampleIID
  change
    Pr[fun m : Fin rows → Fin cols → Scalar p => m i j = y |
      Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ] = Pr[= y | χ]
  calc
    Pr[fun m : Fin rows → Fin cols → Scalar p => m i j = y |
        Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ] =
        Pr[fun row : Fin cols → Scalar p => row j = y |
          Fin.mOfFn cols fun _ => χ] :=
      probEvent_coord_mOfFn rows (fun _ => Fin.mOfFn cols fun _ => χ)
        (fun _ => probFailure_mOfFn cols (fun _ => χ) fun _ => hχ) i
        (fun row : Fin cols → Scalar p => row j = y)
    _ = Pr[(· = y) | χ] :=
      probEvent_coord_mOfFn cols (fun _ => χ) (fun _ => hχ) j (· = y)
    _ = Pr[= y | χ] := probEvent_eq_eq_probOutput χ y

private theorem evalDist_sampleMatrix_row_valMinAbs
    (rows cols : ℕ) (i : Fin rows) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
            fun k => (m i k).valMinAbs) <$>
          sampleMatrix d1Sampler rows cols) =
      evalDist (ProbComp.sampleIID cols d1IntSampler) := by
  calc
    evalDist
          ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
              fun k => (m i k).valMinAbs) <$>
            sampleMatrix d1Sampler rows cols) =
        evalDist
          ((fun xs : Fin cols → Scalar challengeParams =>
              fun k => (xs k).valMinAbs) <$>
            ProbComp.sampleIID cols d1Sampler) := by
      simpa only [Functor.map_map, Function.comp_apply] using
        (evalDist_map_eq_of_evalDist_eq
          (evalDist_sampleMatrix_row d1Sampler probFailure_eq_zero rows cols i)
          (fun xs : Fin cols → Scalar challengeParams => fun k => (xs k).valMinAbs))
    _ = evalDist
          (ProbComp.sampleIID cols
            ((fun x : Scalar challengeParams => x.valMinAbs) <$> d1Sampler)) :=
      evalDist_sampleIID_map cols d1Sampler (fun x => x.valMinAbs)
    _ = evalDist (ProbComp.sampleIID cols d1IntSampler) :=
      evalDist_sampleIID_congr cols _ _ evalDist_valMinAbs_d1Sampler

private theorem evalDist_sampleMatrix_col_valMinAbs
    (rows cols : ℕ) (j : Fin cols) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
            fun k => (m k j).valMinAbs) <$>
          sampleMatrix d1Sampler rows cols) =
      evalDist (ProbComp.sampleIID rows d1IntSampler) := by
  calc
    evalDist
          ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
              fun k => (m k j).valMinAbs) <$>
            sampleMatrix d1Sampler rows cols) =
        evalDist
          ((fun xs : Fin rows → Scalar challengeParams =>
              fun k => (xs k).valMinAbs) <$>
            ProbComp.sampleIID rows d1Sampler) := by
      simpa only [Functor.map_map, Function.comp_apply] using
        (evalDist_map_eq_of_evalDist_eq
          (evalDist_sampleMatrix_col d1Sampler probFailure_eq_zero rows cols j)
          (fun xs : Fin rows → Scalar challengeParams => fun k => (xs k).valMinAbs))
    _ = evalDist
          (ProbComp.sampleIID rows
            ((fun x : Scalar challengeParams => x.valMinAbs) <$> d1Sampler)) :=
      evalDist_sampleIID_map rows d1Sampler (fun x => x.valMinAbs)
    _ = evalDist (ProbComp.sampleIID rows d1IntSampler) :=
      evalDist_sampleIID_congr rows _ _ evalDist_valMinAbs_d1Sampler

private theorem evalDist_sampleMatrix_entry_valMinAbs
    (rows cols : ℕ) (i : Fin rows) (j : Fin cols) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
            (m i j).valMinAbs) <$>
          sampleMatrix d1Sampler rows cols) =
      evalDist d1IntSampler := by
  calc
    evalDist
          ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
              (m i j).valMinAbs) <$>
            sampleMatrix d1Sampler rows cols) =
        evalDist
          ((fun x : Scalar challengeParams => x.valMinAbs) <$> d1Sampler) := by
      simpa only [Functor.map_map, Function.comp_apply] using
        (evalDist_map_eq_of_evalDist_eq
          (evalDist_sampleMatrix_entry d1Sampler probFailure_eq_zero rows cols i j)
          (fun x : Scalar challengeParams => x.valMinAbs))
    _ = evalDist d1IntSampler := evalDist_valMinAbs_d1Sampler

/-- The centered integer noise extracted from an actual entry has the independent scalar law. -/
theorem evalDist_challengeEntryNoiseInt
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar) :
    evalDist ((fun t => challengeEntryNoiseInt c t) <$> challengeCoinsExp) =
      evalDist challengeEntryNoiseIntExp := by
  let projectedExp : ProbComp ℤ := do
    let s0 ←
      (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar)
          (Scalar challengeParams) => fun k => (m k c.2).valMinAbs) <$>
        sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
    let e0 ←
      (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar)
          (Scalar challengeParams) => fun k => (m k c.2).valMinAbs) <$>
        sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
    let s1 ←
      (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n)
          (Scalar challengeParams) => fun k => (m c.1 k).valMinAbs) <$>
        sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
    let e1 ←
      (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n)
          (Scalar challengeParams) => fun k => (m c.1 k).valMinAbs) <$>
        sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
    let extra ←
      (fun m : SharedMatrix challengeParams => (m c.1 c.2).valMinAbs) <$>
        sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  have hActual :
      evalDist ((fun t => challengeEntryNoiseInt c t) <$> challengeCoinsExp) =
        evalDist projectedExp := by
    simp only [challengeCoinsExp, challengeEntryNoiseInt, projectedExp, initKeyGen,
      sampleSendACoins, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams)))
      (probFailure_eq_zero
        (mx := ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))))
      _
  have hHead {A B : Type} {mx my : ProbComp A}
      (h : evalDist mx = evalDist my) (k : A → ProbComp B) :
      evalDist (mx >>= k) = evalDist (my >>= k) := by
    simp only [evalDist_bind, h]
  have hProjected : evalDist projectedExp = evalDist challengeEntryNoiseIntExp := by
    simp only [projectedExp, challengeEntryNoiseIntExp]
    refine (hHead (evalDist_sampleMatrix_col_valMinAbs _ _ c.2) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_col_valMinAbs _ _ c.2) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_row_valMinAbs _ _ c.1) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_row_valMinAbs _ _ c.1) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    exact hHead (evalDist_sampleMatrix_entry_valMinAbs _ _ c.1 c.2) _
  exact hActual.trans hProjected

end lweCKA
