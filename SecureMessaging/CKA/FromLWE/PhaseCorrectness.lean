/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ChallengeExperimentLaw
import SecureMessaging.CKA.FromLWE.NoiseCorrectness
import SecureMessaging.CKA.FromLWE.ReconciliationPhase
import VCVio.EvalDist.Expectation
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Generic phase correctness for historical Frodo parameters

The public matrix is uniform.  After conditioning on all noise coins, an odd coefficient in
each of the two relevant secret vectors makes one public-matrix cell an affine uniformizer.
The exceptional all-even vectors are retained explicitly.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

/-- The integer noise in one entry of a first exchange. -/
def entryNoiseIntExp (n : ℕ) (χ : ProbComp ℤ) : ProbComp ℤ := do
  let s0 ← ProbComp.sampleIID n χ
  let e0 ← ProbComp.sampleIID n χ
  let s1 ← ProbComp.sampleIID n χ
  let e1 ← ProbComp.sampleIID n χ
  let extra ← χ
  return (∑ k : Fin n, s1 k * e0 k) -
    (∑ k : Fin n, e1 k * s0 k) + extra

/-- The fraction of sender phases that fail for a fixed integer noise value. -/
noncomputable def reconciliationFailureRamp (p : Params) (z : ℤ) : ℝ≥0∞ :=
  (min p.halfWidth (modularDistance p (z : Scalar p) 0 -
    2 ^ (p.discardBits - 2)) : ℝ≥0∞) / p.halfWidth

private noncomputable def scalarFailureRamp (p : Params) (z : Scalar p) : ℝ≥0∞ :=
  (min p.halfWidth
    (modularDistance p z 0 - 2 ^ (p.discardBits - 2)) : ℝ≥0∞) / p.halfWidth

private def coinsExp (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (InitKey p × SendACoins p) := do
  let ik ← initKeyGen p χ
  let r ← sampleSendACoins p χ
  return (ik, r)

private def entryMismatch
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) : Prop :=
  let v := t.2.secret * (t.1.baseMatrix * t.1.secret + t.1.error) + t.2.extra
  let w := (t.2.secret * t.1.baseMatrix + t.2.error) * t.1.secret
  reconcileScalar p (w c.1 c.2) (hintScalar p (v c.1 c.2)) ≠
    extractScalar p (v c.1 c.2)

private def noiseCoinsExp (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (InitKey p × SendACoins p) := do
  let s0 ← sampleMatrix χ p.n p.nbar
  let e0 ← sampleMatrix χ p.n p.nbar
  let s1 ← sampleMatrix χ p.nbar p.n
  let e1 ← sampleMatrix χ p.nbar p.n
  let extra ← sampleMatrix χ p.nbar p.nbar
  pure (({ baseMatrix := 0, secret := s0, error := e0 } : InitKey p),
    ({ secret := s1, error := e1, extra := extra } : SendACoins p))

private def withBase
    (p : Params) (a : BaseMatrix p) (t : InitKey p × SendACoins p) :
    InitKey p × SendACoins p :=
  ({ t.1 with baseMatrix := a }, t.2)

private def entryBad
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) : Prop :=
  (∀ k : Fin p.n, Even (t.2.secret c.1 k).val) ∨
  (∀ k : Fin p.n, Even (t.1.secret k c.2).val)

private def entryNoiseScalar
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) : Scalar p :=
  (t.2.secret * t.1.error - t.2.error * t.1.secret + t.2.extra) c.1 c.2

private theorem matrix_ne_iff_exists_entry_ne
    {m n α : Type} (x y : Matrix m n α) :
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

private theorem firstExchangeFailureProb_eq_entry_union
    (p : Params) (χ : ProbComp (Scalar p)) :
    firstExchangeFailureProb p χ =
      Pr[fun t => ∃ c : Fin p.nbar × Fin p.nbar, entryMismatch p c t |
        coinsExp p χ] := by
  classical
  rw [firstExchangeFailureProb, ← probEvent_eq_eq_probOutput]
  simp only [firstExchangeFailureExp, coinsExp, probEvent_bind_eq_tsum,
    probEvent_pure]
  apply tsum_congr
  intro ik
  congr 1
  apply tsum_congr
  intro r
  congr 1
  have hentries := matrix_ne_iff_exists_entry_ne
    (reconcile p ((r.secret * ik.baseMatrix + r.error) * ik.secret)
      (makeHint p (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)))
    (extract p (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra))
  have hevents :
      (reconcile p ((r.secret * ik.baseMatrix + r.error) * ik.secret)
          (makeHint p (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) ≠
        extract p (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) ↔
        ∃ c, entryMismatch p c (ik, r) := by
    rw [hentries]
    rfl
  simp only [decide_eq_true_eq, hevents]

private theorem evalDist_coinsExp_noiseFirst
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist (coinsExp p χ) =
      evalDist (do
        let t ← noiseCoinsExp p χ
        let a ← ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
        return withBase p a t) := by
  simp only [coinsExp, noiseCoinsExp, withBase, initKeyGen, sampleSendACoins,
    bind_assoc, pure_bind]
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
    (sampleMatrix χ p.n p.nbar)]
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
    (sampleMatrix χ p.n p.nbar)]
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
    (sampleMatrix χ p.nbar p.n)]
  refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
    (sampleMatrix χ p.nbar p.n)]
  refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
  rw [evalDist_bind_bind_swap
    ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
    (sampleMatrix χ p.nbar p.nbar)]

private theorem evalDist_sampleIID_map
    {α β : Type} (n : ℕ) (χ : ProbComp α) (f : α → β) :
    evalDist ((fun xs : Fin n → α => fun k => f (xs k)) <$>
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

private theorem evalDist_sampleMatrix_entry
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ)
    (i : Fin rows) (j : Fin cols) :
    evalDist ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m i j) <$>
      sampleMatrix χ rows cols) = evalDist χ := by
  apply evalDist_ext
  intro y
  rw [probOutput_map]
  unfold sampleMatrix ProbComp.sampleIID
  change Pr[fun m : Fin rows → Fin cols → Scalar p => m i j = y |
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

private theorem evalDist_sampleMatrix_row
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ) (i : Fin rows) :
    evalDist ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m i) <$>
      sampleMatrix χ rows cols) = evalDist (ProbComp.sampleIID cols χ) := by
  rw [map_eq_bind_pure_comp]
  exact ChallengeExperimentLaw.evalDist_sampleMatrix_row_bind χ hχ rows cols i

private theorem evalDist_sampleMatrix_col
    {p : Params} (χ : ProbComp (Scalar p))
    (hχ : Pr[⊥ | χ] = 0) (rows cols : ℕ) (j : Fin cols) :
    evalDist ((fun m : Matrix (Fin rows) (Fin cols) (Scalar p) =>
      fun k => m k j) <$> sampleMatrix χ rows cols) =
      evalDist (ProbComp.sampleIID rows χ) := by
  rw [map_eq_bind_pure_comp]
  exact ChallengeExperimentLaw.evalDist_sampleMatrix_col_bind χ hχ rows cols j

private theorem evalDist_entryNoiseScalar_eq_cast
    (p : Params) (χ : ProbComp ℤ) (hχ : Pr[⊥ | χ] = 0)
    (c : Fin p.nbar × Fin p.nbar) :
    evalDist ((fun z : ℤ => (z : Scalar p)) <$> entryNoiseIntExp p.n χ) =
      evalDist ((fun t => entryNoiseScalar p c t) <$> noiseCoinsExp p
        ((fun z : ℤ => (z : Scalar p)) <$> χ)) := by
  let χm : ProbComp (Scalar p) := (fun z : ℤ => (z : Scalar p)) <$> χ
  have hχm : Pr[⊥ | χm] = 0 := by
    simpa only [χm, probFailure_map] using hχ
  let matrixProjectedExp : ProbComp (Scalar p) := do
    let s0 ← (fun m : RightMatrix p => fun k => m k c.2) <$> sampleMatrix χm p.n p.nbar
    let e0 ← (fun m : RightMatrix p => fun k => m k c.2) <$> sampleMatrix χm p.n p.nbar
    let s1 ← (fun m : LeftMatrix p => m c.1) <$> sampleMatrix χm p.nbar p.n
    let e1 ← (fun m : LeftMatrix p => m c.1) <$> sampleMatrix χm p.nbar p.n
    let extra ← (fun m : SharedMatrix p => m c.1 c.2) <$> sampleMatrix χm p.nbar p.nbar
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  let scalarExp : ProbComp (Scalar p) := do
    let s0 ← ProbComp.sampleIID p.n χm
    let e0 ← ProbComp.sampleIID p.n χm
    let s1 ← ProbComp.sampleIID p.n χm
    let e1 ← ProbComp.sampleIID p.n χm
    let extra ← χm
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  let mappedIntExp : ProbComp (Scalar p) := do
    let s0 ← (fun xs : Fin p.n → ℤ => fun k => (xs k : Scalar p)) <$>
      ProbComp.sampleIID p.n χ
    let e0 ← (fun xs : Fin p.n → ℤ => fun k => (xs k : Scalar p)) <$>
      ProbComp.sampleIID p.n χ
    let s1 ← (fun xs : Fin p.n → ℤ => fun k => (xs k : Scalar p)) <$>
      ProbComp.sampleIID p.n χ
    let e1 ← (fun xs : Fin p.n → ℤ => fun k => (xs k : Scalar p)) <$>
      ProbComp.sampleIID p.n χ
    let extra ← χm
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  have hHead {A B : Type} {mx my : ProbComp A}
      (h : evalDist mx = evalDist my) (k : A → ProbComp B) :
      evalDist (mx >>= k) = evalDist (my >>= k) := by
    simp only [evalDist_bind, h]
  have hMatrix : evalDist matrixProjectedExp = evalDist scalarExp := by
    simp only [matrixProjectedExp, scalarExp]
    refine (hHead (evalDist_sampleMatrix_col χm hχm p.n p.nbar c.2) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_col χm hχm p.n p.nbar c.2) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_row χm hχm p.nbar p.n c.1) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleMatrix_row χm hχm p.nbar p.n c.1) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    exact hHead (evalDist_sampleMatrix_entry χm hχm _ _ c.1 c.2) _
  have hProjected :
      evalDist ((fun t => entryNoiseScalar p c t) <$> noiseCoinsExp p χm) =
        evalDist matrixProjectedExp := by
    simp only [entryNoiseScalar, noiseCoinsExp, matrixProjectedExp,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  have hMapped : evalDist mappedIntExp = evalDist scalarExp := by
    simp only [mappedIntExp, scalarExp, χm]
    refine (hHead (evalDist_sampleIID_map p.n χ
      (fun z : ℤ => (z : Scalar p))) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleIID_map p.n χ
      (fun z : ℤ => (z : Scalar p))) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleIID_map p.n χ
      (fun z : ℤ => (z : Scalar p))) _).trans ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine (hHead (evalDist_sampleIID_map p.n χ
      (fun z : ℤ => (z : Scalar p))) _).trans ?_
    rfl
  have hCast :
      evalDist ((fun z : ℤ => (z : Scalar p)) <$> entryNoiseIntExp p.n χ) =
        evalDist mappedIntExp := by
    simp only [entryNoiseIntExp, mappedIntExp, χm, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_apply]
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    refine evalDist_bind_congr' _ fun _ => ?_
    simp only [Int.cast_add, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  exact hCast.trans (hMapped.trans (hMatrix.symm.trans hProjected.symm))

private theorem even_val_intCast_iff
    (p : Params) (hp : p.WellFormed) (z : ℤ) :
    Even ((z : Scalar p).val) ↔ Even z := by
  rw [← Int.even_coe_nat, Int.even_iff, ZMod.val_intCast, Int.even_iff]
  have hlt := hp.keyBits_lt
  have hlog : p.logQ ≠ 0 := by omega
  have hqnat : 2 ∣ p.q := by
    rw [Params.q]
    exact dvd_pow_self 2 hlog
  have hqint : (2 : ℤ) ∣ (p.q : ℤ) := by exact_mod_cast hqnat
  rw [((Int.mod_modEq z (p.q : ℤ)).of_dvd hqint).eq]

private theorem probEvent_even_cast
    (p : Params) (hp : p.WellFormed) (χ : ProbComp ℤ) :
    Pr[fun x : Scalar p => Even x.val |
      (fun z : ℤ => (z : Scalar p)) <$> χ] = Pr[fun z : ℤ => Even z | χ] := by
  rw [probEvent_map]
  apply probEvent_congr'
  · intro z _
    exact even_val_intCast_iff p hp z
  · rfl

private theorem probEvent_vector_all_even
    {p : Params} (χ : ProbComp (Scalar p)) (_hχ : Pr[⊥ | χ] = 0) (n : ℕ) :
    Pr[fun v : Fin n → Scalar p => ∀ k, Even (v k).val |
      ProbComp.sampleIID n χ] = Pr[fun x : Scalar p => Even x.val | χ] ^ n := by
  change Pr[fun v : Fin n → Scalar p => ∀ k, Even (v k).val |
      Fin.mOfFn n fun _ => χ] = _
  calc
    Pr[fun v : Fin n → Scalar p => ∀ k, Even (v k).val |
        Fin.mOfFn n fun _ => χ] =
        ∏ _ : Fin n, Pr[fun x : Scalar p => Even x.val | χ] :=
      probEvent_forall_coord_mOfFn n (fun _ => χ) (fun _ x => Even x.val)
    _ = Pr[fun x : Scalar p => Even x.val | χ] ^ n := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem probFailure_sampleMatrix
    {p : Params} (χ : ProbComp (Scalar p)) (hχ : Pr[⊥ | χ] = 0)
    (rows cols : ℕ) : Pr[⊥ | sampleMatrix χ rows cols] = 0 := by
  exact probFailure_mOfFn rows (fun _ => ProbComp.sampleIID cols χ)
    (fun _ => probFailure_mOfFn cols (fun _ => χ) fun _ => hχ)

private theorem evalDist_noiseCoins_initSecretCol
    (p : Params) (χ : ProbComp (Scalar p)) (hχ : Pr[⊥ | χ] = 0)
    (c : Fin p.nbar × Fin p.nbar) :
    evalDist ((fun t : InitKey p × SendACoins p => fun k => t.1.secret k c.2) <$>
      noiseCoinsExp p χ) = evalDist (ProbComp.sampleIID p.n χ) := by
  simp only [noiseCoinsExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    evalDist (do
          let s0 ← sampleMatrix χ p.n p.nbar
          let _ ← sampleMatrix χ p.n p.nbar
          let _ ← sampleMatrix χ p.nbar p.n
          let _ ← sampleMatrix χ p.nbar p.n
          let _ ← sampleMatrix χ p.nbar p.nbar
          pure fun k => s0 k c.2) =
        evalDist (do
          let s0 ← sampleMatrix χ p.n p.nbar
          pure fun k => s0 k c.2) := by
      refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun _ => ?_
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix χ p.n p.nbar) (probFailure_sampleMatrix χ hχ _ _)]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix χ p.nbar p.n) (probFailure_sampleMatrix χ hχ _ _)]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix χ p.nbar p.n) (probFailure_sampleMatrix χ hχ _ _)]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix χ p.nbar p.nbar) (probFailure_sampleMatrix χ hχ _ _)]
    _ = evalDist (ProbComp.sampleIID p.n χ) :=
      ChallengeExperimentLaw.evalDist_sampleMatrix_col_bind χ hχ p.n p.nbar c.2

private theorem evalDist_noiseCoins_sendSecretRow
    (p : Params) (χ : ProbComp (Scalar p)) (hχ : Pr[⊥ | χ] = 0)
    (c : Fin p.nbar × Fin p.nbar) :
    evalDist ((fun t : InitKey p × SendACoins p => t.2.secret c.1) <$>
      noiseCoinsExp p χ) = evalDist (ProbComp.sampleIID p.n χ) := by
  simp only [noiseCoinsExp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    (sampleMatrix χ p.n p.nbar) (probFailure_sampleMatrix χ hχ _ _)]
  rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    (sampleMatrix χ p.n p.nbar) (probFailure_sampleMatrix χ hχ _ _)]
  calc
    evalDist (do
          let s1 ← sampleMatrix χ p.nbar p.n
          let _ ← sampleMatrix χ p.nbar p.n
          let _ ← sampleMatrix χ p.nbar p.nbar
          pure (s1 c.1)) =
        evalDist (do
          let s1 ← sampleMatrix χ p.nbar p.n
          pure (s1 c.1)) := by
      refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix χ p.nbar p.n) (probFailure_sampleMatrix χ hχ _ _)]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (sampleMatrix χ p.nbar p.nbar) (probFailure_sampleMatrix χ hχ _ _)]
    _ = evalDist (ProbComp.sampleIID p.n χ) :=
      ChallengeExperimentLaw.evalDist_sampleMatrix_row_bind χ hχ p.nbar p.n c.1

private theorem probEvent_entryBad_le
    (p : Params) (χ : ProbComp (Scalar p)) (hχ : Pr[⊥ | χ] = 0)
    (c : Fin p.nbar × Fin p.nbar) :
    Pr[entryBad p c | noiseCoinsExp p χ] ≤
      2 * Pr[fun x : Scalar p => Even x.val | χ] ^ p.n := by
  let q := fun t : InitKey p × SendACoins p =>
    ∀ k : Fin p.n, Even (t.2.secret c.1 k).val
  let r := fun t : InitKey p × SendACoins p =>
    ∀ k : Fin p.n, Even (t.1.secret k c.2).val
  have hq : Pr[q | noiseCoinsExp p χ] =
      Pr[fun x : Scalar p => Even x.val | χ] ^ p.n := by
    calc
      Pr[q | noiseCoinsExp p χ] =
          Pr[fun v : Fin p.n → Scalar p => ∀ k, Even (v k).val |
            (fun t : InitKey p × SendACoins p => t.2.secret c.1) <$>
              noiseCoinsExp p χ] := by
        rw [probEvent_map]
        apply probEvent_congr'
        · intro t _
          rfl
        · rfl
      _ = Pr[fun v : Fin p.n → Scalar p => ∀ k, Even (v k).val |
            ProbComp.sampleIID p.n χ] := by
        simp only [probEvent_def, evalDist_noiseCoins_sendSecretRow p χ hχ c]
      _ = _ := probEvent_vector_all_even χ hχ p.n
  have hr : Pr[r | noiseCoinsExp p χ] =
      Pr[fun x : Scalar p => Even x.val | χ] ^ p.n := by
    calc
      Pr[r | noiseCoinsExp p χ] =
          Pr[fun v : Fin p.n → Scalar p => ∀ k, Even (v k).val |
            (fun t : InitKey p × SendACoins p => fun k => t.1.secret k c.2) <$>
              noiseCoinsExp p χ] := by
        rw [probEvent_map]
        apply probEvent_congr'
        · intro t _
          rfl
        · rfl
      _ = Pr[fun v : Fin p.n → Scalar p => ∀ k, Even (v k).val |
            ProbComp.sampleIID p.n χ] := by
        simp only [probEvent_def, evalDist_noiseCoins_initSecretCol p χ hχ c]
      _ = _ := probEvent_vector_all_even χ hχ p.n
  change Pr[fun t => q t ∨ r t | noiseCoinsExp p χ] ≤ _
  calc
    Pr[fun t => q t ∨ r t | noiseCoinsExp p χ] ≤
        Pr[q | noiseCoinsExp p χ] + Pr[r | noiseCoinsExp p χ] :=
      probEvent_or_le (noiseCoinsExp p χ) q r
    _ = 2 * Pr[fun x : Scalar p => Even x.val | χ] ^ p.n := by
      rw [hq, hr, two_mul]

private theorem q_eq_halfBlocks_mul_halfWidth (p : Params) (hp : p.WellFormed) :
    p.q = 2 ^ (p.keyBits + 1) * p.halfWidth := by
  have hlt := hp.keyBits_lt
  have hd : 2 ≤ p.discardBits := by
    simp only [Params.discardBits]
    omega
  rw [Params.q, Params.halfWidth, Params.discardBits, ← pow_add]
  congr 1
  omega

private instance halfWidth_neZero (p : Params) : NeZero p.halfWidth :=
  ⟨by simp [Params.halfWidth]⟩

private instance phaseBlocks_neZero (p : Params) : NeZero (2 ^ (p.keyBits + 1)) :=
  ⟨by positivity⟩

private def scalarPhaseEquiv (p : Params) (hp : p.WellFormed) :
    Scalar p ≃ Fin p.halfWidth × Fin (2 ^ (p.keyBits + 1)) :=
  (ZMod.finEquiv p.q).toEquiv.symm |>.trans
    ((finCongr (q_eq_halfBlocks_mul_halfWidth p hp)).trans
      ((finProdFinEquiv :
        Fin (2 ^ (p.keyBits + 1)) × Fin p.halfWidth ≃
          Fin (2 ^ (p.keyBits + 1) * p.halfWidth)).symm |>.trans
        (Equiv.prodComm _ _)))

private theorem finEquiv_symm_val :
    ∀ (n : ℕ) [NeZero n] (v : ZMod n),
      ((ZMod.finEquiv n).symm v).val = v.val
  | 0, h, _ => (h.ne _ rfl).elim
  | _ + 1, _, _ => rfl

private theorem scalarPhaseEquiv_fst
    (p : Params) (hp : p.WellFormed) (v : Scalar p) :
    (scalarPhaseEquiv p hp v).1.val = v.val % p.halfWidth := by
  have hv : ((ZMod.finEquiv p.q).symm v).val = v.val :=
    finEquiv_symm_val p.q v
  simp [scalarPhaseEquiv, finProdFinEquiv, hv]

private theorem evalDist_uniform_phase (p : Params) (hp : p.WellFormed) :
    evalDist ((fun v : Scalar p => (scalarPhaseEquiv p hp v).1) <$>
      ($ᵗ (Scalar p) : ProbComp (Scalar p))) =
      evalDist ($ᵗ (Fin p.halfWidth) : ProbComp (Fin p.halfWidth)) := by
  calc
    evalDist ((fun v : Scalar p => (scalarPhaseEquiv p hp v).1) <$>
        ($ᵗ (Scalar p) : ProbComp (Scalar p))) =
        evalDist (Prod.fst <$> (scalarPhaseEquiv p hp <$>
          ($ᵗ (Scalar p) : ProbComp (Scalar p)))) := by rw [Functor.map_map]
    _ = evalDist (Prod.fst <$>
          ($ᵗ (Fin p.halfWidth × Fin (2 ^ (p.keyBits + 1))) :
            ProbComp (Fin p.halfWidth × Fin (2 ^ (p.keyBits + 1))))) := by
      exact evalDist_map_eq_of_evalDist_eq
        (evalDist_map_bijective_uniform_cross (α := Scalar p) (scalarPhaseEquiv p hp)
          (scalarPhaseEquiv p hp).bijective) Prod.fst
    _ = evalDist ($ᵗ (Fin p.halfWidth) : ProbComp (Fin p.halfWidth)) :=
      evalDist_map_fst_uniformSample_prod

private theorem probEvent_uniform_phase_eq_ramp
    (p : Params) (hp : p.WellFormed) (z : Scalar p) :
    Pr[fun v : Scalar p => p.blockWidth ≤
        (((((v.val % p.halfWidth + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) -
          z).val)) |
      ($ᵗ (Scalar p) : ProbComp (Scalar p))] = scalarFailureRamp p z := by
  let phaseBad := fun u : ℕ => p.blockWidth ≤
    ((((u + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) - z).val)
  have hcard :
      ((Finset.univ : Finset (Fin p.halfWidth)).filter
        fun u => phaseBad u.val).card =
      ((Finset.range p.halfWidth).filter phaseBad).card := by
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
      ((Finset.range p.halfWidth).filter phaseBad).card =
        min p.halfWidth
          (modularDistance p z 0 - 2 ^ (p.discardBits - 2)) := by
    dsimp only [phaseBad]
    exact card_reconciliationFailurePhases p hp z
  calc
    Pr[fun v : Scalar p => phaseBad (v.val % p.halfWidth) |
        ($ᵗ (Scalar p) : ProbComp (Scalar p))] =
        Pr[fun u : Fin p.halfWidth => phaseBad u.val |
          (fun v : Scalar p => (scalarPhaseEquiv p hp v).1) <$>
            ($ᵗ (Scalar p) : ProbComp (Scalar p))] := by
      rw [probEvent_map]
      apply probEvent_congr'
      · intro v _
        simp only [Function.comp_apply]
        rw [scalarPhaseEquiv_fst]
      · rfl
    _ = Pr[fun u : Fin p.halfWidth => phaseBad u.val |
          ($ᵗ (Fin p.halfWidth) : ProbComp (Fin p.halfWidth))] := by
      simp only [probEvent_def, evalDist_uniform_phase p hp]
    _ = (((Finset.univ : Finset (Fin p.halfWidth)).filter
          fun u => phaseBad u.val).card : ℝ≥0∞) / p.halfWidth := by
      rw [probEvent_uniformSample]
      simp only [Fintype.card_fin]
    _ = scalarFailureRamp p z := by
      rw [hcard, hphaseCount]
      unfold scalarFailureRamp
      let d := modularDistance p z 0
      change ((min p.halfWidth (d - 2 ^ (p.discardBits - 2)) : ℕ) : ℝ≥0∞) /
          p.halfWidth =
        min (p.halfWidth : ℝ≥0∞)
          ((d : ℝ≥0∞) - 2 ^ (p.discardBits - 2)) / p.halfWidth
      apply congrArg (fun x : ℝ≥0∞ => x / p.halfWidth)
      calc
        ((min p.halfWidth (d - 2 ^ (p.discardBits - 2)) : ℕ) : ℝ≥0∞) =
            min (p.halfWidth : ℝ≥0∞)
              ((d - 2 ^ (p.discardBits - 2) : ℕ) : ℝ≥0∞) :=
          Monotone.map_min Nat.mono_cast
        _ = min (p.halfWidth : ℝ≥0∞)
              ((d : ℝ≥0∞) - 2 ^ (p.discardBits - 2)) := by
          rw [ENNReal.natCast_sub]
          norm_num

private def senderScalar
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) (a : BaseMatrix p) : Scalar p :=
  (t.2.secret * (a * t.1.secret + t.1.error) + t.2.extra) c.1 c.2

private def baseReplace
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
          ((∑ j : ι, Function.update a k (Function.update r l 0) i j * right j) +
            err i) := by
  let rest := ∑ i ∈ (Finset.univ : Finset ι).erase k,
    left i * ((∑ j : ι, a i j * right j) + err i)
  have houter (y : R) :
      (∑ i : ι, left i *
        ((∑ j : ι, Function.update a k (Function.update r l y) i j * right j) +
          err i)) =
        rest + left k * ((∑ j : ι, Function.update r l y j * right j) + err k) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Function.update_apply, if_neg (Finset.ne_of_mem_erase hi)]
    · simp only [Function.update_self]
  rw [houter x, houter 0, sum_update_mul r right l x,
    sum_update_mul r right l 0]
  ring

private theorem senderScalar_replace_affine
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) (a : BaseMatrix p) (k l : Fin p.n)
    (r : Fin p.n → Scalar p) (x : Scalar p) :
    senderScalar p c t (baseReplace p a k l r x) =
      (t.2.secret c.1 k * t.1.secret l c.2) * x +
        senderScalar p c t (baseReplace p a k l r 0) := by
  classical
  unfold senderScalar baseReplace
  change
    (∑ i : Fin p.n, t.2.secret c.1 i *
      ((∑ j : Fin p.n,
        Function.update a k (Function.update r l x) i j * t.1.secret j c.2) +
          t.1.error i c.2)) + t.2.extra c.1 c.2 =
      (t.2.secret c.1 k * t.1.secret l c.2) * x +
        ((∑ i : Fin p.n, t.2.secret c.1 i *
          ((∑ j : Fin p.n,
            Function.update a k (Function.update r l 0) i j *
              t.1.secret j c.2) + t.1.error i c.2)) + t.2.extra c.1 c.2)
  rw [double_sum_update_affine
    (fun i => t.2.secret c.1 i) (fun j => t.1.secret j c.2)
    (fun i => t.1.error i c.2) a k l r x]
  rw [add_assoc]

private theorem isUnit_of_not_even_val
    (p : Params) (hp : p.WellFormed) (x : Scalar p)
    (hx : ¬Even x.val) : IsUnit x := by
  rw [← ZMod.natCast_zmod_val x]
  change IsUnit ((x.val : ℕ) : ZMod (2 ^ p.logQ))
  have hlt := hp.keyBits_lt
  have hlog : 0 < p.logQ := by omega
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two hlog).2
  simpa only [even_iff_two_dvd] using hx

private theorem evalDist_uniform_update_map
    {D R α : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) (ψ : (D → R) → α) :
    evalDist (do
      let u ← ($ᵗ R : ProbComp R)
      let g ← ($ᵗ (D → R) : ProbComp (D → R))
      pure (ψ (Function.update g t u))) =
      evalDist (ψ <$> ($ᵗ (D → R) : ProbComp (D → R))) := by
  rw [map_eq_bind_pure_comp]
  exact OracleComp.evalDist_uniformSample_bind_update_map t ψ

private theorem evalDist_base_update_row
    (p : Params) {α : Type} (k : Fin p.n) (ψ : BaseMatrix p → α) :
    evalDist (do
      let r ← ($ᵗ (Fin p.n → Scalar p) : ProbComp (Fin p.n → Scalar p))
      let a ← ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
      pure (ψ (Function.update a k r))) =
      evalDist (ψ <$> ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))) := by
  exact @evalDist_uniform_update_map (Fin p.n) (Fin p.n → Scalar p) α
    inferInstance inferInstance inferInstance inferInstance
    (inferInstanceAs (SampleableType (Fin p.n → Scalar p)))
    (inferInstanceAs (SampleableType (BaseMatrix p))) k ψ

private theorem evalDist_row_update_cell
    (p : Params) {α : Type} (l : Fin p.n)
    (ψ : (Fin p.n → Scalar p) → α) :
    evalDist (do
      let x ← ($ᵗ (Scalar p) : ProbComp (Scalar p))
      let r ← ($ᵗ (Fin p.n → Scalar p) : ProbComp (Fin p.n → Scalar p))
      pure (ψ (Function.update r l x))) =
      evalDist (do
        let r ← ($ᵗ (Fin p.n → Scalar p) : ProbComp (Fin p.n → Scalar p))
        pure (ψ r)) := by
  exact OracleComp.evalDist_uniformSample_bind_update_map l ψ

private theorem evalDist_bind_pure_of_map
    {α β : Type} (oa : ProbComp α) (f : α → β) (ob : ProbComp β)
    (h : evalDist (f <$> oa) = evalDist ob) :
    evalDist (oa >>= fun x => pure (f x)) = evalDist ob := by
  rw [show (oa >>= fun x => pure (f x)) = f <$> oa from
    (map_eq_bind_pure_comp ProbComp f oa).symm]
  exact h

private theorem evalDist_sender_cell_uniform
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) (k l : Fin p.n)
    (hcoeff : IsUnit (t.2.secret c.1 k * t.1.secret l c.2))
    (a : BaseMatrix p) (r : Fin p.n → Scalar p) :
    evalDist ((fun x : Scalar p => senderScalar p c t
      (baseReplace p a k l r x)) <$>
        ($ᵗ (Scalar p) : ProbComp (Scalar p))) =
      evalDist ($ᵗ (Scalar p) : ProbComp (Scalar p)) := by
  classical
  let coeff := t.2.secret c.1 k * t.1.secret l c.2
  have hmul : Function.Bijective (coeff * ·) :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp hcoeff
  let b := senderScalar p c t (baseReplace p a k l r 0)
  have haffine : Function.Bijective (fun x : Scalar p => coeff * x + b) := by
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
      (fun x : Scalar p => senderScalar p c t (baseReplace p a k l r x)) =
        fun x => coeff * x + b := by
    funext x
    exact senderScalar_replace_affine p c t a k l r x
  rw [hfun]
  exact evalDist_map_bijective_uniform_cross
    (α := Scalar p) (fun x : Scalar p => coeff * x + b) haffine

private theorem evalDist_sender_uniform_of_not_bad
    (p : Params) (hp : p.WellFormed)
    (c : Fin p.nbar × Fin p.nbar) (t : InitKey p × SendACoins p)
    (hgood : ¬entryBad p c t) :
    evalDist ((fun a : BaseMatrix p => senderScalar p c t a) <$>
      ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))) =
      evalDist ($ᵗ (Scalar p) : ProbComp (Scalar p)) := by
  classical
  simp only [entryBad, not_or, not_forall] at hgood
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hgood
  have hcoeff : IsUnit (t.2.secret c.1 k * t.1.secret l c.2) :=
    (isUnit_of_not_even_val p hp _ hk).mul (isUnit_of_not_even_val p hp _ hl)
  let rowType := Fin p.n → Scalar p
  let rowSample : ProbComp rowType := $ᵗ rowType
  let baseSample : ProbComp (BaseMatrix p) := $ᵗ (BaseMatrix p)
  calc
    evalDist ((fun a : BaseMatrix p => senderScalar p c t a) <$> baseSample) =
        evalDist (do
          let r ← rowSample
          let a ← baseSample
          return senderScalar p c t (Function.update a k r)) := by
      exact (evalDist_base_update_row p k
        (fun a : BaseMatrix p => senderScalar p c t a)).symm
    _ = evalDist (do
          let a ← baseSample
          let r ← rowSample
          return senderScalar p c t (Function.update a k r)) :=
      evalDist_bind_bind_swap rowSample baseSample _
    _ = evalDist (do
          let a ← baseSample
          let x ← ($ᵗ (Scalar p) : ProbComp (Scalar p))
          let r ← rowSample
          return senderScalar p c t (baseReplace p a k l r x)) := by
      refine evalDist_bind_congr' baseSample fun a => ?_
      exact (evalDist_row_update_cell p l
        (fun r : rowType => senderScalar p c t (Function.update a k r))).symm
    _ = evalDist (do
          let a ← baseSample
          let r ← rowSample
          let x ← ($ᵗ (Scalar p) : ProbComp (Scalar p))
          return senderScalar p c t (baseReplace p a k l r x)) := by
      refine evalDist_bind_congr' baseSample fun _ => ?_
      exact evalDist_bind_bind_swap
        ($ᵗ (Scalar p) : ProbComp (Scalar p)) rowSample _
    _ = evalDist (do
          let a ← baseSample
          let r ← rowSample
          ($ᵗ (Scalar p) : ProbComp (Scalar p))) := by
      refine evalDist_bind_congr' baseSample fun a => ?_
      refine evalDist_bind_congr' rowSample fun r => ?_
      exact evalDist_bind_pure_of_map
        ($ᵗ (Scalar p) : ProbComp (Scalar p))
        (fun x : Scalar p => senderScalar p c t (baseReplace p a k l r x))
        ($ᵗ (Scalar p) : ProbComp (Scalar p))
        (evalDist_sender_cell_uniform p c t k l hcoeff a r)
    _ = evalDist ($ᵗ (Scalar p) : ProbComp (Scalar p)) := by
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        baseSample probFailure_eq_zero]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        rowSample probFailure_eq_zero]

private theorem entryMismatch_iff_phase
    (p : Params) (hp : p.WellFormed)
    (c : Fin p.nbar × Fin p.nbar) (t : InitKey p × SendACoins p)
    (a : BaseMatrix p) :
    entryMismatch p c (withBase p a t) ↔
      p.blockWidth ≤
        (((((senderScalar p c t a).val % p.halfWidth +
          2 ^ (p.discardBits - 2) : ℕ) : Scalar p) -
            entryNoiseScalar p c t).val) := by
  let tb := withBase p a t
  have hvalue := congrArg (fun m => m c.1 c.2)
    (firstExchangeValue_sub_eq_noise p tb.1 tb.2)
  simp only [Matrix.sub_apply] at hvalue
  have hphase := reconcileScalar_eq_extractScalar_iff_phase p hp
    (((tb.2.secret * tb.1.baseMatrix + tb.2.error) * tb.1.secret) c.1 c.2)
    ((tb.2.secret * (tb.1.baseMatrix * tb.1.secret + tb.1.error) + tb.2.extra)
      c.1 c.2)
  have hdiff :
      (tb.2.secret * (tb.1.baseMatrix * tb.1.secret + tb.1.error) + tb.2.extra)
          c.1 c.2 -
        ((tb.2.secret * tb.1.baseMatrix + tb.2.error) * tb.1.secret) c.1 c.2 =
          entryNoiseScalar p c t := by
    exact hvalue.trans rfl
  rw [hdiff] at hphase
  dsimp only [tb, withBase] at hphase
  simpa only [entryMismatch, withBase, senderScalar, entryNoiseScalar] using
    (not_congr hphase).trans not_lt

private theorem probEvent_entryMismatch_withBase
    (p : Params) (hp : p.WellFormed)
    (c : Fin p.nbar × Fin p.nbar) (t : InitKey p × SendACoins p)
    (hgood : ¬entryBad p c t) :
    Pr[fun a : BaseMatrix p => entryMismatch p c (withBase p a t) |
      ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))] =
      scalarFailureRamp p (entryNoiseScalar p c t) := by
  let phaseBad := fun v : Scalar p =>
    p.blockWidth ≤
      (((v.val % p.halfWidth + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) -
        entryNoiseScalar p c t).val
  calc
    Pr[fun a : BaseMatrix p => entryMismatch p c (withBase p a t) |
        ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))] =
        Pr[phaseBad | (fun a : BaseMatrix p => senderScalar p c t a) <$>
          ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))] := by
      rw [probEvent_map]
      apply probEvent_congr'
      · intro a _
        exact entryMismatch_iff_phase p hp c t a
      · rfl
    _ = Pr[phaseBad | ($ᵗ (Scalar p) : ProbComp (Scalar p))] := by
      simp only [probEvent_def, evalDist_sender_uniform_of_not_bad p hp c t hgood]
    _ = scalarFailureRamp p (entryNoiseScalar p c t) :=
      probEvent_uniform_phase_eq_ramp p hp (entryNoiseScalar p c t)

private noncomputable def fixedFailure
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) : ℝ≥0∞ :=
  Pr[fun a : BaseMatrix p => entryMismatch p c (withBase p a t) |
    ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))]

private noncomputable local instance entryBadDecidable
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) : Decidable (entryBad p c t) :=
  Classical.propDecidable _

private theorem probEvent_bind_pure_map
    {α β : Type} (mx : ProbComp α) (f : α → β) (q : β → Prop) :
    Pr[q | mx >>= fun x => pure (f x)] = Pr[fun x => q (f x) | mx] := by
  rw [show (fun x => pure (f x)) = pure ∘ f from rfl,
    probEvent_bind_pure_comp]
  rfl

private theorem probEvent_entryMismatch_eq_expectedFixed
    (p : Params) (χ : ProbComp (Scalar p))
    (c : Fin p.nbar × Fin p.nbar) :
    Pr[entryMismatch p c | coinsExp p χ] =
      expectedValue (noiseCoinsExp p χ) (fixedFailure p c) := by
  have hprob := probEvent_congr'
    (p := entryMismatch p c) (q := entryMismatch p c)
    (oa := coinsExp p χ)
    (oa' := do
      let t ← noiseCoinsExp p χ
      let a ← ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
      return withBase p a t)
    (fun _ _ => Iff.rfl) (evalDist_coinsExp_noiseFirst p χ)
  rw [hprob, probEvent_bind_eq_tsum]
  unfold expectedValue fixedFailure
  apply tsum_congr
  intro t
  apply congrArg (fun q : ℝ≥0∞ => Pr[= t | noiseCoinsExp p χ] * q)
  exact probEvent_bind_pure_map
    (($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p)))
    (fun a => withBase p a t) (entryMismatch p c)

private theorem expectedValue_noiseCoins_ramp
    (p : Params) (χ : ProbComp ℤ) (hχ : Pr[⊥ | χ] = 0)
    (c : Fin p.nbar × Fin p.nbar) :
    expectedValue (noiseCoinsExp p ((fun z : ℤ => (z : Scalar p)) <$> χ))
        (fun t => scalarFailureRamp p (entryNoiseScalar p c t)) =
      expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) := by
  calc
    expectedValue (noiseCoinsExp p ((fun z : ℤ => (z : Scalar p)) <$> χ))
        (fun t => scalarFailureRamp p (entryNoiseScalar p c t)) =
        expectedValue ((fun t => entryNoiseScalar p c t) <$>
          noiseCoinsExp p ((fun z : ℤ => (z : Scalar p)) <$> χ))
          (scalarFailureRamp p) :=
      (expectedValue_map _ (fun t => entryNoiseScalar p c t)
        (scalarFailureRamp p)).symm
    _ = expectedValue ((fun z : ℤ => (z : Scalar p)) <$> entryNoiseIntExp p.n χ)
          (scalarFailureRamp p) := by
      apply expectedValue_congr
      exact evalDist_ext_iff.mp (evalDist_entryNoiseScalar_eq_cast p χ hχ c).symm
    _ = expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) := by
      rw [expectedValue_map]
      rfl

private theorem expectedValue_badIndicator
    (p : Params) (χ : ProbComp (Scalar p))
    (c : Fin p.nbar × Fin p.nbar) :
    expectedValue (noiseCoinsExp p χ)
        (fun t => if entryBad p c t then 1 else 0) =
      Pr[entryBad p c | noiseCoinsExp p χ] := by
  classical
  rw [expectedValue, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro t
  by_cases hbad : entryBad p c t <;> simp [hbad]

private theorem fixedFailure_le_ramp_add_bad
    (p : Params) (hp : p.WellFormed)
    (c : Fin p.nbar × Fin p.nbar) (t : InitKey p × SendACoins p) :
    fixedFailure p c t ≤ scalarFailureRamp p (entryNoiseScalar p c t) +
      if entryBad p c t then 1 else 0 := by
  classical
  by_cases hbad : entryBad p c t
  · simp only [hbad, if_true]
    exact probEvent_le_one.trans (le_add_left le_rfl)
  · unfold fixedFailure
    rw [probEvent_entryMismatch_withBase p hp c t hbad]
    simp only [hbad, if_false, add_zero]
    exact le_rfl

private theorem probEvent_entryMismatch_le_ramp
    (p : Params) (hp : p.WellFormed)
    (χ : ProbComp ℤ) (hχ : Pr[⊥ | χ] = 0)
    (c : Fin p.nbar × Fin p.nbar) :
    Pr[entryMismatch p c | coinsExp p ((fun z : ℤ => (z : Scalar p)) <$> χ)] ≤
      expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) +
        2 * Pr[fun z : ℤ => Even z | χ] ^ p.n := by
  let χm : ProbComp (Scalar p) := (fun z : ℤ => (z : Scalar p)) <$> χ
  have hχm : Pr[⊥ | χm] = 0 := by
    simpa only [χm, probFailure_map] using hχ
  rw [probEvent_entryMismatch_eq_expectedFixed p χm c]
  calc
    expectedValue (noiseCoinsExp p χm) (fixedFailure p c) ≤
        expectedValue (noiseCoinsExp p χm)
          (fun t => scalarFailureRamp p (entryNoiseScalar p c t) +
            if entryBad p c t then 1 else 0) :=
      expectedValue_mono _ (fixedFailure_le_ramp_add_bad p hp c)
    _ = expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) +
        Pr[entryBad p c | noiseCoinsExp p χm] := by
      rw [expectedValue_add, expectedValue_noiseCoins_ramp p χ hχ c,
        expectedValue_badIndicator]
    _ ≤ expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) +
        2 * Pr[fun x : Scalar p => Even x.val | χm] ^ p.n :=
      add_le_add_right (probEvent_entryBad_le p χm hχm c) _
    _ = expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) +
        2 * Pr[fun z : ℤ => Even z | χ] ^ p.n := by
      rw [probEvent_even_cast p hp χ]

/-- A first-exchange failure is bounded by the union of the generic phase ramps, retaining the
two all-even secret-vector exceptions for every entry. -/
theorem firstExchangeFailureProb_le_ramp
    (p : Params) (hp : p.WellFormed)
    (χ : ProbComp ℤ) (hχ : Pr[⊥ | χ] = 0) :
    firstExchangeFailureProb p ((fun z : ℤ => (z : Scalar p)) <$> χ) ≤
      (p.nbar ^ 2 : ℕ) *
        (expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) +
          2 * Pr[fun z : ℤ => Even z | χ] ^ p.n) := by
  let χm : ProbComp (Scalar p) := (fun z : ℤ => (z : Scalar p)) <$> χ
  let B := expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) +
    2 * Pr[fun z : ℤ => Even z | χ] ^ p.n
  rw [firstExchangeFailureProb_eq_entry_union p χm]
  have hunion := probEvent_exists_finset_le_sum
    (Finset.univ : Finset (Fin p.nbar × Fin p.nbar)) (coinsExp p χm)
    (fun c t => entryMismatch p c t)
  calc
    Pr[fun t => ∃ c : Fin p.nbar × Fin p.nbar, entryMismatch p c t |
        coinsExp p χm] ≤
        ∑ c : Fin p.nbar × Fin p.nbar,
          Pr[entryMismatch p c | coinsExp p χm] := by simpa using hunion
    _ ≤ ∑ _c : Fin p.nbar × Fin p.nbar, B := by
      apply Finset.sum_le_sum
      intro c _
      exact probEvent_entryMismatch_le_ramp p hp χ hχ c
    _ = (p.nbar ^ 2 : ℕ) * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul]
      congr 1
      norm_num [pow_two]

end lweCKA
