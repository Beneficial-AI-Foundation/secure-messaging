/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.ExperimentLaw
import SecureMessaging.CKA.FromLWE.NoiseCorrectness

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

/-- The fraction of sender phases that fail for a fixed scalar noise value. -/
noncomputable def PhaseCorrectness.Internal.scalarFailureRamp (p : Params) (z : Scalar p) : ℝ≥0∞ :=
  (min p.halfWidth
    (modularDistance p z 0 - 2 ^ (p.discardBits - 2)) : ℝ≥0∞) / p.halfWidth

open PhaseCorrectness.Internal

/-- The joint experiment that samples an initialization key and first-message coins. -/
def PhaseCorrectness.Internal.coinsExp (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (InitKey p × SendACoins p) := do
  let ik ← initKeyGen p χ
  let r ← sampleSendACoins p χ
  return (ik, r)

/-- The event that reconciliation fails at one matrix coordinate. -/
def PhaseCorrectness.Internal.entryMismatch
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) : Prop :=
  let v := t.2.secret * (t.1.baseMatrix * t.1.secret + t.1.error) + t.2.extra
  let w := (t.2.secret * t.1.baseMatrix + t.2.error) * t.1.secret
  reconcileScalar p (w c.1 c.2) (hintScalar p (v c.1 c.2)) ≠
    extractScalar p (v c.1 c.2)

/-- Samples all secret and error coins while fixing the public base matrix to zero. -/
def PhaseCorrectness.Internal.noiseCoinsExp (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (InitKey p × SendACoins p) := do
  let s0 ← sampleMatrix χ p.n p.nbar
  let e0 ← sampleMatrix χ p.n p.nbar
  let s1 ← sampleMatrix χ p.nbar p.n
  let e1 ← sampleMatrix χ p.nbar p.n
  let extra ← sampleMatrix χ p.nbar p.nbar
  pure (({ baseMatrix := 0, secret := s0, error := e0 } : InitKey p),
    ({ secret := s1, error := e1, extra := extra } : SendACoins p))

/-- Installs a public base matrix into a tuple of sampled noise coins. -/
def PhaseCorrectness.Internal.withBase
    (p : Params) (a : BaseMatrix p) (t : InitKey p × SendACoins p) :
    InitKey p × SendACoins p :=
  ({ t.1 with baseMatrix := a }, t.2)

/-- The exceptional event that a relevant secret row or column is entirely even. -/
def PhaseCorrectness.Internal.entryBad
    (p : Params) (c : Fin p.nbar × Fin p.nbar)
    (t : InitKey p × SendACoins p) : Prop :=
  (∀ k : Fin p.n, Even (t.2.secret c.1 k).val) ∨
  (∀ k : Fin p.n, Even (t.1.secret k c.2).val)

/-- The scalar error term governing reconciliation at one matrix coordinate. -/
def PhaseCorrectness.Internal.entryNoiseScalar
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

theorem PhaseCorrectness.Internal.firstExchangeFailureProb_eq_entry_union
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

theorem PhaseCorrectness.Internal.evalDist_coinsExp_noiseFirst
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

theorem PhaseCorrectness.Internal.evalDist_entryNoiseScalar_eq_cast
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

theorem PhaseCorrectness.Internal.probEvent_even_cast
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

theorem PhaseCorrectness.Internal.probEvent_entryBad_le
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

end lweCKA
