/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.PhaseCorrectness.EntryNoise
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

open PhaseCorrectness.Internal

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
