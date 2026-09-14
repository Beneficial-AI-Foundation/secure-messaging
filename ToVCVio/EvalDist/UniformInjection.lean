/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.EvalDist.TVDist
import VCVio.OracleComp.Constructions.SampleableType
import ToVCVio.OracleComp.Constructions.BitVec

/-!
# Uniform samples through an injection

The distributional ingredients of the fixed-list PRP/PRF switching bound, which
`CryptoFoundations/PRPSwitching.lean` assembles:

* `tvDist_map_injective_uniformSample`: a uniform sample pushed through an injection
  `A → B` is at total-variation distance exactly `1 - card A / card B` from uniform on `B`;
* `two_mul_sub_descFactorial_le`: the birthday inequality
  `1 - N.descFactorial q / N ^ q ≤ q (q - 1) / (2 N)`, in `ℕ` with denominators cleared;
* `evalDist_listMapM_uniform_eq_map_ofFn`: `q` independent uniform draws are one uniform
  draw from `Fin q → X`.

Candidate for upstream VCVio.
-/

open ENNReal

namespace OracleComp

/-! ## A uniform sample pushed through an injection -/

/-- A uniform sample pushed through an injection `ι : A → B` is at total-variation distance
exactly `1 - card A / card B` from the uniform sample on `B`: on the image of `ι` the two
masses are `(card A)⁻¹` and `(card B)⁻¹`, off it they are `0` and `(card B)⁻¹`. -/
theorem tvDist_map_injective_uniformSample {A B : Type} [Fintype A] [Fintype B]
    [SampleableType A] [SampleableType B] (ι : A → B) (hι : Function.Injective ι) :
    tvDist (ι <$> ($ᵗ A : ProbComp A)) ($ᵗ B : ProbComp B)
      = 1 - (Fintype.card A : ℝ) / (Fintype.card B : ℝ) := by
  -- `DecidableEq` is supplied explicitly rather than by `classical`: instance search from a
  -- bare `SampleableType` context times out at 20000 synthesis heartbeats in this build.
  letI : DecidableEq A := Classical.decEq A
  letI : DecidableEq B := Classical.decEq B
  set S : Finset B := Finset.univ.image ι with hS
  have hcard : Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective ι hι
  have hApos : 0 < Fintype.card A := Fintype.card_pos
  have hBpos : 0 < Fintype.card B := Fintype.card_pos
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hApos.ne'
  have hB0 : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hBpos.ne'
  have hcardS : S.card = Fintype.card A := by
    rw [hS, Finset.card_image_of_injective _ hι, Finset.card_univ]
  -- The mass of the pushed-forward sample: `(card A)⁻¹` on the image, `0` off it.
  have hp : ∀ b : B, Pr[= b | ι <$> ($ᵗ A : ProbComp A)]
      = if b ∈ S then (Fintype.card A : ℝ≥0∞)⁻¹ else 0 := by
    intro b
    by_cases hb : b ∈ S
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
      rw [if_pos hb, probOutput_map_injective _ hι a, probOutput_uniformSample]
    · rw [if_neg hb]
      refine probOutput_eq_zero_of_not_mem_support ?_
      rw [support_map]
      rintro ⟨a, -, rfl⟩
      exact hb (by rw [hS]; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  have hinvle : (Fintype.card B : ℝ)⁻¹ ≤ (Fintype.card A : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) (Nat.cast_le.mpr hcard)
  -- Each summand, measured in `ℝ` rather than in `ℝ≥0∞`.
  have key : ∀ b : B,
      (ENNReal.absDiff (Pr[= b | ι <$> ($ᵗ A : ProbComp A)])
        (Pr[= b | ($ᵗ B : ProbComp B)])).toReal
        = if b ∈ S then (Fintype.card A : ℝ)⁻¹ - (Fintype.card B : ℝ)⁻¹
          else (Fintype.card B : ℝ)⁻¹ := by
    intro b
    rw [ENNReal.absDiff_toReal probOutput_ne_top probOutput_ne_top, hp b,
      probOutput_uniformSample]
    by_cases hb : b ∈ S
    · rw [if_pos hb, if_pos hb, ENNReal.toReal_inv, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast, abs_of_nonneg (by linarith)]
    · rw [if_neg hb, if_neg hb, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
  have habs : ∀ b : B, ENNReal.absDiff (Pr[= b | ι <$> ($ᵗ A : ProbComp A)])
      (Pr[= b | ($ᵗ B : ProbComp B)]) ≠ ⊤ := by
    intro b
    simp only [ENNReal.absDiff, ne_eq, ENNReal.add_eq_top, not_or]
    exact ⟨ENNReal.sub_ne_top probOutput_ne_top, ENNReal.sub_ne_top probOutput_ne_top⟩
  -- Re-shaped so the sum splits as a constant plus a sum over the image alone; this is what
  -- keeps `Fintype.card B - Fintype.card A` out of the statement as a `ℕ` subtraction.
  have hsplit : ∀ b : B,
      (if b ∈ S then (Fintype.card A : ℝ)⁻¹ - (Fintype.card B : ℝ)⁻¹
        else (Fintype.card B : ℝ)⁻¹)
        = (Fintype.card B : ℝ)⁻¹
          + (if b ∈ S then (Fintype.card A : ℝ)⁻¹ - 2 * (Fintype.card B : ℝ)⁻¹ else 0) := by
    intro b
    by_cases hb : b ∈ S
    · rw [if_pos hb, if_pos hb]; ring
    · rw [if_neg hb, if_neg hb, add_zero]
  rw [tvDist, SPMF.tvDist, PMF.tvDist, PMF.etvDist, tsum_option _ ENNReal.summable]
  have hfailx : (𝒟[ι <$> ($ᵗ A : ProbComp A)]).toPMF none = 0 := probFailure_eq_zero
  have hfaily : (𝒟[($ᵗ B : ProbComp B)]).toPMF none = 0 := probFailure_eq_zero
  have hsome :
      (∑' x : B, ENNReal.absDiff ((𝒟[ι <$> ($ᵗ A : ProbComp A)]).toPMF (some x))
          ((𝒟[($ᵗ B : ProbComp B)]).toPMF (some x)))
        = ∑' x : B, ENNReal.absDiff (Pr[= x | ι <$> ($ᵗ A : ProbComp A)])
            (Pr[= x | ($ᵗ B : ProbComp B)]) :=
    tsum_congr fun _ => rfl
  rw [hfailx, hfaily, ENNReal.absDiff_self, zero_add, hsome, tsum_fintype,
    ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_sum (fun b _ => habs b), Finset.sum_congr rfl (fun b _ => key b),
    Finset.sum_congr rfl (fun b _ => hsplit b), Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_univ, hcardS]
  simp only [nsmul_eq_mul]
  field_simp
  ring

/-! ## The birthday arithmetic -/

/-- The birthday inequality `1 - N.descFactorial q / N ^ q ≤ q (q - 1) / (2 N)` with the
denominators cleared, so that it is a single induction in `ℕ`. -/
theorem two_mul_sub_descFactorial_le (N : ℕ) : ∀ q : ℕ,
    2 * N * (N ^ q - N.descFactorial q) ≤ q * (q - 1) * N ^ q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hD : N.descFactorial q ≤ N ^ q := Nat.descFactorial_le_pow N q
    have key : N ^ (q + 1) - N.descFactorial (q + 1)
        ≤ N * (N ^ q - N.descFactorial q) + q * N ^ q := by
      rw [Nat.descFactorial_succ, pow_succ']
      rcases le_or_gt q N with hq | hq
      · have h1 : (N - q) * N.descFactorial q + q * N.descFactorial q
            = N * N.descFactorial q := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hq]
        have h2 : N * (N ^ q - N.descFactorial q) = N * N ^ q - N * N.descFactorial q :=
          Nat.mul_sub _ _ _
        have h3 : N * N.descFactorial q ≤ N * N ^ q := Nat.mul_le_mul_left _ hD
        have h4 : q * N.descFactorial q ≤ q * N ^ q := Nat.mul_le_mul_left _ hD
        omega
      · have hz : N.descFactorial q = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hq
        rw [hz]; simp
    have step : 2 * N * (N ^ (q + 1) - N.descFactorial (q + 1))
        ≤ N * (2 * N * (N ^ q - N.descFactorial q)) + 2 * q * (N * N ^ q) := by
      calc 2 * N * (N ^ (q + 1) - N.descFactorial (q + 1))
          ≤ 2 * N * (N * (N ^ q - N.descFactorial q) + q * N ^ q) :=
            Nat.mul_le_mul_left _ key
        _ = N * (2 * N * (N ^ q - N.descFactorial q)) + 2 * q * (N * N ^ q) := by ring
    refine step.trans ?_
    have h5 : N * (2 * N * (N ^ q - N.descFactorial q)) ≤ N * (q * (q - 1) * N ^ q) :=
      Nat.mul_le_mul_left _ ih
    calc N * (2 * N * (N ^ q - N.descFactorial q)) + 2 * q * (N * N ^ q)
        ≤ N * (q * (q - 1) * N ^ q) + 2 * q * (N * N ^ q) := Nat.add_le_add_right h5 _
      _ = (q * (q - 1) + 2 * q) * N ^ (q + 1) := by rw [pow_succ']; ring
      _ = (q + 1) * (q + 1 - 1) * N ^ (q + 1) := by
          congr 1
          cases q with
          | zero => simp
          | succ p => simp; ring

/-! ## The i.i.d. bridge -/

/-- A list of `pts.length` independent uniform draws is `List.ofFn` of one uniform draw from
`Fin pts.length → X`: `ToVCVio.evalDist_mapM_const_uniform` gives the `Vector` form, and
`arrayVectorEquivFin` carries a uniform draw across. -/
theorem evalDist_listMapM_uniform_eq_map_ofFn {X : Type} [FinEnum X] [Nonempty X]
    (pts : List X) :
    evalDist (pts.mapM (fun _ => ($ᵗ X : ProbComp X)))
      = evalDist ((List.ofFn : (Fin pts.length → X) → List X) <$>
          ($ᵗ (Fin pts.length → X) : ProbComp (Fin pts.length → X))) := by
  rw [ToVCVio.evalDist_mapM_const_uniform]
  have h := evalDist_map_eq_of_evalDist_eq (evalDist_map_bijective_uniform_cross
    (α := Vector X pts.length) (arrayVectorEquivFin X pts.length)
    (arrayVectorEquivFin X pts.length).bijective) List.ofFn
  rw [Functor.map_map] at h
  have hfun : (Vector.toList : Vector X pts.length → List X)
      = fun v => List.ofFn ((arrayVectorEquivFin X pts.length) v) := by
    funext v; refine List.ext_getElem (by simp) fun i h1 h2 => ?_; simp [arrayVectorEquivFin]
  rw [hfun]; exact h

end OracleComp
