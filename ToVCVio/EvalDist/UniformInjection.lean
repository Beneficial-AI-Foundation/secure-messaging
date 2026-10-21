/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToMathlib.MeasureTheory.Measure.Coupling.Maximal
public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.OracleComp.Constructions.SampleableType
public import ToVCVio.OracleComp.Constructions.BitVec

/-!
# Uniform samples through an injection

The distributional ingredients of the fixed-list PRP/PRF switching bound, which
`CryptoFoundations/PRPSwitching.lean` assembles:

* `measureTVDist_map_injective_uniformSample`: a uniform sample pushed through an injection
  `A → B` is at total-variation distance exactly `1 - card A / card B` from uniform on `B`;
* `two_mul_sub_descFactorial_le`: the birthday inequality
  `1 - N.descFactorial q / N^q ≤ q(q - 1)/(2N)`, in `ℕ` with denominators cleared;
* `evalDistEq_listMapM_uniform_map_ofFn`: `q` independent uniform draws are one uniform
  draw from `Fin q → X`.

Candidate for upstream VCVio.
-/

@[expose] public section

open ENNReal

namespace OracleComp

/-! ## A uniform sample pushed through an injection -/

/-- Let `ι : A → B` be injective, `a` uniform on `A` and `b` uniform on `B`. The
total-variation distance between the laws of `ι(a)` and `b` is exactly `1 - |A|/|B|`. -/
theorem measureTVDist_map_injective_uniformSample {A B : Type} [Fintype A] [Fintype B]
    [SampleableType A] [SampleableType B] (ι : A → B) (hι : Function.Injective ι) :
    letI : MeasurableSpace B := ⊤
    measureTVDist (ι <$> ($ᵗ A : ProbComp A)) ($ᵗ B : ProbComp B)
      = 1 - (Fintype.card A : ℝ) / (Fintype.card B : ℝ) := by
  let _ : MeasurableSpace B := ⊤
  -- `DecidableEq` is supplied explicitly rather than by `classical`: instance search from a
  -- bare `SampleableType` context times out at 20000 synthesis heartbeats in this build.
  let : DecidableEq A := Classical.decEq A
  let : DecidableEq B := Classical.decEq B
  set S : Finset B := Finset.univ.image ι with hS
  have hcard : Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective ι hι
  have hApos : 0 < Fintype.card A := Fintype.card_pos
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hApos.ne'
  have hcardS : S.card = Fintype.card A := by
    rw [hS, Finset.card_image_of_injective _ hι, Finset.card_univ]
  -- The mass of the pushed-forward sample: `(card A)⁻¹` on the image, `0` off it.
  have hp : ∀ b : B, Pr{let x ← ι <$> ($ᵗ A : ProbComp A)}[x = b]
      = if b ∈ S then (Fintype.card A : ℝ≥0∞)⁻¹ else 0 := by
    intro b
    by_cases hb : b ∈ S
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
      rw [ite_eq_left hb, prEvent_map_injective _ hι a,
        SampleableType.prEvent_uniformSample_eq_singleton]
    · rw [ite_eq_right hb]
      refine (prEvent_eq_zero_of_not_mem_support _) ?_
      rw [support_map]
      rintro ⟨a, -, rfl⟩
      exact hb (by rw [hS]; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  have hinvle : (Fintype.card B : ℝ≥0∞)⁻¹ ≤ (Fintype.card A : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr hcard)
  -- Both laws live on all of `B`, so the distance is the total excess of `ι(a)` over `b`.
  have hcompl : ((Finset.univ : Finset B) : Set B)ᶜ = ∅ := by
    rw [Finset.coe_univ, Set.compl_univ]
  have hE : measureETVDist (ι <$> ($ᵗ A : ProbComp A)) ($ᵗ B : ProbComp B)
      = (Fintype.card A : ℝ≥0∞) * ((Fintype.card A : ℝ≥0∞)⁻¹ - (Fintype.card B : ℝ≥0∞)⁻¹) := by
    rw [measureETVDist, MeasureTheory.Measure.etvDist_eq_sum_tsub (F := Finset.univ)
      (by rw [hcompl, MeasureTheory.measure_empty]) (by rw [hcompl, MeasureTheory.measure_empty])]
    simp_rw [← prEvent_eq_evalDist_singleton, hp, SampleableType.prEvent_uniformSample_eq_singleton]
    have hterm : ∀ b : B, ((if b ∈ S then (Fintype.card A : ℝ≥0∞)⁻¹ else 0)
        - (Fintype.card B : ℝ≥0∞)⁻¹)
        = if b ∈ S then (Fintype.card A : ℝ≥0∞)⁻¹ - (Fintype.card B : ℝ≥0∞)⁻¹ else 0 := by
      intro b
      by_cases hb : b ∈ S <;> simp only [hb, ↓reduceIte, zero_tsub]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, hcardS, nsmul_eq_mul]
  rw [measureTVDist_eq_toReal_measureETVDist, hE, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hinvle (by simp), ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  field_simp

/-! ## The birthday arithmetic -/

/-- For all `N q : ℕ`, `2N · (N^q - N.descFactorial q) ≤ q(q - 1) · N^q`, where
`N.descFactorial q = N(N - 1)⋯(N - q + 1)`. This is the birthday inequality
`1 - N.descFactorial q / N^q ≤ q(q - 1)/(2N)` with the denominators cleared. -/
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
    -- The closing step is nonlinear in `q` and `N`, so `omega` cannot finish it.
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

/-- Let `q = pts.length`. A list of `q` independent uniform samples from `X` has the same law as
the list `f(0), …, f(q - 1)` for a uniformly random function `f : Fin q → X`. -/
theorem evalDistEq_listMapM_uniform_map_ofFn {X : Type} [FinEnum X] [Nonempty X]
    (pts : List X) :
    pts.mapM (fun _ => ($ᵗ X : ProbComp X))
      =ᵈ (List.ofFn : (Fin pts.length → X) → List X) <$>
          ($ᵗ (Fin pts.length → X) : ProbComp (Fin pts.length → X)) := by
  refine (ToVCVio.evalDistEq_mapM_const_uniform pts).trans ?_
  have h := EvalDistEq.map (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (α := Vector X pts.length) (arrayVectorEquivFin X pts.length).bijective) List.ofFn
  rw [Functor.map_map] at h
  have hfun : (Vector.toList : Vector X pts.length → List X)
      = fun v => List.ofFn ((arrayVectorEquivFin X pts.length) v) := by
    funext v; refine List.ext_getElem (by simp) fun i h1 h2 => ?_; simp [arrayVectorEquivFin]
  rw [hfun]; exact h

end OracleComp
