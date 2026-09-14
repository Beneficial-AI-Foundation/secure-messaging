/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.EvalDist.TVDist
import VCVio.OracleComp.Constructions.SampleableType
import ToVCVio.CryptoFoundations.PRPSwitching
import ToVCVio.OracleComp.Constructions.BitVec
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Uniform samples through an injection, and the fixed-list switching distance

The distance half of the non-adaptive PRP/PRF switching bound. `PRPSwitching.lean` identifies
a uniform permutation applied to `q` distinct points with a `q`-point draw without
replacement; this file bounds the total-variation distance between that draw and `q`
independent uniform draws by `q(q-1)/(2 * card X)`
(`OracleComp.tvDist_map_uniformPerm_mapM_const_uniform_le`). Candidate for upstream VCVio.

The constant is the birthday bound: `q(q-1)/2` unordered pairs of positions, each colliding
with probability `1 / card X`. Here `q` counts the distinct points at which the permutation
is evaluated, which for a mode of operation may exceed its message-block count. Bellare and
Rogaway, *Code-Based Game-Playing Proofs and the Security of Triple Encryption*
(<https://eprint.iacr.org/2004/331.pdf>), state the same bound as `q²/2ⁿ⁺¹`.
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
`Fin pts.length → X`: both put mass `(card X)⁻¹ ^ pts.length` on each list of that length. -/
theorem evalDist_listMapM_uniform_eq_map_ofFn {X : Type} [FinEnum X] [Nonempty X]
    (pts : List X) :
    evalDist (pts.mapM (fun _ => ($ᵗ X : ProbComp X)))
      = evalDist ((List.ofFn : (Fin pts.length → X) → List X) <$>
          ($ᵗ (Fin pts.length → X) : ProbComp (Fin pts.length → X))) := by
  letI : DecidableEq X := Classical.decEq X
  have hRHS : ∀ xs : List X,
      Pr[= xs | (List.ofFn : (Fin pts.length → X) → List X) <$>
          ($ᵗ (Fin pts.length → X) : ProbComp (Fin pts.length → X))]
        = if xs.length = pts.length then ((Fintype.card X : ℝ≥0∞)⁻¹) ^ pts.length else 0 := by
    intro xs
    by_cases hlen : xs.length = pts.length
    · rw [if_pos hlen]
      -- The unique function whose `List.ofFn` is `xs`.
      set f : Fin pts.length → X :=
        fun i => xs[(i : ℕ)]'(Nat.lt_of_lt_of_eq i.isLt hlen.symm) with hf
      have hfn : (List.ofFn f) = xs := by
        refine List.ext_getElem (by simp [hlen]) ?_
        intro i h₁ h₂
        simp [hf, List.getElem_ofFn]
      rw [← hfn, probOutput_map_injective _ List.ofFn_injective f, probOutput_uniformSample,
        Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ENNReal.inv_pow]
    · rw [if_neg hlen]
      refine probOutput_eq_zero_of_not_mem_support ?_
      rw [support_map]
      rintro ⟨f, -, rfl⟩
      exact hlen (by simp)
  refine evalDist_ext fun xs => ?_
  rw [ToVCVio.probOutput_mapM_const_uniform, hRHS]

/-! ## The assembled fixed-list switching bound -/

/-- `tvDist` depends only on the distributions of its arguments. -/
private theorem tvDist_congr {α : Type} {m₁ m₂ m₃ m₄ : ProbComp α}
    (h₁ : evalDist m₁ = evalDist m₂) (h₂ : evalDist m₃ = evalDist m₄) :
    tvDist m₁ m₃ = tvDist m₂ m₄ := by
  rw [tvDist, tvDist, h₁, h₂]

/-- The fixed-list PRP/PRF switching bound: for a duplicate-free list `pts` of `q` points,
applying a uniform permutation of `X` to `pts` and drawing `q` independent uniform elements of
`X` are within total-variation distance `q (q - 1) / (2 * card X)`.

The subtraction `pts.length - 1` is in `ℝ`, so at `q = 0` the bound is `0`, which is correct.
`[Nonempty X]` is needed because `[FinEnum X]` alone does not make `X` sampleable. -/
theorem tvDist_map_uniformPerm_mapM_const_uniform_le {X : Type} [FinEnum X] [Nonempty X]
    (pts : List X) (hpts : pts.Nodup) :
    tvDist ((fun π : Equiv.Perm X => pts.map π) <$>
        ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
        (pts.mapM (fun _ => ($ᵗ X : ProbComp X)))
      ≤ (pts.length * (pts.length - 1) : ℝ) / (2 * Fintype.card X) := by
  letI : DecidableEq X := Classical.decEq X
  haveI hq : Nonempty (Fin pts.length ↪ X) := nonempty_embedding_of_nodup pts hpts
  have hNpos : 0 < Fintype.card X := Fintype.card_pos
  have hN0 : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  -- (a) The permutation side, as a without-replacement draw. `sampleDistinctFrom`'s body is
  -- `rfl`-equal to the explicit map, the `Nonempty` witness being a `Prop`.
  have hRHSperm : sampleDistinctFrom X pts.length (nonempty_embedding_of_nodup pts hpts)
      = (fun e : Fin pts.length ↪ X => List.ofFn (e : Fin pts.length → X)) <$>
        ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X)) := rfl
  have hperm : evalDist ((fun π : Equiv.Perm X => pts.map π) <$>
      ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
      = evalDist ((fun e : Fin pts.length ↪ X => List.ofFn (e : Fin pts.length → X)) <$>
          ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X))) := by
    rw [evalDist_map_uniformPerm_eq_uniformDistinct pts hpts, hRHSperm]
  -- (b) The i.i.d. side, as a single uniform function draw.
  rw [tvDist_congr hperm (evalDist_listMapM_uniform_eq_map_ofFn pts)]
  -- (c) Strip the common `List.ofFn`, leaving the embedding coercion against the full function
  -- space. `rw [Functor.map_map]` is used forwards and beta-reduces, so the coercion side is
  -- stated in its already-beta-reduced shape.
  have hmap : ((fun e : Fin pts.length ↪ X => List.ofFn (e : Fin pts.length → X)) <$>
        ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X)))
      = (List.ofFn : (Fin pts.length → X) → List X) <$>
        ((fun e : Fin pts.length ↪ X => (e : Fin pts.length → X)) <$>
          ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X))) := by
    rw [Functor.map_map]
  rw [hmap]
  refine (tvDist_map_le (List.ofFn : (Fin pts.length → X) → List X) _ _).trans ?_
  -- (d) The distance itself, and the two cardinalities.
  rw [tvDist_map_injective_uniformSample _ Function.Embedding.coe_injective,
    Fintype.card_embedding_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  -- (e) The birthday arithmetic, after the single `ℕ → ℝ` cast. `pts.length = 0` is a real
  -- degenerate case (both sides are `0`); `pts.Nodup` makes `pts.length > card X` vacuous,
  -- although `two_mul_sub_descFactorial_le` covers that branch regardless.
  rcases Nat.eq_zero_or_pos pts.length with hq0 | hq1
  · rw [hq0]; simp
  have hD : (Fintype.card X).descFactorial pts.length ≤ Fintype.card X ^ pts.length :=
    Nat.descFactorial_le_pow _ _
  have hNq : (0 : ℝ) < (Fintype.card X : ℝ) ^ pts.length := by positivity
  have hB4 : 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
        - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ))
      ≤ (pts.length : ℝ) * ((pts.length : ℝ) - 1) * (Fintype.card X : ℝ) ^ pts.length := by
    have h := two_mul_sub_descFactorial_le (Fintype.card X) pts.length
    have hcast : ((2 * Fintype.card X * (Fintype.card X ^ pts.length
          - (Fintype.card X).descFactorial pts.length) : ℕ) : ℝ)
        = 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
          - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)) := by
      push_cast [Nat.cast_sub hD]
      ring
    have hcast' : ((pts.length * (pts.length - 1) * Fintype.card X ^ pts.length : ℕ) : ℝ)
        = (pts.length : ℝ) * ((pts.length : ℝ) - 1)
          * (Fintype.card X : ℝ) ^ pts.length := by
      push_cast [Nat.cast_sub hq1]
      ring
    calc 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
          - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ))
        = ((2 * Fintype.card X * (Fintype.card X ^ pts.length
            - (Fintype.card X).descFactorial pts.length) : ℕ) : ℝ) := hcast.symm
      _ ≤ ((pts.length * (pts.length - 1) * Fintype.card X ^ pts.length : ℕ) : ℝ) :=
          Nat.cast_le.mpr h
      _ = (pts.length : ℝ) * ((pts.length : ℝ) - 1)
          * (Fintype.card X : ℝ) ^ pts.length := hcast'
  have hsub : (1 : ℝ) - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)
        / ((Fintype.card X : ℝ) ^ pts.length)
      = ((Fintype.card X : ℝ) ^ pts.length
          - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ))
        / ((Fintype.card X : ℝ) ^ pts.length) := by
    field_simp
  rw [hsub, div_le_div_iff₀ hNq (by positivity)]
  calc ((Fintype.card X : ℝ) ^ pts.length
        - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)) * (2 * (Fintype.card X : ℝ))
      = 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
        - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)) := by ring
    _ ≤ (pts.length : ℝ) * ((pts.length : ℝ) - 1)
        * (Fintype.card X : ℝ) ^ pts.length := hB4

end OracleComp
