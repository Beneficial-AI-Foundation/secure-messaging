/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model.Counts
import SecureMessaging.CKA.FromLWE.PhaseCorrectness.EntryNoise

/-!
# Exact sampling law for historical Frodo certificates

This unit derives the exact entry-noise distribution from the shared integer
counting measure.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA.Frodo2016.Certificate

open SharedModelInternal

set_option Elab.async false in
section

private theorem counts_neg (c : Config)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    counts c (-z) = counts c z := by
  by_cases hz : z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)
  · have hnz : -z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ) := by
      simpa only [Finset.mem_Icc] using
        (show -(c.a : ℤ) ≤ -z ∧ -z ≤ c.a by
          have := Finset.mem_Icc.mp hz
          omega)
    rw [counts_apply_of_mem c (-z) hnz, counts_apply_of_mem c z hz, hsym]
  · have hnz : -z ∉ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ) := by
      intro h
      apply hz
      simpa only [Finset.mem_Icc] using
        (show -(c.a : ℤ) ≤ z ∧ z ≤ c.a by
          have := Finset.mem_Icc.mp h
          omega)
    rw [counts_apply_of_not_mem c (-z) hnz, counts_apply_of_not_mem c z hz]

private def productExp (χ : ProbComp ℤ) : ProbComp ℤ := do
  let x ← χ
  let y ← χ
  return x * y

private def negProductExp (χ : ProbComp ℤ) : ProbComp ℤ := do
  let x ← (-·) <$> χ
  let y ← χ
  return x * y

private theorem probOutput_mul_counts
    (mx my : ProbComp ℤ) (F G : ToVCVio.IntMeasure) (D E : Nat)
    (hmx : ∀ z, Pr{let x ← mx}[x = z] = (F z : ℝ≥0∞) / D)
    (hmy : ∀ z, Pr{let x ← my}[x = z] = (G z : ℝ≥0∞) / E)
    (z : ℤ) :
    Pr{let w ← (fun x y : ℤ => x * y) <$> mx <*> my}[w = z] =
      (ToVCVio.productMeasure F G z : ℝ≥0∞) / (D * E) := by
  rw [probOutput_seq_map_eq_tsum_ite]
  rw [tsum_eq_sum (s := F.coeff.support)]
  · have hinner (x : ℤ) :
        (∑' y : ℤ, if z = x * y then Pr{let y ← mx}[y = x] * Pr{let x ← my}[x = y] else 0) =
          ∑ y ∈ G.coeff.support,
            if z = x * y then Pr{let y ← mx}[y = x] * Pr{let x ← my}[x = y] else 0 := by
      rw [tsum_eq_sum (s := G.coeff.support)]
      intro y hy
      have hzero : G y = 0 := Finsupp.notMem_support_iff.mp hy
      simp [hmy, hzero]
    simp_rw [hinner, hmx, hmy]
    rw [ToVCVio.productMeasure_apply]
    simp only [Finsupp.sum]
    push_cast
    simp only [div_eq_mul_inv]
    have hinv : ((D : ℝ≥0∞) * E)⁻¹ =
        (D : ℝ≥0∞)⁻¹ * (E : ℝ≥0∞)⁻¹ :=
      ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)
    rw [hinv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y hy => ?_
    by_cases hxy : z = x * y
    · rw [if_pos hxy, if_pos hxy.symm]
      ac_rfl
    · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]
      simp only [zero_mul]
  · intro x hx
    have hzero : F x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hmx, hzero]

private theorem probOutput_productExp
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr{let x ← χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (z : ℤ) :
    Pr{let x ← productExp χ}[x = z] =
      (ToVCVio.productMeasure (counts c) (counts c) z : ℝ≥0∞) /
        (2 ^ c.seedBits) ^ 2 := by
  have hlawNat (u : ℤ) :
      Pr{let x ← χ}[x = u] =
        (counts c u : ℝ≥0∞) / (((2 ^ c.seedBits : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlaw u
  simpa only [productExp, map_eq_bind_pure_comp, seq_eq_bind_map,
    Function.comp_def, bind_assoc, pure_bind, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, pow_two] using
    probOutput_mul_counts χ χ (counts c) (counts c)
      (2 ^ c.seedBits) (2 ^ c.seedBits) hlawNat hlawNat z

private theorem probOutput_neg_map
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr{let x ← χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    Pr{let x ← (-·) <$> χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits := by
  calc
    Pr{let x ← (-·) <$> χ}[x = z] = Pr{let x ← χ}[x = -z] := by
      convert prEvent_map_injective χ (fun _ _ h => neg_inj.mp h) (-z) using 1
      all_goals simp
    _ = (counts c (-z) : ℝ≥0∞) / 2 ^ c.seedBits := hlaw (-z)
    _ = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits := by rw [counts_neg c hsym]

private theorem probOutput_negProductExp
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr{let x ← χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    Pr{let x ← negProductExp χ}[x = z] =
      (ToVCVio.productMeasure (counts c) (counts c) z : ℝ≥0∞) /
        (2 ^ c.seedBits) ^ 2 := by
  have hnegNat (u : ℤ) :
      Pr{let x ← (-·) <$> χ}[x = u] =
        (counts c u : ℝ≥0∞) / (((2 ^ c.seedBits : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      probOutput_neg_map c χ hlaw hsym u
  have hlawNat (u : ℤ) :
      Pr{let x ← χ}[x = u] =
        (counts c u : ℝ≥0∞) / (((2 ^ c.seedBits : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlaw u
  simpa only [negProductExp, map_eq_bind_pure_comp, seq_eq_bind_map,
    Function.comp_def, bind_assoc, pure_bind, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, pow_two] using
    probOutput_mul_counts ((-·) <$> χ) χ (counts c) (counts c)
      (2 ^ c.seedBits) (2 ^ c.seedBits)
      hnegNat hlawNat z

private theorem probOutput_add_counts
    (mx my : ProbComp ℤ) (F G : ToVCVio.IntMeasure) (D E : Nat)
    (hmx : ∀ z, Pr{let x ← mx}[x = z] = (F z : ℝ≥0∞) / D)
    (hmy : ∀ z, Pr{let x ← my}[x = z] = (G z : ℝ≥0∞) / E)
    (z : ℤ) :
    Pr{let w ← (fun x y : ℤ => x + y) <$> mx <*> my}[w = z] =
      ((F * G) z : ℝ≥0∞) / (D * E) := by
  rw [probOutput_seq_map_eq_tsum_ite]
  have hinner (x : ℤ) :
      (∑' y : ℤ, if z = x + y then Pr{let y ← mx}[y = x] * Pr{let x ← my}[x = y] else 0) =
        Pr{let y ← mx}[y = x] * Pr{let y ← my}[y = z - x] := by
    refine (tsum_eq_single (z - x) (fun y hy => ?_)).trans ?_
    · rw [if_neg]
      intro h
      apply hy
      omega
    · rw [if_pos (by omega)]
  simp_rw [hinner]
  rw [tsum_eq_sum (s := F.coeff.support)]
  · simp_rw [hmx, hmy]
    rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
    push_cast
    simp only [div_eq_mul_inv]
    have hinv : ((D : ℝ≥0∞) * E)⁻¹ =
        (D : ℝ≥0∞)⁻¹ * (E : ℝ≥0∞)⁻¹ :=
      ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)
    rw [hinv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [show -x + z = z - x by ring]
    ac_rfl
  · intro x hx
    have hzero : F x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hmx, hzero]

private def differenceBlock (χ : ProbComp ℤ) : ProbComp ℤ := do
  let s0 ← χ
  let e0 ← χ
  let s1 ← χ
  let e1 ← χ
  return s1 * e0 - e1 * s0

private theorem evalDist_differenceBlock_grouped (χ : ProbComp ℤ) :
    finiteLaw (differenceBlock χ) =
      finiteLaw ((fun x y : ℤ => x + y) <$> productExp χ <*> negProductExp χ) := by
  simp only [differenceBlock, productExp, negProductExp,
    map_eq_bind_pure_comp, seq_eq_bind_map, Function.comp_apply, bind_assoc, pure_bind]
  calc
    _ = finiteLaw (do
          let e0 ← χ
          let s0 ← χ
          let s1 ← χ
          let e1 ← χ
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = finiteLaw (do
          let e0 ← χ
          let s1 ← χ
          let s0 ← χ
          let e1 ← χ
          return s1 * e0 - e1 * s0) := by
        refine evalDist_bind_congr' χ fun _ => ?_
        exact evalDist_bind_bind_swap _ _ _
    _ = finiteLaw (do
          let s1 ← χ
          let e0 ← χ
          let s0 ← χ
          let e1 ← χ
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = finiteLaw (do
          let s1 ← χ
          let e0 ← χ
          let e1 ← χ
          let s0 ← χ
          return s1 * e0 - e1 * s0) := by
        refine evalDist_bind_congr' χ fun _ => ?_
        refine evalDist_bind_congr' χ fun _ => ?_
        exact evalDist_bind_bind_swap _ _ _
    _ = _ := by
      refine evalDist_bind_congr' χ fun s1 => ?_
      refine evalDist_bind_congr' χ fun e0 => ?_
      refine evalDist_bind_congr' χ fun e1 => ?_
      refine evalDist_bind_congr' χ fun s0 => ?_
      simp only [evalDist_pure]
      congr 1
      ring

private theorem probOutput_differenceBlock
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr{let x ← χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    Pr{let x ← differenceBlock χ}[x = z] =
      (((ToVCVio.productMeasure (counts c) (counts c)) ^ 2) z : ℝ≥0∞) /
        (2 ^ c.seedBits) ^ 4 := by
  rw [(evalDist_ext_iff.mp (evalDist_differenceBlock_grouped χ)) z]
  have hprodNat (u : ℤ) :
      Pr{let x ← productExp χ}[x = u] =
        (ToVCVio.productMeasure (counts c) (counts c) u : ℝ≥0∞) /
          ((((2 ^ c.seedBits) ^ 2 : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      probOutput_productExp c χ hlaw u
  have hnegProdNat (u : ℤ) :
      Pr{let x ← negProductExp χ}[x = u] =
        (ToVCVio.productMeasure (counts c) (counts c) u : ℝ≥0∞) /
          ((((2 ^ c.seedBits) ^ 2 : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      probOutput_negProductExp c χ hlaw hsym u
  have h := probOutput_add_counts (productExp χ) (negProductExp χ)
    (ToVCVio.productMeasure (counts c) (counts c))
    (ToVCVio.productMeasure (counts c) (counts c))
    ((2 ^ c.seedBits) ^ 2) ((2 ^ c.seedBits) ^ 2)
    hprodNat hnegProdNat z
  have hden : (2 : ℝ≥0∞) ^
        (c.seedBits + c.seedBits + (c.seedBits + c.seedBits)) =
      ((2 : ℝ≥0∞) ^ c.seedBits) ^ 4 := by
    rw [← pow_mul]
    congr 1
    omega
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_two, ← pow_add,
    hden] using h

private theorem evalDist_bind_move_after_two
    {A B C D : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (f : A → B → C → ProbComp D) :
    finiteLaw (do
      let a ← ma
      let b ← mb
      let c ← mc
      f a b c) =
    finiteLaw (do
      let b ← mb
      let c ← mc
      let a ← ma
      f a b c) := by
  calc
    _ = finiteLaw (do
          let b ← mb
          let a ← ma
          let c ← mc
          f a b c) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun _ => evalDist_bind_bind_swap ma mc _

private theorem evalDist_bind_move_after_three
    {A B C D E : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (md : ProbComp D) (f : A → B → C → D → ProbComp E) :
    finiteLaw (do
      let a ← ma
      let b ← mb
      let c ← mc
      let d ← md
      f a b c d) =
    finiteLaw (do
      let b ← mb
      let c ← mc
      let d ← md
      let a ← ma
      f a b c d) := by
  calc
    _ = finiteLaw (do
          let b ← mb
          let a ← ma
          let c ← mc
          let d ← md
          f a b c d) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_move_after_two ma mc md (fun a c d => f a b c d)

private theorem evalDist_bind_move_after_four
    {A B C D E F : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (md : ProbComp D) (me : ProbComp E)
    (f : A → B → C → D → E → ProbComp F) :
    finiteLaw (do
      let a ← ma
      let b ← mb
      let c ← mc
      let d ← md
      let e ← me
      f a b c d e) =
    finiteLaw (do
      let b ← mb
      let c ← mc
      let d ← md
      let e ← me
      let a ← ma
      f a b c d e) := by
  calc
    _ = finiteLaw (do
          let b ← mb
          let a ← ma
          let c ← mc
          let d ← md
          let e ← me
          f a b c d e) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_move_after_three ma mc md me (fun a c d e => f a b c d e)

private theorem evalDist_bind_rotate_four_heads
    {H0 T0 H1 T1 H2 T2 H3 T3 X R : Type}
    (h0 : ProbComp H0) (t0 : ProbComp T0) (h1 : ProbComp H1) (t1 : ProbComp T1)
    (h2 : ProbComp H2) (t2 : ProbComp T2) (h3 : ProbComp H3) (t3 : ProbComp T3)
    (mx : ProbComp X)
    (f : H0 → T0 → H1 → T1 → H2 → T2 → H3 → T3 → X → ProbComp R) :
    finiteLaw (do
      let a0 ← h0
      let b0 ← t0
      let a1 ← h1
      let b1 ← t1
      let a2 ← h2
      let b2 ← t2
      let a3 ← h3
      let b3 ← t3
      let x ← mx
      f a0 b0 a1 b1 a2 b2 a3 b3 x) =
    finiteLaw (do
      let b0 ← t0
      let b1 ← t1
      let b2 ← t2
      let b3 ← t3
      let x ← mx
      let a0 ← h0
      let a1 ← h1
      let a2 ← h2
      let a3 ← h3
      f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
  calc
    _ = finiteLaw (do
          let b0 ← t0
          let a0 ← h0
          let a1 ← h1
          let b1 ← t1
          let a2 ← h2
          let b2 ← t2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := evalDist_bind_bind_swap h0 t0 _
    _ = finiteLaw (do
          let b0 ← t0
          let b1 ← t1
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let b2 ← t2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        exact (evalDist_bind_move_after_two t1 h0 h1
          (fun b1 a0 a1 => do
            let a2 ← h2
            let b2 ← t2
            let a3 ← h3
            let b3 ← t3
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = finiteLaw (do
          let b0 ← t0
          let b1 ← t1
          let b2 ← t2
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        exact (evalDist_bind_move_after_three t2 h0 h1 h2
          (fun b2 a0 a1 a2 => do
            let a3 ← h3
            let b3 ← t3
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = finiteLaw (do
          let b0 ← t0
          let b1 ← t1
          let b2 ← t2
          let b3 ← t3
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let a3 ← h3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        refine evalDist_bind_congr' t2 fun b2 => ?_
        exact (evalDist_bind_move_after_four t3 h0 h1 h2 h3
          (fun b3 a0 a1 a2 a3 => do
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = _ := by
      refine evalDist_bind_congr' t0 fun b0 => ?_
      refine evalDist_bind_congr' t1 fun b1 => ?_
      refine evalDist_bind_congr' t2 fun b2 => ?_
      refine evalDist_bind_congr' t3 fun b3 => ?_
      exact (evalDist_bind_move_after_four mx h0 h1 h2 h3
        (fun x a0 a1 a2 a3 => f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm

private theorem evalDist_entryNoiseIntExp_succ (n : ℕ) (χ : ProbComp ℤ) :
    finiteLaw (entryNoiseIntExp (n + 1) χ) =
      finiteLaw (do
        let rest ← entryNoiseIntExp n χ
        let delta ← differenceBlock χ
        return rest + delta) := by
  let tail : ProbComp (Fin n → ℤ) := Fin.mOfFn n fun _ => χ
  let finish (s0 : ℤ) (s0s : Fin n → ℤ) (e0 : ℤ) (e0s : Fin n → ℤ)
      (s1 : ℤ) (s1s : Fin n → ℤ) (e1 : ℤ) (e1s : Fin n → ℤ)
      (extra : ℤ) : ProbComp ℤ :=
    pure ((∑ k, Fin.cons s1 s1s k * Fin.cons e0 e0s k) -
      (∑ k, Fin.cons e1 e1s k * Fin.cons s0 s0s k) + extra)
  simp only [entryNoiseIntExp, differenceBlock, ProbComp.sampleIID,
    Fin.mOfFn, bind_assoc, pure_bind]
  change finiteLaw (do
      let s0 ← χ
      let s0s ← tail
      let e0 ← χ
      let e0s ← tail
      let s1 ← χ
      let s1s ← tail
      let e1 ← χ
      let e1s ← tail
      let extra ← χ
      finish s0 s0s e0 e0s s1 s1s e1 e1s extra) = _
  calc
    _ = finiteLaw (do
          let s0s ← tail
          let e0s ← tail
          let s1s ← tail
          let e1s ← tail
          let extra ← χ
          let s0 ← χ
          let e0 ← χ
          let s1 ← χ
          let e1 ← χ
          finish s0 s0s e0 e0s s1 s1s e1 e1s extra) :=
        evalDist_bind_rotate_four_heads χ tail χ tail χ tail χ tail χ finish
    _ = _ := by
      refine evalDist_bind_congr' tail fun s0s => ?_
      refine evalDist_bind_congr' tail fun e0s => ?_
      refine evalDist_bind_congr' tail fun s1s => ?_
      refine evalDist_bind_congr' tail fun e1s => ?_
      refine evalDist_bind_congr' χ fun extra => ?_
      refine evalDist_bind_congr' χ fun s0 => ?_
      refine evalDist_bind_congr' χ fun e0 => ?_
      refine evalDist_bind_congr' χ fun s1 => ?_
      refine evalDist_bind_congr' χ fun e1 => ?_
      simp only [finish, evalDist_pure]
      congr 1
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring

theorem SharedModelInternal.probOutput_entryNoiseIntExp_counts
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr{let x ← χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z)
    (n : ℕ) (z : ℤ) :
    Pr{let x ← entryNoiseIntExp n χ}[x = z] =
      (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) * counts c) z :
          ℝ≥0∞) /
        (2 ^ c.seedBits) ^ (4 * n + 1) := by
  induction n generalizing z with
  | zero =>
      simp only [entryNoiseIntExp, ProbComp.sampleIID, Fin.mOfFn, pure_bind,
        Fin.sum_univ_zero, zero_sub, neg_zero, zero_add, bind_pure, Nat.mul_zero, pow_zero,
        one_mul, Nat.zero_add, pow_one]
      exact hlaw z
  | succ n ih =>
      rw [(evalDist_ext_iff.mp (evalDist_entryNoiseIntExp_succ n χ)) z]
      rw [show (do
          let rest ← entryNoiseIntExp n χ
          let delta ← differenceBlock χ
          return rest + delta) =
          (fun x y : ℤ => x + y) <$> entryNoiseIntExp n χ <*> differenceBlock χ by
        simp only [map_eq_bind_pure_comp, seq_eq_bind_map,
          Function.comp_def, bind_assoc, pure_bind]]
      have ihNat (u : ℤ) :
          Pr{let x ← entryNoiseIntExp n χ}[x = u] =
            (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) *
                counts c) u : ℝ≥0∞) /
              (((2 ^ c.seedBits) ^ (4 * n + 1) : Nat) : ℝ≥0∞) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using ih u
      have hstepNat (u : ℤ) :
          Pr{let x ← differenceBlock χ}[x = u] =
            ((((ToVCVio.productMeasure (counts c) (counts c)) ^ 2) u : ℝ≥0∞) /
              (((2 ^ c.seedBits) ^ 4 : Nat) : ℝ≥0∞)) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          probOutput_differenceBlock c χ hlaw hsym u
      calc
        _ = ((((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) *
                counts c) *
              (ToVCVio.productMeasure (counts c) (counts c)) ^ 2) z : ℝ≥0∞) /
            ((((2 ^ c.seedBits) ^ (4 * n + 1)) *
                (2 ^ c.seedBits) ^ 4 : Nat) : ℝ≥0∞) := by
          simpa only [Nat.cast_mul] using probOutput_add_counts
            (entryNoiseIntExp n χ) (differenceBlock χ)
            ((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) * counts c)
            ((ToVCVio.productMeasure (counts c) (counts c)) ^ 2)
            ((2 ^ c.seedBits) ^ (4 * n + 1)) ((2 ^ c.seedBits) ^ 4)
            ihNat hstepNat z
        _ = (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * (n + 1)) *
              counts c) z : ℝ≥0∞) /
            (2 ^ c.seedBits) ^ (4 * (n + 1) + 1) := by
          have hmeasure :
              ((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) *
                  counts c) *
                (ToVCVio.productMeasure (counts c) (counts c)) ^ 2 =
              (ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * (n + 1)) *
                counts c := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
            ring
          rw [hmeasure]
          simp only [Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
          congr 2


end

end lweCKA.Frodo2016.Certificate
