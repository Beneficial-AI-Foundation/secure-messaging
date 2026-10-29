/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Parameters

/-!
# Closed forms for kernel evaluation of rounded-convolution certificates

`certificateValues` is stated with long Horner folds (the window mask and the bad-event weight
pack each have thousands of terms). The kernel caches every intermediate of such a fold, which
costs gigabytes. This file rewrites those folds into closed geometric forms, so that each
certificate reduces to a single `decide +kernel` on the semantic definitions with no stored
witnesses.
-/

namespace FailureCertificate.RoundedConvolution

private theorem two_pow_eq_shift (k : ℕ) : (2 : ℕ) ^ k = 1 <<< k := by
  simp [Nat.shiftLeft_eq]

/-- `productPack` with each `radix ^ k` written as a shift. -/
def shiftedProductPack (c : Config) : ℕ :=
  (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
    (List.range (2 * c.a + 1)).foldl (fun acc (j : ℕ) =>
      let x := (i : ℤ) - c.a
      let y := (j : ℤ) - c.a
      acc + c.weight x * c.weight y *
        (1 <<< (bits c * (x * y + (c.a : ℤ) ^ 2).toNat))) acc) 0

theorem productPack_shifted (c : Config) : productPack c = shiftedProductPack c := by
  unfold productPack shiftedProductPack
  apply congrArg (fun f : ℕ → ℕ → ℕ => (List.range (2 * c.a + 1)).foldl f 0)
  funext acc i
  apply congrArg (fun f : ℕ → ℕ → ℕ => (List.range (2 * c.a + 1)).foldl f acc)
  funext acc j
  simp only [radix]
  rw [← pow_mul, two_pow_eq_shift]

/-- Closed geometric form of `mask`, avoiding its Horner fold over the window. -/
def shiftedMask (c : Config) : ℕ :=
  ((1 <<< (c.precision + 1)) - 1) *
    (((1 <<< (bits c * (2 * c.window + 1))) - 1) / ((1 <<< bits c) - 1))

theorem radix_ge_two (c : Config) : 2 ≤ radix c := by
  change 2 ^ 1 ≤ 2 ^ (c.precision + 1 + 2 * c.seedBits)
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem mask_shifted (c : Config) : mask c = shiftedMask c := by
  unfold mask shiftedMask
  rw [ToVCVio.Packing.foldl_range_mul_add_one_eq_pack, Nat.geomSum_eq (radix_ge_two c)]
  simp only [radix]
  rw [← pow_mul]
  simp only [two_pow_eq_shift]

/-- `extraPack` with each `radix ^ k` written as a shift. -/
def shiftedExtraPack (c : Config) : ℕ :=
  (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
    acc + c.weight ((i : ℤ) - c.a) * (1 <<< (bits c * i))) 0

theorem extraPack_shifted (c : Config) : extraPack c = shiftedExtraPack c := by
  unfold extraPack shiftedExtraPack
  apply congrArg (fun f : ℕ → ℕ → ℕ => (List.range (2 * c.a + 1)).foldl f 0)
  funext acc i
  simp only [radix]
  rw [← pow_mul, two_pow_eq_shift]

/-- `step` over the shifted product pack and the closed mask. -/
def shiftedStep (c : Config) (x : ℕ) : ℕ :=
  ((x * shiftedProductPack c) >>> (c.a ^ 2 * bits c + 2 * c.seedBits)) &&& shiftedMask c

theorem step_shifted (c : Config) : step c = shiftedStep c := by
  funext x
  simp only [step, shiftedStep, productPack_shifted, mask_shifted]

/-- Initial scaled point mass of `runN`, as a shift. -/
def shiftedInit (c : Config) : ℕ := 1 <<< (c.precision + bits c * c.window)

theorem init_shifted (c : Config) :
    2 ^ c.precision * radix c ^ c.window = shiftedInit c := by
  unfold shiftedInit radix
  rw [← pow_mul, ← pow_add, two_pow_eq_shift]

theorem runN_shifted (c : Config) (k : ℕ) :
    runN c k = (List.range k).foldl (fun x _ => shiftedStep c x) (shiftedInit c) := by
  unfold runN
  rw [step_shifted, init_shifted]

/-- Horner fold of `f 0, …, f (n - 1)` in base `R`, starting from `acc`. -/
def horner (R : ℕ) (f : ℕ → ℕ) (acc n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i => acc * R + f i) acc

theorem horner_add (R : ℕ) (f : ℕ → ℕ) (acc a b : ℕ) :
    horner R f acc (a + b) = horner R (fun i => f (a + i)) (horner R f acc a) b := by
  unfold horner
  rw [List.range_add, List.foldl_append, List.foldl_map]

/-- The base-`R` repunit with `n` digits. -/
def onesPack (R n : ℕ) : ℕ := (List.range n).foldl (fun a _ => a * R + 1) 0

theorem horner_const (R : ℕ) (f : ℕ → ℕ) (k acc n : ℕ) (h : ∀ i < n, f i = k) :
    horner R f acc n = acc * R ^ n + k * onesPack R n := by
  induction n with
  | zero => simp [horner, onesPack]
  | succ n ih =>
    have ih' := ih (fun i hi => h i (by omega))
    simp only [horner, onesPack, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at ih' ⊢
    rw [ih', h n (by omega)]
    ring

theorem onesPack_closed (R n : ℕ) (hR : 2 ≤ R) : onesPack R n = (R ^ n - 1) / (R - 1) := by
  unfold onesPack
  rw [ToVCVio.Packing.foldl_range_mul_add_one_eq_pack, Nat.geomSum_eq hR]

/-- A Horner fold of a `1`/`0`/`1` indicator collapses to two repunits. -/
theorem horner_segments (R : ℕ) (f : ℕ → ℕ) (lo mid hi : ℕ)
    (hlo : ∀ i < lo, f i = 1) (hmid : ∀ i < mid, f (lo + i) = 0)
    (hhi : ∀ i < hi, f (lo + mid + i) = 1) :
    horner R f 0 (lo + mid + hi) = onesPack R lo * R ^ mid * R ^ hi + onesPack R hi := by
  rw [horner_add, horner_add, horner_const R f 1 0 lo hlo,
    horner_const R (fun i => f (lo + i)) 0 _ mid hmid,
    horner_const R (fun i => f (lo + mid + i)) 1 _ hi hhi]
  ring

/-- `certificateValues` with every long fold replaced by its closed form, for a weight that is
`1` on the first `lo` and last `hi` offsets of the extended window and `0` on the `mid` between. -/
def closedValues (c : Config) (lo mid hi : ℕ) : ℕ × ℕ :=
  let M := c.window + c.a
  let ones := fun n => ((1 <<< (bits c * n)) - 1) / ((1 <<< bits c) - 1)
  let wp := ones lo * (1 <<< (bits c * mid)) * (1 <<< (bits c * hi)) + ones hi
  let run := (List.range c.steps).foldl (fun x _ => shiftedStep c x) (shiftedInit c)
  (((run * shiftedExtraPack c * wp) >>> (bits c * (2 * M))) % (1 <<< bits c),
    (1 <<< c.precision) - run % ((1 <<< bits c) - 1))

theorem certificateValues_eq_closedValues (c : Config) (w : ℤ → ℕ) (lo mid hi : ℕ)
    (hlen : 2 * (c.window + c.a) + 1 = lo + mid + hi)
    (hlo : ∀ i < lo, w ((i : ℤ) - ((c.window + c.a : ℕ) : ℤ)) = 1)
    (hmid : ∀ i < mid, w (((lo + i : ℕ) : ℤ) - ((c.window + c.a : ℕ) : ℤ)) = 0)
    (hhi : ∀ i < hi, w (((lo + mid + i : ℕ) : ℤ) - ((c.window + c.a : ℕ) : ℤ)) = 1) :
    certificateValues c w = closedValues c lo mid hi := by
  have hwp :
      (List.range (2 * (c.window + c.a) + 1)).foldl
        (fun acc (i : ℕ) => acc * radix c + w ((i : ℤ) - ((c.window + c.a : ℕ) : ℤ))) 0 =
        onesPack (radix c) lo * radix c ^ mid * radix c ^ hi + onesPack (radix c) hi := by
    change horner (radix c) (fun i => w ((i : ℤ) - ((c.window + c.a : ℕ) : ℤ))) 0
      (2 * (c.window + c.a) + 1) = _
    rw [hlen]
    exact horner_segments _ _ lo mid hi hlo hmid hhi
  unfold certificateValues closedValues
  dsimp only
  rw [runN_shifted, extraPack_shifted, hwp, onesPack_closed _ _ (radix_ge_two c),
    onesPack_closed _ _ (radix_ge_two c)]
  simp only [radix]
  simp only [← pow_mul]
  simp only [two_pow_eq_shift]

end FailureCertificate.RoundedConvolution

namespace FrodoKEM.Certificate

open FailureCertificate.RoundedConvolution

/-- For a FrodoKEM family, the bad-event weight splits at the decoding threshold `t` around the
extended-window centre `m`, so its certificate reduces to `closedValues`. -/
theorem certificateValues_eq_closed (ps : ParameterSet) (t m : ℕ)
    (ht : Ideal.threshold ps = t) (hm : (config ps).window + (config ps).a = m) (htm : t ≤ m) :
    certificateValues (config ps) (badWeight ps) =
      closedValues (config ps) (m - t) (2 * t) (m - t + 1) := by
  apply certificateValues_eq_closedValues
  · omega
  all_goals
    intro i hi
    simp only [badWeight, Ideal.entryBad, ht, hm]
    split_ifs <;> omega

end FrodoKEM.Certificate
