/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.KEM.MLKEM.Correctness.NoiseDistribution
public import ToVCVio.Probability.IntMeasure.Packing

/-!
# The radix-packing engine

This file specializes the generic radix packing of integer measures
(`ToVCVio.Radix`, `ToVCVio.Packing`) to the ML-KEM decode-failure mass. It
supplies the ML-KEM-specific periodization modulo `q` and the weight function.

For a finitely supported function `F : ℤ →₀ ℕ`, write the associated counting
measure on the discrete space `ℤ` as

`μ_F(A) = ∑_{v ∈ A} F(v)`.

Thus `F(v)` is the mass of the singleton `{v}`. This file works with these
unnormalized natural-number masses; a probability is obtained only later by
dividing by the total mass `∑_v F(v)`.

When `F` is supported in `[lo, hi]`, define the mass-generating polynomial

`P_F(X) = ∑_{v=lo}^{hi} F(v) X^(v-lo)`.

`measurePack R lo F` is the evaluation `P_F(R)`. The polynomial is just a
finite algebraic encoding of the singleton masses `μ_F({v}) = F(v)`. The radix
`R` is chosen larger than the coefficients that can appear in the intermediate
products, so coefficient extraction from `P_F(R)` by division and remainder is
exact: no carry can change the coefficient being read.

More explicitly, additive convolution is

`(F*G)(v)=∑_{a+b=v}F(a)G(b)`,

and `measurePack_mul` proves

`P_{F*G}(R)=P_F(R)P_G(R)`

with the appropriate shift of the lower support endpoint.

Suppose the support of `F` is divided into `m` consecutive blocks of length
`q`. Define its residue-class masses and their packing by

```
a_t = ∑_{j=0}^{m-1} F(lo+qj+t),
A_R = ∑_{t=0}^{q-1} a_t R^t.
```

Since `X^q=1` modulo `X^q-1`, `sum_mul_pow_mod_repunit` proves, under the
explicit no-carry bound,

`A_R = measurePack R lo F mod (R^q-1)`.                  (1)

For weights `b_t`, let

`B_R^rev=∑_{t=0}^{q-1} b_{q-1-t}R^t`.

The coefficient of degree `q-1` in `A(X)B^rev(X)` is exactly
`∑_t a_t b_t`. If every product coefficient is below `R`, base-`R` digit
extraction therefore gives

`∑_t a_t b_t = (A_R B_R^rev / R^{q-1}) mod R`.           (2)

`decodeFailureMass_eq` applies (1)--(2) with `q=3329`, `F` equal to
`coefficientNoiseMeasure p`, and `b_t` equal to the exact number of message
bits that fail at residue `lo+t`.  The implementation uses `foldedNoiseMeasure`,
defined with `Finsupp.mapDomain`, to sum the masses in each congruence class.  The extracted “middle
coefficient” is the coefficient of `X^{q-1}` in the product with the reversed
weight polynomial.
-/

@[expose] public section

open ToVCVio ToVCVio.Radix LatticeCrypto
open scoped ENNReal

namespace MLKEM

/-! ## Periodization modulo `q` and the weighted coefficient -/

private theorem mapDomain_apply_eq_sum {β : Type*} [DecidableEq β] (g : ℤ → β)
    (F : IntMeasure) (r : β) :
    Finsupp.mapDomain g F r = Finsupp.sum F fun v m => if g v = r then m else 0 := by
  rw [Finsupp.mapDomain]
  refine (Finsupp.sum_apply).trans ?_
  exact Finsupp.sum_congr fun v _ => Finsupp.single_apply

/-- A mass of the folded measure is the block sum of the integer-measure masses
over the residue class inside the window. -/
private theorem foldedNoiseMeasure_apply_block (p : ParameterSet) {lo : ℤ} {m : ℕ}
    (hwin : MeasureWindow (coefficientNoiseMeasure p) lo (lo + ((modulus * m : ℕ) : ℤ) - 1))
    {t : ℕ} (ht : t < modulus) :
    foldedNoiseMeasure p (((lo + (t : ℤ)) : ℤ) : Coeff) =
      ∑ j ∈ Finset.range m,
        coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ)) := by
  rw [foldedNoiseMeasure, mapDomain_apply_eq_sum]
  have hsub : (coefficientNoiseMeasure p).coeff.support ⊆
      (Finset.range (modulus * m)).image fun i : ℕ => lo + (i : ℤ) := by
    intro v hv
    have hw := hwin v (Finsupp.mem_support_iff.mp hv)
    rw [Finset.mem_image]
    exact ⟨(v - lo).toNat, Finset.mem_range.mpr (by omega), by omega⟩
  refine Eq.trans (Finsupp.sum_of_support_subset _ hsub _ fun i _ => ite_self 0) ?_
  refine Eq.trans (Finset.sum_image fun i _ j _ h => by omega) ?_
  have ht' : t < 3329 := by simpa [modulus] using ht
  have hcond : ∀ i : ℕ,
      (((lo + (i : ℤ)) : ℤ) : Coeff) = (((lo + (t : ℤ)) : ℤ) : Coeff) ↔
        i % modulus = t := by
    intro i
    rw [ZMod.intCast_eq_intCast_iff, Int.ModEq]
    simp only [modulus]
    constructor
    · intro h
      omega
    · intro h
      omega
  have hite : ∀ i ∈ Finset.range (modulus * m),
      (if (((lo + (i : ℤ)) : ℤ) : Coeff) = (((lo + (t : ℤ)) : ℤ) : Coeff) then
        coefficientNoiseMeasure p (lo + (i : ℤ)) else 0) =
      (if i % modulus = t then coefficientNoiseMeasure p (lo + (i : ℤ)) else 0) := by
    intro i _
    exact if_congr (hcond i) rfl rfl
  rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
  have hfilter : (Finset.range (modulus * m)).filter (fun i => i % modulus = t) =
      (Finset.range m).image fun j => modulus * j + t := by
    ext i
    rw [Finset.mem_filter]
    simp only [Finset.mem_range, Finset.mem_image, modulus]
    constructor
    · rintro ⟨hi, hmod⟩
      refine ⟨i / 3329, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      constructor
      · omega
      · omega
  rw [hfilter, Finset.sum_image fun i _ j _ h => by simp only [modulus] at h; omega]

/-- Evaluation form of the decode-failure mass: pack the coefficient-noise
measure by evaluating its generating polynomial at `R`, fold with the repunit
modulus, multiply by the reversed weight packing, and extract the middle
coefficient. -/
theorem decodeFailureMass_eq (p : ParameterSet) {R : ℕ} {lo : ℤ} {m : ℕ}
    (hR : 2 ≤ R)
    (hwin : MeasureWindow (coefficientNoiseMeasure p) lo (lo + ((modulus * m : ℕ) : ℤ) - 1))
    (hden : 2 * totalMass (coefficientNoiseMeasure p) < R) :
    decodeFailureMass p =
      measurePack R lo (coefficientNoiseMeasure p) % (R ^ modulus - 1) *
        (∑ t ∈ Finset.range modulus,
          decodeFailureWeight
            ((lo + ((modulus - 1 : ℕ) : ℤ) - (t : ℤ) : ℤ) : Coeff) * R ^ t) /
        R ^ (modulus - 1) % R := by
  have hq : 0 < modulus := by norm_num [modulus]
  have htot : ∑ t ∈ Finset.range modulus,
      (∑ j ∈ Finset.range m, coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ))) =
      totalMass (coefficientNoiseMeasure p) := by
    rw [totalMass_eq_range_sum hwin,
      sum_range_mul_eq_sum_sum fun i => coefficientNoiseMeasure p (lo + (i : ℤ)), Finset.sum_comm]
  have hfold_lt : ∀ t < modulus,
      2 * ∑ j ∈ Finset.range m,
        coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ)) < R := by
    intro t ht
    have hle : (∑ j ∈ Finset.range m,
        coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ))) ≤
        totalMass (coefficientNoiseMeasure p) := by
      rw [← htot]
      exact Finset.single_le_sum
        (f := fun t => ∑ j ∈ Finset.range m,
          coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ)))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
    omega
  -- the mass as a fold-weight dot product
  have h1 : decodeFailureMass p = ∑ t ∈ Finset.range modulus,
      (∑ j ∈ Finset.range m, coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ))) *
        decodeFailureWeight (((lo + (t : ℤ)) : ℤ) : Coeff) := by
    rw [decodeFailureMass]
    refine Finset.sum_nbij' (i := fun r => (r - ((lo : ℤ) : Coeff)).val)
      (j := fun t => (((lo + (t : ℤ)) : ℤ) : Coeff)) ?_ ?_ ?_ ?_ ?_
    · intro r _
      exact Finset.mem_range.mpr (ZMod.val_lt _)
    · intro t _
      exact Finset.mem_univ _
    · intro r _
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    · intro t ht
      push_cast
      rw [add_sub_cancel_left]
      exact ZMod.val_cast_of_lt (by simpa using Finset.mem_range.mp ht)
    · intro r _
      have harg : (((lo + ((r - ((lo : ℤ) : Coeff)).val : ℤ)) : ℤ) : Coeff) = r := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        ring
      conv_lhs => rw [← harg]
      rw [foldedNoiseMeasure_apply_block p hwin (ZMod.val_lt _)]
  -- extract the dot product from the packings
  have hdot := ToVCVio.Packing.dot_eq_pack_extract_bound (B := 2) hq
    (fun t => ∑ j ∈ Finset.range m,
      coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ)))
    (fun t => decodeFailureWeight (((lo + (t : ℤ)) : ℤ) : Coeff))
    (fun t _ => decodeFailureWeight_le_two _) (by rw [htot]; exact hden)
  rw [h1, hdot]
  -- identify the fold packing with the repunit reduction of the measure packing
  have hpackA : (∑ t ∈ Finset.range modulus,
      (∑ j ∈ Finset.range m, coefficientNoiseMeasure p (lo + ((modulus * j + t : ℕ) : ℤ))) *
        R ^ t) = measurePack R lo (coefficientNoiseMeasure p) % (R ^ modulus - 1) := by
    rw [measurePack_eq_range_sum hwin,
      sum_mul_pow_mod_repunit (f := fun i => coefficientNoiseMeasure p (lo + (i : ℤ)))
        hR hq hfold_lt]
  rw [hpackA]
  -- align the reversed weight indices
  have hw : (∑ t ∈ Finset.range modulus,
      decodeFailureWeight (((lo + ((modulus - 1 - t : ℕ) : ℤ)) : ℤ) : Coeff) * R ^ t) =
      ∑ t ∈ Finset.range modulus,
        decodeFailureWeight
          ((lo + ((modulus - 1 : ℕ) : ℤ) - (t : ℤ) : ℤ) : Coeff) * R ^ t := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have hlt := Finset.mem_range.mp ht
    have hmod1 : (1 : ℕ) ≤ modulus := by norm_num [modulus]
    have harg : lo + ((modulus - 1 - t : ℕ) : ℤ) =
        lo + ((modulus - 1 : ℕ) : ℤ) - (t : ℤ) := by
      push_cast [Nat.cast_sub (by omega : t ≤ modulus - 1)]
      ring
    rw [harg]
  rw [hw]

/-- The reversed decode-failure-weight packing of `decodeFailureMass_eq`, split
into `53` blocks of `64` digits, padding the `3329` weights with zeros up to
`64 * 53`. Generic in the radix, so no closed power of `2` appears before the
final kernel check. -/
theorem weightPack_blocked (R : ℕ) (lo : ℤ) :
    (∑ t ∈ Finset.range modulus,
        decodeFailureWeight
          ((lo + ((modulus - 1 : ℕ) : ℤ) - (t : ℤ) : ℤ) : Coeff) * R ^ t) =
      ∑ j ∈ Finset.range 53,
        (∑ i ∈ Finset.range 64,
          (if 64 * j + i < modulus then
            decodeFailureWeight
              ((lo + ((modulus - 1 : ℕ) : ℤ) - ((64 * j + i : ℕ) : ℤ) : ℤ) : Coeff)
          else 0) * R ^ i) * (R ^ 64) ^ j := by
  rw [sum_mul_pow_pad (show modulus ≤ 64 * 53 by norm_num [modulus])
      (fun t => decodeFailureWeight ((lo + ((modulus - 1 : ℕ) : ℤ) - (t : ℤ) : ℤ) : Coeff)),
    sum_mul_pow_blocks 64 53
      (fun t => if t < modulus then
        decodeFailureWeight ((lo + ((modulus - 1 : ℕ) : ℤ) - (t : ℤ) : ℤ) : Coeff) else 0)]

end MLKEM
