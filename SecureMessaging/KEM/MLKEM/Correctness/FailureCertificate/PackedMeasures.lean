/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Tables

/-!
# Packed form of the coefficient-noise counting measure

Let `C_η` denote the centered-binomial counting measure `cbdMeasure η`, `E_d` denote
`compressionErrorMeasure d`, `*` denote additive convolution, and `F⊠G`
denote `productMeasure F G`, the push-forward of the product counting measure
under integer multiplication.  For parameters `(k,η₁,η₂,d_u,d_v)` and
`n=256`, the measure packed in this file is exactly

```
M = (C_{η₁} ⊠ C_{η₁}) ^{*(kn)}
    * (C_{η₁} ⊠ (C_{η₂} * E_{d_u})) ^{*(kn)}
    * (C_{η₂} * E_{d_v}).                                (1)
```

The three factors respectively model the coefficient contributions from
`eᵀy`, `-sᵀ(e₁+ε_u)`, and `e₂+ε_v`.  In the simplified model, signs on the
product terms do not change their counting measure because one factor is a
symmetric centered-binomial variable.  Equation (1) is the definition
`coefficientNoiseMeasure`; its comparison with the honest sampler is stated in
`NoiseModel.lean`.

For a measure `F` supported above `lo`, `measurePack R lo F` evaluates its
mass-generating polynomial at `R`.  Each theorem
`measurePack_coefficientNoiseMeasure_*` expands the packed value of (1) into
the product of three finite sums:

* a sum over two `CBD_{η₁}` values, raised to `kn`;
* a sum over a `CBD_{η₁}` value and the convolution `C_{η₂}*E_{d_u}`, raised
  to `kn`;
* the product of the finite sums for `C_{η₂}` and `E_{d_v}`.

These closed forms let the later `decide +kernel` certificate evaluate one
finite natural-number expression instead of repeatedly unfolding
convolutions.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

theorem measurePack_coefficientNoiseMeasure_mlkem512 :
    measurePack (2 ^ 17280) (-10858) (coefficientNoiseMeasure .MLKEM512) =
      (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 7,
          ((Finset.range (4 ^ 3)).filter fun y => cbdValue 3 y = -3 + (i : ℤ)).card *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-3 + (i : ℤ)) + 9).toNat) ^ 512 *
        (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-4 + (i : ℤ)) + 12).toNat) ^ 512 *
        ((∑ x ∈ Finset.range (4 ^ 2), (2 ^ 17280 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
          ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 17280 : ℕ) ^ i) := by
  have hkey : MeasureWindow (keyNoiseProductMeasure .MLKEM512) (-9) 9 := by
    have := measureWindow_productMeasure measureWindow_cbdMeasure_three
      measureWindow_cbdMeasure_three
    norm_num at this; exact this
  have hctxt : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM512) (-12) 12 := by
    have hin : MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 10) (-4) 4 := by
      have := measureWindow_mul measureWindow_cbdMeasure_two
        measureWindow_compressionErrorMeasure_ten
      norm_num at this; exact this
    have := measureWindow_productMeasure measureWindow_cbdMeasure_three hin
    norm_num at this; exact this
  have hadd : MeasureWindow (additiveNoiseMeasure .MLKEM512) (-106) 106 := by
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_four
    norm_num at this; exact this
  have hkeypow : MeasureWindow (keyNoiseProductMeasure .MLKEM512 ^ 512) (-4608) 4608 := by
    have := measureWindow_pow hkey 512; norm_num at this; exact this
  have hctxtpow : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM512 ^ 512) (-6144) 6144 := by
    have := measureWindow_pow hctxt 512; norm_num at this; exact this
  have hcbd3' :
      MeasureWindow (enumMeasure (4 ^ 3) (cbdValue 3)) (-3)
        (-3 + ((7 : ℕ) : ℤ) - 1) := by
    have h : (-3 + ((7 : ℕ) : ℤ) - 1) = (3 : ℤ) := by norm_num
    rw [h]; exact measureWindow_cbdMeasure_three
  have hHten :
      MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 10) (-4)
        (-4 + ((9 : ℕ) : ℤ) - 1) := by
    have h : (-4 + ((9 : ℕ) : ℤ) - 1) = (4 : ℤ) := by norm_num
    rw [h]
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_ten
    norm_num at this; exact this
  have hKeyBase : measurePack (2 ^ 17280) (-9) (keyNoiseProductMeasure .MLKEM512) =
      ∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 7,
        ((Finset.range (4 ^ 3)).filter fun y => cbdValue 3 y = -3 + (i : ℤ)).card *
          (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-3 + (i : ℤ)) + 9).toNat := by
    rw [keyNoiseProductMeasure]
    simp only [ParameterSet.params]
    rw [cbdMeasure, measurePack_productMeasure_enumMeasure hcbd3' (-9) (4 ^ 3) (cbdValue 3)]
    simp only [enumMeasure_apply, sub_neg_eq_add]
  have hCtxtBase : measurePack (2 ^ 17280) (-12) (ciphertextNoiseProductMeasure .MLKEM512) =
      ∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 9,
        convTableTen i * (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-4 + (i : ℤ)) + 12).toNat := by
    rw [ciphertextNoiseProductMeasure]
    simp only [ParameterSet.params]
    nth_rewrite 1 [cbdMeasure]
    rw [measurePack_productMeasure_enumMeasure hHten (-12) (4 ^ 3) (cbdValue 3)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => ?_
    rw [convTableTen_spec i (Finset.mem_range.mp hi), sub_neg_eq_add]
  have hAdd : measurePack (2 ^ 17280) (-106) (additiveNoiseMeasure .MLKEM512) =
      (∑ x ∈ Finset.range (4 ^ 2), (2 ^ 17280 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
        ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 17280 : ℕ) ^ i := by
    rw [additiveNoiseMeasure]
    simp only [ParameterSet.params]
    have h106 : (-106 : ℤ) = -2 + -104 := by norm_num
    rw [h106,
      measurePack_mul measureWindow_cbdMeasure_two measureWindow_compressionErrorMeasure_four,
      cbdMeasure,
      measurePack_enumMeasure, measurePack_compressionErrorMeasure_four]
    simp only [sub_neg_eq_add]
  have hunfold : coefficientNoiseMeasure .MLKEM512 =
      keyNoiseProductMeasure .MLKEM512 ^ 512 *
        ciphertextNoiseProductMeasure .MLKEM512 ^ 512 *
        additiveNoiseMeasure .MLKEM512 := by
    simp only [coefficientNoiseMeasure, ParameterSet.params, ringDegree]
  have hKey : measurePack (2 ^ 17280) (-4608) (keyNoiseProductMeasure .MLKEM512 ^ 512) =
      (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 7,
          ((Finset.range (4 ^ 3)).filter fun y => cbdValue 3 y = -3 + (i : ℤ)).card *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-3 + (i : ℤ)) + 9).toNat) ^ 512 := by
    have hp := measurePack_pow (R := 2 ^ 17280) hkey 512
    norm_num at hp
    rw [hp, hKeyBase]
  have hCtxt : measurePack (2 ^ 17280) (-6144) (ciphertextNoiseProductMeasure .MLKEM512 ^ 512) =
      (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-4 + (i : ℤ)) + 12).toNat) ^ 512 := by
    have hp := measurePack_pow (R := 2 ^ 17280) hctxt 512
    norm_num at hp
    rw [hp, hCtxtBase]
  have hsplit : (-10858 : ℤ) = (-4608 + -6144) + -106 := by norm_num
  rw [hunfold, hsplit, measurePack_mul (measureWindow_mul hkeypow hctxtpow) hadd,
    measurePack_mul hkeypow hctxtpow, hKey, hCtxt, hAdd]

theorem measurePack_coefficientNoiseMeasure_mlkem768 :
    measurePack (2 ^ 21312) (-9322) (coefficientNoiseMeasure .MLKEM768) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 768 *
        (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-4 + (i : ℤ)) + 8).toNat) ^ 768 *
        ((∑ x ∈ Finset.range (4 ^ 2), (2 ^ 21312 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
          ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 21312 : ℕ) ^ i) := by
  have hkey : MeasureWindow (keyNoiseProductMeasure .MLKEM768) (-4) 4 := by
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two
      measureWindow_cbdMeasure_two
    norm_num at this; exact this
  have hctxt : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM768) (-8) 8 := by
    have hin : MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 10) (-4) 4 := by
      have := measureWindow_mul measureWindow_cbdMeasure_two
        measureWindow_compressionErrorMeasure_ten
      norm_num at this; exact this
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two hin
    norm_num at this; exact this
  have hadd : MeasureWindow (additiveNoiseMeasure .MLKEM768) (-106) 106 := by
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_four
    norm_num at this; exact this
  have hkeypow : MeasureWindow (keyNoiseProductMeasure .MLKEM768 ^ 768) (-3072) 3072 := by
    have := measureWindow_pow hkey 768; norm_num at this; exact this
  have hctxtpow : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM768 ^ 768) (-6144) 6144 := by
    have := measureWindow_pow hctxt 768; norm_num at this; exact this
  have hcbd2' :
      MeasureWindow (enumMeasure (4 ^ 2) (cbdValue 2)) (-2)
        (-2 + ((5 : ℕ) : ℤ) - 1) := by
    have h : (-2 + ((5 : ℕ) : ℤ) - 1) = (2 : ℤ) := by norm_num
    rw [h]; exact measureWindow_cbdMeasure_two
  have hHten :
      MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 10) (-4)
        (-4 + ((9 : ℕ) : ℤ) - 1) := by
    have h : (-4 + ((9 : ℕ) : ℤ) - 1) = (4 : ℤ) := by norm_num
    rw [h]
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_ten
    norm_num at this; exact this
  have hKeyBase : measurePack (2 ^ 21312) (-4) (keyNoiseProductMeasure .MLKEM768) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
        ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
          (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat := by
    rw [keyNoiseProductMeasure]
    simp only [ParameterSet.params]
    rw [cbdMeasure, measurePack_productMeasure_enumMeasure hcbd2' (-4) (4 ^ 2) (cbdValue 2)]
    simp only [enumMeasure_apply, sub_neg_eq_add]
  have hCtxtBase : measurePack (2 ^ 21312) (-8) (ciphertextNoiseProductMeasure .MLKEM768) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 9,
        convTableTen i * (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-4 + (i : ℤ)) + 8).toNat := by
    rw [ciphertextNoiseProductMeasure]
    simp only [ParameterSet.params]
    nth_rewrite 1 [cbdMeasure]
    rw [measurePack_productMeasure_enumMeasure hHten (-8) (4 ^ 2) (cbdValue 2)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => ?_
    rw [convTableTen_spec i (Finset.mem_range.mp hi), sub_neg_eq_add]
  have hAdd : measurePack (2 ^ 21312) (-106) (additiveNoiseMeasure .MLKEM768) =
      (∑ x ∈ Finset.range (4 ^ 2), (2 ^ 21312 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
        ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 21312 : ℕ) ^ i := by
    rw [additiveNoiseMeasure]
    simp only [ParameterSet.params]
    have h106 : (-106 : ℤ) = -2 + -104 := by norm_num
    rw [h106,
      measurePack_mul measureWindow_cbdMeasure_two measureWindow_compressionErrorMeasure_four,
      cbdMeasure,
      measurePack_enumMeasure, measurePack_compressionErrorMeasure_four]
    simp only [sub_neg_eq_add]
  have hunfold : coefficientNoiseMeasure .MLKEM768 =
      keyNoiseProductMeasure .MLKEM768 ^ 768 *
        ciphertextNoiseProductMeasure .MLKEM768 ^ 768 *
        additiveNoiseMeasure .MLKEM768 := by
    simp only [coefficientNoiseMeasure, ParameterSet.params, ringDegree]
  have hKey : measurePack (2 ^ 21312) (-3072) (keyNoiseProductMeasure .MLKEM768 ^ 768) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 768 := by
    have hp := measurePack_pow (R := 2 ^ 21312) hkey 768
    norm_num at hp
    rw [hp, hKeyBase]
  have hCtxt : measurePack (2 ^ 21312) (-6144) (ciphertextNoiseProductMeasure .MLKEM768 ^ 768) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-4 + (i : ℤ)) + 8).toNat) ^ 768 := by
    have hp := measurePack_pow (R := 2 ^ 21312) hctxt 768
    norm_num at hp
    rw [hp, hCtxtBase]
  have hsplit : (-9322 : ℤ) = (-3072 + -6144) + -106 := by norm_num
  rw [hunfold, hsplit, measurePack_mul (measureWindow_mul hkeypow hctxtpow) hadd,
    measurePack_mul hkeypow hctxtpow, hKey, hCtxt, hAdd]

theorem measurePack_coefficientNoiseMeasure_mlkem1024 :
    measurePack (2 ^ 28416) (-10294) (coefficientNoiseMeasure .MLKEM1024) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 1024 *
        (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 7,
          convTableEleven i *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-3 + (i : ℤ)) + 6).toNat) ^ 1024 *
        ((∑ x ∈ Finset.range (4 ^ 2), (2 ^ 28416 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
          ∑ i ∈ Finset.range 105, ceTableFive i * (2 ^ 28416 : ℕ) ^ i) := by
  have hkey : MeasureWindow (keyNoiseProductMeasure .MLKEM1024) (-4) 4 := by
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two
      measureWindow_cbdMeasure_two
    norm_num at this; exact this
  have hctxt : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM1024) (-6) 6 := by
    have hin : MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 11) (-3) 3 := by
      have := measureWindow_mul measureWindow_cbdMeasure_two
        measureWindow_compressionErrorMeasure_eleven
      norm_num at this; exact this
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two hin
    norm_num at this; exact this
  have hadd : MeasureWindow (additiveNoiseMeasure .MLKEM1024) (-54) 54 := by
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_five
    norm_num at this; exact this
  have hkeypow : MeasureWindow (keyNoiseProductMeasure .MLKEM1024 ^ 1024) (-4096) 4096 := by
    have := measureWindow_pow hkey 1024; norm_num at this; exact this
  have hctxtpow : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM1024 ^ 1024) (-6144) 6144 := by
    have := measureWindow_pow hctxt 1024; norm_num at this; exact this
  have hcbd2' :
      MeasureWindow (enumMeasure (4 ^ 2) (cbdValue 2)) (-2)
        (-2 + ((5 : ℕ) : ℤ) - 1) := by
    have h : (-2 + ((5 : ℕ) : ℤ) - 1) = (2 : ℤ) := by norm_num
    rw [h]; exact measureWindow_cbdMeasure_two
  have hHeleven :
      MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 11) (-3)
        (-3 + ((7 : ℕ) : ℤ) - 1) := by
    have h : (-3 + ((7 : ℕ) : ℤ) - 1) = (3 : ℤ) := by norm_num
    rw [h]
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_eleven
    norm_num at this; exact this
  have hKeyBase : measurePack (2 ^ 28416) (-4) (keyNoiseProductMeasure .MLKEM1024) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
        ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
          (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat := by
    rw [keyNoiseProductMeasure]
    simp only [ParameterSet.params]
    rw [cbdMeasure, measurePack_productMeasure_enumMeasure hcbd2' (-4) (4 ^ 2) (cbdValue 2)]
    simp only [enumMeasure_apply, sub_neg_eq_add]
  have hCtxtBase : measurePack (2 ^ 28416) (-6) (ciphertextNoiseProductMeasure .MLKEM1024) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 7,
        convTableEleven i * (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-3 + (i : ℤ)) + 6).toNat := by
    rw [ciphertextNoiseProductMeasure]
    simp only [ParameterSet.params]
    nth_rewrite 1 [cbdMeasure]
    rw [measurePack_productMeasure_enumMeasure hHeleven (-6) (4 ^ 2) (cbdValue 2)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => ?_
    rw [convTableEleven_spec i (Finset.mem_range.mp hi), sub_neg_eq_add]
  have hAdd : measurePack (2 ^ 28416) (-54) (additiveNoiseMeasure .MLKEM1024) =
      (∑ x ∈ Finset.range (4 ^ 2), (2 ^ 28416 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
        ∑ i ∈ Finset.range 105, ceTableFive i * (2 ^ 28416 : ℕ) ^ i := by
    rw [additiveNoiseMeasure]
    simp only [ParameterSet.params]
    have h54 : (-54 : ℤ) = -2 + -52 := by norm_num
    rw [h54,
      measurePack_mul measureWindow_cbdMeasure_two measureWindow_compressionErrorMeasure_five,
      cbdMeasure,
      measurePack_enumMeasure, measurePack_compressionErrorMeasure_five]
    simp only [sub_neg_eq_add]
  have hunfold : coefficientNoiseMeasure .MLKEM1024 =
      keyNoiseProductMeasure .MLKEM1024 ^ 1024 * ciphertextNoiseProductMeasure .MLKEM1024 ^ 1024 *
        additiveNoiseMeasure .MLKEM1024 := by
    simp only [coefficientNoiseMeasure, ParameterSet.params, ringDegree]
  have hKey : measurePack (2 ^ 28416) (-4096) (keyNoiseProductMeasure .MLKEM1024 ^ 1024) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 1024 := by
    have hp := measurePack_pow (R := 2 ^ 28416) hkey 1024
    norm_num at hp
    rw [hp, hKeyBase]
  have hCtxt : measurePack (2 ^ 28416) (-6144) (ciphertextNoiseProductMeasure .MLKEM1024 ^ 1024) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 7,
          convTableEleven i *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-3 + (i : ℤ)) + 6).toNat) ^ 1024 := by
    have hp := measurePack_pow (R := 2 ^ 28416) hctxt 1024
    norm_num at hp
    rw [hp, hCtxtBase]
  have hsplit : (-10294 : ℤ) = (-4096 + -6144) + -54 := by norm_num
  rw [hunfold, hsplit, measurePack_mul (measureWindow_mul hkeypow hctxtpow) hadd,
    measurePack_mul hkeypow hctxtpow, hKey, hCtxt, hAdd]

/-- Five times the FIPS 203 Table 1 decapsulation-failure exponent, an integer. -/
def scaledFailureExponent : ParameterSet → ℕ
  | .MLKEM512 => 694
  | .MLKEM768 => 824
  | .MLKEM1024 => 874

end MLKEM
