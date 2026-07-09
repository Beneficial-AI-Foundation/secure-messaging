/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Tables

/-!
# The packed coefficient-noise laws

The closed base-`R` packed forms of the three coefficient-noise laws.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

theorem lawPack_coefficientNoiseLaw_mlkem512 :
    lawPack (2 ^ 17280) (-10858) (coefficientNoiseLaw .MLKEM512) =
      (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 7,
          ((Finset.range (4 ^ 3)).filter fun y => cbdValue 3 y = -3 + (i : ℤ)).card *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-3 + (i : ℤ)) + 9).toNat) ^ 512 *
        (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-4 + (i : ℤ)) + 12).toNat) ^ 512 *
        ((∑ x ∈ Finset.range (4 ^ 2), (2 ^ 17280 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
          ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 17280 : ℕ) ^ i) := by
  have hkey : LawWindow (keyNoiseProductLaw .MLKEM512) (-9) 9 := by
    have := lawWindow_prodLaw lawWindow_cbdLaw_three lawWindow_cbdLaw_three
    norm_num at this; exact this
  have hctxt : LawWindow (ciphertextNoiseProductLaw .MLKEM512) (-12) 12 := by
    have hin : LawWindow (cbdLaw 2 * compressionErrorLaw 10) (-4) 4 := by
      have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_ten
      norm_num at this; exact this
    have := lawWindow_prodLaw lawWindow_cbdLaw_three hin
    norm_num at this; exact this
  have hadd : LawWindow (additiveNoiseLaw .MLKEM512) (-106) 106 := by
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_four
    norm_num at this; exact this
  have hkeypow : LawWindow (keyNoiseProductLaw .MLKEM512 ^ 512) (-4608) 4608 := by
    have := lawWindow_pow hkey 512; norm_num at this; exact this
  have hctxtpow : LawWindow (ciphertextNoiseProductLaw .MLKEM512 ^ 512) (-6144) 6144 := by
    have := lawWindow_pow hctxt 512; norm_num at this; exact this
  have hcbd3' : LawWindow (enumLaw (4 ^ 3) (cbdValue 3)) (-3) (-3 + ((7 : ℕ) : ℤ) - 1) := by
    have h : (-3 + ((7 : ℕ) : ℤ) - 1) = (3 : ℤ) := by norm_num
    rw [h]; exact lawWindow_cbdLaw_three
  have hHten : LawWindow (cbdLaw 2 * compressionErrorLaw 10) (-4) (-4 + ((9 : ℕ) : ℤ) - 1) := by
    have h : (-4 + ((9 : ℕ) : ℤ) - 1) = (4 : ℤ) := by norm_num
    rw [h]
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_ten
    norm_num at this; exact this
  have hKeyBase : lawPack (2 ^ 17280) (-9) (keyNoiseProductLaw .MLKEM512) =
      ∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 7,
        ((Finset.range (4 ^ 3)).filter fun y => cbdValue 3 y = -3 + (i : ℤ)).card *
          (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-3 + (i : ℤ)) + 9).toNat := by
    rw [keyNoiseProductLaw]
    simp only [ParameterSet.params]
    rw [cbdLaw, lawPack_prodLaw_enumLaw hcbd3' (-9) (4 ^ 3) (cbdValue 3)]
    simp only [enumLaw_apply, sub_neg_eq_add]
  have hCtxtBase : lawPack (2 ^ 17280) (-12) (ciphertextNoiseProductLaw .MLKEM512) =
      ∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 9,
        convTableTen i * (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-4 + (i : ℤ)) + 12).toNat := by
    rw [ciphertextNoiseProductLaw]
    simp only [ParameterSet.params]
    nth_rewrite 1 [cbdLaw]
    rw [lawPack_prodLaw_enumLaw hHten (-12) (4 ^ 3) (cbdValue 3)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => ?_
    rw [convTableTen_spec i (Finset.mem_range.mp hi), sub_neg_eq_add]
  have hAdd : lawPack (2 ^ 17280) (-106) (additiveNoiseLaw .MLKEM512) =
      (∑ x ∈ Finset.range (4 ^ 2), (2 ^ 17280 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
        ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 17280 : ℕ) ^ i := by
    rw [additiveNoiseLaw]
    simp only [ParameterSet.params]
    have h106 : (-106 : ℤ) = -2 + -104 := by norm_num
    rw [h106, lawPack_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_four, cbdLaw,
      lawPack_enumLaw, lawPack_compressionErrorLaw_four]
    simp only [sub_neg_eq_add]
  have hunfold : coefficientNoiseLaw .MLKEM512 =
      keyNoiseProductLaw .MLKEM512 ^ 512 * ciphertextNoiseProductLaw .MLKEM512 ^ 512 *
        additiveNoiseLaw .MLKEM512 := by
    simp only [coefficientNoiseLaw, ParameterSet.params, ringDegree]
  have hKey : lawPack (2 ^ 17280) (-4608) (keyNoiseProductLaw .MLKEM512 ^ 512) =
      (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 7,
          ((Finset.range (4 ^ 3)).filter fun y => cbdValue 3 y = -3 + (i : ℤ)).card *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-3 + (i : ℤ)) + 9).toNat) ^ 512 := by
    have hp := lawPack_pow (R := 2 ^ 17280) hkey 512
    norm_num at hp
    rw [hp, hKeyBase]
  have hCtxt : lawPack (2 ^ 17280) (-6144) (ciphertextNoiseProductLaw .MLKEM512 ^ 512) =
      (∑ x ∈ Finset.range (4 ^ 3), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 17280 : ℕ) ^ (cbdValue 3 x * (-4 + (i : ℤ)) + 12).toNat) ^ 512 := by
    have hp := lawPack_pow (R := 2 ^ 17280) hctxt 512
    norm_num at hp
    rw [hp, hCtxtBase]
  have hsplit : (-10858 : ℤ) = (-4608 + -6144) + -106 := by norm_num
  rw [hunfold, hsplit, lawPack_mul (lawWindow_mul hkeypow hctxtpow) hadd,
    lawPack_mul hkeypow hctxtpow, hKey, hCtxt, hAdd]

theorem lawPack_coefficientNoiseLaw_mlkem768 :
    lawPack (2 ^ 21312) (-9322) (coefficientNoiseLaw .MLKEM768) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 768 *
        (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-4 + (i : ℤ)) + 8).toNat) ^ 768 *
        ((∑ x ∈ Finset.range (4 ^ 2), (2 ^ 21312 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
          ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 21312 : ℕ) ^ i) := by
  have hkey : LawWindow (keyNoiseProductLaw .MLKEM768) (-4) 4 := by
    have := lawWindow_prodLaw lawWindow_cbdLaw_two lawWindow_cbdLaw_two
    norm_num at this; exact this
  have hctxt : LawWindow (ciphertextNoiseProductLaw .MLKEM768) (-8) 8 := by
    have hin : LawWindow (cbdLaw 2 * compressionErrorLaw 10) (-4) 4 := by
      have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_ten
      norm_num at this; exact this
    have := lawWindow_prodLaw lawWindow_cbdLaw_two hin
    norm_num at this; exact this
  have hadd : LawWindow (additiveNoiseLaw .MLKEM768) (-106) 106 := by
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_four
    norm_num at this; exact this
  have hkeypow : LawWindow (keyNoiseProductLaw .MLKEM768 ^ 768) (-3072) 3072 := by
    have := lawWindow_pow hkey 768; norm_num at this; exact this
  have hctxtpow : LawWindow (ciphertextNoiseProductLaw .MLKEM768 ^ 768) (-6144) 6144 := by
    have := lawWindow_pow hctxt 768; norm_num at this; exact this
  have hcbd2' : LawWindow (enumLaw (4 ^ 2) (cbdValue 2)) (-2) (-2 + ((5 : ℕ) : ℤ) - 1) := by
    have h : (-2 + ((5 : ℕ) : ℤ) - 1) = (2 : ℤ) := by norm_num
    rw [h]; exact lawWindow_cbdLaw_two
  have hHten : LawWindow (cbdLaw 2 * compressionErrorLaw 10) (-4) (-4 + ((9 : ℕ) : ℤ) - 1) := by
    have h : (-4 + ((9 : ℕ) : ℤ) - 1) = (4 : ℤ) := by norm_num
    rw [h]
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_ten
    norm_num at this; exact this
  have hKeyBase : lawPack (2 ^ 21312) (-4) (keyNoiseProductLaw .MLKEM768) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
        ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
          (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat := by
    rw [keyNoiseProductLaw]
    simp only [ParameterSet.params]
    rw [cbdLaw, lawPack_prodLaw_enumLaw hcbd2' (-4) (4 ^ 2) (cbdValue 2)]
    simp only [enumLaw_apply, sub_neg_eq_add]
  have hCtxtBase : lawPack (2 ^ 21312) (-8) (ciphertextNoiseProductLaw .MLKEM768) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 9,
        convTableTen i * (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-4 + (i : ℤ)) + 8).toNat := by
    rw [ciphertextNoiseProductLaw]
    simp only [ParameterSet.params]
    nth_rewrite 1 [cbdLaw]
    rw [lawPack_prodLaw_enumLaw hHten (-8) (4 ^ 2) (cbdValue 2)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => ?_
    rw [convTableTen_spec i (Finset.mem_range.mp hi), sub_neg_eq_add]
  have hAdd : lawPack (2 ^ 21312) (-106) (additiveNoiseLaw .MLKEM768) =
      (∑ x ∈ Finset.range (4 ^ 2), (2 ^ 21312 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
        ∑ i ∈ Finset.range 209, ceTableFour i * (2 ^ 21312 : ℕ) ^ i := by
    rw [additiveNoiseLaw]
    simp only [ParameterSet.params]
    have h106 : (-106 : ℤ) = -2 + -104 := by norm_num
    rw [h106, lawPack_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_four, cbdLaw,
      lawPack_enumLaw, lawPack_compressionErrorLaw_four]
    simp only [sub_neg_eq_add]
  have hunfold : coefficientNoiseLaw .MLKEM768 =
      keyNoiseProductLaw .MLKEM768 ^ 768 * ciphertextNoiseProductLaw .MLKEM768 ^ 768 *
        additiveNoiseLaw .MLKEM768 := by
    simp only [coefficientNoiseLaw, ParameterSet.params, ringDegree]
  have hKey : lawPack (2 ^ 21312) (-3072) (keyNoiseProductLaw .MLKEM768 ^ 768) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 768 := by
    have hp := lawPack_pow (R := 2 ^ 21312) hkey 768
    norm_num at hp
    rw [hp, hKeyBase]
  have hCtxt : lawPack (2 ^ 21312) (-6144) (ciphertextNoiseProductLaw .MLKEM768 ^ 768) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 9,
          convTableTen i *
            (2 ^ 21312 : ℕ) ^ (cbdValue 2 x * (-4 + (i : ℤ)) + 8).toNat) ^ 768 := by
    have hp := lawPack_pow (R := 2 ^ 21312) hctxt 768
    norm_num at hp
    rw [hp, hCtxtBase]
  have hsplit : (-9322 : ℤ) = (-3072 + -6144) + -106 := by norm_num
  rw [hunfold, hsplit, lawPack_mul (lawWindow_mul hkeypow hctxtpow) hadd,
    lawPack_mul hkeypow hctxtpow, hKey, hCtxt, hAdd]

theorem lawPack_coefficientNoiseLaw_mlkem1024 :
    lawPack (2 ^ 28416) (-10294) (coefficientNoiseLaw .MLKEM1024) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 1024 *
        (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 7,
          convTableEleven i *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-3 + (i : ℤ)) + 6).toNat) ^ 1024 *
        ((∑ x ∈ Finset.range (4 ^ 2), (2 ^ 28416 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
          ∑ i ∈ Finset.range 105, ceTableFive i * (2 ^ 28416 : ℕ) ^ i) := by
  have hkey : LawWindow (keyNoiseProductLaw .MLKEM1024) (-4) 4 := by
    have := lawWindow_prodLaw lawWindow_cbdLaw_two lawWindow_cbdLaw_two
    norm_num at this; exact this
  have hctxt : LawWindow (ciphertextNoiseProductLaw .MLKEM1024) (-6) 6 := by
    have hin : LawWindow (cbdLaw 2 * compressionErrorLaw 11) (-3) 3 := by
      have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_eleven
      norm_num at this; exact this
    have := lawWindow_prodLaw lawWindow_cbdLaw_two hin
    norm_num at this; exact this
  have hadd : LawWindow (additiveNoiseLaw .MLKEM1024) (-54) 54 := by
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_five
    norm_num at this; exact this
  have hkeypow : LawWindow (keyNoiseProductLaw .MLKEM1024 ^ 1024) (-4096) 4096 := by
    have := lawWindow_pow hkey 1024; norm_num at this; exact this
  have hctxtpow : LawWindow (ciphertextNoiseProductLaw .MLKEM1024 ^ 1024) (-6144) 6144 := by
    have := lawWindow_pow hctxt 1024; norm_num at this; exact this
  have hcbd2' : LawWindow (enumLaw (4 ^ 2) (cbdValue 2)) (-2) (-2 + ((5 : ℕ) : ℤ) - 1) := by
    have h : (-2 + ((5 : ℕ) : ℤ) - 1) = (2 : ℤ) := by norm_num
    rw [h]; exact lawWindow_cbdLaw_two
  have hHeleven :
      LawWindow (cbdLaw 2 * compressionErrorLaw 11) (-3) (-3 + ((7 : ℕ) : ℤ) - 1) := by
    have h : (-3 + ((7 : ℕ) : ℤ) - 1) = (3 : ℤ) := by norm_num
    rw [h]
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_eleven
    norm_num at this; exact this
  have hKeyBase : lawPack (2 ^ 28416) (-4) (keyNoiseProductLaw .MLKEM1024) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
        ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
          (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat := by
    rw [keyNoiseProductLaw]
    simp only [ParameterSet.params]
    rw [cbdLaw, lawPack_prodLaw_enumLaw hcbd2' (-4) (4 ^ 2) (cbdValue 2)]
    simp only [enumLaw_apply, sub_neg_eq_add]
  have hCtxtBase : lawPack (2 ^ 28416) (-6) (ciphertextNoiseProductLaw .MLKEM1024) =
      ∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 7,
        convTableEleven i * (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-3 + (i : ℤ)) + 6).toNat := by
    rw [ciphertextNoiseProductLaw]
    simp only [ParameterSet.params]
    nth_rewrite 1 [cbdLaw]
    rw [lawPack_prodLaw_enumLaw hHeleven (-6) (4 ^ 2) (cbdValue 2)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => ?_
    rw [convTableEleven_spec i (Finset.mem_range.mp hi), sub_neg_eq_add]
  have hAdd : lawPack (2 ^ 28416) (-54) (additiveNoiseLaw .MLKEM1024) =
      (∑ x ∈ Finset.range (4 ^ 2), (2 ^ 28416 : ℕ) ^ (cbdValue 2 x + 2).toNat) *
        ∑ i ∈ Finset.range 105, ceTableFive i * (2 ^ 28416 : ℕ) ^ i := by
    rw [additiveNoiseLaw]
    simp only [ParameterSet.params]
    have h54 : (-54 : ℤ) = -2 + -52 := by norm_num
    rw [h54, lawPack_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_five, cbdLaw,
      lawPack_enumLaw, lawPack_compressionErrorLaw_five]
    simp only [sub_neg_eq_add]
  have hunfold : coefficientNoiseLaw .MLKEM1024 =
      keyNoiseProductLaw .MLKEM1024 ^ 1024 * ciphertextNoiseProductLaw .MLKEM1024 ^ 1024 *
        additiveNoiseLaw .MLKEM1024 := by
    simp only [coefficientNoiseLaw, ParameterSet.params, ringDegree]
  have hKey : lawPack (2 ^ 28416) (-4096) (keyNoiseProductLaw .MLKEM1024 ^ 1024) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 5,
          ((Finset.range (4 ^ 2)).filter fun y => cbdValue 2 y = -2 + (i : ℤ)).card *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-2 + (i : ℤ)) + 4).toNat) ^ 1024 := by
    have hp := lawPack_pow (R := 2 ^ 28416) hkey 1024
    norm_num at hp
    rw [hp, hKeyBase]
  have hCtxt : lawPack (2 ^ 28416) (-6144) (ciphertextNoiseProductLaw .MLKEM1024 ^ 1024) =
      (∑ x ∈ Finset.range (4 ^ 2), ∑ i ∈ Finset.range 7,
          convTableEleven i *
            (2 ^ 28416 : ℕ) ^ (cbdValue 2 x * (-3 + (i : ℤ)) + 6).toNat) ^ 1024 := by
    have hp := lawPack_pow (R := 2 ^ 28416) hctxt 1024
    norm_num at hp
    rw [hp, hCtxtBase]
  have hsplit : (-10294 : ℤ) = (-4096 + -6144) + -54 := by norm_num
  rw [hunfold, hsplit, lawPack_mul (lawWindow_mul hkeypow hctxtpow) hadd,
    lawPack_mul hkeypow hctxtpow, hKey, hCtxt, hAdd]

/-- Five times the FIPS 203 Table 1 decapsulation-failure exponent, an integer. -/
def scaledFailureExponent : ParameterSet → ℕ
  | .MLKEM512 => 694
  | .MLKEM768 => 824
  | .MLKEM1024 => 874

end MLKEM
