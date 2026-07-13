/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.Probability.IntMeasure
import LatticeCrypto.MLKEM.Concrete.Encoding
import SecureMessaging.KEM.MLKEM.Correctness.Noise

/-!
# Exact coefficient-noise finite measures for the ML-KEM failure-bound proof

This file composes the per-coefficient decryption-noise counting measure
evaluated by the failure bound. The composition follows the decryption-noise
identity
`w − μ = eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u`
(`kpkeDecryptDifference_eq_noise`): `k·n` coefficient products for each
transposed-vector product, and one additive term for the `v` component.

The generic support — `IntMeasure`, windows, total mass, convolution, and
`productMeasure` — lives in `ToVCVio.Probability.IntMeasure`. This file
contains only the ML-KEM specialization. The main objects are:

* `cbdMeasure η`: counts the `4^η` bit samples of `CBD_η` by centered binomial
  value;
* `compressionErrorMeasure d`: counts the `q` residues by their `Compress_d`
  round-trip error;
* `coefficientNoiseMeasure`: the composed one-coordinate noise counting measure;
* `foldedNoiseMeasure`: reduction of that integer measure into `ZMod q`;
* `decodeFailureMass`: the folded mass weighted by the exact per-bit
  `Compress₁` decode-failure count.

Every measure here is a definition. No statement in this file relates these
finite measures to the honest sampler.
-/

open LatticeCrypto

namespace MLKEM

/-! ## Component measures -/

/-- The centered binomial value of a `2η`-bit sample `x`: the number of set bits
among the low `η` bits minus the number among the next `η` bits (FIPS 203,
Algorithm 8). -/
def cbdValue (η x : ℕ) : ℤ :=
  ((∑ j ∈ Finset.range η, (x >>> j) % 2 : ℕ) : ℤ) -
    ((∑ j ∈ Finset.range η, (x >>> (η + j)) % 2 : ℕ) : ℤ)

/-- The centered binomial counting measure `CBD_η`: it counts the `4^η` bit
samples by their centered binomial value. -/
noncomputable def cbdMeasure (η : ℕ) : IntMeasure := enumMeasure (4 ^ η) (cbdValue η)

theorem measureWindow_cbdMeasure_two : MeasureWindow (cbdMeasure 2) (-2) 2 :=
  measureWindow_enumMeasure (by decide)

theorem measureWindow_cbdMeasure_three : MeasureWindow (cbdMeasure 3) (-3) 3 :=
  measureWindow_enumMeasure (by decide)

/-- The `Compress_d` round-trip error of the residue `x`: the centered
representative of `Decompress_d (Compress_d x) - x`. -/
def compressionError (d x : ℕ) : ℤ :=
  centeredRepr (Concrete.decompress d (Concrete.compress d (x : Coeff)) - (x : Coeff))

/-- The compression-error counting measure: the `Compress_d` round-trip error
under counting over the `q` residues. -/
noncomputable def compressionErrorMeasure (d : ℕ) : IntMeasure :=
  enumMeasure modulus (compressionError d)

theorem measureWindow_compressionErrorMeasure_four :
    MeasureWindow (compressionErrorMeasure 4) (-104) 104 :=
  measureWindow_enumMeasure (by decide +kernel)

theorem measureWindow_compressionErrorMeasure_five :
    MeasureWindow (compressionErrorMeasure 5) (-52) 52 :=
  measureWindow_enumMeasure (by decide +kernel)

theorem measureWindow_compressionErrorMeasure_ten :
    MeasureWindow (compressionErrorMeasure 10) (-2) 2 :=
  measureWindow_enumMeasure (by decide +kernel)

theorem measureWindow_compressionErrorMeasure_eleven :
    MeasureWindow (compressionErrorMeasure 11) (-1) 1 :=
  measureWindow_enumMeasure (by decide +kernel)

/-! ## The failure-bound coefficient-noise measure -/

/-- The finite measure of one coefficient product in `eᵀy`, as composed here: a
product of two independent `CBD_{η₁}` draws. -/
noncomputable def keyNoiseProductMeasure (p : ParameterSet) : IntMeasure :=
  productMeasure (cbdMeasure p.params.eta1) (cbdMeasure p.params.eta1)

/-- The finite measure of one coefficient product in `sᵀ(e₁ + ε_u)`, as
composed here: a product of an independent `CBD_{η₁}` draw with an independent sum of a
`CBD_{η₂}` draw and a `Compress_{d_u}` round-trip error. -/
noncomputable def ciphertextNoiseProductMeasure (p : ParameterSet) : IntMeasure :=
  productMeasure (cbdMeasure p.params.eta1)
    (cbdMeasure p.params.eta2 * compressionErrorMeasure p.params.du)

/-- The finite measure of the additive noise `e₂ + ε_v`, as composed here: an
independent sum of a `CBD_{η₂}` draw and a `Compress_{d_v}` round-trip error. -/
noncomputable def additiveNoiseMeasure (p : ParameterSet) : IntMeasure :=
  cbdMeasure p.params.eta2 * compressionErrorMeasure p.params.dv

/-- The finite counting measure for one coefficient of the decryption noise.
It mirrors

`w − μ = eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u`.

The factor `keyNoiseProductMeasure p ^ (p.params.k * ringDegree)` accounts for the
`eᵀy` products; `ciphertextNoiseProductMeasure p ^ (p.params.k * ringDegree)`
accounts for the `sᵀ(e₁ + ε_u)` products; and `additiveNoiseMeasure p` accounts for
`e₂ + ε_v`. This file does not assert that the honest per-coordinate sampler has
this measure. -/
noncomputable def coefficientNoiseMeasure (p : ParameterSet) : IntMeasure :=
  keyNoiseProductMeasure p ^ (p.params.k * ringDegree) *
    ciphertextNoiseProductMeasure p ^ (p.params.k * ringDegree) *
    additiveNoiseMeasure p

/-- The coefficient-noise measure folded into `ZMod q`, matching reduction of
the integer noise into the coefficient ring. -/
noncomputable def foldedNoiseMeasure (p : ParameterSet) : ZMod modulus →₀ ℕ :=
  Finsupp.mapDomain (fun v : ℤ => (v : ZMod modulus)) (coefficientNoiseMeasure p)

/-- The number of message bits (0, 1, or 2 of them) whose encoded coefficient is
decoded wrongly by `Compress₁` after adding the noise residue `r`. -/
def decodeFailureWeight (r : Coeff) : ℕ :=
  (if Concrete.compress 1 (Concrete.decompress 1 0 + r) ≠ 0 then 1 else 0) +
    (if Concrete.compress 1 (Concrete.decompress 1 1 + r) ≠ 1 then 1 else 0)

theorem decodeFailureWeight_le_two (r : Coeff) : decodeFailureWeight r ≤ 2 := by
  rw [decodeFailureWeight]
  split <;> split <;> omega

/-- The bit-summed decode-failure mass of the folded coefficient-noise measure.
Over a uniform message bit, the decode-failure probability for the finite
measure defined here is this mass divided by twice the total mass. -/
noncomputable def decodeFailureMass (p : ParameterSet) : ℕ :=
  ∑ r : Coeff, foldedNoiseMeasure p r * decodeFailureWeight r

/-- The total mass of the coefficient-noise measure used by the failure-bound proof. -/
noncomputable def noiseDenominator (p : ParameterSet) : ℕ :=
  totalMass (coefficientNoiseMeasure p)

/-! ## Per-parameter-set windows and totals -/

theorem noiseDenominator_mlkem512 :
    noiseDenominator .MLKEM512 = 2 ^ 11268 * 3329 ^ 513 := by
  simp only [noiseDenominator, coefficientNoiseMeasure, keyNoiseProductMeasure,
    ciphertextNoiseProductMeasure, additiveNoiseMeasure, ParameterSet.params, cbdMeasure,
    compressionErrorMeasure, totalMass_mul, totalMass_pow, totalMass_productMeasure,
    totalMass_enumMeasure, ringDegree, modulus]
  decide +kernel

theorem noiseDenominator_mlkem768 :
    noiseDenominator .MLKEM768 = 2 ^ 12292 * 3329 ^ 769 := by
  simp only [noiseDenominator, coefficientNoiseMeasure, keyNoiseProductMeasure,
    ciphertextNoiseProductMeasure, additiveNoiseMeasure, ParameterSet.params, cbdMeasure,
    compressionErrorMeasure, totalMass_mul, totalMass_pow, totalMass_productMeasure,
    totalMass_enumMeasure, ringDegree, modulus]
  decide +kernel

theorem noiseDenominator_mlkem1024 :
    noiseDenominator .MLKEM1024 = 2 ^ 16388 * 3329 ^ 1025 := by
  simp only [noiseDenominator, coefficientNoiseMeasure, keyNoiseProductMeasure,
    ciphertextNoiseProductMeasure, additiveNoiseMeasure, ParameterSet.params, cbdMeasure,
    compressionErrorMeasure, totalMass_mul, totalMass_pow, totalMass_productMeasure,
    totalMass_enumMeasure, ringDegree, modulus]
  decide +kernel

theorem measureWindow_coefficientNoiseMeasure_mlkem512 :
    MeasureWindow (coefficientNoiseMeasure .MLKEM512) (-10858) 10858 := by
  have h1 : MeasureWindow (keyNoiseProductMeasure .MLKEM512) (-9) 9 := by
    have := measureWindow_productMeasure measureWindow_cbdMeasure_three
      measureWindow_cbdMeasure_three
    norm_num at this
    exact this
  have h2 : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM512) (-12) 12 := by
    have hin := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_ten
    norm_num at hin
    have hin' : MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 10) (-4) 4 := hin
    have := measureWindow_productMeasure measureWindow_cbdMeasure_three hin'
    norm_num at this
    exact this
  have h3 : MeasureWindow (additiveNoiseMeasure .MLKEM512) (-106) 106 := by
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_four
    norm_num at this
    exact this
  have hc1 := measureWindow_pow h1 (2 * 256)
  have hc2 := measureWindow_pow h2 (2 * 256)
  norm_num at hc1 hc2
  have := measureWindow_mul (measureWindow_mul hc1 hc2) h3
  norm_num at this
  exact this

theorem measureWindow_coefficientNoiseMeasure_mlkem768 :
    MeasureWindow (coefficientNoiseMeasure .MLKEM768) (-9322) 9322 := by
  have h1 : MeasureWindow (keyNoiseProductMeasure .MLKEM768) (-4) 4 := by
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two
      measureWindow_cbdMeasure_two
    norm_num at this
    exact this
  have h2 : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM768) (-8) 8 := by
    have hin := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_ten
    norm_num at hin
    have hin' : MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 10) (-4) 4 := hin
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two hin'
    norm_num at this
    exact this
  have h3 : MeasureWindow (additiveNoiseMeasure .MLKEM768) (-106) 106 := by
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_four
    norm_num at this
    exact this
  have hc1 := measureWindow_pow h1 (3 * 256)
  have hc2 := measureWindow_pow h2 (3 * 256)
  norm_num at hc1 hc2
  have := measureWindow_mul (measureWindow_mul hc1 hc2) h3
  norm_num at this
  exact this

theorem measureWindow_coefficientNoiseMeasure_mlkem1024 :
    MeasureWindow (coefficientNoiseMeasure .MLKEM1024) (-10294) 10294 := by
  have h1 : MeasureWindow (keyNoiseProductMeasure .MLKEM1024) (-4) 4 := by
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two
      measureWindow_cbdMeasure_two
    norm_num at this
    exact this
  have h2 : MeasureWindow (ciphertextNoiseProductMeasure .MLKEM1024) (-6) 6 := by
    have hin := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_eleven
    norm_num at hin
    have hin' : MeasureWindow (cbdMeasure 2 * compressionErrorMeasure 11) (-3) 3 := hin
    have := measureWindow_productMeasure measureWindow_cbdMeasure_two hin'
    norm_num at this
    exact this
  have h3 : MeasureWindow (additiveNoiseMeasure .MLKEM1024) (-54) 54 := by
    have := measureWindow_mul measureWindow_cbdMeasure_two
      measureWindow_compressionErrorMeasure_five
    norm_num at this
    exact this
  have hc1 := measureWindow_pow h1 (4 * 256)
  have hc2 := measureWindow_pow h2 (4 * 256)
  norm_num at hc1 hc2
  have := measureWindow_mul (measureWindow_mul hc1 hc2) h3
  norm_num at this
  exact this

end MLKEM
