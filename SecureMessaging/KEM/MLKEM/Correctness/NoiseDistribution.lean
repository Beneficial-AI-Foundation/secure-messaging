/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.Probability.IntMeasure
import LatticeCrypto.MLKEM.Concrete.Encoding
import SecureMessaging.KEM.MLKEM.Correctness.Noise

/-!
# The independent one-coefficient noise model

This file defines the finite counting measure used by the ML-KEM numerical
certificate.  The algebraic source is the decryption-noise identity proved in
`NoiseIdentity.lean`:

`w-μ=eᵀy+e₂+ε_v-sᵀe₁-sᵀε_u`.                            (1)

## Why construct a distribution for one polynomial coefficient?

The honest correctness experiment has sample space

`Ω_hon=Seed32×Seed32×Message`.

An outcome `ω=(d,z,m)` determines the message bit `B_i(ω)` and decryption-noise
coefficient `N_i(ω)` at every index `i`.  K-PKE recovery fails exactly when

`∃ i, Compress₁(Decompress₁(B_i(ω))+N_i(ω))≠B_i(ω)`.

The union bound therefore reduces the failure problem to bounding the joint
distribution of one message bit `B_i` and one scalar coefficient `N_i`.  This
is why polynomial coefficients enter the probability calculation: ML-KEM
performs its arithmetic in a polynomial quotient ring, while message recovery
tests the resulting polynomial one coefficient at a time.

The auxiliary model in this file has a different, much larger product sample
space `Ξ_p`.  For each scalar coefficient, an outcome `ξ∈Ξ_p` chooses the
underlying `2η`-bit input to a centered-binomial variable or the underlying
uniform residue used to define a compression error.  Applying those scalar
random variables and assembling their outputs determines the random
polynomials `S,E,Y,E₁,E₂,C_u,C_v` introduced below.  They in turn determine a
random polynomial `N_p^ind` and hence an integer-valued random variable

`N_{p,i}^ind : Ξ_p → ℤ,    ξ ↦ coefficient i of N_p^ind(ξ)`.

The measure `M_p=coefficientNoiseMeasure p` is the pushforward of counting
measure on `Ξ_p` along `N_{p,i}^ind`:

`M_p(x)=#{ξ∈Ξ_p | N_{p,i}^ind(ξ)=x}`.

We are therefore not plugging measures into a polynomial.  We put the product
measure on the tuple of scalar coefficient choices and push that measure
forward through the function “form the random polynomials, evaluate the noise
expression, and take coefficient `i`.”

Thus an outcome is not encoded in a single polynomial coefficient.  An outcome
chooses all the scalar inputs; polynomial arithmetic combines them; and one
coefficient of the result is the scalar random variable whose distribution we
need.  Computing `M_p` by direct enumeration of `Ξ_p` would be infeasible.  The
convolutions below compute the same pushforward measure compositionally from
the distributions of the scalar inputs.

This auxiliary distribution enters the correctness proof as follows.  Put
`D_p=∑_xM_p(x)`, reduce `M_p` modulo `q`, and let `F_p` be the mass of the
resulting `(message bit, noise residue)` pairs for which decoding fails.  The
auxiliary message bit is uniform and independent, which accounts for the
factor `2` in the denominator.  Given the `NTTRingLaws` algebraic certificate
and the hypothesis `CoefficientFailureBound`, each of the `256` coordinates
satisfies

`Pr[the honest coordinate fails] ≤ F_p/(2D_p)`.

The union bound and the exact arithmetic certificate then give

```
ε_ML-KEM ≤ 256·F_p/(2D_p) ≤ 2^{-e_p} = δ_p.
```

The final inequality is what yields the conditional theorem
`deltaCorrect_fips203`.  The calculation of `M_p` is exact for the auxiliary
model; `CoefficientFailureBound`, stated in `NoiseModel.lean`, is the separate
hypothesis relating it to the honest `(d,z,m)` experiment.

## Terminology: the law of a random variable

In probability theory, the *law* of a random variable `X : Ω → S` on a
probability space `(Ω,P)` means its distribution, namely the pushforward
measure `X_*P`:

`(X_*P)(A)=P(X⁻¹(A))`.

For a discrete random variable, its probability mass function is
`x ↦ P[X=x]`.  The `IntMeasure` values in this file are unnormalized versions
of such laws: they push forward counting measure rather than probability
measure.  Thus

`x ↦ #{ω∈Ω | X(ω)=x}`

has total mass `|Ω|`, and division by `|Ω|` gives the law of `X` under the
uniform probability measure.  For independent variables, additive convolution
computes the law of `X+Y`, while `productMeasure` pushes the product law forward
along integer multiplication to compute the law of `XY`.  Every occurrence of
“law” below has this standard pushforward-measure meaning.  It is unrelated to
Lean structures named `Laws`, which bundle equations satisfied by algebraic or
encoding operations.

## Centered binomial and compression-error variables

For `η≥0`, let `Ω_η={0,1}^{2η}` and equip it with the uniform probability
measure.  If `ω=(a₁,…,a_η,b₁,…,b_η)`, define the random variable

`CBD_η : Ω_η → ℤ`,

`CBD_η(ω)=∑_{j=1}^{η}a_j-∑_{j=1}^{η}b_j`.

Thus `CBD_η` is the difference of two independent `Binomial(η,1/2)` random
variables.  Its name abbreviates *centered binomial distribution*, and its
image is contained in `{-η,…,η}`.

The counting measure

`C_η(x)=#{ω∈Ω_η | CBD_η(ω)=x}`

has total mass `|Ω_η|=2^{2η}=4^η`; its probability mass function is
`C_η(x)/4^η`.  Lean enumerates `Ω_η` by the natural numbers
`{0,…,4^η-1}`: `cbdValue η` is the function `CBD_η` in this enumeration and
`cbdMeasure η` is the counting measure `C_η`.

For a compression width `d`, define a second random variable on the uniform
probability space `ℤ/qℤ` by

`c_d : ℤ/qℤ → ℤ`,

`c_d(a)=centered(Decompress_d(Compress_d(a))-a)`.

The measure `compressionErrorMeasure d` is

`E_d(x)=#{a∈ℤ/qℤ | c_d(a)=x}`.

It has total mass `q`, and `E_d(x)/q=Pr[c_d=x]`.

## From polynomial arithmetic to a coefficient measure

The model is most naturally described before reduction modulo `q`.  Put

`R_ℤ=ℤ[X]/(X^n+1)`, with `n=256`.

Choose random polynomial vectors

```
S,E,Y,E₁,C_u ∈ R_ℤ^k
```

and random polynomials `E₂,C_v∈R_ℤ`.  All their scalar coefficients are
mutually independent, with distributions

```
S_{ℓj}, E_{ℓj}, Y_{ℓj}  ∼ CBD_{η₁},
(E₁)_{ℓj}, (E₂)_j       ∼ CBD_{η₂},
(C_u)_{ℓj}               ∼ E_{d_u}/q,
(C_v)_j                  ∼ E_{d_v}/q.
```

Here `0≤ℓ<k`, `0≤j<n`, and `E_d/q` denotes the normalized compression-error
measure above.  Define the auxiliary random polynomial

`N_p^ind=EᵀY-Sᵀ(E₁+C_u)+E₂+C_v ∈ R_ℤ`.                   (2)

Thus the model samples scalar coefficients, assembles them into random
polynomials, and performs polynomial multiplication in the quotient ring.
No symbolic substitution into `R_q` is involved.  Reducing the coefficients
of `N_p^ind` modulo `q` gives an element of
`R_q=(ℤ/qℤ)[X]/(X^n+1)` having the same algebraic form as (1).

Since `X^n=-1`, the coefficient of degree `i` in a product in either quotient
ring is

`(fg)_i=∑_{j=0}^{i}f_jg_{i-j}-∑_{j=i+1}^{n-1}f_jg_{n+i-j}`.  (3)

Thus a coefficient of one polynomial product is a sum of `n` scalar products,
and a coefficient of an inner product of vectors of length `k` is a sum of
`kn` scalar products.  Each product affected by a minus sign in (2)--(3) has
an independent centered-binomial factor.  Since that factor is symmetric
about zero, negating the product does not change its distribution.  It follows
that every fixed coefficient of `N_p^ind` has the same distribution.

Writing `*` for the counting measure of a sum of independent variables and
`⊠` for the counting measure of their integer product, the resulting
unnormalized measure for one coefficient is

```
M_p=(C_{η₁}⊠C_{η₁})^{*(kn)}
    *(C_{η₁}⊠(C_{η₂}*E_{d_u}))^{*(kn)}
    *(C_{η₂}*E_{d_v}).                                    (4)
```

The first factor is the coefficient distribution (pushforward law) of `EᵀY`:
it is the additive convolution of `kn` product distributions
`C_{η₁}⊠C_{η₁}`.  The second is the coefficient distribution of
`Sᵀ(E₁+C_u)`: each scalar product has one
`CBD_{η₁}` factor and one independent sum of a `CBD_{η₂}` variable and a
`d_u`-compression error.  The last factor is the coefficient distribution of
`E₂+C_v`.  They therefore correspond to `eᵀy`, `sᵀ(e₁+ε_u)`, and `e₂+ε_v`
in (1), respectively.

`coefficientNoiseMeasure p` is the unnormalized pushforward distribution (4),
and `noiseDenominator p` is its total mass.  `foldedNoiseMeasure p` is the
pushforward of (4) under
`ℤ→ℤ/qℤ`, obtained by summing the masses in each congruence class.
`decodeFailureMass p` then weights each residue by the number of message bits
that it causes `Compress₁` to decode incorrectly.

The generic definitions of finite integer measures, additive convolution, and
product pushforward live in `ToVCVio.Probability.IntMeasure`.  The proposition
relating the model (4) to the honest sampler is stated separately in
`NoiseModel.lean`.
-/

open LatticeCrypto

namespace MLKEM

/-! ## Component measures -/

/-- The random-variable function `CBD_η : Ω_η → ℤ`, after identifying
`Ω_η={0,1}^{2η}` with `{0,…,4^η-1}`.  It sends a `2η`-bit sample `x` to the
number of set bits among its low `η` bits minus the number among its next `η`
bits (FIPS 203, Algorithm 8). -/
def cbdValue (η x : ℕ) : ℤ :=
  ((∑ j ∈ Finset.range η, (x >>> j) % 2 : ℕ) : ℤ) -
    ((∑ j ∈ Finset.range η, (x >>> (η + j)) % 2 : ℕ) : ℤ)

/-- The unnormalized pushforward distribution of the uniformly sampled random
variable `CBD_η : Ω_η → ℤ`:

`x ↦ #{ω∈{0,1}^{2η} | CBD_η(ω)=x}`.

Its total mass is `4^η`; division by `4^η` gives its probability mass
function. -/
noncomputable def cbdMeasure (η : ℕ) : IntMeasure := enumMeasure (4 ^ η) (cbdValue η)

theorem measureWindow_cbdMeasure_two : MeasureWindow (cbdMeasure 2) (-2) 2 :=
  measureWindow_enumMeasure (by decide)

theorem measureWindow_cbdMeasure_three : MeasureWindow (cbdMeasure 3) (-3) 3 :=
  measureWindow_enumMeasure (by decide)

/-- The `Compress_d` round-trip error of the residue `x`: the centered
representative of `Decompress_d (Compress_d x) - x`. -/
def compressionError (d x : ℕ) : ℤ :=
  centeredRepr (Concrete.decompress d (Concrete.compress d (x : Coeff)) - (x : Coeff))

/-- The unnormalized compression-error measure for a uniform input residue:
the mass at `x` is the number of `a∈ℤ/qℤ` for which
`centered(Decompress_d(Compress_d(a))-a)=x`. -/
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

/-- The pushforward counting measure of one scalar product in `eᵀy`: the
distribution of the integer product of two independent `CBD_{η₁}` draws. -/
noncomputable def keyNoiseProductMeasure (p : ParameterSet) : IntMeasure :=
  productMeasure (cbdMeasure p.params.eta1) (cbdMeasure p.params.eta1)

/-- The pushforward counting measure of one scalar product in `sᵀ(e₁+ε_u)`:
the distribution of the product of an independent `CBD_{η₁}` draw with an
independent sum of a `CBD_{η₂}` draw and a `Compress_{d_u}` round-trip error. -/
noncomputable def ciphertextNoiseProductMeasure (p : ParameterSet) : IntMeasure :=
  productMeasure (cbdMeasure p.params.eta1)
    (cbdMeasure p.params.eta2 * compressionErrorMeasure p.params.du)

/-- The pushforward counting measure of the additive term `e₂+ε_v`: the
distribution of an independent sum of a `CBD_{η₂}` draw and a
`Compress_{d_v}` round-trip error. -/
noncomputable def additiveNoiseMeasure (p : ParameterSet) : IntMeasure :=
  cbdMeasure p.params.eta2 * compressionErrorMeasure p.params.dv

/-- The unnormalized pushforward distribution of any fixed coefficient of the
auxiliary random polynomial

`N_p^ind=EᵀY-Sᵀ(E₁+C_u)+E₂+C_v ∈ ℤ[X]/(X^256+1)`.

After reduction modulo `q`, this polynomial mirrors the honest decryption-noise
identity

`w − μ = eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u`.

The coefficients of `E,Y,S,E₁,E₂,C_u,C_v` are independent and have the
distributions specified in the module comment.  The factor
`keyNoiseProductMeasure p ^ (p.params.k * ringDegree)` accounts for the
`eᵀy` products; `ciphertextNoiseProductMeasure p ^
(p.params.k * ringDegree)` accounts for the `sᵀ(e₁+ε_u)` products; and
`additiveNoiseMeasure p` accounts for `e₂+ε_v`.  The proposition
`CoefficientFailureBound` in `NoiseModel.lean` is the separate hypothesis that
compares this auxiliary distribution with the honest per-coordinate sampler. -/
noncomputable def coefficientNoiseMeasure (p : ParameterSet) : IntMeasure :=
  keyNoiseProductMeasure p ^ (p.params.k * ringDegree) *
    ciphertextNoiseProductMeasure p ^ (p.params.k * ringDegree) *
    additiveNoiseMeasure p

/-- The pushforward of `coefficientNoiseMeasure p` under the reduction map
`ℤ→ℤ/qℤ`.  Its mass at `r` is the sum of the integer masses over the congruence
class `r`; equivalently, it is the periodization of the measure modulo `q`. -/
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

/-- The bit-summed decode-failure mass of the periodized coefficient-noise measure.
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
