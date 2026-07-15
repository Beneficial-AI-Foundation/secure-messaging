/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Construction
import SecureMessaging.KEM.MLKEM.Correctness.ConcreteEncoding
import SecureMessaging.KEM.MLKEM.Correctness.FailureBounds
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate
import SecureMessaging.KEM.MLKEM.Correctness.FailureRates
import SecureMessaging.KEM.MLKEM.Correctness.FIPS203FailureExperiment
import SecureMessaging.KEM.MLKEM.Correctness.Noise
import SecureMessaging.KEM.MLKEM.Correctness.NoiseDistribution
import SecureMessaging.KEM.MLKEM.Correctness.NoiseIdentity
import SecureMessaging.KEM.MLKEM.Correctness.NoiseModel
import SecureMessaging.KEM.MLKEM.Correctness.Reduction

/-!
# Conditional correctness bound for honest ML-KEM decapsulation

This module is the entry point for the quantitative correctness theorem in
this directory.  To help the reader, we first give an overview of the
experiment, the decryption algebra, and the finite probability calculation
implemented by the Lean definitions.

## 1. Correctness of a key-encapsulation mechanism

Let `Π = (KeyGen, Encaps, Decaps)` be a key-encapsulation mechanism.  Its honest
correctness experiment is

```
(ek,dk) ← KeyGen;
(c,K)   ← Encaps(ek);
K'      ← Decaps(dk,c);
return (K' = some K).
```

Write `p_T` and `p_F` for the probabilities that this experiment returns
`true` and `false`.  The output measure of a general probabilistic computation
is allowed to have total mass less than one.  Its missing mass is

`p_⊥ = 1 - p_T - p_F`

and represents executions that produce no Boolean result, for example because
the computation fails or does not terminate.  The correctness error used here
is

`ε_Π := 1 - p_T = p_F + p_⊥`.                              (1)

Thus `Π` is perfectly correct when `ε_Π=0`, and is `δ`-correct when
`ε_Π≤δ`.  The equality in (1) is
`KEMScheme.correctnessError_eq_probOutput_false_add_probFailure`.  ML-KEM is
interpreted by the total semantics `ProbComp`; hence `p_⊥=0` and its
correctness error is simply the probability that honest decapsulation does
not return the key produced by encapsulation.

The probability library represents `ε_Π` and `δ` in the extended nonnegative
reals `ℝ≥0∞`.  Every probability and every threshold used below is finite and
lies in `[0,1]`; mathematically, one may regard them as ordinary nonnegative
real numbers.  The larger codomain is an interface choice made by the generic
probability library, which also has to represent countable sums and the
missing mass above.  It is not an additional hypothesis in the ML-KEM theorem.

Correctness in this sense is a reliability property.  KEM security is instead
formulated by an indistinguishability experiment in which an adversary must
distinguish an encapsulated key from an independent uniform key.  The two
experiments answer different questions.

## 2. The honest ML-KEM experiment

Fix a parameter set `p`, transform operations `ring`, and primitive operations
`prims`.  The FIPS 203 honest experiment has the finite uniform sample space

`Ω = Seed32 × Seed32 × Message`.

For `ω=(d,z,m)∈Ω`, define

```
(ek,dk) = keygenInternal(d,z),
(K,c)   = encapsInternal(ek,m),
K'      = decapsInternal(dk,c).
```

The event of interest is `E_KEM={ω | K'(ω)≠K(ω)}`.  The definition
`fips203DecapsulationFailureExp` returns its indicator, and
`correctnessError_eq_fips203DecapsulationFailureProb` proves

`ε_{ML-KEM-p} = Pr[E_KEM]`.                                (2)

The deterministic Fujisaki--Okamoto reduction proves the inclusion

`E_KEM ⊆ E_PKE`,                                           (3)

where `E_PKE` is failure of the underlying honest K-PKE decryption to recover
`m`.  This is `correctnessError_le_underlyingCorrectnessError`.

## 3. The decryption-noise identity

Put `q=3329`, `n=256`, and

`R_q=(ℤ/qℤ)[X]/(X^n+1)`.

An element of `R_q` has a unique representative of degree less than `n`, so we
refer interchangeably to an element of `R_q` and to its coefficient vector of
length `n`.  A parameter set supplies five integers `(k,η₁,η₂,d_u,d_v)`:

* `k` is the module rank.  The public matrix is `k×k`, and the secret,
  key-generation error, encryption secret, encryption error, and first
  ciphertext component are vectors of length `k` over `R_q`;
* `η₁` is the centered-binomial parameter used for the secret `s`, the
  key-generation error `e`, and the encryption secret `y`;
* `η₂` is the centered-binomial parameter used for the encryption errors
  `e₁` and `e₂`;
* `d_u` and `d_v` are the numbers of bits retained per coefficient when the
  two ciphertext components `u` and `v` are compressed.

Suppressing transform-domain hats, honest key generation and encryption are
described in `R_q` by

```
t = As + e,                 t ∈ R_q^k,
u = Aᵀy + e₁,               u ∈ R_q^k,
v = tᵀy + e₂ + μ,           v ∈ R_q,
μ = Decompress₁(ByteDecode₁(m)) ∈ R_q.                    (4)
```

Here `t` is the polynomial vector contained in the public key (stored by the
implementation in transform representation), and `(u,v)` are the two
uncompressed ciphertext components.  Let

```
u'  = Decompress_{d_u}(Compress_{d_u}(u)) = u + ε_u,
v'  = Decompress_{d_v}(Compress_{d_v}(v)) = v + ε_v,
w   = v' - sᵀu'.                                             (5)
```

The polynomial `w` is the value from which decryption reads the message.
Substitution of (4)--(5), followed by distributivity and cancellation of
`(As)ᵀy=sᵀ(Aᵀy)`, gives

```
w - μ
  = (As+e)ᵀy + e₂ + μ + ε_v
      - sᵀ(Aᵀy+e₁+ε_u) - μ
  = eᵀy + e₂ + ε_v - sᵀe₁ - sᵀε_u.                       (6)
```

The file `NoiseIdentity.lean` defines every term in (4)--(6) and proves (6)
as `kpkeDecryptDifference_eq_noise`.

The generic proof takes `hRing : NTTRingLaws ring`, an algebraic certificate
that the forward and inverse transforms are mutually inverse and transport the
addition and multiplication of `R_q`.  For the concrete ML-KEM transform,
`Concrete.concreteNTTRingLaws` is the corresponding proof bundle; its inverse
matrix identity is discharged by a finite `native_decide` certificate.  This
is algebraic infrastructure for (6), distinct from the probabilistic
comparison introduced below.

## 4. Exact coefficient-recovery events

For `b∈{0,1}` and `r∈ℤ/qℤ`, define

`Fail(b,r) :⇔ Compress₁(Decompress₁(b)+r) ≠ b`.             (7)

For an honest outcome `ω`, let `B_i(ω)` be coefficient `i` of
`ByteDecode₁(m)`, and let `N_i(ω)` be coefficient `i` of the decryption-noise
element `w-μ` in (6).  The exact recovery theorem proves

`E_PKE = {ω | ∃ i<n, Fail(B_i(ω),N_i(ω))}`.                (8)

There is also a useful sufficient condition:

`max_i |centered(N_i)| ≤ ⌊q/4⌋-1 = 831  ⇒  ω∉E_PKE`.

The quantitative theorem uses the exact event (8).  The union bound gives

`Pr[E_PKE] ≤ ∑_{i=0}^{n-1} Pr[Fail(B_i,N_i)]`.             (9)

## 5. The auxiliary independent one-coefficient model

We now define the finite counting measure used in the numerical certificate.
For `η≥0`, let

`Ω_η={0,1}^{2η}`

and equip this finite set with the uniform probability measure.  Writing an
element as `(a₁,…,a_η,b₁,…,b_η)`, define the integer-valued random variable

`CBD_η : Ω_η → ℤ`,

`CBD_η(a₁,…,a_η,b₁,…,b_η)=∑_{j=1}^{η} a_j-∑_{j=1}^{η} b_j`.

The acronym CBD means *centered binomial distribution*: `CBD_η` is the
difference of two independent binomial random variables with parameters
`(η,1/2)`, and hence takes values in `{-η,…,η}`.  Its unnormalized counting
measure is

`C_η(x)=#{ω∈Ω_η | CBD_η(ω)=x}`.                            (10)

Since `|Ω_η|=2^{2η}=4^η`, its probability mass function is `C_η(x)/4^η`.
These variables model the coefficients sampled for `s,e,y,e₁,e₂`, with the
parameters specified above.

For a compression width `d`, define a second counting measure

```
E_d(x)=#{a∈ℤ/qℤ |
  centered(Decompress_d(Compress_d(a))-a)=x}.              (11)
```

Thus `E_d/q` is the compression-error distribution obtained from a uniform
input coefficient in `ℤ/qℤ`.  For finitely supported counting measures
`F,G : ℤ→ℕ`, write

```
(F*G)(z)   = ∑_{x+y=z} F(x)G(y),
(F⊠G)(z)   = ∑_{xy=z} F(x)G(y).
```

These are the counting measures of a sum and a product of independent random
variables.

To state precisely what the model represents, first work in the integer
quotient ring

`R_ℤ=ℤ[X]/(X^n+1)`.

Choose all coefficients of random elements

```
S,E,Y,E₁,C_u ∈ R_ℤ^k,       E₂,C_v ∈ R_ℤ
```

independently, with

```
S_{ℓj}, E_{ℓj}, Y_{ℓj}  distributed as CBD_{η₁},
(E₁)_{ℓj}, (E₂)_j       distributed as CBD_{η₂},
(C_u)_{ℓj}               distributed as E_{d_u}/q,
(C_v)_j                  distributed as E_{d_v}/q,
```

where `0≤ℓ<k` and `0≤j<n`.  Form the auxiliary random polynomial

`N_p^ind = EᵀY - Sᵀ(E₁+C_u) + E₂+C_v ∈ R_ℤ`.             (12)

Thus scalar random variables are sampled first, assembled into polynomial
vectors, and then multiplied in the quotient ring.  This is not symbolic
substitution of random variables into `R_q`.  Reducing the coefficients of
`N_p^ind` modulo `q` gives an element of `R_q` with the same formal shape as
the right-hand side of (6).

Multiplication in either quotient ring is determined by `X^n=-1`.
Explicitly, for representatives of degree less than `n`,

`(fg)_i = ∑_{j=0}^{i} f_jg_{i-j} - ∑_{j=i+1}^{n-1} f_jg_{n+i-j}`.  (13)

Consequently one coefficient of a product contains `n` scalar products, and
one coefficient of an inner product of length `k` contains `kn` of them.  The
minus signs in (12)--(13) do not alter the relevant product distributions:
each negated product contains an independent centered-binomial factor, whose
distribution is symmetric about zero.

For any fixed coefficient index, the unnormalized counting measure of that
coefficient of `N_p^ind` is

```
M_p = (C_{η₁} ⊠ C_{η₁}) ^{*(kn)}
      * (C_{η₁} ⊠ (C_{η₂} * E_{d_u})) ^{*(kn)}
      * (C_{η₂} * E_{d_v}).                               (14)
```

The first factor is the coefficient law of `EᵀY`: a sum of `kn` products of
independent `CBD_{η₁}` variables.  The second is the coefficient law of
`Sᵀ(E₁+C_u)`: a sum of `kn` products whose first factor has law `CBD_{η₁}` and
whose second factor is the sum of a `CBD_{η₂}` variable and a compression-error
variable.  The third is the coefficient law of `E₂+C_v`.  Thus the factors
represent `eᵀy`, `sᵀ(e₁+ε_u)`, and `e₂+ε_v` in (6), respectively.  In Lean,
(14) is `coefficientNoiseMeasure p`; it is the law, up to normalization, of a
coefficient in this auxiliary independent model.

Let

```
D_p     = ∑_{x∈ℤ} M_p(x),
M̄_p(r) = ∑_{x∈ℤ : x≡r (mod q)} M_p(x),
W(r)    = ∑_{b∈{0,1}} 1_{Fail(b,r)},
F_p     = ∑_{r∈ℤ/qℤ} M̄_p(r)W(r).                         (15)
```

Here `D_p` is the total mass and therefore the normalization constant.
`M̄_p` is the pushforward of `M_p` under the reduction map
`ℤ→ℤ/qℤ`, equivalently its periodization modulo `q`.  The integer
`W(r)∈{0,1,2}` counts the message bits decoded incorrectly after adding `r`.
Finally, `F_p` is the unnormalized number of failing `(bit,noise)` outcomes.
The auxiliary single-coordinate failure probability is therefore

`F_p/(2D_p)`.                                              (16)

The Lean names in (15) are `noiseDenominator`, `foldedNoiseMeasure`,
`decodeFailureWeight`, and `decodeFailureMass`.

## 6. The conditional correctness theorem

For `e_p=138.8,164.8,174.8` at the three parameter sets, respectively, the
exact arithmetic certificate proves

`nF_p/(2D_p) ≤ 2^{-e_p}`.                                  (17)

This is a theorem about the explicitly defined finite measure (14).  It is
proved with natural-number arithmetic.  More precisely, each exponent has the
form `e_p=E_p/5`, with `E_p∈{694,824,874}`.  For
`a=nF_p` and the positive integer `b=2D_p`, monotonicity of `x↦x^5` gives

`a/b≤2^{-E_p/5}  ↔  a^5·2^{E_p}≤b^5`.

The right side is an exact natural-number inequality, so the fifth power
eliminates the rational exponent without using floating-point approximation.
The full derivation is given in `FailureCertificate.lean`.

It remains to relate the actual random variables `(B_i,N_i)` from (8) to the
independent model.  `CoefficientFailureBound p ring prims` is the proposition
that, for every coordinate `i` and every pair satisfying `Fail(b,r)`,

`Pr[B_i=b ∧ N_i=r] ≤ M̄_p(r)/(2D_p)`.                      (18)

Summing (18) over the failing pairs gives

`Pr[Fail(B_i,N_i)] ≤ F_p/(2D_p)`.

Combining this inequality with (2), (3), (9), and (17) yields

`ε_{ML-KEM-p} ≤ 2^{-e_p}`.                                 (19)

This is `correctnessError_le_fips203`; `deltaCorrect_fips203` expresses the
same inequality using the generic predicate `KEMScheme.deltaCorrect`.

The mathematical form of the result is therefore the implication

`CoefficientFailureBound(p,ring,prims) ⇒ ε_{ML-KEM-p}≤2^{-e_p}`.  (20)

The deterministic reduction, identity (6), event equality (8), union bound,
finite measure, and arithmetic certificate are proved in Lean.  The
pointwise comparison (18) is supplied to the theorem as a premise.  In
particular, establishing (18) for the concrete SHA-3/SHAKE primitives is the
remaining step required to turn (20) into an unconditional numerical theorem
about those primitives.

## 7. Relation with the correctness theorem of Barbosa et al.

Barbosa, Kannwischer, Lim, Schwabe, and Strub define random-oracle PKE
correctness by the experiment

```
(pk,sk) ← Gen^O;
m       ← A^O(pk,sk);
c       ← Enc^O(pk,m);
return (Dec^O(sk,c) ≠ m).
```

Their definition requires the failure probability to be at most `δ(Q)` for
every, possibly unbounded, adversary making at most `Q` oracle queries.  The
dependence on `Q` accounts for the adversary's oracle access and adaptive
choice of `m`.

The honest experiment (2) samples `m` uniformly and fixes `prims`, so its
error bound is the constant `2^{-e_p}` rather than a function of a query
budget.  Barbosa et al. also formalize the independent-noise calculation used
for the small ML-KEM design rates and identify the uniform, independent
compression-error treatment as a heuristic approximation.  Their separate
argument gives a larger bound under the MLWE assumption by replacing that
approximation with a conservative decomposition.

The probabilistic premise (18) used here is not the same statement as the
uniform-and-independent compression-error heuristic.  Rather than postulating
a generative description of the ciphertext components, it directly requires
each failing `(bit,noise-residue)` cell of the honest experiment to be bounded
by the corresponding cell of the auxiliary measure.  It is therefore a
different, strong sufficient condition for applying the exact finite
calculation.  Establishing (18) from a standard assumption about the concrete
SHA-3/SHAKE primitives, or replacing it by the distinct MLWE reduction of
Barbosa et al., would require another theorem.
-/

open OracleComp KEMScheme ENNReal

namespace MLKEM

/-- Let `ring` satisfy the algebraic NTT interface and suppose that every
failing actual `(bit, noise-residue)` cell is bounded by the corresponding cell
of `coefficientNoiseMeasure p`.  Then the honest ML-KEM correctness error at
parameter set `p` is at most the Table 1 threshold `2 ^ (-e_p)`. -/
theorem correctnessError_le_fips203 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : CoefficientFailureBound p ring prims) :
    (mlkemScheme p ring prims).correctnessError ProbCompRuntime.probComp ≤
      fips203DecapsulationFailureBound p :=
  le_trans (correctnessError_le_underlyingCorrectnessError ring _ prims)
    (underlyingCorrectnessError_le_fips203 p ring prims hRing hModel)

/-- Under the coefficient-distribution comparison
`CoefficientFailureBound`, ML-KEM at parameter set `p` is `δ`-correct for
`δ=2^(-e_p)`. -/
-- ANCHOR: deltaCorrectFips203
theorem deltaCorrect_fips203 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : CoefficientFailureBound p ring prims) :
    (mlkemScheme p ring prims).deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound p)
-- ANCHOR_END: deltaCorrectFips203
    :=
  deltaCorrect_of_underlying ring _ prims
    (underlyingCorrectnessError_le_fips203 p ring prims hRing hModel)

/-- Under the coefficient-distribution comparison, the probability that the
Section 3.2 honest decapsulation experiment reports a failure is at most its
Table 1 threshold. -/
theorem fips203DecapsulationFailureProb_le_bound (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : CoefficientFailureBound p ring prims) :
    Pr[= true | fips203DecapsulationFailureExp p ring
        (Concrete.concreteEncoding (ParameterSet.params p)) prims] ≤
      fips203DecapsulationFailureBound p := by
  rw [← correctnessError_eq_fips203DecapsulationFailureProb]
  exact correctnessError_le_fips203 p ring prims hRing hModel

/-- Given the concrete NTT algebra certificate and the coefficient-distribution
coefficient comparison, honest ML-KEM-512 decapsulation has error at most
`2^(-138.8)`.  The canonical value for `hRing` is
`Concrete.concreteNTTRingLaws`; it is kept explicit because its finite inverse
matrix certificate is currently discharged by `native_decide`. -/
theorem deltaCorrect_mlkem512
    (hRing : NTTRingLaws Concrete.concreteNTTRingOps)
    (hModel : CoefficientFailureBound .MLKEM512 Concrete.concreteNTTRingOps
      Concrete.mlkem512Primitives) :
    mlkem512Scheme.deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound .MLKEM512) :=
  deltaCorrect_fips203 _ _ _ hRing hModel

/-- Given the concrete NTT algebra certificate and the coefficient-distribution
coefficient comparison, honest ML-KEM-768 decapsulation has error at most
`2^(-164.8)`. -/
theorem deltaCorrect_mlkem768
    (hRing : NTTRingLaws Concrete.concreteNTTRingOps)
    (hModel : CoefficientFailureBound .MLKEM768 Concrete.concreteNTTRingOps
      Concrete.mlkem768Primitives) :
    mlkem768Scheme.deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound .MLKEM768) :=
  deltaCorrect_fips203 _ _ _ hRing hModel

/-- Given the concrete NTT algebra certificate and the coefficient-distribution
coefficient comparison, honest ML-KEM-1024 decapsulation has error at most
`2^(-174.8)`. -/
theorem deltaCorrect_mlkem1024
    (hRing : NTTRingLaws Concrete.concreteNTTRingOps)
    (hModel : CoefficientFailureBound .MLKEM1024 Concrete.concreteNTTRingOps
      Concrete.mlkem1024Primitives) :
    mlkem1024Scheme.deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound .MLKEM1024) :=
  deltaCorrect_fips203 _ _ _ hRing hModel

end MLKEM
