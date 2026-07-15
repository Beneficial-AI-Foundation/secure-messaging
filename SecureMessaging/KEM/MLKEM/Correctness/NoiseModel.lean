/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.ConcreteEncoding
import SecureMessaging.KEM.MLKEM.Correctness.FailureBounds
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate
import SecureMessaging.KEM.MLKEM.Correctness.NoiseIdentity

/-!
# Comparing the honest noise with the independent coefficient model

The variables in this file come from the decryption algebra developed in
`NoiseIdentity.lean`.  In particular, that module defines
`A,s,e,y,e₁,e₂,μ,u,v,w,ε_u,ε_v` and proves

`w-μ=eᵀy+e₂+ε_v-sᵀe₁-sᵀε_u`.                            (1)

Here `w-μ` is an element of
`R_q=(ℤ/qℤ)[X]/(X^256+1)`.  We call it the decryption-noise polynomial because
elements of this quotient ring are represented uniquely by polynomials of
degree less than `256`; the public matrix `A` is a matrix over `R_q`.

## Actual random variables

Fix a parameter set `p`, transform operations `ring`, and primitive operations
`prims`.  The honest experiment uses the finite uniform sample space

`Ω=Seed32×Seed32×Message`.

For `ω=(d,z,m)∈Ω` and `i∈{0,…,255}`, define

```
B_i(ω) = coefficient i of ByteDecode₁(m) ∈ {0,1},
N_i(ω) = coefficient i of (w-μ)(d,z,m) ∈ ℤ/qℤ.
```

Equation (1) shows that `N_i` is independent of the implicit-rejection seed
`z`; that seed affects the fallback shared secret rather than the honest K-PKE
ciphertext arithmetic.  A pair `(b,r)` causes a coefficient error precisely
when

`Fail(b,r) :⇔ Compress₁(Decompress₁(b)+r)≠b`.              (2)

## The comparison measure

Let `M_p=coefficientNoiseMeasure p` be the unnormalized independent-noise
measure defined in `NoiseDistribution.lean`, and put

```
D_p     = ∑_{x∈ℤ}M_p(x),
M̄_p(r)  = ∑_{x∈ℤ : x≡r (mod q)}M_p(x),
ν_p(b,r)= M̄_p(r)/(2D_p).                                  (3)
```

Thus `D_p` normalizes `M_p`, while `M̄_p` is its pushforward along
`ℤ→ℤ/qℤ`.  The factor `2` makes the bit coordinate uniform.
`sum_foldedNoiseMeasure` proves `∑_r M̄_p(r)=D_p`, and hence `ν_p` is a
probability measure on `{0,1}×ℤ/qℤ`.

`CoefficientFailureBound p ring prims` is the cellwise comparison

`Fail(b,r) → Pr[B_i=b ∧ N_i=r]≤ν_p(b,r)`                 (4)

for every `i,b,r`.  Only cells contributing to the exact failure event (2)
are needed.  Summing (4) over those cells gives

`Pr[Fail(B_i,N_i)]≤decodeFailureMass(p)/(2D_p)`.           (5)

A union bound over the `256` coordinates, followed by the exact arithmetic
certificate, yields

`underlyingCorrectnessError≤2^{-e_p}`.                    (6)

The declarations `coordinateTail_le` and
`underlyingCorrectnessError_le_fips203` prove (5) and (6).  The comparison
(4) is an argument to these theorems.  It is a direct, strong domination
condition on the failing cells; it is not merely the assertion that an XOF is
a random function, nor is it identical to the heuristic that compression
inputs are independent and uniform.  A proof of (4) for the concrete
SHA-3/SHAKE primitives would supply the probabilistic link between the honest
experiment and the independent coefficient calculation.
-/

open OracleComp LatticeCrypto
open scoped ENNReal

namespace MLKEM

/-- The decryption-noise element of `R_q` for the honest run from key seed `d`
and message `m`:
`eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u`, with every product computed through the NTT
isomorphism. By `kpkeDecryptDifference_eq_noise` this equals `w − μ` on the
honest run from `(d, z, m)` for every implicit-rejection seed `z`. -/
def kpkeHonestNoise {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : Rq :=
  ring.invNTT (ring.dot (ring.nttVec (kpkeKeygenError prims d))
      (ring.nttVec (kpkeEncryptionSecret ring prims d m))) +
    kpkeEncryptionError2 ring prims d m +
    kpkeCompressionErrorV ring prims d m -
    ring.invNTT (ring.dot (ring.nttVec (kpkeSecret prims d))
      (ring.nttVec (kpkeEncryptionError1 ring prims d m))) -
    ring.invNTT (ring.dot (ring.nttVec (kpkeSecret prims d))
      (ring.nttVec (kpkeCompressionErrorU ring prims d m)))

/-- The decryption noise `w − μ` of the honest run equals `kpkeHonestNoise`; in
particular it does not depend on the implicit-rejection seed `z`. -/
theorem kpkeDecryptDifference_eq_honestNoise {params : Params} {encoding : Encoding params}
    (ring : NTTRingOps) (prims : Primitives params encoding) (hEnc : encoding.Laws)
    (hRing : NTTRingLaws ring) (d z : Seed32) (m : Message) :
    kpkeDecryptDifference ring encoding prims d z m = kpkeHonestNoise ring prims d m :=
  kpkeDecryptDifference_eq_noise ring prims hEnc hRing d z m

/-- Pushforward along `ℤ→ℤ/qℤ` preserves the total mass of the coefficient-noise
measure: its values over `ZMod q` sum to the noise denominator.

The normalized residue distribution is

`r ↦ foldedNoiseMeasure p r / noiseDenominator p`.

Since the decoded coefficient is always a bit, the auxiliary probabilities on the
right-hand side of `CoefficientFailureBound.prob_le_of_decodeFailure` divide
by `2 * noiseDenominator p`; summing over the two bits and all residues gives
`1`, so the auxiliary coefficient distribution is a probability distribution.
-/
theorem sum_foldedNoiseMeasure (p : ParameterSet) :
    ∑ r : Coeff, foldedNoiseMeasure p r = noiseDenominator p := by
  have h1 : ∑ r : Coeff, foldedNoiseMeasure p r = (foldedNoiseMeasure p).sum fun _ m => m :=
    (Finsupp.sum_fintype (foldedNoiseMeasure p) (fun _ m => m) fun _ => rfl).symm
  rw [h1, foldedNoiseMeasure, Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl]
  rfl

/-- Coordinate `i` of `compress1` for the concrete encoding is `Compress₁` of
coordinate `i`, since `compress1` acts coefficientwise. -/
private theorem concreteEncoding_compress1_get (params : Params) (f : Rq) (i : Fin ringDegree) :
    ((Concrete.concreteEncoding params).compress1 f).get i = Concrete.compress 1 (f.get i) := by
  change (Concrete.compressPoly 1 f)[i.val] = Concrete.compress 1 (f[i.val])
  unfold Concrete.compressPoly
  exact Vector.getElem_map (f := Concrete.compress 1) (xs := f) i.isLt

/-- Coordinate `i` of `decompress1` for the concrete encoding is `Decompress₁` of
coordinate `i`, since `decompress1` acts coefficientwise. -/
private theorem concreteEncoding_decompress1_get (params : Params) (f : Rq) (i : Fin ringDegree) :
    ((Concrete.concreteEncoding params).decompress1 f).get i = Concrete.decompress 1 (f.get i) := by
  change (Concrete.decompressPoly 1 f)[i.val] = Concrete.decompress 1 (f[i.val])
  unfold Concrete.decompressPoly
  exact Vector.getElem_map (f := Concrete.decompress 1) (xs := f) i.isLt

/-- At the concrete encoding, coordinate `i` of K-PKE decryption fails exactly
when `Compress₁` misreads the decoded bit after the decryption noise is added:
`Compress₁ (Decompress₁ b_i + n_i) ≠ b_i`, where `b_i` is the decoded message
coefficient and `n_i` the coordinate of the decryption noise. -/
theorem kpkeCoordinateDecodeFailure_iff_compress {params : Params} (ring : NTTRingOps)
    (prims : Primitives params (Concrete.concreteEncoding params)) (d z : Seed32)
    (m : Message) (i : Fin ringDegree) :
    kpkeCoordinateDecodeFailure ring (Concrete.concreteEncoding params) prims d z m i ↔
      Concrete.compress 1
          (Concrete.decompress 1
              (((Concrete.concreteEncoding params).byteDecode1 m).get i) +
            (kpkeDecryptDifference ring (Concrete.concreteEncoding params) prims d z m).get i)
        ≠ ((Concrete.concreteEncoding params).byteDecode1 m).get i := by
  have harg :
      (kpkeDecryptRepresentative ring (Concrete.concreteEncoding params) prims d z m).get i
        = Concrete.decompress 1 (((Concrete.concreteEncoding params).byteDecode1 m).get i)
          + (kpkeDecryptDifference ring (Concrete.concreteEncoding params) prims d z m).get i := by
    have hsub :
        (kpkeDecryptDifference ring (Concrete.concreteEncoding params) prims d z m).get i
          = (kpkeDecryptRepresentative ring (Concrete.concreteEncoding params) prims d z m).get i -
            ((Concrete.concreteEncoding params).decompress1
              ((Concrete.concreteEncoding params).byteDecode1 m)).get i := by
      simpa [kpkeDecryptDifference, vectorBackend_coeff] using
        vectorBackend_sub_coeff
          (kpkeDecryptRepresentative ring (Concrete.concreteEncoding params) prims d z m)
          ((Concrete.concreteEncoding params).decompress1
            ((Concrete.concreteEncoding params).byteDecode1 m)) i
    rw [concreteEncoding_decompress1_get] at hsub
    rw [hsub]; ring
  unfold kpkeCoordinateDecodeFailure
  rw [concreteEncoding_compress1_get, harg]

/-- Whether the pair `(b, r)` causes one-coordinate message decoding to fail:
`Compress₁` misreads the decoded bit `b` after the noise residue `r` is
added. -/
def coefficientDecodeFailure (b : Fin 2) (r : Coeff) : Prop :=
  Concrete.compress 1 (Concrete.decompress 1 ((b : ℕ) : Coeff) + r) ≠ ((b : ℕ) : Coeff)

/-- The eventwise coefficient comparison (4) from the module statement.

For every coordinate `i` and every pair `(b,r)` satisfying the exact decoding
failure predicate (2), this structure bounds the actual joint event by

`Pr[B_i=b ∧ N_i=r] ≤ foldedNoiseMeasure p r / (2*noiseDenominator p)`.

This is the probabilistic premise used to pass from the honest experiment to
the independent coefficient calculation. -/
structure CoefficientFailureBound (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) : Prop where
  /-- For every coefficient `i` and every pair `(b, r)` at which decoding
  fails, the event `B_i = b ∧ N_i = r` has probability at most
  `foldedNoiseMeasure p r / (2 * noiseDenominator p)`. -/
  prob_le_of_decodeFailure : ∀ (i : Fin ringDegree) (b : Fin 2) (r : Coeff),
    coefficientDecodeFailure b r →
    Pr[ fun dzm : Seed32 × Seed32 × Message =>
        ((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i =
            ((b : ℕ) : Coeff) ∧
          (kpkeHonestNoise ring prims dzm.1 dzm.2.2).get i = r
      | honestNoiseSample ]
      ≤ (foldedNoiseMeasure p r : ℝ≥0∞) / (2 * noiseDenominator p)

/-- Summing the folded masses over the failing `(bit, residue)` pairs gives the
decode-failure mass: at each residue, the failing bits are counted by
`decodeFailureWeight`. -/
private theorem sum_filter_foldedNoiseMeasure_eq_decodeFailureMass (p : ParameterSet) :
    ∑ br ∈ (Finset.univ : Finset (Fin 2 × Coeff)).filter
        (fun br => Concrete.compress 1
            (Concrete.decompress 1 ((br.1 : ℕ) : Coeff) + br.2) ≠ ((br.1 : ℕ) : Coeff)),
      foldedNoiseMeasure p br.2 = decodeFailureMass p := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm, decodeFailureMass]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    decodeFailureWeight, mul_add, mul_ite, mul_one, mul_zero]

/-- The per-coordinate decode-failure witness at the concrete encoding: the
decoded bit `b_i`, paired with the coefficient of the decryption noise, is a
failing `(bit, residue)` pair that the honest run realizes. The decoded
coefficient is `0` or `1`, so a concrete bit witness closes each case. -/
private theorem coordinateDecodeFailure_exists_failing_pair (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (i : Fin ringDegree) (dzm : Seed32 × Seed32 × Message)
    (hfail : coordinateDecodeFailureEvent ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims i dzm) :
    ∃ br ∈ (Finset.univ : Finset (Fin 2 × Coeff)).filter
        (fun br => Concrete.compress 1
            (Concrete.decompress 1 ((br.1 : ℕ) : Coeff) + br.2) ≠ ((br.1 : ℕ) : Coeff)),
      ((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i
          = ((br.1 : ℕ) : Coeff) ∧
        (kpkeHonestNoise ring prims dzm.1 dzm.2.2).get i = br.2 := by
  simp only [coordinateDecodeFailureEvent] at hfail
  rw [kpkeCoordinateDecodeFailure_iff_compress ring prims dzm.1 dzm.2.1 dzm.2.2 i,
    kpkeDecryptDifference_eq_honestNoise ring prims
      (Concrete.fips203EncodingLaws p).laws hRing dzm.1 dzm.2.1 dzm.2.2] at hfail
  have hval :
      (((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i).val < 2 :=
    Concrete.byteDecode1_get_val_lt_two (ParameterSet.params p) dzm.2.2 i
  have hcast :
      ((((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i).val
          : Coeff)
        = ((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i :=
    ZMod.natCast_zmod_val _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  obtain h | h :
      (((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i).val = 0 ∨
        (((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i).val
          = 1 := by omega
  · have hbit : ((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i
        = 0 := by rw [← hcast, h]; simp
    rw [hbit] at hfail
    exact ⟨(0, (kpkeHonestNoise ring prims dzm.1 dzm.2.2).get i), hfail, hbit, rfl⟩
  · have hbit : ((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i
        = 1 := by rw [← hcast, h]; simp
    rw [hbit] at hfail
    exact ⟨(1, (kpkeHonestNoise ring prims dzm.1 dzm.2.2).get i), hfail, hbit, rfl⟩

/-- Under the `CoefficientFailureBound` hypothesis, the probability that a
coordinate decodes incorrectly is at most the bit-averaged decode-failure
mass `decodeFailureMass p / (2 * noiseDenominator p)`: sum the probabilities
of the pairs `(b, r)` at which decoding fails, bound each by
`prob_le_of_decodeFailure`, and identify the auxiliary total with
`decodeFailureMass`. -/
theorem coordinateTail_le (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : CoefficientFailureBound p ring prims)
    (i : Fin ringDegree) :
    Pr[ coordinateDecodeFailureEvent ring
          (Concrete.concreteEncoding (ParameterSet.params p)) prims i
      | honestNoiseSample ] ≤
      (decodeFailureMass p : ℝ≥0∞) / (2 * noiseDenominator p) := by
  refine le_trans (probEvent_mono''
      (coordinateDecodeFailure_exists_failing_pair p ring prims hRing i))
    (le_trans (probEvent_exists_finset_le_sum _ honestNoiseSample _) ?_)
  refine le_trans (Finset.sum_le_sum fun br hbr =>
      hModel.prob_le_of_decodeFailure i br.1 br.2 (Finset.mem_filter.mp hbr).2)
    (le_of_eq ?_)
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_filter_foldedNoiseMeasure_eq_decodeFailureMass p]

/-- Under the `CoefficientFailureBound` hypothesis, the K-PKE
recovery-failure probability of the honest run is at most the FIPS 203
Table 1 decapsulation-failure bound: the union bound over the `256`
coefficients of the per-coordinate tail, closed by the decode-failure
arithmetic check. -/
theorem underlyingCorrectnessError_le_fips203 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : CoefficientFailureBound p ring prims) :
    underlyingCorrectnessError ring (Concrete.concreteEncoding (ParameterSet.params p)) prims ≤
      fips203DecapsulationFailureBound p := by
  refine le_trans (underlyingCorrectnessError_le_sum_coordinateDecodeFailure ring
    (Concrete.concreteEncoding (ParameterSet.params p)) prims
    (Concrete.fips203EncodingLaws p).laws) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => coordinateTail_le p ring prims hRing hModel i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_div_assoc]
  exact decodeFailureMass_le_fips203Bound p

end MLKEM
