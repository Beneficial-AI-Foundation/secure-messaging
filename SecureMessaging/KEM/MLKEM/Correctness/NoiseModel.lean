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
# The FIPS 203 noise model and the failure-probability bridge

FIPS 203 Section 3.2 takes the decapsulation-failure probability over uniformly
random seeds `d`, `z` and message `m`, under the heuristic assumption that hash
functions and XOFs behave like uniformly random functions. This file states
that heuristic as `FIPS203NoiseModel`: at every coefficient, the decoded
message bit and the coefficient of the decryption noise form an independent
pair of a uniform bit and a draw from the folded coefficient-noise measure. The
model is a hypothesis on the primitive bundle; nothing here proves it.

Under the model, the exact per-coordinate decoding-failure probability is at
most the bit-averaged decode-failure mass (`coordinateTail_le`), so the union
bound over the `256` coefficients and the Table 1 arithmetic check close
the chain: the K-PKE recovery-failure probability of the honest run is at most
the FIPS 203 decapsulation-failure bound
(`underlyingCorrectnessError_le_fips203`).

The decryption noise enters through `kpkeHonestNoise`, the expansion
`eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u` of `w − μ` given by the decryption-noise
identity; it does not depend on the implicit-rejection seed `z`.
-/

open OracleComp LatticeCrypto
open scoped ENNReal

namespace MLKEM

/-- The decryption noise of the honest run from key seed `d` and message `m`:
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

/-- The folded coefficient-noise measure carries the full mass of the integer
measure: its values over `ZMod q` sum to the noise denominator.

This is a total-mass statement, not a claim that `foldedNoiseMeasure p` already
has total mass `1`. The normalized residue distribution is

`r ↦ foldedNoiseMeasure p r / noiseDenominator p`.

Since the decoded coefficient is always a bit, the joint probabilities in
`FIPS203NoiseModel.coordinateDistribution` divide by
`2 * noiseDenominator p`; summing over the two bits and all residues gives `1`.
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

/-- The FIPS 203 random-function heuristic, instantiated for the honest run at
the concrete encoding. Section 3.2 takes the decapsulation-failure probability
over uniformly random seeds `d`, `z` and message `m`, under the heuristic
assumption that hash functions and XOFs behave like uniformly random
functions. The standard's failure-rate computation accordingly treats each
coefficient of the decryption noise as a draw from the composed
coefficient-noise measure, independent of the uniform encoded message bit.

`coordinateDistribution` states the joint distribution at each coordinate: every
outcome `(bit, residue)` has probability
`foldedNoiseMeasure p r / (2 * noiseDenominator p)`. The decoded coefficient is
always a bit (`Concrete.byteDecode1_get_val_lt_two`) and the stated
probabilities sum to `1` (`sum_foldedNoiseMeasure`), so one probability for each
pair `(bit, residue)` describes the whole joint distribution. This structure is
an assumption on `ring` and `prims`; the correctness theorems consume it as a
hypothesis, and nothing proves it. -/
structure FIPS203NoiseModel (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) : Prop where
  /-- The joint distribution of the decoded message coefficient and the coefficient of
  the decryption noise at coordinate `i`: a uniform bit, independent of a draw
  from the folded coefficient-noise measure. -/
  coordinateDistribution : ∀ (i : Fin ringDegree) (b : Fin 2) (r : Coeff),
    Pr[ fun dzm : Seed32 × Seed32 × Message =>
        ((Concrete.concreteEncoding (ParameterSet.params p)).byteDecode1 dzm.2.2).get i =
            ((b : ℕ) : Coeff) ∧
          (kpkeHonestNoise ring prims dzm.1 dzm.2.2).get i = r
      | honestNoiseSample ]
      = (foldedNoiseMeasure p r : ℝ≥0∞) / (2 * noiseDenominator p)

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
failing `(bit, residue)` pair whose cell the honest run lands in. The decoded
coefficient is `0` or `1`, so a concrete bit witness closes each case. -/
private theorem coordinateDecodeFailure_exists_failing_cell (p : ParameterSet) (ring : NTTRingOps)
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

/-- Under the noise model, the probability of the exact per-coordinate decoding
failure is at most the bit-averaged decode-failure mass of the folded
coefficient-noise measure. -/
theorem coordinateTail_le (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : FIPS203NoiseModel p ring prims)
    (i : Fin ringDegree) :
    Pr[ coordinateDecodeFailureEvent ring
          (Concrete.concreteEncoding (ParameterSet.params p)) prims i
      | honestNoiseSample ] ≤
      (decodeFailureMass p : ℝ≥0∞) / (2 * noiseDenominator p) := by
  refine le_trans (probEvent_mono''
      (coordinateDecodeFailure_exists_failing_cell p ring prims hRing i))
    (le_trans (probEvent_exists_finset_le_sum _ honestNoiseSample _) ?_)
  refine le_of_eq
    ((Finset.sum_congr rfl fun br _ => hModel.coordinateDistribution i br.1 br.2).trans ?_)
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_filter_foldedNoiseMeasure_eq_decodeFailureMass p]

/-- Under the noise model, the K-PKE recovery-failure probability of the honest
run is at most the FIPS 203 Table 1 decapsulation-failure bound: the union
bound over the `256` coefficients of the per-coordinate tail, closed by the
decode-failure arithmetic check. -/
theorem underlyingCorrectnessError_le_fips203 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : FIPS203NoiseModel p ring prims) :
    underlyingCorrectnessError ring (Concrete.concreteEncoding (ParameterSet.params p)) prims ≤
      fips203DecapsulationFailureBound p := by
  refine le_trans (underlyingCorrectnessError_le_sum_coordinateDecodeFailure ring
    (Concrete.concreteEncoding (ParameterSet.params p)) prims
    (Concrete.fips203EncodingLaws p).laws) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => coordinateTail_le p ring prims hRing hModel i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_div_assoc]
  exact decodeFailureMass_le_fips203Bound p

end MLKEM
