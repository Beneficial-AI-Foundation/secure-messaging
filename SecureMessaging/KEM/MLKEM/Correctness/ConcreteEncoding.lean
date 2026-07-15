/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.MLKEM.Concrete.Encoding
import SecureMessaging.KEM.MLKEM.Correctness.Noise

/-!
# Concrete `Compress₁` recovery at the message-recovery radius

For the concrete ML-KEM encoding over `q = 3329`, a coefficient within
`messageRecoveryRadius = ⌊q/4⌋ - 1 = 831` of `Decompress₁ b` for a bit `b` is
read back as `b` by `Compress₁`. Decoding is asymmetric at the positive boundary,
where `Decompress₁(1) = 1665 = ⌈q/2⌉` rather than `q/2`, so the radius is sharp:
recovery already fails at distance `832` for the bit `1`.

The scalar recovery fact lifts coefficientwise to the polynomial theorem
`compress1_recovery`, and `fips203EncodingLaws` combines it with the abstract
round-trip identities to show the concrete encoding satisfies `FIPS203EncodingLaws` for
every parameter set.
-/

open LatticeCrypto MLKEM

namespace MLKEM.Concrete

/-- The value of `Compress₁` as an integer:
`Compress₁(x) = ⌊(2·x + ⌊q/2⌋)/q⌋ mod 2`. -/
private theorem compress1_val (x : Coeff) :
    (compress 1 x).val = ((x.val * 2 + 1664) / 3329) % 2 := by
  have hrw : compress 1 x = ((((x.val * 2 + 1664) / 3329) % 2 : ℕ) : Coeff) := rfl
  rw [hrw, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by decide))

/-- `Compress₁` recovers the decoded bit `b` from any coefficient `w` whose centered
distance to `Decompress₁ b` is within the recovery radius. The two decoded values
`b ∈ {0, 1}` are the only ones reached by `ByteDecode₁`. -/
theorem compress1_recovers_decoded_bit_of_centered_distance_le (b w : Coeff) (hb : b.val < 2)
    (h : (centeredRepr (w - decompress 1 b)).natAbs ≤ messageRecoveryRadius) :
    compress 1 w = b := by
  obtain ⟨e, rfl⟩ : ∃ e, w = decompress 1 b + e := ⟨w - decompress 1 b, by ring⟩
  rw [show decompress 1 b + e - decompress 1 b = e from by ring,
      MLKEM.messageRecoveryRadius_eq] at h
  have hev : e.val < 3329 := by have := ZMod.val_lt e; simpa [modulus] using this
  have hdisj : e.val ≤ 831 ∨ 2498 ≤ e.val := by
    have h' := h
    rw [centeredRepr, show ((modulus : ℕ) : ℤ) = 3329 from rfl] at h'
    split_ifs at h' with hc <;> omega
  have hb2 : b = 0 ∨ b = 1 := by
    rcases (show b.val = 0 ∨ b.val = 1 from by omega) with hh | hh
    · left;  rw [← ZMod.natCast_zmod_val b, hh]; simp
    · right; rw [← ZMod.natCast_zmod_val b, hh]; simp
  rcases hb2 with rfl | rfl
  · rw [show decompress 1 (0 : Coeff) = (0 : Coeff) from by decide, zero_add]
    apply ZMod.val_injective modulus
    rw [compress1_val, show (0 : Coeff).val = 0 from by decide]
    omega
  · rw [show decompress 1 (1 : Coeff) = (1665 : Coeff) from by decide]
    apply ZMod.val_injective modulus
    rw [compress1_val, show (1 : Coeff).val = 1 from by decide]
    have hadd : ((1665 : Coeff) + e).val = (1665 + e.val) % 3329 := by
      rw [ZMod.val_add, show (1665 : Coeff).val = 1665 from by decide]; rfl
    rw [hadd]
    omega

/-- The recovery radius is sharp: at one step beyond it, recovery is not uniform over
both decoded bits. The bit `1` already decodes wrongly at distance `832`, since
`Compress₁(Decompress₁(1) + 832) = Compress₁(2497) = 0`. -/
theorem messageRecoveryRadius_succ_not_uniform :
    ¬ ∀ (b w : Coeff), b.val < 2 →
      (centeredRepr (w - decompress 1 b)).natAbs ≤ messageRecoveryRadius + 1 →
      compress 1 w = b := by
  intro hall
  exact absurd (hall 1 2497 (by decide) (by decide)) (by decide)

/-- Coordinate `i` of `compressPoly d f` is `compress d` applied to coordinate `i`
of `f`, since `compressPoly` acts coefficientwise. -/
private theorem compressPoly_get (d : Nat) (f : Rq) (i : Fin ringDegree) :
    (compressPoly d f).get i = compress d (f.get i) := by
  change (compressPoly d f)[i.val] = compress d (f[i.val])
  unfold compressPoly
  exact Vector.getElem_map (f := compress d) (xs := f) i.isLt

/-- Coordinate `i` of `decompressPoly d f` is `decompress d` applied to coordinate
`i` of `f`, since `decompressPoly` acts coefficientwise. -/
private theorem decompressPoly_get (d : Nat) (f : Rq) (i : Fin ringDegree) :
    (decompressPoly d f).get i = decompress d (f.get i) := by
  change (decompressPoly d f)[i.val] = decompress d (f[i.val])
  unfold decompressPoly
  exact Vector.getElem_map (f := decompress d) (xs := f) i.isLt

/-- Polynomial `Compress₁` recovery for the concrete encoding: if the centered
infinity norm of `w - Decompress₁(ByteDecode₁ m)` is within the message-recovery
radius, then `Compress₁ w` reads back the decoded message `ByteDecode₁ m`. The
coefficientwise lift of `compress1_recovers_decoded_bit_of_centered_distance_le`,
whose per-coordinate bit hypothesis is discharged by `byteDecode1_get_val_lt_two`. -/
theorem compress1_recovery (params : Params) (w : Rq) (m : Message)
    (h : cInfNorm
      (w - (concreteEncoding params).decompress1
        ((concreteEncoding params).byteDecode1 m))
        ≤ messageRecoveryRadius) :
    (concreteEncoding params).compress1 w =
      (concreteEncoding params).byteDecode1 m := by
  refine Poly.ext_get_eq fun i => ?_
  have hcoord := cInfNorm_le_iff.mp h i
  have hsub : (w - (concreteEncoding params).decompress1
        ((concreteEncoding params).byteDecode1 m)).get i
      = w.get i - ((concreteEncoding params).decompress1
        ((concreteEncoding params).byteDecode1 m)).get i := by
    simpa [vectorBackend_coeff] using
      vectorBackend_sub_coeff w ((concreteEncoding params).decompress1
        ((concreteEncoding params).byteDecode1 m)) i
  have hdec : ((concreteEncoding params).decompress1
        ((concreteEncoding params).byteDecode1 m)).get i
      = decompress 1 (((concreteEncoding params).byteDecode1 m).get i) :=
    decompressPoly_get 1 ((concreteEncoding params).byteDecode1 m) i
  have hcomp : ((concreteEncoding params).compress1 w).get i = compress 1 (w.get i) :=
    compressPoly_get 1 w i
  rw [hsub, hdec] at hcoord
  rw [hcomp]
  exact compress1_recovers_decoded_bit_of_centered_distance_le _ _
    (byteDecode1_get_val_lt_two params m i) hcoord

/-- The concrete ML-KEM encoding satisfies `FIPS203EncodingLaws` for every parameter
set: the required round-trip identities hold, and `Compress₁` recovers the message within
the recovery radius. -/
theorem fips203EncodingLaws (p : ParameterSet) :
    FIPS203EncodingLaws (concreteEncoding (ParameterSet.params p)) where
  laws := by
    cases p <;> exact concreteEncodingLaws _ (by decide) (by decide) (by decide) (by decide)
  compress1_recovery := compress1_recovery (ParameterSet.params p)

end MLKEM.Concrete
