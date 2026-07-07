/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.Reduction
import SecureMessaging.KEM.MLKEM.Correctness.Noise
import SecureMessaging.KEM.MLKEM.Correctness.FailureRates

/-!
# K-PKE recovery failure as a coordinate union bound

This file rewrites the honest K-PKE recovery-failure probability over the exact,
message-dependent decoding event and bounds it by a sum over the `256`
coefficients.

Recovery fails exactly when, on the honest sampling of `(d, z, m)`, some
coefficient of `Compress₁` of the recomputed representative disagrees with the
decoded message (`kpke_decrypt_ne_iff_exists_coordinateDecodeFailure`). A union
bound then bounds the failure probability by the sum of the `256` per-coordinate
decoding-failure probabilities. Each such probability is the honest-sampling
probability that `Compress₁` of the representative disagrees with the decoded bit
at that coordinate, determined by the CBD and compression noise distributions.

The symmetric recovery-radius event is kept as a coarse sufficient condition:
recovery fails only on noise exceeding the radius, so the failure probability is
at most the bad-noise probability. That route is generic and does not feed the
per-coordinate bound.
-/

open OracleComp LatticeCrypto
open scoped ENNReal

namespace MLKEM

section Generic

variable {params : Params}
variable (ring : NTTRingOps) (encoding : Encoding params)
  (prims : Primitives params encoding)

/-- The honest sampling of the key seeds `(d, z)` and message `m` shared by the
correctness and bad-noise experiments. -/
def honestNoiseSample : ProbComp (Seed32 × Seed32 × Message) := do
  let d ← $ᵗ Seed32
  let z ← $ᵗ Seed32
  let m ← $ᵗ Message
  pure (d, z, m)

theorem map_honestNoiseSample {β : Type} (f : Seed32 × Seed32 × Message → β) :
    f <$> honestNoiseSample =
      (do let d ← $ᵗ Seed32; let z ← $ᵗ Seed32; let m ← $ᵗ Message; pure (f (d, z, m))) := by
  simp only [honestNoiseSample, map_bind, map_pure]

/-- The experiment that reports whether the honest run's decryption noise exceeds
the recovery radius. -/
def kpkeBadNoiseExp : ProbComp Bool := do
  let d ← $ᵗ Seed32
  let z ← $ᵗ Seed32
  let m ← $ᵗ Message
  pure (decide (kpkeBadNoise ring encoding prims d z m))

/-- The per-coordinate failure event: coordinate `i` of the decryption noise
exceeds the recovery radius. -/
def coordinateFailureEvent (i : Fin ringDegree) : Seed32 × Seed32 × Message → Prop :=
  fun dzm =>
    messageRecoveryRadius <
      (centeredRepr
        ((kpkeDecryptDifference ring encoding prims dzm.1 dzm.2.1 dzm.2.2).get i)).natAbs

/-- The bad-noise probability rewritten as a `probEvent` over the honest sample. -/
theorem probOutput_true_kpkeBadNoiseExp :
    Pr[= true | kpkeBadNoiseExp ring encoding prims] =
      Pr[ (fun dzm => kpkeBadNoise ring encoding prims dzm.1 dzm.2.1 dzm.2.2)
          | honestNoiseSample ] := by
  have hmap : kpkeBadNoiseExp ring encoding prims =
      (fun dzm => decide (kpkeBadNoise ring encoding prims dzm.1 dzm.2.1 dzm.2.2)) <$>
        honestNoiseSample := by
    rw [map_honestNoiseSample]; simp only [kpkeBadNoiseExp]
  rw [hmap, ← probEvent_true_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]

/-- The recovery-failure probability rewritten as a `probEvent` over the honest sample. -/
theorem underlyingCorrectnessError_eq_probEvent :
    underlyingCorrectnessError ring encoding prims =
      Pr[ (fun dzm => KPKE.decrypt ring encoding prims
              (keygenInternal ring encoding prims dzm.1 dzm.2.1).2.dkPKE
              (encapsInternal ring encoding prims
                (keygenInternal ring encoding prims dzm.1 dzm.2.1).1 dzm.2.2).2 ≠ dzm.2.2)
          | honestNoiseSample ] := by
  have hmap : underlyingCorrectExp ring encoding prims =
      (fun dzm => decide (KPKE.decrypt ring encoding prims
          (keygenInternal ring encoding prims dzm.1 dzm.2.1).2.dkPKE
          (encapsInternal ring encoding prims
            (keygenInternal ring encoding prims dzm.1 dzm.2.1).1 dzm.2.2).2 = dzm.2.2)) <$>
        honestNoiseSample := by
    rw [map_honestNoiseSample]; simp only [underlyingCorrectExp]
  rw [underlyingCorrectnessError, hmap, ← probEvent_not_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_false_iff_not]

/-- Recovery fails only on bad noise, so the recovery-failure probability is at
most the bad-noise probability. -/
theorem underlyingCorrectnessError_le_badNoise (hEnc : FIPS203EncodingLaws encoding) :
    underlyingCorrectnessError ring encoding prims ≤
      Pr[= true | kpkeBadNoiseExp ring encoding prims] := by
  rw [underlyingCorrectnessError_eq_probEvent, probOutput_true_kpkeBadNoiseExp]
  refine probEvent_mono'' fun dzm hfail => ?_
  rw [kpkeBadNoise_iff_not_within]
  exact fun hwithin => hfail
    (kpke_decrypt_eq_of_noiseWithinRecoveryRadius ring encoding prims hEnc _ _ _ hwithin)

/-- The decryption noise exceeds the recovery radius exactly when some coordinate
does. -/
theorem kpkeBadNoise_iff_exists_coordinate (dzm : Seed32 × Seed32 × Message) :
    kpkeBadNoise ring encoding prims dzm.1 dzm.2.1 dzm.2.2 ↔
      ∃ i ∈ Finset.univ, coordinateFailureEvent ring encoding prims i dzm := by
  simp only [kpkeBadNoise, coordinateFailureEvent, Finset.mem_univ, true_and, ← not_le,
    cInfNorm_le_iff, not_forall]

/-- The exact per-coordinate decoding-failure event over the honest sample:
coordinate `i` of `Compress₁` of the recomputed representative disagrees with the
decoded message. -/
def coordinateDecodeFailureEvent (i : Fin ringDegree) :
    Seed32 × Seed32 × Message → Prop :=
  fun dzm => kpkeCoordinateDecodeFailure ring encoding prims dzm.1 dzm.2.1 dzm.2.2 i

/-- The K-PKE recovery-failure probability equals the probability that some one of
the `256` coordinate decoding events holds. -/
theorem underlyingCorrectnessError_eq_coordinateDecodeFailureEvent (hEnc : encoding.Laws) :
    underlyingCorrectnessError ring encoding prims =
      Pr[ (fun dzm => ∃ i : Fin ringDegree,
        coordinateDecodeFailureEvent ring encoding prims i dzm) | honestNoiseSample ] := by
  rw [underlyingCorrectnessError_eq_probEvent]
  have hpred : (fun dzm : Seed32 × Seed32 × Message => KPKE.decrypt ring encoding prims
          (keygenInternal ring encoding prims dzm.1 dzm.2.1).2.dkPKE
          (encapsInternal ring encoding prims
            (keygenInternal ring encoding prims dzm.1 dzm.2.1).1 dzm.2.2).2 ≠ dzm.2.2) =
      (fun dzm => ∃ i : Fin ringDegree,
        coordinateDecodeFailureEvent ring encoding prims i dzm) := by
    funext dzm
    exact propext
      (kpke_decrypt_ne_iff_exists_coordinateDecodeFailure ring encoding prims hEnc _ _ _)
  rw [hpred]

/-- Union bound: the K-PKE recovery-failure probability is at most the sum over the
`256` coefficients of the per-coordinate decoding-failure probabilities. -/
theorem underlyingCorrectnessError_le_sum_coordinateDecodeFailure (hEnc : encoding.Laws) :
    underlyingCorrectnessError ring encoding prims ≤
      ∑ i : Fin ringDegree,
        Pr[ coordinateDecodeFailureEvent ring encoding prims i | honestNoiseSample ] := by
  rw [underlyingCorrectnessError_eq_coordinateDecodeFailureEvent ring encoding prims hEnc]
  have hpred : (fun dzm => ∃ i : Fin ringDegree,
        coordinateDecodeFailureEvent ring encoding prims i dzm) =
      (fun dzm => ∃ i ∈ Finset.univ,
        coordinateDecodeFailureEvent ring encoding prims i dzm) := by
    funext dzm; simp
  rw [hpred]
  exact probEvent_exists_finset_le_sum Finset.univ honestNoiseSample
    (coordinateDecodeFailureEvent ring encoding prims)

end Generic

end MLKEM
