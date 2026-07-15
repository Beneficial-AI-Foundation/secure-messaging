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
bound then bounds the failure probability by the sum of the `256`
per-coordinate decoding-failure probabilities.  Each summand is still a
probability in the honest `(d,z,m)` experiment.  `NoiseModel.lean` states the
separate comparison that bounds these summands by an explicitly constructed
independent coefficient measure.

The symmetric recovery-radius proposition gives a second, coarser implication:
recovery failure implies that the noise exceeds the safe radius.  The exact
coordinate event is the one used in the numerical proof.
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
exceeds the recovery radius in the honest sample `(d, z, m)`. -/
def coordinateFailureEvent (i : Fin ringDegree) : Seed32 × Seed32 × Message → Prop :=
  fun (d, z, m) =>
    messageRecoveryRadius <
      (centeredRepr
        ((kpkeDecryptDifference ring encoding prims d z m).get i)).natAbs

/-- The bad-noise probability rewritten as a `probEvent` over the honest sample. -/
theorem probOutput_true_kpkeBadNoiseExp :
    Pr[= true | kpkeBadNoiseExp ring encoding prims] =
      Pr[ (fun (d, z, m) => kpkeBadNoise ring encoding prims d z m)
          | honestNoiseSample ] := by
  have hmap : kpkeBadNoiseExp ring encoding prims =
      (fun (d, z, m) => decide (kpkeBadNoise ring encoding prims d z m)) <$>
        honestNoiseSample := by
    rw [map_honestNoiseSample]; simp only [kpkeBadNoiseExp]
  rw [hmap, ← probEvent_true_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]

/-- The recovery-failure probability rewritten as a `probEvent` over the honest sample. -/
theorem underlyingCorrectnessError_eq_probEvent :
    underlyingCorrectnessError ring encoding prims =
      Pr[ (fun (d, z, m) => KPKE.decrypt ring encoding prims
              (keygenInternal ring encoding prims d z).2.dkPKE
              (encapsInternal ring encoding prims
                (keygenInternal ring encoding prims d z).1 m).2 ≠ m)
          | honestNoiseSample ] := by
  have hmap : underlyingCorrectExp ring encoding prims =
      (fun (d, z, m) => decide (KPKE.decrypt ring encoding prims
          (keygenInternal ring encoding prims d z).2.dkPKE
          (encapsInternal ring encoding prims
            (keygenInternal ring encoding prims d z).1 m).2 = m)) <$>
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
  refine probEvent_mono'' ?_
  rintro ⟨d, z, m⟩ hfail
  change kpkeBadNoise ring encoding prims d z m
  rw [kpkeBadNoise_iff_not_within]
  exact fun hwithin => hfail
    (kpke_decrypt_eq_of_noiseWithinRecoveryRadius ring encoding prims hEnc d z m hwithin)

/-- The decryption noise exceeds the recovery radius exactly when some coordinate
does in the honest sample `(d, z, m)`. -/
theorem kpkeBadNoise_iff_exists_coordinate (d z : Seed32) (m : Message) :
    kpkeBadNoise ring encoding prims d z m ↔
      ∃ i ∈ Finset.univ, coordinateFailureEvent ring encoding prims i (d, z, m) := by
  simp only [kpkeBadNoise, coordinateFailureEvent, Finset.mem_univ, true_and, ← not_le,
    cInfNorm_le_iff, not_forall]

/-- The exact per-coordinate decoding-failure event over the honest sample:
coordinate `i` of `Compress₁` of the recomputed representative disagrees with the
decoded message. -/
def coordinateDecodeFailureEvent (i : Fin ringDegree) :
    Seed32 × Seed32 × Message → Prop :=
  fun (d, z, m) => kpkeCoordinateDecodeFailure ring encoding prims d z m i

/-- The K-PKE recovery-failure probability equals the probability that some one of
the `256` coordinate decoding events holds. -/
theorem underlyingCorrectnessError_eq_coordinateDecodeFailureEvent (hEnc : encoding.Laws) :
    underlyingCorrectnessError ring encoding prims =
      Pr[ (fun dzm => ∃ i : Fin ringDegree,
        coordinateDecodeFailureEvent ring encoding prims i dzm) | honestNoiseSample ] := by
  rw [underlyingCorrectnessError_eq_probEvent]
  have hpred : (fun (d, z, m) => KPKE.decrypt ring encoding prims
          (keygenInternal ring encoding prims d z).2.dkPKE
          (encapsInternal ring encoding prims (keygenInternal ring encoding prims d z).1 m).2 ≠ m) =
      (fun dzm => ∃ i : Fin ringDegree,
        coordinateDecodeFailureEvent ring encoding prims i dzm) := by
    funext dzm
    rcases dzm with ⟨d, z, m⟩
    exact propext
      (kpke_decrypt_ne_iff_exists_coordinateDecodeFailure ring encoding prims hEnc d z m)
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
