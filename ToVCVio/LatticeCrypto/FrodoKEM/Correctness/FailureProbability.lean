/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Deterministic
import VCVio.EvalDist.ProbabilityBounds

/-!
# FrodoKEM honest failure containment

Honest decapsulation failure is contained in the residual-noise bad event under the actual
joint distribution of key generation and encapsulation coins. This result preserves the
dependencies introduced by seed derivation and assumes no sampling property of SHAKE.
-/

namespace FrodoKEM.KEM

open OracleComp
open scoped ENNReal

/-- The probability that honestly generated keys and encapsulation disagree on the shared key. -/
noncomputable def honestFailureProb {ps : ParameterSet}
    (ops : Operations ps) : ℝ≥0∞ :=
  Pr{let keys ← keygen ops; let out ← encaps ops keys.1}[
    decaps ops keys.2 out.1 ≠ out.2]

/-- Residual-noise failure with the sampling seeds derived by the actual KEM operations. -/
noncomputable def honestNoiseBadProb {ps : ParameterSet}
    (ops : Operations ps) : ℝ≥0∞ :=
  Pr{
    let fallback ← $ᵗ (SharedSecretBits ps)
    let keySeed ← $ᵗ (SeedSEBits ps)
    let z ← $ᵗ (Bits lenZ)
    let message ← $ᵗ (MessageBits ps)
    let salt ← $ᵗ (SaltBits ps)
  }[
    ¬ NoiseBound ps.params
      (PKE.decryptionNoise ops keySeed
        (deriveSeedAndKey ops
          (hashPublicKey ops (keygenFromCoins ops fallback keySeed z).1)
          message salt).1)
  ]

/-- The actual honest KEM failure probability is bounded by its joint residual-noise event. -/
theorem honestFailureProb_le_honestNoiseBadProb
    {ps : ParameterSet} (ops : Operations ps) :
    honestFailureProb ops ≤ honestNoiseBadProb ops := by
  classical
  simp only [honestFailureProb, honestNoiseBadProb, keygen_eq, encaps_eq, monad_norm]
  refine prEvent_bind_mono_of_support _ _ _ fun fallback _ =>
    prEvent_bind_mono_of_support _ _ _ fun keySeed _ =>
    prEvent_bind_mono_of_support _ _ _ fun z _ =>
    prEvent_bind_mono_of_support _ _ _ fun message _ =>
    prEvent_bind_mono_of_support _ _ _ fun salt _ => ?_
  apply prEvent_pure_mono
  intro hfailure hnoise
  exact hfailure (decaps_encapsFromCoins_of_noiseBound ops fallback keySeed z message salt hnoise)

end FrodoKEM.KEM
