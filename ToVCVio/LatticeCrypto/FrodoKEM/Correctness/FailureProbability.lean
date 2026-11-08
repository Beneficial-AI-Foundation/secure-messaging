/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Deterministic

/-!
# FrodoKEM failure from large noise

Honest decapsulation fails only if the decryption noise is too large, so the failure
probability is at most the probability of large noise. The seeds are derived exactly as the
KEM derives them, and no property of SHAKE is assumed.
-/

@[expose] public section

namespace FrodoKEM.KEM

open OracleComp
open scoped ENNReal

/-- The probability that honestly generated keys and encapsulation disagree on the shared key. -/
noncomputable def honestFailureProb {ps : ParameterSet}
    (ops : Operations ps) : ℝ≥0∞ :=
  Pr{let keys ← keygen ops; let out ← encaps ops keys.1}[
    decaps ops keys.2 out.1 ≠ out.2]

/-- The probability of large decryption noise, with seeds derived as the KEM derives them. -/
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

/-- Honest KEM failure is at most as likely as large decryption noise. -/
-- ANCHOR: frodoKEM_failure_le_noise
theorem honestFailureProb_le_honestNoiseBadProb
    {ps : ParameterSet} (ops : Operations ps) :
    honestFailureProb ops ≤ honestNoiseBadProb ops
-- ANCHOR_END: frodoKEM_failure_le_noise
    := by
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
