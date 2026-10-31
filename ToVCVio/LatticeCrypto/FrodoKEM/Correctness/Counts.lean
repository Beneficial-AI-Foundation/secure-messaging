/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Parameters
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.ScalarNoise

/-!
# Exact noise counts for FrodoKEM

Applies the general result of `Certificate/ScalarNoise.lean` to FrodoKEM's error sampler,
giving the exact distribution of one entry of the decryption noise.
-/

namespace FrodoKEM.Certificate

open OracleComp
open scoped BigOperators ENNReal

private theorem counts_apply (ps : ParameterSet) (z : ℤ) :
    FailureCertificate.RoundedConvolution.counts (config ps) z = noiseCount ps z := by
  classical
  by_cases hz : z ∈ Finset.Icc (-(ps.errorTable.d : ℤ)) (ps.errorTable.d : ℤ)
  · rw [FailureCertificate.RoundedConvolution.counts_apply_of_mem (config ps) z hz]
    rfl
  · have hzero : noiseCount ps z = 0 := by
      have hn : ¬ z.natAbs ≤ ps.errorTable.d := by
        simp only [Finset.mem_Icc] at hz
        cases z <;> simp_all; omega
      simp [noiseCount, hn]
    rw [hzero, FailureCertificate.RoundedConvolution.counts_apply_of_not_mem (config ps) z hz]

/-- The error-sampler counts add up to `2 ^ 16`, one for each 16-bit input. -/
theorem counts_totalMass (ps : ParameterSet) :
    ToVCVio.totalMass
      (FailureCertificate.RoundedConvolution.counts (config ps)) = 2 ^ lenChi := by
  change ToVCVio.totalMassHom
      (∑ z ∈ Finset.Icc (-(ps.errorTable.d : ℤ)) (ps.errorTable.d : ℤ),
        AddMonoidAlgebra.single z (noiseCount ps z)) = 2 ^ lenChi
  rw [map_sum]
  have hsingle (z : ℤ) (m : ℕ) :
      ToVCVio.totalMassHom (AddMonoidAlgebra.single z m) = m :=
    ToVCVio.totalMass_single z m
  simp_rw [hsingle]
  cases ps <;> decide

/-- One noise entry is distributed as a sum of `2n` products of two errors and one more error. -/
theorem probOutput_entryNoiseExp (ps : ParameterSet) (z : ℤ) :
    Pr{let x ← Ideal.entryNoiseExp ps}[x = z] =
      (((ToVCVio.productMeasure
          (FailureCertificate.RoundedConvolution.counts (config ps))
          (FailureCertificate.RoundedConvolution.counts (config ps))) ^
          (2 * ps.params.n) *
        FailureCertificate.RoundedConvolution.counts (config ps)) z :
          ℝ≥0∞) /
        (2 ^ lenChi) ^ (4 * ps.params.n + 1) := by
  have hlaw (u : ℤ) :
      Pr{let x ← sampleError ps}[x = u] =
        (FailureCertificate.RoundedConvolution.counts (config ps) u : ℝ≥0∞) /
          2 ^ lenChi := by
    rw [counts_apply, probOutput_sampleError]
  exact ToVCVio.Probability.ScalarNoise.probOutput_entryNoiseIntExp_counts
    (config ps) (sampleError ps) hlaw (noiseCount_neg ps) ps.params.n z

end FrodoKEM.Certificate
