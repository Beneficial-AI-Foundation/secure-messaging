/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Parameters
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.ScalarNoise

/-!
# Exact scalar noise counts for modern FrodoKEM

The generic scalar convolution theorem applies to the independent scalar experiment.
The adapter uses its source distribution and contains no reconciliation data.
-/

namespace FrodoKEM.Certificate

open OracleComp
open scoped BigOperators ENNReal

private theorem counts_apply (ps : ParameterSet) (z : ℤ) :
    FailureCertificate.RoundedConvolution.counts (config ps) z = noiseCount ps z := by
  classical
  by_cases hz : z ∈ Finset.Icc (-(ps.errorTable.d : ℤ)) (ps.errorTable.d : ℤ)
  · rw [FailureCertificate.RoundedConvolution.counts,
      AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single z]
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
      rfl
    · intro y hy hne
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false]
    · exact fun h => (h hz).elim
  · have hzero : noiseCount ps z = 0 := by
      have hn : ¬ z.natAbs ≤ ps.errorTable.d := by
        simp only [Finset.mem_Icc] at hz
        cases z <;> simp_all; omega
      simp [noiseCount, hn]
    rw [hzero, FailureCertificate.RoundedConvolution.counts,
      AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro y hy
    have hne : y ≠ z := fun h => hz (h ▸ hy)
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false]

/-- The modern source count measure has exactly sixteen bits of mass. -/
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

/-- An ideal residual entry has the exact convolution law of `2n` products and one error. -/
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
