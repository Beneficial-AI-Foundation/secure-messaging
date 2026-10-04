/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import ToVCVio.EvalDist.Monad.Basic

/-!
# Real-valued DDH guess advantage

VCVio #806 replaced `DiffieHellman.ddhGuessAdvantage : ℝ` by the `ℝ≥0∞` Boolean bias of
`ddhGame`. The CKA-from-DDH bound is still stated in `ℝ`, so the real form and its
two-branch decomposition `ddhGame_probOutput_sub_half` are kept here until that bound moves to
`ℝ≥0∞`.
-/

open OracleComp ENNReal

namespace DiffieHellman

variable {F : Type} [Field F] {G : Type} [AddCommGroup G] [Module F G] [SampleableType F]

/-- DDH guess advantage: the absolute distance of the DDH game's success probability from `1/2`.
Uses `ℝ` with absolute value rather than `ℝ≥0∞` subtraction, which would saturate at zero for
adversaries that guess the wrong bit more often than not. -/
noncomputable def ddhGuessAdvantage (g : G) (adversary : DDHAdversary F G) : ℝ :=
  |(Pr[= true | ddhGame g adversary]).toReal - 1 / 2|

/-- The single-game DDH experiment is a uniform-bit branch over the real and random DDH
experiments. -/
private lemma ddhGame_probOutput_eq_branch (g : G) (adversary : DDHAdversary F G) :
    Pr[= true | ddhGame g adversary] =
    Pr[= true | do
      let bit ← ($ᵗ Bool)
      let z ← if bit then ddhRealExperiment g adversary
               else ddhRandomExperiment g adversary
      pure (bit == z)] := by
  unfold ddhGame
  rw [probOutput_bind_congr fun a _ => probOutput_bind_bind_swap _ _ _ _,
      probOutput_bind_bind_swap]
  refine probOutput_bind_congr' ($ᵗ Bool) true fun bit => ?_
  cases bit <;> simp [ddhRealExperiment, ddhRandomExperiment]

/-- The single-game DDH decomposes: `Pr[win] - 1/2 = (Pr[real = 1] - Pr[rand = 1]) / 2`. -/
lemma ddhGame_probOutput_sub_half (g : G) (adversary : DDHAdversary F G) :
    (Pr[= true | ddhGame g adversary]).toReal - 1 / 2 =
    ((Pr[= true | ddhRealExperiment g adversary]).toReal -
      (Pr[= true | ddhRandomExperiment g adversary]).toReal) / 2 := by
  rw [ddhGame_probOutput_eq_branch]
  exact ToVCVio.probOutput_uniformBool_branch_toReal_sub_half _ _

end DiffieHellman
