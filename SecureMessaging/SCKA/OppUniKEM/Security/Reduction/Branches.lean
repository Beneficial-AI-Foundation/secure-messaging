/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# Fixed-bit KEM branches of the explicit reduction

**Experiments.** For each selected epoch `e` and bit `b`, `fixedBranch`
samples the KEM public key and ciphertext and runs the simulator with the
encapsulated key when `b = true`, or an independent uniform key when
`b = false`. These bits follow the KEM convention.

**Results.** For every SCKA adversary, the branch equals the corresponding
IND-CPA experiment of `epochReduction` on each output probability. The
single reduction `securityReduction` is the mixture of these branches
under `epochChoice q`. Thus its real-minus-random acceptance difference is
the uniformly weighted sum of the per-epoch signed differences for `q > 0`.
-/

open ToVCVio OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
variable (ecEk : ErasureCodePayload PK Sym)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)

/-- For selected epoch `e`, sample an IND-CPA tuple and execute the simulator.
Bit `true` supplies the encapsulated key; bit `false` supplies an independent
uniform key. The output is the simulator's Boolean guess. -/
def fixedBranch (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) : ProbComp Bool := do
  let (pk, _) ← base.keygen
  let (ct, key) ← base.encaps pk
  let randomKey ← ($ᵗ K : ProbComp K)
  run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey)

/-- For every adversary, selected epoch, challenge bit, and Boolean output,
the explicit fixed branch and `epochReduction`'s IND-CPA experiment assign
the same output probability. -/
theorem epochReduction_probOutput
    (adv : SecurityAdversary leak Sym) (e : ℕ) (b output : Bool) :
    Pr[= output | base.IND_CPA_Exp ProbCompRuntime.probComp
      (epochReduction base onoff ecEk ecCt0 ecCt1 leak adv e) b] =
    Pr[= output | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] := by
  unfold KEMScheme.IND_CPA_Exp
  rw [probOutput_probCompRuntime_evalDist_eq]
  simp [epochReduction, fixedBranch, ProbCompRuntime.probComp,
    ProbCompRuntime.liftProbComp, ProbCompLift.id, monad_norm]

/-- For every send budget `q`, challenge bit, and Boolean output, the
single reduction's IND-CPA output probability is the mixture obtained by
sampling `e ← epochChoice q` and running the corresponding fixed branch. -/
theorem securityReduction_probOutput
    (adv : SecurityAdversary leak Sym) (q : ℕ) (b output : Bool) :
    Pr[= output | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) b] =
    Pr[= output | do
      let e ← epochChoice q
      fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] := by
  unfold KEMScheme.IND_CPA_Exp
  rw [probOutput_probCompRuntime_evalDist_eq]
  simp only [securityReduction, fixedBranch, ProbCompRuntime.probComp,
    ProbCompRuntime.liftProbComp, ProbCompLift.id, bind_assoc, pure_bind]
  exact probOutput_bind_bind_swap base.keygen (epochChoice q) _ output

/-- With a positive send budget `q`, the single reduction's fixed-bit
acceptance probability is the arithmetic mean of the `q` selected-epoch
branch acceptance probabilities. -/
theorem securityReduction_acceptance_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) (b : Bool) :
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) b]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv (i.val + 1) b]).toReal := by
  rw [securityReduction_probOutput]
  let : NeZero q := ⟨hq⟩
  simp only [epochChoice, hq, ↓reduceDIte, bind_map_left, probOutput_bind_eq_sum_fintype,
    probOutput_uniformSample, Fintype.card_fin, ← Finset.mul_sum]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ => probOutput_ne_top)]

/-- With `q > 0`, the single reduction's real-minus-random acceptance gap
is `1/q` times the sum of its selected-epoch real-minus-random gaps.
The signed sum retains cancellation between different epochs. -/
-- ANCHOR: securityReduction_signed_gap_average
theorem securityReduction_signed_gap_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) :
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) true]).toReal -
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) false]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      ((Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) true]).toReal -
       (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) false]).toReal) := by
  rw [securityReduction_acceptance_average base onoff ecEk ecCt0 ecCt1 leak adv q hq true,
    securityReduction_acceptance_average base onoff ecEk ecCt0 ecCt1 leak adv q hq false,
    Finset.sum_sub_distrib, mul_sub]
-- ANCHOR_END: securityReduction_signed_gap_average

end oppUniKemCKA.Security.Embedding
