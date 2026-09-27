/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.OracleComp.EvalDist

/-!
# KEM advantage normalization

For a KEM adversary `B`, let `p_b` be its probability of returning `true`
in the fixed-bit IND-CPA experiment with bit `b` (`true` selects the real key).
The library's sampled-bit bias equals `|p_true - p_false|`; a guessing
advantage measured relative to one half is half this quantity.

This identity applies to every KEM over `ProbComp`, independently of any
protocol, correctness assumption, or challenge embedding.
-/

open ToVCVio OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {K PK SK C : Type}

/-- Data produced by the IND-CPA experiment before the challenge bit is used:
the reduction's paused state, the challenge ciphertext, and the real and
random candidate keys. -/
private structure INDCPAPrefixState
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) where
  st : red.State
  cStar : C
  kReal : K
  kRand : K

/-- The bit-independent prefix of the IND-CPA experiment: key generation, the
reduction's pre-challenge phase, encapsulation, and the random key draw. -/
private def indCPAPrefix [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp (INDCPAPrefixState kem red) := do
  let (pk, _sk) ← kem.keygen
  let st ← red.preChallenge pk
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  pure { st := st, cStar := cStar, kReal := kReal, kRand := kRand }

/-- The IND-CPA experiment with a fixed challenge bit, phrased over
`indCPAPrefix`. -/
private def indCPAExpProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) (b : Bool) : ProbComp Bool := do
  let p ← indCPAPrefix kem red
  red.postChallenge p.st p.cStar (if b then p.kReal else p.kRand)


/-- The game underlying VCVio's `IND_CPA_Advantage`, spelled out: sample the
challenge bit inside the game and compare it with the reduction's guess.
Definitionally equal to the library's game. -/
private def indCPAGameProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let (pk, _sk) ← kem.keygen
  let st ← red.preChallenge pk
  let b ← ($ᵗ Bool)
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  let b' ← red.postChallenge st cStar (if b then kReal else kRand)
  return (b == b')

/-- `indCPAGameProb` with the bit-independent prefix hoisted before the bit
draw, the bridge between the sampled-bit game and the fixed-bit branches. -/
private def indCPABranchGameProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let p ← indCPAPrefix kem red
  let b ← ($ᵗ Bool)
  let z ← if b then red.postChallenge p.st p.cStar p.kReal
          else red.postChallenge p.st p.cStar p.kRand
  pure (b == z)

/-- Hoisting the prefix past the bit draw does not change the game's output
distribution: the bit is independent of the prefix samples. -/
private lemma indCPAGameProb_evalDist_eq_branch [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) :
    𝒟[indCPAGameProb kem red] = 𝒟[indCPABranchGameProb kem red] := by
  apply evalDist_ext
  intro x
  unfold indCPAGameProb indCPABranchGameProb indCPAPrefix
  simp only [monad_norm]
  refine probOutput_bind_congr' kem.keygen x ?_
  intro pk_sk
  refine probOutput_bind_congr' (red.preChallenge pk_sk.1) x ?_
  intro st
  rw [probOutput_bind_bind_swap ($ᵗ Bool) (kem.encaps pk_sk.1)
    (fun b ck => do
      let kRand ← ($ᵗ K)
      let b' ← red.postChallenge st ck.1 (if b then ck.2 else kRand)
      pure (b == b')) x]
  refine probOutput_bind_congr' (kem.encaps pk_sk.1) x ?_
  intro ck
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ K)
    (fun b kRand => do
      let b' ← red.postChallenge st ck.1 (if b then ck.2 else kRand)
      pure (b == b')) x]
  refine probOutput_bind_congr' ($ᵗ K) x ?_
  intro kRand
  refine probOutput_bind_congr' ($ᵗ Bool) x ?_
  intro b
  cases b <;> rfl

/-- The sampled-bit bias advantage of the IND-CPA game equals the
distinguishing advantage of its two fixed-bit experiments. -/
private lemma indCPAGameProb_advantage_eq_fixed_dist [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) :
    (indCPAGameProb kem red).boolBiasAdvantage =
      (indCPAExpProb kem red true).boolDistAdvantage
        (indCPAExpProb kem red false) := by
  rw [show (indCPAGameProb kem red).boolBiasAdvantage =
      (indCPABranchGameProb kem red).boolBiasAdvantage by
    unfold ProbComp.boolBiasAdvantage
    rw [evalDist_ext_iff.mp (indCPAGameProb_evalDist_eq_branch kem red) true]
    rw [evalDist_ext_iff.mp (indCPAGameProb_evalDist_eq_branch kem red) false]]
  simpa [indCPABranchGameProb, indCPAExpProb] using
    ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage
      (indCPAPrefix kem red)
      (fun p => red.postChallenge p.st p.cStar p.kReal)
      (fun p => red.postChallenge p.st p.cStar p.kRand)

/-- The local fixed-bit experiment matches the library's `IND_CPA_Exp` on
`true`-output probability. -/
private lemma indCPAExpProb_probOutput_true_eq [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) (b : Bool) :
    Pr[= true | indCPAExpProb kem red b] =
      Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red b] := by
  unfold KEMScheme.IND_CPA_Exp
  rw [probOutput_probCompRuntime_evalDist_eq]
  cases b <;>
    simp [indCPAExpProb, indCPAPrefix,
      ProbCompRuntime.probComp, ProbCompRuntime.liftProbComp, ProbCompLift.id,
      monad_norm]


/-- VCVio's `IND_CPA_Advantage` equals the absolute `true`-output gap of the
two fixed-bit `IND_CPA_Exp` runs: split the sampled bit into its two branches
and normalize the bias to a distinguishing gap. -/
theorem IND_CPA_Advantage_eq_fixed_branch_dist [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Advantage ProbCompRuntime.probComp red =
      |(Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red true]).toReal -
        (Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red false]).toReal| := by
  rw [show kem.IND_CPA_Advantage ProbCompRuntime.probComp red =
      (indCPAGameProb kem red).boolBiasAdvantage by rfl]
  rw [indCPAGameProb_advantage_eq_fixed_dist]
  unfold ProbComp.boolDistAdvantage
  rw [indCPAExpProb_probOutput_true_eq kem red true]
  rw [indCPAExpProb_probOutput_true_eq kem red false]

end KEMScheme
