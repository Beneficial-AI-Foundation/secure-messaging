/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.OracleComp.EvalDist

/-!
# Two definitions of KEM IND-CPA advantage

The normalized guessing advantage `Adv_guess` is twice the absolute deviation
from `1/2` of the probability of an adversary correctly guessing whether a
challenge key is real or random.

The distinguishing advantage `Adv_dist` is the absolute difference between
the probabilities that the same adversary outputs `true` in the real-key
and random-key experiments.

For every KEM and every IND-CPA adversary against it, these two advantages are equal.

**Setting.** Let

- `kem : KEMScheme ProbComp K PK SK C` be a randomized KEM with shared-key
  space `K`, public-key space `PK`, secret-key space `SK`, and ciphertext
  space `C`. Assume `[SampleableType K]`: its shared-key space is finite and
  nonempty, and `$ᵗ K` samples each key with probability `1 / |K|` to supply
  the independent replacement key in the random-key experiment;
- `adv : kem.IND_CPA_Adversary` be a two-phase IND-CPA adversary against `kem`.

**Fixed-bit experiments.** For each `b : Bool`, let `G_b` be the experiment that:

1. Samples `(pk, sk) ← kem.keygen` and `st ← adv.preChallenge pk`.
2. Samples `(c, k) ← kem.encaps pk` and `u ← $ᵗ K` independently.
3. Returns `adv.postChallenge st c k*`, where `k* = k` if `b = true`, and `k* = u` otherwise.

The pair `(c, k*)` is the IND-CPA challenge.

In Lean, this experiment is written as `G_b := kem.IND_CPA_Exp ProbCompRuntime.probComp adv b`.

For each `b : Bool`,
let `p_b := Pr[G_b = true]` be the probability that `adv` outputs `true`.

The distinguishing advantage of `adv` against `kem` is defined as
`Adv_dist := |p_true - p_false|`.

**Guessing game.** Let `H` be the experiment that:

1. Samples a uniform bit `b`, hidden from `adv`.
2. Runs `G_b`, obtaining the adversary's guess `b'`.
3. Returns `true` exactly when `b' = b`.

Let `w := Pr[H = true]` be the probability of a correct guess.

The normalized guessing advantage of `adv` against `kem` is defined as
`Adv_guess := |2w - 1| = 2 |w - 1/2|`.

**Theorem.** For every `kem` and `adv` satisfying the assumptions above,
`Adv_guess = Adv_dist`, equivalently `2 |w - 1/2| = |p_true - p_false|`.

The Lean theorem `IND_CPA_Advantage_eq_fixed_branch_dist` proves this equality,
with `kem.IND_CPA_Advantage ProbCompRuntime.probComp adv` denoting `Adv_guess`.

-/

open ToVCVio OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {K PK SK C : Type}

/-- Data shared by the two fixed-bit experiments of `adv` against `kem`: the state `st`
returned by `adv.preChallenge pk`, the encapsulation ciphertext `cStar` with its shared key
`kReal`, and the independent uniform key `kRand` of the random-key experiment. -/
private structure INDCPAPrefixState
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) where
  st : adv.State
  cStar : C
  kReal : K
  kRand : K

/-- The bit-independent prefix of the IND-CPA experiment: key generation, the
adversary's pre-challenge phase, encapsulation, and the random key draw. -/
private def indCPAPrefix [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) : ProbComp (INDCPAPrefixState kem adv) := do
  let (pk, _sk) ← kem.keygen
  let st ← adv.preChallenge pk
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  pure { st := st, cStar := cStar, kReal := kReal, kRand := kRand }

/-- A formulation of the fixed-bit experiment `G_b` over `indCPAPrefix`: it returns
`adv.postChallenge st cStar k*`, where `k* = kReal` if `b = true` and `k* = kRand` otherwise. -/
private def indCPAExpProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) (b : Bool) : ProbComp Bool := do
  let p ← indCPAPrefix kem adv
  adv.postChallenge p.st p.cStar (if b then p.kReal else p.kRand)


/-- The IND-CPA guessing game as a computation of type `ProbComp Bool`.
Its evaluated distribution `𝒟[indCPAGameProb kem adv]` is definitionally equal
to `kem.IND_CPA_Game ProbCompRuntime.probComp adv`, which has type `SPMF Bool`.
This private helper names the computation so the proof can reorder its
independent samples using `probOutput_bind_bind_swap`. -/
private def indCPAGameProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let (pk, _sk) ← kem.keygen
  let st ← adv.preChallenge pk
  let b ← ($ᵗ Bool)
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  let b' ← adv.postChallenge st cStar (if b then kReal else kRand)
  return (b == b')

/-- The IND-CPA guessing game with encapsulation and the independent uniform
key draw performed before sampling the challenge bit. The bit then selects
the real or random key passed to `adv.postChallenge`. -/
private def indCPABranchGameProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let p ← indCPAPrefix kem adv
  let b ← ($ᵗ Bool)
  let z ← if b then adv.postChallenge p.st p.cStar p.kReal
          else adv.postChallenge p.st p.cStar p.kRand
  pure (b == z)

/-- For every `kem` and `adv`, the guessing-game distributions agree when
encapsulation and uniform key sampling are performed before or after the
independent challenge-bit draw. -/
private lemma indCPAGameProb_evalDist_eq_branch [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) :
    𝒟[indCPAGameProb kem adv] = 𝒟[indCPABranchGameProb kem adv] := by
  apply evalDist_ext
  intro x
  unfold indCPAGameProb indCPABranchGameProb indCPAPrefix
  simp only [monad_norm]
  refine probOutput_bind_congr' kem.keygen x ?_
  intro pk_sk
  refine probOutput_bind_congr' (adv.preChallenge pk_sk.1) x ?_
  intro st
  rw [probOutput_bind_bind_swap ($ᵗ Bool) (kem.encaps pk_sk.1)
    (fun b ck => do
      let kRand ← ($ᵗ K)
      let b' ← adv.postChallenge st ck.1 (if b then ck.2 else kRand)
      pure (b == b')) x]
  refine probOutput_bind_congr' (kem.encaps pk_sk.1) x ?_
  intro ck
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ K)
    (fun b kRand => do
      let b' ← adv.postChallenge st ck.1 (if b then ck.2 else kRand)
      pure (b == b')) x]
  refine probOutput_bind_congr' ($ᵗ K) x ?_
  intro kRand
  refine probOutput_bind_congr' ($ᵗ Bool) x ?_
  intro b
  cases b <;> rfl

/-- For every KEM `kem` and IND-CPA adversary `adv`,
the normalized guessing advantage of `adv` against `kem` equals the absolute
difference between its probabilities of returning `true` in the real-key
and random-key experiments. -/
private lemma indCPAGameProb_advantage_eq_fixed_dist [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) :
    (indCPAGameProb kem adv).boolBiasAdvantage =
      (indCPAExpProb kem adv true).boolDistAdvantage
        (indCPAExpProb kem adv false) := by
  rw [show (indCPAGameProb kem adv).boolBiasAdvantage =
      (indCPABranchGameProb kem adv).boolBiasAdvantage by
    unfold ProbComp.boolBiasAdvantage
    rw [evalDist_ext_iff.mp (indCPAGameProb_evalDist_eq_branch kem adv) true]
    rw [evalDist_ext_iff.mp (indCPAGameProb_evalDist_eq_branch kem adv) false]]
  simpa [indCPABranchGameProb, indCPAExpProb] using
    ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage
      (indCPAPrefix kem adv)
      (fun p => adv.postChallenge p.st p.cStar p.kReal)
      (fun p => adv.postChallenge p.st p.cStar p.kRand)

/-- The local fixed-bit experiment and the standard IND-CPA experiment
`IND_CPA_Exp` have the same probability of returning `true`. -/
private lemma indCPAExpProb_probOutput_true_eq [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) (b : Bool) :
    Pr[= true | indCPAExpProb kem adv b] =
      Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp adv b] := by
  unfold KEMScheme.IND_CPA_Exp
  rw [probOutput_probCompRuntime_evalDist_eq]
  cases b <;>
    simp [indCPAExpProb, indCPAPrefix,
      ProbCompRuntime.probComp, ProbCompRuntime.liftProbComp, ProbCompLift.id,
      monad_norm]


/-- For every KEM `kem` and IND-CPA adversary `adv`,
the normalized guessing advantage `IND_CPA_Advantage` of `adv` against `kem`
equals the absolute difference between its probabilities of returning
`true` in the real-key and random-key experiments `IND_CPA_Exp`. -/
theorem IND_CPA_Advantage_eq_fixed_branch_dist [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Advantage ProbCompRuntime.probComp adv =
      |(Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp adv true]).toReal -
        (Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp adv false]).toReal| := by
  rw [show kem.IND_CPA_Advantage ProbCompRuntime.probComp adv =
      (indCPAGameProb kem adv).boolBiasAdvantage by rfl]
  rw [indCPAGameProb_advantage_eq_fixed_dist]
  unfold ProbComp.boolDistAdvantage
  rw [indCPAExpProb_probOutput_true_eq kem adv true]
  rw [indCPAExpProb_probOutput_true_eq kem adv false]

end KEMScheme
