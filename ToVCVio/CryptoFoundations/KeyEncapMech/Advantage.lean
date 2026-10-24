/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.SecExp.Measure

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

In Lean, this experiment is written as
`G_b := kem.IND_CPA_Experiment ProbCompRuntime.probComp adv b`.

For each `b : Bool`,
let `p_b := Pr{let x ← G_b}[x = true]` be the probability that `adv` outputs `true`.

The distinguishing advantage of `adv` against `kem` is defined as
`Adv_dist := |p_true - p_false|`.

**Guessing game.** Let `H` be the experiment that:

1. Samples a uniform bit `b`, hidden from `adv`.
2. Runs `G_b`, obtaining the adversary's guess `b'`.
3. Returns `true` exactly when `b' = b`.

Let `w := Pr{let x ← H}[x = true]` be the probability of a correct guess.

The normalized guessing advantage of `adv` against `kem` is defined as
`Adv_guess := |2w - 1| = 2 |w - 1/2|`.

**Theorem.** For every `kem` and `adv` satisfying the assumptions above,
`Adv_guess = Adv_dist`, equivalently `2 |w - 1/2| = |p_true - p_false|`.

The Lean theorem `IND_CPA_Advantage_eq_fixed_branch_dist` proves this equality,
with `kem.IND_CPA_Advantage ProbCompRuntime.probComp adv` denoting `Adv_guess`.

-/

open OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {K PK SK C : Type}

/-- Data shared by the two fixed-bit experiments of `adv` against `kem`: the state `st`
returned by `adv.preChallenge pk`, the encapsulation ciphertext `cStar` with its shared key
`kReal`, and the independent uniform key `kRand` of the random-key experiment. -/
structure INDCPAPrefixState
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) where
  /-- State returned by `adv.preChallenge pk`. -/
  st : adv.State
  /-- Encapsulation ciphertext. -/
  cStar : C
  /-- Shared key produced together with `cStar`. -/
  kReal : K
  /-- Independent uniform key of the random-key experiment. -/
  kRand : K

/-- The bit-independent prefix of the IND-CPA experiment: key generation, the
adversary's pre-challenge phase, encapsulation, and the random key draw. -/
def indCPAPrefix [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) : ProbComp (INDCPAPrefixState kem adv) := do
  let (pk, _sk) ← kem.keygen
  let st ← adv.preChallenge pk
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  pure { st := st, cStar := cStar, kReal := kReal, kRand := kRand }

/-- A formulation of the fixed-bit experiment `G_b` over `indCPAPrefix`: it returns
`adv.postChallenge st cStar k*`, where `k* = kReal` if `b = true` and `k* = kRand` otherwise. -/
def indCPAExpProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) (b : Bool) : ProbComp Bool := do
  let p ← indCPAPrefix kem adv
  adv.postChallenge p.st p.cStar (if b then p.kReal else p.kRand)


/-- The IND-CPA guessing game as a computation of type `ProbComp Bool`.
Its output measure `𝒟[indCPAGameProb kem adv]` is definitionally equal
to `ProbCompRuntime.probComp.evalDist (kem.IND_CPA_Game ProbCompRuntime.probComp adv)`.
This private helper names the computation so the proof can reorder its
independent samples using `OracleComp.EvalDistEq.bind_bind_swap`. -/
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

/-- For every `kem` and `adv`, the guessing game has the same distribution when
encapsulation and uniform key sampling are performed before or after the
independent challenge-bit draw. -/
private lemma indCPAGameProb_evalDistEq_branch [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) :
    indCPAGameProb kem adv =ᵈ indCPABranchGameProb kem adv := by
  unfold indCPAGameProb indCPABranchGameProb indCPAPrefix
  simp only [monad_norm]
  refine EvalDistEq.bind_right kem.keygen fun pk_sk => ?_
  refine EvalDistEq.bind_right (adv.preChallenge pk_sk.1) fun st => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Bool) (kem.encaps pk_sk.1)
    (fun b ck => do
      let kRand ← ($ᵗ K)
      let b' ← adv.postChallenge st ck.1 (if b then ck.2 else kRand)
      pure (b == b'))).trans ?_
  refine EvalDistEq.bind_right (kem.encaps pk_sk.1) fun ck => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Bool) ($ᵗ K)
    (fun b kRand => do
      let b' ← adv.postChallenge st ck.1 (if b then ck.2 else kRand)
      pure (b == b'))).trans ?_
  refine EvalDistEq.bind_right ($ᵗ K) fun kRand => ?_
  refine EvalDistEq.bind_right ($ᵗ Bool) fun b => ?_
  cases b <;> exact EvalDistEq.rfl

/-- The branch game is the uniform-bit choice between the two fixed-bit experiments. -/
private lemma indCPABranchGameProb_evalDistEq_bit [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) :
    indCPABranchGameProb kem adv =ᵈ (do
      let b ← ($ᵗ Bool)
      let z ← if b then indCPAExpProb kem adv true else indCPAExpProb kem adv false
      pure (b == z) : ProbComp Bool) := by
  unfold indCPABranchGameProb
  refine (OracleComp.EvalDistEq.bind_bind_swap (indCPAPrefix kem adv) ($ᵗ Bool) _).trans ?_
  refine EvalDistEq.bind_right ($ᵗ Bool) fun b => ?_
  cases b <;> simp only [indCPAExpProb, Bool.false_eq_true, ↓reduceIte, bind_assoc] <;>
    exact EvalDistEq.rfl

/-- For every bit `b`, `indCPAExpProb kem adv b` is the standard fixed-bit experiment
`kem.IND_CPA_Experiment ProbCompRuntime.probComp adv b`. -/
lemma indCPAExpProb_eq_IND_CPA_Experiment [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) (b : Bool) :
    indCPAExpProb kem adv b = kem.IND_CPA_Experiment ProbCompRuntime.probComp adv b := by
  simp only [indCPAExpProb, indCPAPrefix, bind_pure_comp, map_eq_bind_pure_comp, bind_assoc,
    Function.comp_apply, pure_bind, IND_CPA_Experiment, ProbCompRuntime.liftProbComp,
    ProbCompRuntime.probComp, ProbCompLift.id, MonadHom.id_apply]

/-- For every bit `b`, `indCPAExpProb kem adv b` and the standard experiment
`kem.IND_CPA_Experiment ProbCompRuntime.probComp adv b` return `true` with the same
probability. -/
lemma indCPAExpProb_prEvent_true_eq [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) (b : Bool) :
    Pr{let x ← indCPAExpProb kem adv b}[x = true] =
      Pr{let x ← kem.IND_CPA_Experiment ProbCompRuntime.probComp adv b}[x = true] := by
  rw [indCPAExpProb_eq_IND_CPA_Experiment]

/-- For every KEM `kem` and IND-CPA adversary `adv`,
the normalized guessing advantage `IND_CPA_Advantage` of `adv` against `kem`
equals `|p_true - p_false|`, where `p_b` is the probability that `adv` returns `true` in the
fixed-bit experiment `IND_CPA_Experiment` with bit `b`. -/
theorem IND_CPA_Advantage_eq_fixed_branch_dist [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adv : kem.IND_CPA_Adversary) :
    kem.IND_CPA_Advantage ProbCompRuntime.probComp adv =
      ENNReal.absDiff
        Pr{let x ← kem.IND_CPA_Experiment ProbCompRuntime.probComp adv true}[x = true]
        Pr{let x ← kem.IND_CPA_Experiment ProbCompRuntime.probComp adv false}[x = true] := by
  rw [show kem.IND_CPA_Advantage ProbCompRuntime.probComp adv =
      𝒟[indCPAGameProb kem adv].boolBias by rfl,
    (indCPAGameProb_evalDistEq_branch kem adv).evalDist_eq,
    (indCPABranchGameProb_evalDistEq_bit kem adv).evalDist_eq,
    evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.boolDist,
    ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton,
    indCPAExpProb_prEvent_true_eq, indCPAExpProb_prEvent_true_eq]

end KEMScheme
