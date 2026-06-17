/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import SecureMessaging.CKA.FromKEM.Security.ReductionBranch
import ToVCVio.OracleComp.EvalDist

/-!
# CKA from KEM — Branch and IND-CPA Bridge

This file packages the reduction's Boolean branch experiments and the advantage
normalization that connects them to VCVio's KEM IND-CPA game, following
[ACD19, Section 4.1.2].

* `ckaSecurityFixedBranch` is the CKA fixed-bit branch;
* `ckaReductionINDCPABranch` is the KEM challenge branch of the concrete
  reduction, and `ckaReductionINDCPABranchRaw` drops its final `not` so the
  absolute gap absorbs the CKA/KEM bit-orientation reversal;
* `kem_ind_cpa_advantage_eq_fixed_branch_dist` rewrites VCVio's single-game
  `IND_CPA_Advantage` as the fixed-branch gap used by the proof chain.

This layer defines the branch experiments and their advantage bridges only. It
does not prove the hidden-state simulation or the key-injection equivalences.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

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


/-- The KEM challenge branch of the concrete reduction with a fixed challenge
bit: run the prefix to the paused challenge, encapsulate against the
challenge public key, and finish with the real (`b = true`) or random
(`b = false`) key. This is the reduction's side of the IND-CPA experiment,
written as one `ProbComp`. -/
def ckaReductionINDCPABranch [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) : ProbComp Bool := do
  let (pkStar, _skStar) ← kem.keygen
  let (pk0, sk0) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (State.recvReady sk0)
  let (res, σ) ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
  let (cStar, kReal) ← kem.encaps pkStar
  let kRand ← ($ᵗ K)
  finishChallengeStep kem hDet leak gp res σ cStar (if b then kReal else kRand)

/-- `ckaReductionINDCPABranch` without the final guess negation. The raw form
is the one coupled against the honest CKA branches; the gap is unchanged
(`ckaReductionINDCPABranch_gap_eq_raw_gap`). -/
def ckaReductionINDCPABranchRaw [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) : ProbComp Bool := do
  let (pkStar, _skStar) ← kem.keygen
  let (pk0, sk0) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (State.recvReady sk0)
  let (res, σ) ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
  let (cStar, kReal) ← kem.encaps pkStar
  let kRand ← ($ᵗ K)
  finishChallengeStepRaw kem hDet leak gp res σ cStar (if b then kReal else kRand)

/-- The fixed-bit CKA game run from an explicit initial state: simulate the
adversary under the honest implementation and return its guess. -/
def ckaSecurityFixedFromState [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (isRandom : Bool) : ProbComp Bool := do
  let (guess, _) ←
    (simulateQ (securityImpl kem hDet leak gp isRandom) adv).run σ
  pure guess

/-- The honest fixed-bit CKA branch: generate the initial key pair and run
`ckaSecurityFixedFromState` from the standard initial state. -/
def ckaSecurityFixedBranch [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (State.sendReady pk0)
      (State.recvReady sk0)
  ckaSecurityFixedFromState kem hDet leak adv gp σ0 isRandom

/-- The generic fixed-bit CKA security experiment for the KEM construction is
exactly the honest fixed-bit branch: unfolding the scheme's initialization
gives the same game. -/
lemma securityExpFixedBit_eq_ckaSecurityFixedBranch
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    CKAScheme.securityExpFixedBit (scheme kem hDet leak) adv isRandom gp =
      ckaSecurityFixedBranch kem hDet leak adv gp isRandom := by
  unfold CKAScheme.securityExpFixedBit ckaSecurityFixedBranch
  unfold ckaSecurityFixedFromState securityImpl
  simp [scheme, initA, initB]

/-- The negated and raw reduction branches differ by a final `(! ·)` map,
inherited from the challenge finishers. -/
private lemma ckaReductionINDCPABranch_eq_not_map_raw [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    ckaReductionINDCPABranch kem hDet leak adv gp b =
      (! ·) <$> ckaReductionINDCPABranchRaw kem hDet leak adv gp b := by
  unfold ckaReductionINDCPABranch ckaReductionINDCPABranchRaw
  simp only [map_bind]
  refine bind_congr (m := ProbComp) fun pkStar_skStar => ?_
  refine bind_congr (m := ProbComp) fun pk0_sk0 => ?_
  refine bind_congr (m := ProbComp) fun res_σ => ?_
  refine bind_congr (m := ProbComp) fun cStar_kReal => ?_
  refine bind_congr (m := ProbComp) fun kRand => ?_
  rw [finishChallengeStep_eq_not_map_raw]

/-- The reduction branch gap equals the raw (un-negated) branch gap: the
final negation flips each branch's bias but not the absolute gap. -/
lemma ckaReductionINDCPABranch_gap_eq_raw_gap [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) :
    |(Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp false]).toReal| =
    |(Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp false]).toReal| := by
  rw [ckaReductionINDCPABranch_eq_not_map_raw]
  rw [ckaReductionINDCPABranch_eq_not_map_raw]
  exact abs_probOutput_true_not_map_gap_eq
    (ckaReductionINDCPABranchRaw kem hDet leak adv gp true)
    (ckaReductionINDCPABranchRaw kem hDet leak adv gp false)

/-- For the concrete reduction, the fixed-bit IND-CPA experiment is the
reduction branch: the reduction's two phases recombine into the single-pass
branch program. -/
private lemma indCPAExpProb_ckaToINDCPAReduction_eq_branch
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    indCPAExpProb kem (ckaToINDCPAReduction kem hDet leak adv gp) b =
      ckaReductionINDCPABranch kem hDet leak adv gp b := by
  unfold indCPAExpProb indCPAPrefix ckaReductionINDCPABranch ckaToINDCPAReduction
  cases b <;>
    simp only [Bool.and_eq_true, beq_iff_eq, monad_norm, bind_assoc, pure_bind]
  · refine bind_congr (m := ProbComp) fun pkStar_skStar => ?_
    refine bind_congr (m := ProbComp) fun pk0_sk0 => ?_
    refine bind_congr (m := ProbComp) fun res_σ => ?_
    cases res_σ.1 <;> simp [finishChallengeStep]
  · refine bind_congr (m := ProbComp) fun pkStar_skStar => ?_
    refine bind_congr (m := ProbComp) fun pk0_sk0 => ?_
    refine bind_congr (m := ProbComp) fun res_σ => ?_
    cases res_σ.1 <;> simp [finishChallengeStep]

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


/-- For the concrete reduction, the library IND-CPA experiment with fixed bit
`b` returns `true` with the same probability as the reduction branch. This is
the step that lets `Security.lean` replace the library game by the branch
program. -/
lemma ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp) b] =
      Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp b] := by
  rw [← indCPAExpProb_probOutput_true_eq]
  rw [indCPAExpProb_ckaToINDCPAReduction_eq_branch]

/-- VCVio's `IND_CPA_Advantage` equals the absolute `true`-output gap of the
two fixed-bit `IND_CPA_Exp` runs: split the sampled bit into its two branches
and normalize the bias to a distinguishing gap. -/
lemma kem_ind_cpa_advantage_eq_fixed_branch_dist [SampleableType K]
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


end kemCKA
