/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/


import SecureMessaging.CKA.FromKEM.Security.ReductionBranch
import ToVCVio.OracleComp.EvalDist
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# CKA from KEM — Branch and IND-CPA Bridge

This file packages the reduction's Boolean branch experiments and connects them to VCVio's KEM
IND-CPA game, following [ACD19, Section 4.1.2].

* `ckaSecurityFixedBranch` is the CKA fixed-bit branch;
* `ckaReductionINDCPABranch` is the KEM challenge branch of the concrete
  reduction, and `ckaReductionINDCPABranchRaw` drops its final `not` so the
  absolute gap absorbs the CKA/KEM bit-orientation reversal;
* `ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch` identifies the fixed-bit
  `IND_CPA_Exp` of the concrete reduction with its branch. With
  `KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist` from ToVCVio, which rewrites VCVio's
  single-game `IND_CPA_Advantage` as the fixed-branch gap, this connects the two games.

This layer defines the branch experiments and their advantage bridges only. It
does not prove the hidden-state simulation or the key-injection equivalences.
-/

open ToVCVio OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

variable {K PK SK C : Type}

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
  unfold KEMScheme.indCPAExpProb KEMScheme.indCPAPrefix ckaReductionINDCPABranch
    ckaToINDCPAReduction
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
  rw [← KEMScheme.indCPAExpProb_probOutput_true_eq]
  rw [indCPAExpProb_ckaToINDCPAReduction_eq_branch]

end kemCKA
