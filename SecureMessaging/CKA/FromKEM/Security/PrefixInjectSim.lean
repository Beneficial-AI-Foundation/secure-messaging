/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.ChallengeBridge

/-!
# CKA from KEM — Prefix Injection Simulation

This file starts the top-level hybrid that connects the honest CKA branch to the
raw IND-CPA reduction branch.  The prepared challenge state is already handled
in `ChallengeBridge`; the remaining work is to move the reduction's sampled
challenge key pair to the point where the honest game would generate that key
pair.
-/

open OracleSpec OracleComp ENNReal

namespace kemCKA

variable {K PK SK C : Type}

/-- The challenged party has already reached or passed the challenge epoch. -/
def challengePassed
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Prop :=
  match gp.challengedParty with
  | .A => gp.challengeEpoch ≤ σ.tA
  | .B => gp.challengeEpoch ≤ σ.tB

lemma securityImpl_true_false_run_eq_of_challengePassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (SecuritySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (hpass : challengePassed (K := K) (PK := PK) (SK := SK) (C := C)
      gp σ) :
    (securityImpl kem hDet leak gp true t).run σ =
      (securityImpl kem hDet leak gp false t).run σ := by
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  · rfl
  · cases uSendA
    rfl
  · cases uRecvA
    rfl
  · cases uSendB
    rfl
  · cases uRecvB
    rfl
  · cases uChallA
    unfold securityImpl SecurityCKA
    change
      (CKAScheme.oracleChallA gp true (schemeWithLeak kem hDet leak) ()).run σ =
        (CKAScheme.oracleChallA gp false (schemeWithLeak kem hDet leak) ()).run σ
    by_cases hvalid : CKAScheme.validStep σ.lastAction .challA = true
    · cases hparty : gp.challengedParty
      · have hne : ¬ σ.tA + 1 = gp.challengeEpoch := by
          simp [challengePassed, hparty] at hpass
          omega
        simp [CKAScheme.oracleChallA, hvalid, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty, hne]
      · simp [CKAScheme.oracleChallA, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty]
    · have hvalidFalse :
        CKAScheme.validStep σ.lastAction .challA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      simp [CKAScheme.oracleChallA, hvalidFalse]
  · cases uChallB
    unfold securityImpl SecurityCKA
    change
      (CKAScheme.oracleChallB gp true (schemeWithLeak kem hDet leak) ()).run σ =
        (CKAScheme.oracleChallB gp false (schemeWithLeak kem hDet leak) ()).run σ
    by_cases hvalid : CKAScheme.validStep σ.lastAction .challB = true
    · cases hparty : gp.challengedParty
      · simp [CKAScheme.oracleChallB, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty]
      · have hne : ¬ σ.tB + 1 = gp.challengeEpoch := by
          simp [challengePassed, hparty] at hpass
          omega
        simp [CKAScheme.oracleChallB, hvalid, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty, hne]
    · have hvalidFalse :
        CKAScheme.validStep σ.lastAction .challB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      simp [CKAScheme.oracleChallB, hvalidFalse]
  · cases uCorrA
    rfl
  · cases uCorrB
    rfl
  · cases uRLeakA
    rfl
  · cases uRLeakB
    rfl

/-- Honest fixed-bit branch with the challenge KEM key pair sampled explicitly.

When the challenged epoch is the initial A-send epoch, this branch uses
`(pkStar, skStar)` as the initial shared KEM key pair.  Otherwise it behaves like
the ordinary honest branch and keeps `(pkStar, skStar)` available for the later
prefix-injection hybrid. -/
def ckaSecurityFixedBranchWithChallengeKey
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.recvReady skStar
      else
        State.recvReady sk0)
  ckaSecurityFixedFromState kem hDet leak adv gp σ0 isRandom

lemma ckaSecurityFixedBranch_challenge_key_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    Pr[= true | ckaSecurityFixedBranch kem hDet leak adv gp isRandom] =
      Pr[= true |
        ckaSecurityFixedBranchWithChallengeKey kem hDet leak adv gp isRandom] := by
  unfold ckaSecurityFixedBranch ckaSecurityFixedBranchWithChallengeKey
  by_cases hinit :
      (gp.challengeEpoch == 1 && gp.challengedParty == .A) = true
  · simp only [hinit, ↓reduceIte]
    rw [probOutput_bind_const]
    simp only [HasEvalPMF.probFailure_eq_zero, tsub_zero, one_mul]
  · have hinitFalse :
        (gp.challengeEpoch == 1 && gp.challengedParty == .A) = false :=
      Bool.eq_false_of_not_eq_true hinit
    simp only [hinitFalse, Bool.false_eq_true, ↓reduceIte]
    refine probOutput_bind_congr' kem.keygen true ?_
    intro pk0_sk0
    rw [probOutput_bind_const]
    simp only [HasEvalPMF.probFailure_eq_zero, tsub_zero, one_mul]

lemma ckaSecurityFixedBranch_challenge_key_gap_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) :
    |(Pr[= true | ckaSecurityFixedBranch kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaSecurityFixedBranch kem hDet leak adv gp false]).toReal| =
    |(Pr[= true |
        ckaSecurityFixedBranchWithChallengeKey kem hDet leak adv gp true]).toReal -
      (Pr[= true |
        ckaSecurityFixedBranchWithChallengeKey kem hDet leak adv gp false]).toReal| := by
  rw [ckaSecurityFixedBranch_challenge_key_probOutput_true_eq]
  rw [ckaSecurityFixedBranch_challenge_key_probOutput_true_eq]

/-- Raw reduction branch with the two initial KEM key-generation draws swapped.

This is extensionally the same probability experiment as
`ckaReductionINDCPABranchRaw`, but exposes the ordinary initial CKA key pair
before the challenge key pair.  It is the first sampling commute needed by the
prefix-injection hybrid. -/
def ckaReductionINDCPABranchRawKeygenSwapped
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, _skStar) ← kem.keygen
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

lemma ckaReductionINDCPABranchRaw_keygen_swapped_probOutput_true
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp b] =
      Pr[= true |
        ckaReductionINDCPABranchRawKeygenSwapped kem hDet leak adv gp b] := by
  unfold ckaReductionINDCPABranchRaw
  unfold ckaReductionINDCPABranchRawKeygenSwapped
  rw [probOutput_bind_bind_swap (mx := kem.keygen) (my := kem.keygen)
    (f := fun pkStar_skStar pk0_sk0 => do
      let σ0 :=
        CKAScheme.initGameState
          (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
            State.sendReady pkStar_skStar.1
          else
            State.sendReady pk0_sk0.1)
          (State.recvReady pk0_sk0.2)
      let (res, σ) ←
        (challengePrefix kem hDet leak gp pkStar_skStar.1 adv).run σ0
      let (cStar, kReal) ← kem.encaps pkStar_skStar.1
      let kRand ← ($ᵗ K)
      finishChallengeStepRaw kem hDet leak gp res σ cStar
        (if b then kReal else kRand))
    (z := true)]

lemma ckaReductionINDCPABranchRaw_keygen_swapped_gap_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) :
    |(Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp false]).toReal| =
    |(Pr[= true |
        ckaReductionINDCPABranchRawKeygenSwapped kem hDet leak adv gp true]).toReal -
      (Pr[= true |
        ckaReductionINDCPABranchRawKeygenSwapped kem hDet leak adv gp false]).toReal| := by
  rw [ckaReductionINDCPABranchRaw_keygen_swapped_probOutput_true]
  rw [ckaReductionINDCPABranchRaw_keygen_swapped_probOutput_true]

/-- Honest A-send oracle that injects the sampled challenge key pair.

This mirrors `oracleSendAWithChallengePk`, but at the predecessor send for a
B-challenge (`sendAInjectsChallengeKey`) it uses `pkStar` as the message's next
public key *and* stores the matching secret `skStar` as A's next receive secret.
The ordinary fresh `kem.keygen` draw is kept so the bind structure matches the
raw reduction prefix; its result is unused on the injection send. -/
def oracleSendAWithChallengeKeyPair
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK) :
    QueryImpl (Unit →ₒ Option (Message C PK × K))
      (StateT (SecurityState K PK SK C) ProbComp) :=
  fun () => do
    let σ ← get
    if CKAScheme.validStep σ.lastAction .sendA then
      let σSend := { σ with tA := σ.tA + 1 }
      match σSend.stA with
      | .sendReady pk => do
          let (c, key) ← liftM (kem.encaps pk)
          let (pkGenerated, skGenerated) ← liftM kem.keygen
          let useStar := sendAInjectsChallengeKey gp σSend
          let pkNext := if useStar then pkStar else pkGenerated
          let skNext := if useStar then skStar else skGenerated
          let msg : Message C PK := (c, pkNext)
          set { σSend with
            stA := State.recvReady skNext,
            rhoA := some msg,
            keyA := some key,
            lastAction := some .sendA }
          return some (msg, key)
      | .recvReady _ =>
          return none
    else
      return none

/-- Honest B-send oracle that injects the sampled challenge key pair.

Mirror of `oracleSendAWithChallengeKeyPair` for the predecessor send of an
A-challenge (`sendBInjectsChallengeKey`). -/
def oracleSendBWithChallengeKeyPair
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK) :
    QueryImpl (Unit →ₒ Option (Message C PK × K))
      (StateT (SecurityState K PK SK C) ProbComp) :=
  fun () => do
    let σ ← get
    if CKAScheme.validStep σ.lastAction .sendB then
      let σSend := { σ with tB := σ.tB + 1 }
      match σSend.stB with
      | .sendReady pk => do
          let (c, key) ← liftM (kem.encaps pk)
          let (pkGenerated, skGenerated) ← liftM kem.keygen
          let useStar := sendBInjectsChallengeKey gp σSend
          let pkNext := if useStar then pkStar else pkGenerated
          let skNext := if useStar then skStar else skGenerated
          let msg : Message C PK := (c, pkNext)
          set { σSend with
            stB := State.recvReady skNext,
            rhoB := some msg,
            keyB := some key,
            lastAction := some .sendB }
          return some (msg, key)
      | .recvReady _ =>
          return none
    else
      return none

/-- Honest security implementation that injects the sampled challenge key pair at
the predecessor send.

This is the honest fixed-bit implementation `securityImpl … isRandom` with the
send oracles replaced by the injecting variants.  Non-send queries — including
the actual challenge oracles — keep the honest behaviour with the real bit
`isRandom`. -/
def securityImplWithChallengeKeyPair [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK) :
    QueryImpl (SecuritySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
  fun t =>
    match t with
    | CKAScheme.ckaSecuritySpec.OSendA =>
        oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()
    | CKAScheme.ckaSecuritySpec.OSendB =>
        oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()
    | other =>
        securityImpl kem hDet leak gp isRandom other

/-- Honest fixed-bit branch with the challenge key pair injected at the
predecessor send.

This is `ckaSecurityFixedBranchWithChallengeKey` with the honest implementation
replaced by `securityImplWithChallengeKeyPair`, so the send immediately before
the challenge installs `pkStar`/`skStar` instead of a freshly generated pair. -/
def ckaSecurityFixedBranchWithInjectedChallengeKey
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.recvReady skStar
      else
        State.recvReady sk0)
  let (guess, _) ←
    (simulateQ
      (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar)
      adv).run σ0
  pure guess

/-! ## Injecting send-oracle run reductions -/

/-- Run reduction for the injecting A-send oracle on a send-ready state. -/
lemma oracleSendAWithChallengeKeyPair_run_sendReady
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendA = true)
    (hstA : σ.stA = State.sendReady pk) :
    (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ =
      (do
        let (c, key) ← kem.encaps pk
        let (pkGenerated, skGenerated) ← kem.keygen
        let useStar := sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 }
        let pkNext := if useStar then pkStar else pkGenerated
        let skNext := if useStar then skStar else skGenerated
        let msg : Message C PK := (c, pkNext)
        pure (some (msg, key),
          ({ σ with
              tA := σ.tA + 1,
              stA := State.recvReady skNext,
              rhoA := some msg,
              keyA := some key,
              lastAction := some .sendA } : SecurityState K PK SK C))) := by
  simp only [oracleSendAWithChallengeKeyPair, hvalid, ↓reduceIte, hstA,
    StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]

/-- Run reduction for the injecting B-send oracle on a send-ready state. -/
lemma oracleSendBWithChallengeKeyPair_run_sendReady
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendB = true)
    (hstB : σ.stB = State.sendReady pk) :
    (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ =
      (do
        let (c, key) ← kem.encaps pk
        let (pkGenerated, skGenerated) ← kem.keygen
        let useStar := sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 }
        let pkNext := if useStar then pkStar else pkGenerated
        let skNext := if useStar then skStar else skGenerated
        let msg : Message C PK := (c, pkNext)
        pure (some (msg, key),
          ({ σ with
              tB := σ.tB + 1,
              stB := State.recvReady skNext,
              rhoB := some msg,
              keyB := some key,
              lastAction := some .sendB } : SecurityState K PK SK C))) := by
  simp only [oracleSendBWithChallengeKeyPair, hvalid, ↓reduceIte, hstB,
    StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]

/-- Run reduction for the honest A-send oracle on a send-ready state. -/
lemma securityImpl_OSendA_run_sendReady [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendA = true)
    (hstA : σ.stA = State.sendReady pk) :
    (securityImpl kem hDet leak gp isRandom
        (CKAScheme.ckaSecuritySpec.OSendA : (SecuritySpec leak).Domain)).run σ =
      (do
        let (c, key) ← kem.encaps pk
        let (pkGenerated, skGenerated) ← kem.keygen
        let msg : Message C PK := (c, pkGenerated)
        pure (some (msg, key),
          ({ σ with
              tA := σ.tA + 1,
              stA := State.recvReady skGenerated,
              rhoA := some msg,
              keyA := some key,
              lastAction := some .sendA } : SecurityState K PK SK C))) := by
  change (CKAScheme.oracleSendA (schemeWithLeak kem hDet leak) ()).run σ = _
  simp only [CKAScheme.oracleSendA, schemeWithLeak, send, hvalid, ↓reduceIte, hstA,
    StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
  rfl

/-- Run reduction for the honest B-send oracle on a send-ready state. -/
lemma securityImpl_OSendB_run_sendReady [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendB = true)
    (hstB : σ.stB = State.sendReady pk) :
    (securityImpl kem hDet leak gp isRandom
        (CKAScheme.ckaSecuritySpec.OSendB : (SecuritySpec leak).Domain)).run σ =
      (do
        let (c, key) ← kem.encaps pk
        let (pkGenerated, skGenerated) ← kem.keygen
        let msg : Message C PK := (c, pkGenerated)
        pure (some (msg, key),
          ({ σ with
              tB := σ.tB + 1,
              stB := State.recvReady skGenerated,
              rhoB := some msg,
              keyB := some key,
              lastAction := some .sendB } : SecurityState K PK SK C))) := by
  change (CKAScheme.oracleSendB (schemeWithLeak kem hDet leak) ()).run σ = _
  simp only [CKAScheme.oracleSendB, schemeWithLeak, send, hvalid, ↓reduceIte, hstB,
    StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
  rfl

end kemCKA
