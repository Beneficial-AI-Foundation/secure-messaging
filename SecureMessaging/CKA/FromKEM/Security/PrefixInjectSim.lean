/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.ChallengeBridge
import ToVCVio.ProgramLogic.Tactics.Support

/-!
# CKA from KEM — Prefix Injection Simulation

This file starts the top-level hybrid that connects the honest CKA branch to the
raw IND-CPA reduction branch.  The prepared challenge state is already handled
in `ChallengeBridge`; the remaining work is to move the reduction's sampled
challenge key pair to the point where the honest game would generate that key
pair.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-- The challenged party has already reached or passed the challenge epoch. -/
def challengePassed
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Prop :=
  match gp.challengedParty with
  | .A => gp.challengeEpoch ≤ σ.tA
  | .B => gp.challengeEpoch ≤ σ.tB

/-- Once the challenge epoch has passed (`challengePassed`), the two
fixed-bit implementations agree on every query: the challenge oracle can no
longer fire at the challenged epoch, and no other oracle reads the bit. -/
lemma securityImpl_true_false_run_eq_of_challengePassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (securitySpec leak).Domain)
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
    unfold securityImpl
    change
      (CKAScheme.oracleChallA gp true (scheme kem hDet leak) ()).run σ =
        (CKAScheme.oracleChallA gp false (scheme kem hDet leak) ()).run σ
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
    unfold securityImpl
    change
      (CKAScheme.oracleChallB gp true (scheme kem hDet leak) ()).run σ =
        (CKAScheme.oracleChallB gp false (scheme kem hDet leak) ()).run σ
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
    (leak : RandLeak kem)
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

/-- Pointwise (per-bit) equality behind
`ckaSecurityFixedBranch_challenge_key_gap_eq`. -/
private lemma ckaSecurityFixedBranch_challenge_key_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
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

/-- Game hop: the honest fixed branch and
`ckaSecurityFixedBranchWithChallengeKey` have the same true-output gap. Per
bit, one of the two up-front key draws is unused — the challenge draw in the
general case, the ordinary initial draw when the challenge is the very first
A-send — so it drops out. -/
lemma ckaSecurityFixedBranch_challenge_key_gap_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
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
    (leak : RandLeak kem)
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

/-- Pointwise (per-bit) equality behind
`ckaReductionINDCPABranchRaw_keygen_swapped_gap_eq`. -/
private lemma ckaReductionINDCPABranchRaw_keygen_swapped_probOutput_true
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
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

/-- Game hop: swapping the two initial key-generation draws of the raw
reduction branch preserves the true-output gap. The swap is a pure sampling
commute, proved pointwise per bit. -/
lemma ckaReductionINDCPABranchRaw_keygen_swapped_gap_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
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
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK) :
    QueryImpl (securitySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
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
    (leak : RandLeak kem)
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
    stateT_run, bind_assoc]

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
    stateT_run, bind_assoc]

/-- Run reduction for the honest A-send oracle on a send-ready state. -/
lemma securityImpl_OSendA_run_sendReady [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendA = true)
    (hstA : σ.stA = State.sendReady pk) :
    (securityImpl kem hDet leak gp isRandom
        (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ =
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
  change (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ = _
  simp only [CKAScheme.oracleSendA, scheme, send, hvalid, ↓reduceIte, hstA,
    stateT_run, bind_assoc]
  rfl

/-- Run reduction for the honest B-send oracle on a send-ready state. -/
lemma securityImpl_OSendB_run_sendReady [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendB = true)
    (hstB : σ.stB = State.sendReady pk) :
    (securityImpl kem hDet leak gp isRandom
        (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ =
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
  change (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ = _
  simp only [CKAScheme.oracleSendB, scheme, send, hvalid, ↓reduceIte, hstB,
    stateT_run, bind_assoc]
  rfl

/-! ## Counter monotonicity of the honest security implementation -/

/-- Every security-game oracle leaves both epoch counters non-decreasing on its support:
unchanged-state oracles fix the state, and each counter-bumping oracle increases exactly one of
`tA`/`tB` by one. -/
lemma securityImpl_run_counters_mono [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (t : (securitySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (z : (securitySpec leak).Range t × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp isRandom t).run σ)) :
    σ.tA ≤ z.2.tA ∧ σ.tB ≤ z.2.tB := by
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  · -- O-Unif
    change z ∈ support ((CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run σ) at hz
    obtain ⟨x, -, hz'⟩ := Set.mem_iUnion₂.mp hz
    have hz2 : z = (x, σ) := hz'
    vcv_support
  · -- O-Send-A
    cases uSendA
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
    · cases hst : σ.stA with
      | sendReady pk =>
          rw [securityImpl_OSendA_run_sendReady kem hDet leak gp isRandom σ pk hvalid hst] at hz
          vcv_support
      | recvReady sk =>
          change z ∈ support ((CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ) at hz
          simp only [CKAScheme.oracleSendA, hvalid, hst, stateT_run] at hz
          vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support ((CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ) at hz
      simp only [CKAScheme.oracleSendA, hvalidFalse, stateT_run] at hz
      vcv_support
  · -- O-Recv-A
    cases uRecvA
    by_cases hvalid : CKAScheme.validStep σ.lastAction .recvA = true
    · change z ∈ support ((CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σ) at hz
      cases hrhoB : σ.rhoB with
      | none =>
          simp only [CKAScheme.oracleRecvA, hvalid, hrhoB, stateT_run] at hz
          vcv_support
      | some ρ =>
          cases hrecv : recv hDet σ.stA ρ with
          | none =>
              simp only [CKAScheme.oracleRecvA, scheme, hvalid, hrhoB, hrecv,
                stateT_run] at hz
              vcv_support
          | some keyStA =>
              simp only [CKAScheme.oracleRecvA, scheme, hvalid, hrhoB, hrecv,
                stateT_run] at hz
              vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .recvA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support ((CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σ) at hz
      simp only [CKAScheme.oracleRecvA, hvalidFalse, stateT_run] at hz
      vcv_support
  · -- O-Send-B
    cases uSendB
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
    · cases hst : σ.stB with
      | sendReady pk =>
          rw [securityImpl_OSendB_run_sendReady kem hDet leak gp isRandom σ pk hvalid hst] at hz
          vcv_support
      | recvReady sk =>
          change z ∈ support ((CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ) at hz
          simp only [CKAScheme.oracleSendB, hvalid, hst, stateT_run] at hz
          vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support ((CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ) at hz
      simp only [CKAScheme.oracleSendB, hvalidFalse, stateT_run] at hz
      vcv_support
  · -- O-Recv-B
    cases uRecvB
    by_cases hvalid : CKAScheme.validStep σ.lastAction .recvB = true
    · change z ∈ support ((CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σ) at hz
      cases hrhoA : σ.rhoA with
      | none =>
          simp only [CKAScheme.oracleRecvB, hvalid, hrhoA, stateT_run] at hz
          vcv_support
      | some ρ =>
          cases hrecv : recv hDet σ.stB ρ with
          | none =>
              simp only [CKAScheme.oracleRecvB, scheme, hvalid, hrhoA, hrecv,
                stateT_run] at hz
              vcv_support
          | some keyStB =>
              simp only [CKAScheme.oracleRecvB, scheme, hvalid, hrhoA, hrecv,
                stateT_run] at hz
              vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .recvB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support ((CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σ) at hz
      simp only [CKAScheme.oracleRecvB, hvalidFalse, stateT_run] at hz
      vcv_support
  · -- O-Chall-A
    cases uChallA
    by_cases hvalid : CKAScheme.validStep σ.lastAction .challA = true
    · change z ∈ support
        ((CKAScheme.oracleChallA gp isRandom (scheme kem hDet leak) ()).run σ) at hz
      cases hst : σ.stA with
      | sendReady pk =>
          simp only [CKAScheme.oracleChallA, scheme, send, hvalid, hst, ↓reduceIte,
            stateT_run] at hz
          split_ifs at hz
          · vcv_support hz; grind
          · vcv_support hz; grind
          · vcv_support
      | recvReady sk =>
          simp only [CKAScheme.oracleChallA, scheme, send, hvalid, hst, ↓reduceIte,
            stateT_run] at hz
          split_ifs at hz <;> vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .challA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support
        ((CKAScheme.oracleChallA gp isRandom (scheme kem hDet leak) ()).run σ) at hz
      simp only [CKAScheme.oracleChallA, hvalidFalse, stateT_run] at hz
      vcv_support
  · -- O-Chall-B
    cases uChallB
    by_cases hvalid : CKAScheme.validStep σ.lastAction .challB = true
    · change z ∈ support
        ((CKAScheme.oracleChallB gp isRandom (scheme kem hDet leak) ()).run σ) at hz
      cases hst : σ.stB with
      | sendReady pk =>
          simp only [CKAScheme.oracleChallB, scheme, send, hvalid, hst, ↓reduceIte,
            stateT_run] at hz
          split_ifs at hz
          · vcv_support hz; grind
          · vcv_support hz; grind
          · vcv_support
      | recvReady sk =>
          simp only [CKAScheme.oracleChallB, scheme, send, hvalid, hst, ↓reduceIte,
            stateT_run] at hz
          split_ifs at hz <;> vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .challB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support
        ((CKAScheme.oracleChallB gp isRandom (scheme kem hDet leak) ()).run σ) at hz
      simp only [CKAScheme.oracleChallB, hvalidFalse, stateT_run] at hz
      vcv_support
  · -- O-Corrupt-A
    cases uCorrA
    change z ∈ support ((CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run σ) at hz
    simp only [CKAScheme.oracleCorruptA, stateT_run] at hz
    split_ifs at hz <;> vcv_support
  · -- O-Corrupt-B
    cases uCorrB
    change z ∈ support ((CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run σ) at hz
    simp only [CKAScheme.oracleCorruptB, stateT_run] at hz
    split_ifs at hz <;> vcv_support
  · -- O-Send-A-rleak
    cases uRLeakA
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
    · change z ∈ support ((CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σ)
        at hz
      cases hst : σ.stA with
      | sendReady pk =>
          simp only [CKAScheme.oracleSendA_rleak, scheme, send_rleak, hvalid, hst,
            ↓reduceIte, stateT_run] at hz
          split_ifs at hz
          · vcv_support hz; grind
          · vcv_support
      | recvReady sk =>
          simp only [CKAScheme.oracleSendA_rleak, scheme, send_rleak, hvalid, hst,
            ↓reduceIte, stateT_run] at hz
          split_ifs at hz <;> vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support ((CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σ)
        at hz
      simp only [CKAScheme.oracleSendA_rleak, hvalidFalse, stateT_run] at hz
      vcv_support
  · -- O-Send-B-rleak
    cases uRLeakB
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
    · change z ∈ support ((CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σ)
        at hz
      cases hst : σ.stB with
      | sendReady pk =>
          simp only [CKAScheme.oracleSendB_rleak, scheme, send_rleak, hvalid, hst,
            ↓reduceIte, stateT_run] at hz
          split_ifs at hz
          · vcv_support hz; grind
          · vcv_support
      | recvReady sk =>
          simp only [CKAScheme.oracleSendB_rleak, scheme, send_rleak, hvalid, hst,
            ↓reduceIte, stateT_run] at hz
          split_ifs at hz <;> vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change z ∈ support ((CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σ)
        at hz
      simp only [CKAScheme.oracleSendB_rleak, hvalidFalse, stateT_run] at hz
      vcv_support

/-! ## Past-injection equivalence of the injecting and honest implementations -/

/-- The challenged party's predecessor counter has reached the injection epoch,
so no later send can install the challenge key pair.

For an A-challenge the predecessor send is a B-send (so the relevant counter is
`tB`); for a B-challenge it is an A-send (so the counter is `tA`). -/
def injectionPassed
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Prop :=
  match gp.challengedParty with
  | .A => gp.challengeEpoch - 1 ≤ σ.tB
  | .B => gp.challengeEpoch - 1 ≤ σ.tA

/-- Once the predecessor counter has passed the injection epoch, the honest
implementation keeps it passed: counters are monotone along every oracle. -/
private lemma securityImpl_preservesInv_injectionPassed [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    QueryImpl.PreservesInv (securityImpl kem hDet leak gp isRandom)
      (injectionPassed (K := K) (PK := PK) (SK := SK) (C := C) gp) := by
  intro t σ0 h z hz
  have hmono := securityImpl_run_counters_mono kem hDet leak gp isRandom t σ0 z hz
  cases hcp : gp.challengedParty <;>
    simp only [injectionPassed, hcp] at h ⊢ <;> omega

/-- Past the injection epoch, the injecting implementation coincides with the
honest one on every oracle.

Only the two send oracles differ between the implementations, and the `useStar`
guard there is forced false once `injectionPassed` holds (either the challenged
party makes that send never inject, or its counter has already passed the
injection epoch), so both install the freshly generated key pair. Every other
oracle is shared definitionally. -/
private lemma securityImplWithChallengeKeyPair_run_eq_securityImpl_of_injectionPassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    (t : (securitySpec leak).Domain)
    (s : SecurityState K PK SK C)
    (hs : injectionPassed gp s) :
    (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar t).run s =
      (securityImpl kem hDet leak gp isRandom t).run s := by
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  · rfl
  · -- O-Send-A: the injecting and honest A-send agree (no injection past the epoch)
    cases uSendA
    have hnotInj : sendAInjectsChallengeKey gp { s with tA := s.tA + 1 } = false := by
      cases hcp : gp.challengedParty with
      | A => simp [sendAInjectsChallengeKey, hcp]
      | B =>
          simp only [injectionPassed, hcp] at hs
          have hne : s.tA + 1 ≠ gp.challengeEpoch - 1 := by omega
          simp [sendAInjectsChallengeKey, hcp, hne]
    change (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run s = _
    by_cases hvalid : CKAScheme.validStep s.lastAction .sendA = true
    · cases hst : s.stA with
      | sendReady pk =>
          rw [oracleSendAWithChallengeKeyPair_run_sendReady kem gp pkStar skStar s pk hvalid hst,
            securityImpl_OSendA_run_sendReady kem hDet leak gp isRandom s pk hvalid hst];
          simp only [hnotInj]; rfl
      | recvReady sk =>
          change _ = (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run s
          simp only [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, scheme, send,
            hvalid, ↓reduceIte, hst, stateT_run]
    · have hvalidFalse : CKAScheme.validStep s.lastAction .sendA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change _ = (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run s
      simp only [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, hvalidFalse,
        Bool.false_eq_true, ↓reduceIte, stateT_run]
  · rfl
  · -- O-Send-B: mirror of O-Send-A
    cases uSendB
    have hnotInj : sendBInjectsChallengeKey gp { s with tB := s.tB + 1 } = false := by
      cases hcp : gp.challengedParty with
      | A =>
          simp only [injectionPassed, hcp] at hs
          have hne : s.tB + 1 ≠ gp.challengeEpoch - 1 := by omega
          simp [sendBInjectsChallengeKey, hcp, hne]
      | B => simp [sendBInjectsChallengeKey, hcp]
    change (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run s = _
    by_cases hvalid : CKAScheme.validStep s.lastAction .sendB = true
    · cases hst : s.stB with
      | sendReady pk =>
          rw [oracleSendBWithChallengeKeyPair_run_sendReady kem gp pkStar skStar s pk hvalid hst,
            securityImpl_OSendB_run_sendReady kem hDet leak gp isRandom s pk hvalid hst]
          simp only [hnotInj]; rfl
      | recvReady sk =>
          change _ = (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run s
          simp only [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, scheme, send,
            hvalid, ↓reduceIte, hst, stateT_run]
    · have hvalidFalse : CKAScheme.validStep s.lastAction .sendB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change _ = (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run s
      simp only [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, hvalidFalse,
        Bool.false_eq_true, ↓reduceIte, stateT_run]
  all_goals rfl

/-- Past the injection epoch, the injecting and honest implementations induce the
same output-state distribution on any adversary.

The per-step equivalence
`securityImplWithChallengeKeyPair_run_eq_securityImpl_of_injectionPassed` lifts
through `simulateQ`; counter monotonicity
(`securityImpl_preservesInv_injectionPassed`) keeps `injectionPassed` true along
the whole run. -/
lemma probOutput_simulateQ_securityImplWithChallengeKeyPair_run_eq_of_injectionPassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    (adv : Adversary (kem := kem) leak)
    (s : SecurityState K PK SK C)
    (hs : injectionPassed gp s)
    (z : Bool × SecurityState K PK SK C) :
    Pr[= z | (simulateQ
        (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar) adv).run s] =
      Pr[= z | (simulateQ (securityImpl kem hDet leak gp isRandom) adv).run s] :=
  probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
    (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar)
    (securityImpl kem hDet leak gp isRandom)
    (injectionPassed gp) adv
    (securityImplWithChallengeKeyPair_run_eq_securityImpl_of_injectionPassed
      kem hDet leak gp isRandom pkStar skStar)
    (securityImpl_preservesInv_injectionPassed kem hDet leak gp isRandom)
    s hs z

end kemCKA
