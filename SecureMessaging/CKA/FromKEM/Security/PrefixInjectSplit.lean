/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectSim

/-!
# CKA from KEM — Prefix Injection Splitter

The honest fixed-bit branch `ckaSecurityFixedBranchWithChallengeKey` samples the
challenge KEM key pair up front and never uses it (in the general, non-initial
case), while `ckaSecurityFixedBranchWithInjectedChallengeKey` installs that pair
at the predecessor send.  This file shows the two branches induce the same
Boolean output distribution.

The argument splits each run at the first send that installs the challenge key
pair.  Before that send the injecting and honest implementations agree, so the
prefix is shared; at the send the up-front key draw is coupled with the send's
fresh key draw; after the send `injectionPassed` holds, so the post-injection
equivalence (`probOutput_simulateQ_securityImplWithChallengeKeyPair_run_eq_of_injectionPassed`)
finishes the suffix.
-/

open OracleSpec OracleComp ENNReal OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## The injecting send -/

/-- The next A-send actually installs the challenge key pair: it is a valid send
on a send-ready state at the predecessor epoch for a B-challenge.

This is precisely the configuration in which `oracleSendAWithChallengeKeyPair`
diverges from the honest A-send. -/
private def sendAEffectivelyInjects
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .sendA &&
    (match σ.stA with | .sendReady _ => true | _ => false) &&
    sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 }

/-- Mirror of `sendAEffectivelyInjects` for the predecessor send of an
A-challenge. -/
private def sendBEffectivelyInjects
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .sendB &&
    (match σ.stB with | .sendReady _ => true | _ => false) &&
    sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 }

/-! ## The prefix simulation -/

/-- Run the honest fixed-bit game until the first send that installs the
challenge key pair, pausing there.

Before that send the injecting and honest implementations agree, so the prefix
uses the honest implementation `securityImpl` and is shared by both branches. -/
private def injectPrefix [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    {α : Type} :
    OracleComp (SecuritySpec leak) α →
      StateT (SecurityState K PK SK C) ProbComp
        (CKAChallengeStepResult leak α) :=
  OracleComp.construct
    (fun a => pure (.done a))
    (fun t oa rec => do
      match t with
      | CKAScheme.ckaSecuritySpec.OSendA =>
          let σ ← get
          if sendAEffectivelyInjects gp σ then
            pure (.pausedA oa)
          else
            let out ← securityImpl kem hDet leak gp isRandom
              (CKAScheme.ckaSecuritySpec.OSendA : (SecuritySpec leak).Domain)
            rec out
      | CKAScheme.ckaSecuritySpec.OSendB =>
          let σ ← get
          if sendBEffectivelyInjects gp σ then
            pure (.pausedB oa)
          else
            let out ← securityImpl kem hDet leak gp isRandom
              (CKAScheme.ckaSecuritySpec.OSendB : (SecuritySpec leak).Domain)
            rec out
      | other =>
          let out ← securityImpl kem hDet leak gp isRandom other
          rec out)

/-- Off the effective injecting send, the injecting and honest implementations
run identically on every oracle.

The send oracles only diverge when `useStar` fires, which the effective-inject
guard rules out; every other oracle is shared definitionally. -/
private lemma securityImplWithChallengeKeyPair_run_eq_securityImpl_of_step
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    (t : (SecuritySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (hA : t = (CKAScheme.ckaSecuritySpec.OSendA : (SecuritySpec leak).Domain) →
      sendAEffectivelyInjects gp σ = false)
    (hB : t = (CKAScheme.ckaSecuritySpec.OSendB : (SecuritySpec leak).Domain) →
      sendBEffectivelyInjects gp σ = false) :
    (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar t).run σ =
      (securityImpl kem hDet leak gp isRandom t).run σ := by
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  · rfl
  · -- O-Send-A
    cases uSendA
    change (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ = _
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
    · cases hst : σ.stA with
      | sendReady pk =>
          have hnotInj : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = false := by
            simpa [sendAEffectivelyInjects, hvalid, hst] using hA rfl
          rw [oracleSendAWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σ pk hvalid hst,
            securityImpl_OSendA_run_sendReady kem hDet leak gp isRandom σ pk hvalid hst]
          simp only [hnotInj]; rfl
      | recvReady sk =>
          change _ = (CKAScheme.oracleSendA (schemeWithLeak kem hDet leak) ()).run σ
          simp only [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, schemeWithLeak, send,
            hvalid, ↓reduceIte, hst, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
            monadLift_self, StateT.run_pure, pure_bind]
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change _ = (CKAScheme.oracleSendA (schemeWithLeak kem hDet leak) ()).run σ
      simp only [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, hvalidFalse,
        Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
  · rfl
  · -- O-Send-B
    cases uSendB
    change (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ = _
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
    · cases hst : σ.stB with
      | sendReady pk =>
          have hnotInj : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = false := by
            simpa [sendBEffectivelyInjects, hvalid, hst] using hB rfl
          rw [oracleSendBWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σ pk hvalid hst,
            securityImpl_OSendB_run_sendReady kem hDet leak gp isRandom σ pk hvalid hst]
          simp only [hnotInj]; rfl
      | recvReady sk =>
          change _ = (CKAScheme.oracleSendB (schemeWithLeak kem hDet leak) ()).run σ
          simp only [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, schemeWithLeak, send,
            hvalid, ↓reduceIte, hst, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
            monadLift_self, StateT.run_pure, pure_bind]
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change _ = (CKAScheme.oracleSendB (schemeWithLeak kem hDet leak) ()).run σ
      simp only [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, hvalidFalse,
        Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
  all_goals rfl

end kemCKA
