/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Correctness

/-!
# CKA from KEM — Security Statements

This file states the security property for the generic CKA-from-KEM construction
of [ACD19, Section 4.1.2].

The paper's Theorem 2 says that the generic KEM-based construction has
`Delta_CKA = 0` and reduces CKA security to KEM security.
-/

open OracleSpec OracleComp ENNReal

namespace kemCKA

variable {K PK SK C : Type}

/-- The challenged epoch must be a send epoch for the challenged party in the
A-first alternating CKA game.

The CKA game starts with A sending. Since both send/challenge and receive
increment the local party counter, A can be challenged on odd send counters and
B on positive even send counters.
-/
def challengeEpochCompatible (gp : CKAScheme.GameParams) : Prop :=
  match gp.challengedParty with
  | .A => gp.challengeEpoch % 2 = 1
  | .B => gp.challengeEpoch % 2 = 0 ∧ 0 < gp.challengeEpoch

/-- Parameter admissibility for applying the generic KEM-to-CKA security
statement.

* `ΔFS = 0` records the paper's claim that the generic KEM construction achieves
  optimal forward-secrecy delay.
* `2 ≤ ΔPCS` records the paper/game convention that corruptions and randomness
  leaks are excluded less than two epochs before the challenge.
* `challengeEpochCompatible` says the static challenge epoch is actually a send
  epoch for the challenged party in the A-first alternating game.
-/
structure AdmissibleParams (gp : CKAScheme.GameParams) : Prop where
  deltaFS_zero : gp.ΔFS = 0
  two_le_deltaPCS : 2 ≤ gp.ΔPCS
  challenge_epoch_compatible : challengeEpochCompatible gp

lemma challengeEpoch_pos_of_compatible
    (gp : CKAScheme.GameParams)
    (h : challengeEpochCompatible gp) :
    0 < gp.challengeEpoch := by
  cases hp : gp.challengedParty
  · have hmod : gp.challengeEpoch % 2 = 1 := by
      simpa [challengeEpochCompatible, hp] using h
    omega
  · have hb : gp.challengeEpoch % 2 = 0 ∧ 0 < gp.challengeEpoch := by
      simpa [challengeEpochCompatible, hp] using h
    exact hb.2

lemma challengeEpoch_pos_of_admissible
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    0 < gp.challengeEpoch :=
  challengeEpoch_pos_of_compatible gp hgp.challenge_epoch_compatible

/-- Send-randomness type exposed by the KEM-CKA construction.

For one KEM-CKA send, the leaked randomness consists of the randomness used for
KEM encapsulation and the randomness used for the fresh next KEM key pair.
-/
abbrev Rand {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem) :=
  leak.EncapsRand × leak.KeygenRand

/-- The CKA adversary interface specialized to the leaking KEM construction.

The adversary receives the generic CKA security oracle family with the
send-randomness type induced by `KEMRandLeak`.
-/
abbrev Adversary {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem) :=
  CKAScheme.CKAAdversary (State PK SK) (Message C PK) K (Rand leak)

/-- IND-CPA reductions generated from CKA adversaries. -/
abbrev INDCPAReduction [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (leak : KEMRandLeak kem)
    (_adv : Adversary (kem := kem) leak)
    (_gp : CKAScheme.GameParams) :=
  kem.IND_CPA_Adversary

abbrev SecuritySpec
    {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem) :=
  CKAScheme.ckaSecuritySpec (State PK SK) (Message C PK) K (Rand leak)

abbrev SecurityState
    (K PK SK C : Type) :=
  CKAScheme.GameState (State PK SK) K (Message C PK)

abbrev SecurityCKA
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem) :=
  schemeWithLeak kem hDet leak

def securityImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    QueryImpl (SecuritySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
  CKAScheme.ckaSecurityImpl gp isRandom (SecurityCKA kem hDet leak)

def willChallengeA
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .challA &&
    (gp.challengedParty == .A) &&
    (σ.tA + 1 == gp.challengeEpoch)

def willChallengeB
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .challB &&
    (gp.challengedParty == .B) &&
    (σ.tB + 1 == gp.challengeEpoch)

def sendAInjectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  (gp.challengedParty == .B) && (σ.tA == gp.challengeEpoch - 1)

def sendBInjectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  (gp.challengedParty == .A) && (σ.tB == gp.challengeEpoch - 1)

lemma allowCorrPCS_false_of_two_le_deltaPCS_of_tA_pred
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hΔ : 2 ≤ gp.ΔPCS)
    (ht : σ.tA = gp.challengeEpoch - 1) :
    CKAScheme.allowCorrPCS gp σ = false := by
  by_cases hle : max σ.tA σ.tB + gp.ΔPCS ≤ gp.challengeEpoch
  · have hmax : gp.challengeEpoch - 1 ≤ max σ.tA σ.tB := by
      rw [← ht]
      exact le_max_left _ _
    have : gp.challengeEpoch - 1 + 2 ≤ gp.challengeEpoch := by
      exact (Nat.add_le_add hmax hΔ).trans hle
    omega
  · simp [CKAScheme.allowCorrPCS, hle]

lemma allowCorrPCS_false_of_two_le_deltaPCS_of_tB_pred
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hΔ : 2 ≤ gp.ΔPCS)
    (ht : σ.tB = gp.challengeEpoch - 1) :
    CKAScheme.allowCorrPCS gp σ = false := by
  by_cases hle : max σ.tA σ.tB + gp.ΔPCS ≤ gp.challengeEpoch
  · have hmax : gp.challengeEpoch - 1 ≤ max σ.tA σ.tB := by
      rw [← ht]
      exact le_max_right _ _
    have : gp.challengeEpoch - 1 + 2 ≤ gp.challengeEpoch := by
      exact (Nat.add_le_add hmax hΔ).trans hle
    omega
  · simp [CKAScheme.allowCorrPCS, hle]

lemma allowCorrPCS_false_of_sendA_injectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hinj : sendAInjectsChallengeKey gp σ = true) :
    CKAScheme.allowCorrPCS gp σ = false := by
  have hparts :
      (gp.challengedParty == .B) = true ∧
        (σ.tA == gp.challengeEpoch - 1) = true := by
    simpa [sendAInjectsChallengeKey] using ((Bool.and_eq_true _ _).mp hinj)
  have ht : σ.tA = gp.challengeEpoch - 1 := beq_iff_eq.mp hparts.2
  exact allowCorrPCS_false_of_two_le_deltaPCS_of_tA_pred gp σ hΔ ht

lemma allowCorrPCS_false_of_sendB_injectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hinj : sendBInjectsChallengeKey gp σ = true) :
    CKAScheme.allowCorrPCS gp σ = false := by
  have hparts :
      (gp.challengedParty == .A) = true ∧
        (σ.tB == gp.challengeEpoch - 1) = true := by
    simpa [sendBInjectsChallengeKey] using ((Bool.and_eq_true _ _).mp hinj)
  have ht : σ.tB = gp.challengeEpoch - 1 := beq_iff_eq.mp hparts.2
  exact allowCorrPCS_false_of_two_le_deltaPCS_of_tB_pred gp σ hΔ ht

def oracleSendAWithChallengePk
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) :
    QueryImpl (Unit →ₒ Option (Message C PK × K))
      (StateT (SecurityState K PK SK C) ProbComp) :=
  fun () => do
    let σ ← get
    if CKAScheme.validStep σ.lastAction .sendA then
      let σSend := { σ with tA := σ.tA + 1 }
      match σSend.stA with
      | .sendReady pk => do
          let (c, key) ← liftM (kem.encaps pk)
          let (pkGenerated, skNext) ← liftM kem.keygen
          let pkNext := if sendAInjectsChallengeKey gp σSend then pkStar else pkGenerated
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

def oracleSendBWithChallengePk
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) :
    QueryImpl (Unit →ₒ Option (Message C PK × K))
      (StateT (SecurityState K PK SK C) ProbComp) :=
  fun () => do
    let σ ← get
    if CKAScheme.validStep σ.lastAction .sendB then
      let σSend := { σ with tB := σ.tB + 1 }
      match σSend.stB with
      | .sendReady pk => do
          let (c, key) ← liftM (kem.encaps pk)
          let (pkGenerated, skNext) ← liftM kem.keygen
          let pkNext := if sendBInjectsChallengeKey gp σSend then pkStar else pkGenerated
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

def prefixImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) :
    QueryImpl (SecuritySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
  fun t =>
    match t with
    | CKAScheme.ckaSecuritySpec.OSendA =>
        oracleSendAWithChallengePk kem gp pkStar ()
    | CKAScheme.ckaSecuritySpec.OSendB =>
        oracleSendBWithChallengePk kem gp pkStar ()
    | other =>
        securityImpl kem hDet leak gp false other

end kemCKA
