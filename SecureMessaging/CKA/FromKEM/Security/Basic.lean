/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Correctness

/-!
# CKA from KEM — Security Foundations

Shared setup for the security analysis of the generic CKA-from-KEM construction
of [ACD19, Section 4.1.2]: the admissible challenge parameters, the specialized
adversary and oracle-spec aliases, the epoch-counter invariant of the A-first
alternating game, and the modified send oracles that embed a KEM challenge
public key at the epoch before the challenge.

These declarations are the Lean counterpart of the bookkeeping in the paper's
reduction. They fix when the challenge epoch is a send epoch for the challenged
party, show that corruption and randomness leaks are disallowed around the
challenge, and describe how the reduction installs `pkStar` one epoch before the
challenge send.
-/

open OracleSpec OracleComp ENNReal KEMScheme

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

/-- The CKA adversary interface specialized to the leaking KEM construction.

The adversary receives the generic CKA security oracle family with the
send-randomness type `RandLeak.Rand leak`: the randomness of KEM encapsulation
paired with the randomness of the fresh next KEM key pair.
-/
abbrev Adversary {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem) :=
  CKAScheme.CKAAdversary (State PK SK) (Message C PK) K leak.Rand

/-- The generic CKA security oracle spec specialized to the leaking KEM
construction: the send-randomness type is `RandLeak.Rand leak`. -/
abbrev securitySpec {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem) :=
  CKAScheme.ckaSecuritySpec (State PK SK) (Message C PK) K leak.Rand

/-- The CKA game state specialized to the KEM construction. -/
abbrev SecurityState (K PK SK C : Type) :=
  CKAScheme.GameState (State PK SK) K (Message C PK)

/-- Epoch-counter invariant for the A-first alternating CKA game.

After a send/challenge by one party, that party's counter is exactly one ahead
of the receiver's counter. After a receive, counters are synchronized again.
-/
def epochCounterInv (s : SecurityState K PK SK C) : Prop :=
  match s.lastAction with
  | none | some .recvA | some .recvB => s.tA = s.tB
  | some .sendA | some .challA => s.tA = s.tB + 1
  | some .sendB | some .challB => s.tB = s.tA + 1

lemma epochCounterInv_after_sendA
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hstep : CKAScheme.validStep σ.lastAction .sendA = true) :
    epochCounterInv
      ({ σ with lastAction := some .sendA, tA := σ.tA + 1 } :
        SecurityState K PK SK C) := by
  cases hlast : σ.lastAction with
  | none =>
      simp [epochCounterInv, hlast] at hInv ⊢
      omega
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hstep
      case recvA =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega

lemma epochCounterInv_after_challA
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hstep : CKAScheme.validStep σ.lastAction .challA = true) :
    epochCounterInv
      ({ σ with lastAction := some .challA, tA := σ.tA + 1 } :
        SecurityState K PK SK C) := by
  cases hlast : σ.lastAction with
  | none =>
      simp [epochCounterInv, hlast] at hInv ⊢
      omega
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hstep
      case recvA =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega

lemma epochCounterInv_after_recvB
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hstep : CKAScheme.validStep σ.lastAction .recvB = true) :
    epochCounterInv
      ({ σ with lastAction := some .recvB, tB := σ.tB + 1 } :
        SecurityState K PK SK C) := by
  cases hlast : σ.lastAction with
  | none =>
      simp [CKAScheme.validStep, hlast] at hstep
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hstep
      case sendA =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega
      case challA =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega

lemma epochCounterInv_after_sendB
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hstep : CKAScheme.validStep σ.lastAction .sendB = true) :
    epochCounterInv
      ({ σ with lastAction := some .sendB, tB := σ.tB + 1 } :
        SecurityState K PK SK C) := by
  cases hlast : σ.lastAction with
  | none =>
      simp [CKAScheme.validStep, hlast] at hstep
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hstep
      case recvB =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega

lemma epochCounterInv_after_challB
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hstep : CKAScheme.validStep σ.lastAction .challB = true) :
    epochCounterInv
      ({ σ with lastAction := some .challB, tB := σ.tB + 1 } :
        SecurityState K PK SK C) := by
  cases hlast : σ.lastAction with
  | none =>
      simp [CKAScheme.validStep, hlast] at hstep
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hstep
      case recvB =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega

lemma epochCounterInv_after_recvA
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hstep : CKAScheme.validStep σ.lastAction .recvA = true) :
    epochCounterInv
      ({ σ with lastAction := some .recvA, tA := σ.tA + 1 } :
        SecurityState K PK SK C) := by
  cases hlast : σ.lastAction with
  | none =>
      simp [CKAScheme.validStep, hlast] at hstep
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hstep
      case sendB =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega
      case challB =>
        simp [epochCounterInv, hlast] at hInv ⊢
        omega

def securityImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    QueryImpl (securitySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
  CKAScheme.ckaSecurityImpl gp isRandom (scheme kem hDet leak)

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

lemma lastAction_of_willChallengeA
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeA gp σ = true) :
    σ.lastAction = none ∨ σ.lastAction = some .recvA := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have hvalidAndParty := (Bool.and_eq_true _ _).mp hparts.1
  have hvalid : CKAScheme.validStep σ.lastAction .challA = true :=
    hvalidAndParty.1
  cases hlast : σ.lastAction with
  | none =>
      exact Or.inl rfl
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hvalid
      case recvA =>
        exact Or.inr rfl

lemma lastAction_of_willChallengeB
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeB gp σ = true) :
    σ.lastAction = some .recvB := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have hvalidAndParty := (Bool.and_eq_true _ _).mp hparts.1
  have hvalid : CKAScheme.validStep σ.lastAction .challB = true :=
    hvalidAndParty.1
  cases hlast : σ.lastAction with
  | none =>
      simp [CKAScheme.validStep, hlast] at hvalid
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at hvalid
      case recvB =>
        rfl

lemma allowCorr_receiverB_false_after_challA
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true) :
    CKAScheme.allowCorr gp
      ({ σ with lastAction := some .challA, tA := σ.tA + 1 } :
        SecurityState K PK SK C) .B = false := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have ht : σ.tA + 1 = gp.challengeEpoch := beq_iff_eq.mp hparts.2
  have hlast := lastAction_of_willChallengeA gp σ hWill
  have hsync : σ.tA = σ.tB := by
    rcases hlast with hlast | hlast <;>
      simpa [epochCounterInv, hlast] using hInv
  have hΔ : 2 ≤ gp.ΔPCS := hgp.two_le_deltaPCS
  have hfsNot : ¬ gp.challengeEpoch + gp.ΔFS ≤ σ.tB := by
    rw [hgp.deltaFS_zero]
    omega
  have hmax : max (σ.tA + 1) σ.tB = gp.challengeEpoch := by
    apply le_antisymm
    · rw [max_le_iff]
      constructor <;> omega
    · rw [← ht]
      exact Nat.le_max_left _ _
  have hpcsNot : ¬ max (σ.tA + 1) σ.tB + gp.ΔPCS ≤ gp.challengeEpoch := by
    rw [hmax]
    omega
  have hpcs :
      CKAScheme.allowCorrPCS gp
        ({ σ with lastAction := some .challA, tA := σ.tA + 1 } :
          SecurityState K PK SK C) = false := by
    simp [CKAScheme.allowCorrPCS, hpcsNot]
  have hfs :
      CKAScheme.allowCorrFS gp
        ({ σ with lastAction := some .challA, tA := σ.tA + 1 } :
          SecurityState K PK SK C) .B = false := by
    simp [CKAScheme.allowCorrFS, hfsNot]
  unfold CKAScheme.allowCorr
  rw [hpcs]
  simp [hfs]

lemma allowCorr_receiverA_false_after_challB
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true) :
    CKAScheme.allowCorr gp
      ({ σ with lastAction := some .challB, tB := σ.tB + 1 } :
        SecurityState K PK SK C) .A = false := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have ht : σ.tB + 1 = gp.challengeEpoch := beq_iff_eq.mp hparts.2
  have hlast := lastAction_of_willChallengeB gp σ hWill
  have hsync : σ.tA = σ.tB := by
    simpa [epochCounterInv, hlast] using hInv
  have hΔ : 2 ≤ gp.ΔPCS := hgp.two_le_deltaPCS
  have hfsNot : ¬ gp.challengeEpoch + gp.ΔFS ≤ σ.tA := by
    rw [hgp.deltaFS_zero]
    omega
  have hmax : max σ.tA (σ.tB + 1) = gp.challengeEpoch := by
    apply le_antisymm
    · rw [max_le_iff]
      constructor <;> omega
    · rw [← ht]
      exact Nat.le_max_right _ _
  have hpcsNot : ¬ max σ.tA (σ.tB + 1) + gp.ΔPCS ≤ gp.challengeEpoch := by
    rw [hmax]
    omega
  have hpcs :
      CKAScheme.allowCorrPCS gp
        ({ σ with lastAction := some .challB, tB := σ.tB + 1 } :
          SecurityState K PK SK C) = false := by
    simp [CKAScheme.allowCorrPCS, hpcsNot]
  have hfs :
      CKAScheme.allowCorrFS gp
        ({ σ with lastAction := some .challB, tB := σ.tB + 1 } :
          SecurityState K PK SK C) .A = false := by
    simp [CKAScheme.allowCorrFS, hfsNot]
  unfold CKAScheme.allowCorr
  rw [hpcs]
  simp [hfs]

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
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) :
    QueryImpl (securitySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
  fun t =>
    match t with
    | CKAScheme.ckaSecuritySpec.OSendA =>
        oracleSendAWithChallengePk kem gp pkStar ()
    | CKAScheme.ckaSecuritySpec.OSendB =>
        oracleSendBWithChallengePk kem gp pkStar ()
    | other =>
        securityImpl kem hDet leak gp false other

end kemCKA
