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

Throughout the security modules, "honest" means: run by the construction's own
algorithms exactly as the security experiment prescribes — honestly generated
keys come from `kem.keygen` at the protocol step, and the honest implementation
`securityImpl` answers every oracle that way. It contrasts with the hybrid
oracles that embed KEM challenge material and with the reduction's simulated
implementations that answer without the challenge secrets. It is unrelated to
the corruption oracles: both parties always follow the protocol, and corruption
only exposes state.
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

/-- The generic CKA security oracle implementation instantiated with the KEM
construction and a fixed challenge bit. -/
def securityImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    QueryImpl (securitySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
  CKAScheme.ckaSecurityImpl gp isRandom (scheme kem hDet leak)

/-- The A-challenge is due: a `challA` step is valid from the current state,
A is the challenged party, and A's next counter value is the challenge
epoch. -/
def willChallengeA
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .challA &&
    (gp.challengedParty == .A) &&
    (σ.tA + 1 == gp.challengeEpoch)

/-- The B-challenge is due, the mirror of `willChallengeA`. -/
def willChallengeB
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .challB &&
    (gp.challengedParty == .B) &&
    (σ.tB + 1 == gp.challengeEpoch)

/-- When the A-challenge is due, the previous action can only be the game
start or a receive by A: those are the states from which `challA` is a valid
step. -/
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

/-- When the B-challenge is due, the previous action must be a receive by B:
`challB` is not a valid first step, so the game-start case is excluded. -/
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

/-- Right after the A-challenge, corrupting the receiver B is disallowed.

Counters are synchronized before the challenge, so the challenge epoch equals
the counter maximum just after it; `2 ≤ ΔPCS` then blocks the corruption, and
`ΔFS = 0` closes the forward-secrecy exception. -/
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

/-- Right after the B-challenge, corrupting the receiver A is disallowed, the
mirror of `allowCorr_receiverB_false_after_challA`. -/
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

/-- A's current send precedes a B-challenge: B is the challenged party and A
is sending at the epoch before the challenge epoch. On this send the modified
oracles put the challenge public key into the outgoing message, so the
challenged B-send encapsulates against it. -/
def sendAInjectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  (gp.challengedParty == .B) && (σ.tA == gp.challengeEpoch - 1)

/-- B's current send precedes an A-challenge, the mirror of
`sendAInjectsChallengeKey`. -/
def sendBInjectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  (gp.challengedParty == .A) && (σ.tB == gp.challengeEpoch - 1)

/-- Corruption is PCS-blocked whenever A's counter sits at the epoch before
the challenge: the counter maximum is then inside the `2 ≤ ΔPCS` window. -/
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

/-- Corruption is PCS-blocked whenever B's counter sits at the epoch before
the challenge, the mirror of
`allowCorrPCS_false_of_two_le_deltaPCS_of_tA_pred`. -/
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

/-- Honest A-send oracle that embeds the challenge public key.

Identical to the construction's send oracle except at the send preceding a
B-challenge (`sendAInjectsChallengeKey`): there the outgoing message carries
`pkStar` instead of the freshly generated public key. The fresh key pair is
still drawn, so the randomness shape matches the honest oracle, and A still
stores the generated secret key. -/
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

/-- Honest B-send oracle that embeds the challenge public key, the mirror of
`oracleSendAWithChallengePk`. -/
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

/-- The pre-challenge oracle implementation of the reduction: the honest
implementation with both send oracles replaced by their `pkStar`-embedding
versions. The challenge bit only matters at a valid challenge query, which
the prefix machinery intercepts, so it is fixed to `false`. -/
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
