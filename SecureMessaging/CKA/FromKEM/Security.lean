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

private lemma challengeEpoch_pos_of_compatible
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

private lemma challengeEpoch_pos_of_admissible
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

private abbrev SecuritySpec
    {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem) :=
  CKAScheme.ckaSecuritySpec (State PK SK) (Message C PK) K (Rand leak)

private abbrev SecurityState
    (K PK SK C : Type) :=
  CKAScheme.GameState (State PK SK) K (Message C PK)

private abbrev SecurityCKA
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem) :=
  schemeWithLeak kem hDet leak

private def securityImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    QueryImpl (SecuritySpec leak) (StateT (SecurityState K PK SK C) ProbComp) :=
  CKAScheme.ckaSecurityImpl gp isRandom (SecurityCKA kem hDet leak)

private def willChallengeA
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .challA &&
    (gp.challengedParty == .A) &&
    (σ.tA + 1 == gp.challengeEpoch)

private def willChallengeB
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .challB &&
    (gp.challengedParty == .B) &&
    (σ.tB + 1 == gp.challengeEpoch)

private def sendAInjectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  (gp.challengedParty == .B) && (σ.tA == gp.challengeEpoch - 1)

private def sendBInjectsChallengeKey
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  (gp.challengedParty == .A) && (σ.tB == gp.challengeEpoch - 1)

private lemma allowCorrPCS_false_of_two_le_deltaPCS_of_tA_pred
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

private lemma allowCorrPCS_false_of_two_le_deltaPCS_of_tB_pred
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

private lemma allowCorrPCS_false_of_sendA_injectsChallengeKey
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

private lemma allowCorrPCS_false_of_sendB_injectsChallengeKey
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

private def oracleSendAWithChallengePk
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

private def oracleSendBWithChallengePk
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

private def prefixImpl [SampleableType K] [DecidableEq K]
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

private inductive CKAChallengeStepResult
    {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem)
    (α : Type) where
  | done (a : α)
  | pausedA
      (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) α)
  | pausedB
      (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) α)

private def CKAChallengeStepResult.map
    {K PK SK C α β : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    {leak : KEMRandLeak kem}
    (f : α → β) :
    CKAChallengeStepResult leak α → CKAChallengeStepResult leak β
  | .done a => .done (f a)
  | .pausedA cont => .pausedA (fun x => f <$> cont x)
  | .pausedB cont => .pausedB (fun x => f <$> cont x)

private inductive CKAReductionState
    {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem) where
  | done (guess : Bool)
  | pausedA
      (σ : SecurityState K PK SK C)
      (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) Bool)
  | pausedB
      (σ : SecurityState K PK SK C)
      (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) Bool)

private inductive PendingChallengeRecv (K PK C : Type) where
  | none
  | aToB (key : K) (nextPk : PK) (msg : Message C PK)
  | bToA (key : K) (nextPk : PK) (msg : Message C PK)

private structure PostChallengeState
    (K PK SK C : Type) where
  game : SecurityState K PK SK C
  pending : PendingChallengeRecv K PK C

private def liftSecurityImplToPost [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (SecuritySpec leak).Domain) :
    StateT (PostChallengeState K PK SK C) ProbComp ((SecuritySpec leak).Range t) := do
  let ps ← get
  let (out, game') ← (securityImpl kem hDet leak gp false t).run ps.game
  set { ps with game := game' }
  return out

private def postChallengeImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams) :
    QueryImpl (SecuritySpec leak) (StateT (PostChallengeState K PK SK C) ProbComp) :=
  fun t => do
    let ps ← get
    match t with
    | CKAScheme.ckaSecuritySpec.ORecvB =>
        match ps.pending with
        | .aToB key nextPk _msg =>
            if CKAScheme.validStep ps.game.lastAction .recvB then
              let ps' : PostChallengeState K PK SK C := {
                game := { ps.game with
                  stB := State.sendReady nextPk,
                  rhoA := none,
                  keyA := none,
                  correct := ps.game.correct && (ps.game.keyA == some key),
                  lastAction := some .recvB,
                  tB := ps.game.tB + 1 },
                pending := .none }
              set ps'
              return ()
            else
              liftSecurityImplToPost kem hDet leak gp
                (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)
        | _ =>
            liftSecurityImplToPost kem hDet leak gp
              (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)
    | CKAScheme.ckaSecuritySpec.ORecvA =>
        match ps.pending with
        | .bToA key nextPk _msg =>
            if CKAScheme.validStep ps.game.lastAction .recvA then
              let ps' : PostChallengeState K PK SK C := {
                game := { ps.game with
                  stA := State.sendReady nextPk,
                  rhoB := none,
                  keyB := none,
                  correct := ps.game.correct && (ps.game.keyB == some key),
                  lastAction := some .recvA,
                  tA := ps.game.tA + 1 },
                pending := .none }
              set ps'
              return ()
            else
              liftSecurityImplToPost kem hDet leak gp
                (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)
        | _ =>
            liftSecurityImplToPost kem hDet leak gp
              (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)
    | other =>
        liftSecurityImplToPost kem hDet leak gp other

private def finishChallengeStep [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (res : CKAChallengeStepResult leak Bool)
    (σ : SecurityState K PK SK C)
    (cStar : C) (kStar : K) : ProbComp Bool :=
  match res with
  | .done guess => pure (!guess)
  | .pausedA cont => do
      let (pkNext, skNext) ← kem.keygen
      let msg : Message C PK := (cStar, pkNext)
      let σ' : SecurityState K PK SK C := { σ with
        stA := State.recvReady skNext,
        rhoA := some msg,
        keyA := some kStar,
        lastAction := some .challA,
        tA := σ.tA + 1 }
      let ps0 : PostChallengeState K PK SK C :=
        { game := σ', pending := .aToB kStar pkNext msg }
      let (guess, _) ←
        (simulateQ (postChallengeImpl kem hDet leak gp) (cont (some (msg, kStar)))).run ps0
      pure (!guess)
  | .pausedB cont => do
      let (pkNext, skNext) ← kem.keygen
      let msg : Message C PK := (cStar, pkNext)
      let σ' : SecurityState K PK SK C := { σ with
        stB := State.recvReady skNext,
        rhoB := some msg,
        keyB := some kStar,
        lastAction := some .challB,
        tB := σ.tB + 1 }
      let ps0 : PostChallengeState K PK SK C :=
        { game := σ', pending := .bToA kStar pkNext msg }
      let (guess, _) ←
        (simulateQ (postChallengeImpl kem hDet leak gp) (cont (some (msg, kStar)))).run ps0
      pure (!guess)

private def finishChallengeStepRaw [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (res : CKAChallengeStepResult leak Bool)
    (σ : SecurityState K PK SK C)
    (cStar : C) (kStar : K) : ProbComp Bool :=
  match res with
  | .done guess => pure guess
  | .pausedA cont => do
      let (pkNext, skNext) ← kem.keygen
      let msg : Message C PK := (cStar, pkNext)
      let σ' : SecurityState K PK SK C := { σ with
        stA := State.recvReady skNext,
        rhoA := some msg,
        keyA := some kStar,
        lastAction := some .challA,
        tA := σ.tA + 1 }
      let ps0 : PostChallengeState K PK SK C :=
        { game := σ', pending := .aToB kStar pkNext msg }
      let (guess, _) ←
        (simulateQ (postChallengeImpl kem hDet leak gp) (cont (some (msg, kStar)))).run ps0
      pure guess
  | .pausedB cont => do
      let (pkNext, skNext) ← kem.keygen
      let msg : Message C PK := (cStar, pkNext)
      let σ' : SecurityState K PK SK C := { σ with
        stB := State.recvReady skNext,
        rhoB := some msg,
        keyB := some kStar,
        lastAction := some .challB,
        tB := σ.tB + 1 }
      let ps0 : PostChallengeState K PK SK C :=
        { game := σ', pending := .bToA kStar pkNext msg }
      let (guess, _) ←
        (simulateQ (postChallengeImpl kem hDet leak gp) (cont (some (msg, kStar)))).run ps0
      pure guess

private lemma finishChallengeStep_eq_not_map_raw [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (res : CKAChallengeStepResult leak Bool)
    (σ : SecurityState K PK SK C)
    (cStar : C) (kStar : K) :
    finishChallengeStep kem hDet leak gp res σ cStar kStar =
      (! ·) <$> finishChallengeStepRaw kem hDet leak gp res σ cStar kStar := by
  cases res <;> simp [finishChallengeStep, finishChallengeStepRaw]

private inductive ReductionBranchState (K PK SK C : Type) where
  | pre (game : SecurityState K PK SK C)
  | post (post : PostChallengeState K PK SK C)

private def reductionBranchInitialState
    (gp : CKAScheme.GameParams)
    (pkStar pk0 : PK) (sk0 : SK) :
    ReductionBranchState K PK SK C :=
  .pre <|
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (State.recvReady sk0)

/-- Single-pass view of the concrete IND-CPA reduction branch.

While in `.pre`, ordinary queries are handled by the prefix simulator that has
installed `pkStar` at the would-be challenge public key. The first valid
challenge query consumes `(cStar, kStar)`, installs the pending receive override,
and switches to `.post`. All later queries delegate to `postChallengeImpl`.
This is equivalent to the split `preChallenge`/`postChallenge` API, but has the
right shape for relational `simulateQ` reasoning over the adversary. -/
private def reductionBranchImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K) :
    QueryImpl (SecuritySpec leak)
      (StateT (ReductionBranchState K PK SK C) ProbComp) :=
  fun t => do
    let rs ← get
    match rs with
    | .pre σ =>
        match t with
        | CKAScheme.ckaSecuritySpec.OChallA =>
            if willChallengeA gp σ then
              let (pkNext, skNext) ← liftM kem.keygen
              let msg : Message C PK := (cStar, pkNext)
              let σ' : SecurityState K PK SK C := { σ with
                stA := State.recvReady skNext,
                rhoA := some msg,
                keyA := some kStar,
                lastAction := some .challA,
                tA := σ.tA + 1 }
              let ps' : PostChallengeState K PK SK C :=
                { game := σ', pending := .aToB kStar pkNext msg }
              set (ReductionBranchState.post ps')
              return some (msg, kStar)
            else
              let (out, σ') ←
                (prefixImpl kem hDet leak gp pkStar
                  (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)).run σ
              set (ReductionBranchState.pre σ')
              return out
        | CKAScheme.ckaSecuritySpec.OChallB =>
            if willChallengeB gp σ then
              let (pkNext, skNext) ← liftM kem.keygen
              let msg : Message C PK := (cStar, pkNext)
              let σ' : SecurityState K PK SK C := { σ with
                stB := State.recvReady skNext,
                rhoB := some msg,
                keyB := some kStar,
                lastAction := some .challB,
                tB := σ.tB + 1 }
              let ps' : PostChallengeState K PK SK C :=
                { game := σ', pending := .bToA kStar pkNext msg }
              set (ReductionBranchState.post ps')
              return some (msg, kStar)
            else
              let (out, σ') ←
                (prefixImpl kem hDet leak gp pkStar
                  (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)).run σ
              set (ReductionBranchState.pre σ')
              return out
        | other =>
            let (out, σ') ← (prefixImpl kem hDet leak gp pkStar other).run σ
            set (ReductionBranchState.pre σ')
            return out
    | .post ps =>
        let (out, ps') ← (postChallengeImpl kem hDet leak gp t).run ps
        set (ReductionBranchState.post ps')
        return out

private def ckaReductionBranchRun [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let rs0 : ReductionBranchState K PK SK C :=
    reductionBranchInitialState gp pkStar pk0 sk0
  let (guess, _) ←
    (simulateQ (reductionBranchImpl kem hDet leak gp pkStar cStar kStar) adv).run rs0
  pure (!guess)

private lemma reductionBranchImpl_post_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (t : (SecuritySpec leak).Domain)
    (ps : PostChallengeState K PK SK C) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar t).run
        (ReductionBranchState.post ps) =
      (do
        let (out, ps') ← (postChallengeImpl kem hDet leak gp t).run ps
        pure (out, ReductionBranchState.post ps')) := by
  simp [reductionBranchImpl, StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma reductionBranchImpl_post_simulateQ_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    {α : Type}
    (adv : OracleComp (SecuritySpec leak) α)
    (ps : PostChallengeState K PK SK C) :
    (simulateQ (reductionBranchImpl kem hDet leak gp pkStar cStar kStar) adv).run
        (ReductionBranchState.post ps) =
      (do
        let (out, ps') ← (simulateQ (postChallengeImpl kem hDet leak gp) adv).run ps
        pure (out, ReductionBranchState.post ps')) := by
  induction adv using OracleComp.inductionOn generalizing ps with
  | pure a =>
      simp
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [reductionBranchImpl_post_run]
      simp only [bind_assoc, pure_bind]
      refine bind_congr (m := ProbComp) fun p => ?_
      simpa using ih p.1 p.2

private lemma reductionBranchImpl_pre_challA_run_of_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeA gp σ = true) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)).run
        (ReductionBranchState.pre σ) =
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let σ' : SecurityState K PK SK C := { σ with
          stA := State.recvReady skNext,
          rhoA := some msg,
          keyA := some kStar,
          lastAction := some .challA,
          tA := σ.tA + 1 }
        let ps' : PostChallengeState K PK SK C :=
          { game := σ', pending := .aToB kStar pkNext msg }
        pure (some (msg, kStar), ReductionBranchState.post ps')) := by
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma reductionBranchImpl_pre_challA_run_of_not_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeA gp σ = false) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)).run
        (ReductionBranchState.pre σ) =
      (do
        let (out, σ') ←
          (prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)).run σ
        pure (out, ReductionBranchState.pre σ')) := by
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma reductionBranchImpl_pre_challB_run_of_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeB gp σ = true) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)).run
        (ReductionBranchState.pre σ) =
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let σ' : SecurityState K PK SK C := { σ with
          stB := State.recvReady skNext,
          rhoB := some msg,
          keyB := some kStar,
          lastAction := some .challB,
          tB := σ.tB + 1 }
        let ps' : PostChallengeState K PK SK C :=
          { game := σ', pending := .bToA kStar pkNext msg }
        pure (some (msg, kStar), ReductionBranchState.post ps')) := by
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma reductionBranchImpl_pre_challB_run_of_not_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeB gp σ = false) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)).run
        (ReductionBranchState.pre σ) =
      (do
        let (out, σ') ←
          (prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)).run σ
        pure (out, ReductionBranchState.pre σ')) := by
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

private def challengePrefix [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type} :
    OracleComp (SecuritySpec leak) α →
      StateT (SecurityState K PK SK C) ProbComp
        (CKAChallengeStepResult leak α) :=
  OracleComp.construct
    (fun a => pure (.done a))
    (fun t oa rec => do
      match t with
      | CKAScheme.ckaSecuritySpec.OChallA =>
          let σ ← get
          if willChallengeA gp σ then
            pure (.pausedA oa)
          else
            let out ←
              (prefixImpl kem hDet leak gp pkStar
                (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain))
            rec out
      | CKAScheme.ckaSecuritySpec.OChallB =>
          let σ ← get
          if willChallengeB gp σ then
            pure (.pausedB oa)
          else
            let out ←
              (prefixImpl kem hDet leak gp pkStar
                (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain))
            rec out
      | other =>
          let out ← (prefixImpl kem hDet leak gp pkStar other)
          rec out)

private lemma challengePrefix_pure [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type} (a : α) :
    challengePrefix kem hDet leak gp pkStar (pure a : OracleComp (SecuritySpec leak) α) =
      pure (.done a) := by
  simp [challengePrefix]

private lemma challengePrefix_query_challA [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type}
    (mx : Option (Message C PK × K) → OracleComp (SecuritySpec leak) α) :
    challengePrefix kem hDet leak gp pkStar
        ((SecuritySpec leak).query
            (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain) >>= mx) =
      (do
        let σ ← get
        if willChallengeA gp σ then
          pure (.pausedA mx)
        else
          let out ← prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)
          challengePrefix kem hDet leak gp pkStar (mx out)) := by
  simp [challengePrefix]

private lemma challengePrefix_query_challB [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type}
    (mx : Option (Message C PK × K) → OracleComp (SecuritySpec leak) α) :
    challengePrefix kem hDet leak gp pkStar
        ((SecuritySpec leak).query
            (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain) >>= mx) =
      (do
        let σ ← get
        if willChallengeB gp σ then
          pure (.pausedB mx)
        else
          let out ← prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)
          challengePrefix kem hDet leak gp pkStar (mx out)) := by
  simp [challengePrefix]

private def ckaToINDCPAReduction [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) :
    INDCPAReduction kem leak adv gp where
  State := CKAReductionState leak
  preChallenge pkStar := do
    let (pk0, sk0) ← kem.keygen
    let σ0 :=
      CKAScheme.initGameState
        (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
          State.sendReady pkStar
        else
          State.sendReady pk0)
        (State.recvReady sk0)
    let (res, σ) ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
    match res with
    | .done guess => pure (.done guess)
    | .pausedA cont => pure (.pausedA σ cont)
    | .pausedB cont => pure (.pausedB σ cont)
  postChallenge st cStar kStar :=
    match st with
    | .done guess => pure (!guess)
    | .pausedA σ cont =>
        finishChallengeStep kem hDet leak gp (.pausedA cont) σ cStar kStar
    | .pausedB σ cont =>
        finishChallengeStep kem hDet leak gp (.pausedB cont) σ cStar kStar

private lemma ckaToINDCPAReduction_pre_post_eq_finish
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K) :
    (do
      let st ← (ckaToINDCPAReduction kem hDet leak adv gp).preChallenge pkStar
      (ckaToINDCPAReduction kem hDet leak adv gp).postChallenge st cStar kStar) =
    (do
      let (pk0, sk0) ← kem.keygen
      let σ0 :=
        CKAScheme.initGameState
          (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
            State.sendReady pkStar
          else
            State.sendReady pk0)
          (State.recvReady sk0)
      let (res, σ) ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
      finishChallengeStep kem hDet leak gp res σ cStar kStar) := by
  unfold ckaToINDCPAReduction
  simp only [Bool.and_eq_true, beq_iff_eq, bind_assoc]
  refine bind_congr (m := ProbComp) fun pk0_sk0 => ?_
  refine bind_congr (m := ProbComp) fun res_σ => ?_
  cases res_σ.1 <;> rfl

private lemma probCompRuntime_probOutput_eq {α : Type} (mx : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist mx] = Pr[= x | mx] := by
  rfl

private structure INDCPAPrefixState
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) where
  st : red.State
  cStar : C
  kReal : K
  kRand : K

private def indCPAPrefix [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp (INDCPAPrefixState kem red) := do
  let (pk, _sk) ← kem.keygen
  let st ← red.preChallenge pk
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  pure { st := st, cStar := cStar, kReal := kReal, kRand := kRand }

private def indCPAExpProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) (b : Bool) : ProbComp Bool := do
  let p ← indCPAPrefix kem red
  red.postChallenge p.st p.cStar (if b then p.kReal else p.kRand)


private def ckaReductionINDCPABranch [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
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

private def ckaReductionINDCPABranchRaw [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
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

private def ckaSecurityFixedFromState [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (isRandom : Bool) : ProbComp Bool := do
  let (guess, _) ←
    (simulateQ (securityImpl kem hDet leak gp isRandom) adv).run σ
  pure guess

private def ckaReductionRawFromState [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (adv : Adversary (kem := kem) leak)
    (rs : ReductionBranchState K PK SK C) : ProbComp Bool := do
  let (guess, _) ←
    (simulateQ (reductionBranchImpl kem hDet leak gp pkStar cStar kStar) adv).run rs
  pure guess

private def ckaReductionRawSplitFromState [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (adv : Adversary (kem := kem) leak)
    (σ : SecurityState K PK SK C) : ProbComp Bool := do
  let (res, σ') ← (challengePrefix kem hDet leak gp pkStar adv).run σ
  finishChallengeStepRaw kem hDet leak gp res σ' cStar kStar

private lemma ckaReductionRawFromState_post_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (adv : Adversary (kem := kem) leak)
    (ps : PostChallengeState K PK SK C) :
    ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar adv
        (ReductionBranchState.post ps) =
      (do
        let (guess, _ps') ←
          (simulateQ (postChallengeImpl kem hDet leak gp) adv).run ps
        pure guess) := by
  unfold ckaReductionRawFromState
  rw [reductionBranchImpl_post_simulateQ_run]
  simp

private lemma ckaReductionRawFromState_query_post_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (ps : PostChallengeState K PK SK C)
    (t : (SecuritySpec leak).Domain)
    (cont : (SecuritySpec leak).Range t → OracleComp (SecuritySpec leak) Bool) :
    ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
        (((liftM ((SecuritySpec leak).query t) :
            OracleComp (SecuritySpec leak) ((SecuritySpec leak).Range t)) >>= cont :
          OracleComp (SecuritySpec leak) Bool))
        (ReductionBranchState.post ps) =
      (do
        let (out, ps') ← (postChallengeImpl kem hDet leak gp t).run ps
        ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
          (cont out) (ReductionBranchState.post ps')) := by
  simp [ckaReductionRawFromState, simulateQ_bind, reductionBranchImpl,
    StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma ckaReductionRawFromState_query_challA_of_will
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) Bool)
    (hWill : willChallengeA gp σ = true) :
    ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
        (((liftM ((SecuritySpec leak).query
          (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)) :
            OracleComp (SecuritySpec leak) (Option (Message C PK × K))) >>= cont :
          OracleComp (SecuritySpec leak) Bool))
        (ReductionBranchState.pre σ) =
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let σ' : SecurityState K PK SK C := { σ with
          stA := State.recvReady skNext,
          rhoA := some msg,
          keyA := some kStar,
          lastAction := some .challA,
          tA := σ.tA + 1 }
        let ps' : PostChallengeState K PK SK C :=
          { game := σ', pending := .aToB kStar pkNext msg }
        ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
          (cont (some (msg, kStar))) (ReductionBranchState.post ps')) := by
  simp [ckaReductionRawFromState, simulateQ_bind, reductionBranchImpl, hWill,
    StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma ckaReductionRawFromState_query_challA_of_not_will
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) Bool)
    (hWill : willChallengeA gp σ = false) :
    ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
        (((liftM ((SecuritySpec leak).query
          (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)) :
            OracleComp (SecuritySpec leak) (Option (Message C PK × K))) >>= cont :
          OracleComp (SecuritySpec leak) Bool))
        (ReductionBranchState.pre σ) =
      (do
        let (out, σ') ←
          (prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)).run σ
        ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
          (cont out) (ReductionBranchState.pre σ')) := by
  simp [ckaReductionRawFromState, simulateQ_bind, reductionBranchImpl, hWill,
    StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma ckaReductionRawFromState_query_challB_of_will
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) Bool)
    (hWill : willChallengeB gp σ = true) :
    ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
        (((liftM ((SecuritySpec leak).query
          (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)) :
            OracleComp (SecuritySpec leak) (Option (Message C PK × K))) >>= cont :
          OracleComp (SecuritySpec leak) Bool))
        (ReductionBranchState.pre σ) =
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let σ' : SecurityState K PK SK C := { σ with
          stB := State.recvReady skNext,
          rhoB := some msg,
          keyB := some kStar,
          lastAction := some .challB,
          tB := σ.tB + 1 }
        let ps' : PostChallengeState K PK SK C :=
          { game := σ', pending := .bToA kStar pkNext msg }
        ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
          (cont (some (msg, kStar))) (ReductionBranchState.post ps')) := by
  simp [ckaReductionRawFromState, simulateQ_bind, reductionBranchImpl, hWill,
    StateT.run_bind, StateT.run_get, StateT.run_set]

private lemma ckaReductionRawFromState_query_challB_of_not_will
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) Bool)
    (hWill : willChallengeB gp σ = false) :
    ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
        (((liftM ((SecuritySpec leak).query
          (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)) :
            OracleComp (SecuritySpec leak) (Option (Message C PK × K))) >>= cont :
          OracleComp (SecuritySpec leak) Bool))
        (ReductionBranchState.pre σ) =
      (do
        let (out, σ') ←
          (prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)).run σ
        ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
          (cont out) (ReductionBranchState.pre σ')) := by
  simp [ckaReductionRawFromState, simulateQ_bind, reductionBranchImpl, hWill,
    StateT.run_bind, StateT.run_get, StateT.run_set]

private def ckaSecurityFixedBranch [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (State.sendReady pk0)
      (State.recvReady sk0)
  ckaSecurityFixedFromState kem hDet leak adv gp σ0 isRandom

private lemma securityExpFixedBit_eq_ckaSecurityFixedBranch
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv isRandom gp =
      ckaSecurityFixedBranch kem hDet leak adv gp isRandom := by
  unfold CKAScheme.securityExpFixedBit ckaSecurityFixedBranch
  unfold ckaSecurityFixedFromState SecurityCKA securityImpl
  simp [schemeWithLeak, initA, initB]

private lemma ckaReductionINDCPABranch_eq_not_map_raw [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
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

private lemma abs_probOutput_true_not_map_gap_eq (mx my : ProbComp Bool) :
    |(Pr[= true | (! ·) <$> mx]).toReal -
      (Pr[= true | (! ·) <$> my]).toReal| =
    |(Pr[= true | mx]).toReal - (Pr[= true | my]).toReal| := by
  simp [probOutput_false_eq_sub]
  ring_nf
  rw [show -Pr[= true | my].toReal + Pr[= true | mx].toReal =
      Pr[= true | mx].toReal - Pr[= true | my].toReal by ring]
  exact abs_sub_comm (Pr[= true | my].toReal) (Pr[= true | mx].toReal)

private lemma ckaReductionINDCPABranch_gap_eq_raw_gap [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
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

private lemma indCPAExpProb_ckaToINDCPAReduction_eq_branch
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
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

private def indCPABranchGameProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let p ← indCPAPrefix kem red
  let b ← ($ᵗ Bool)
  let z ← if b then red.postChallenge p.st p.cStar p.kReal
          else red.postChallenge p.st p.cStar p.kRand
  pure (b == z)

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

private lemma indCPAExpProb_probOutput_true_eq [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) (b : Bool) :
    Pr[= true | indCPAExpProb kem red b] =
      Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red b] := by
  unfold KEMScheme.IND_CPA_Exp
  rw [probCompRuntime_probOutput_eq]
  cases b <;>
    simp [indCPAExpProb, indCPAPrefix,
      ProbCompRuntime.probComp, ProbCompRuntime.liftProbComp, ProbCompLift.id,
      monad_norm]


private lemma ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp) b] =
      Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp b] := by
  rw [← indCPAExpProb_probOutput_true_eq]
  rw [indCPAExpProb_ckaToINDCPAReduction_eq_branch]

private lemma kem_ind_cpa_advantage_eq_fixed_branch_dist [SampleableType K]
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

private lemma abs_half_gap_le_abs (x : ℝ) : |x / 2| ≤ |x| := by
  have hnonneg : 0 ≤ |x| := abs_nonneg _
  rw [abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

private lemma cka_securityAdvantage_le_ind_cpa_of_fixed_gap
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (red : kem.IND_CPA_Adversary)
    (hGap :
      |(Pr[= true |
          CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
        (Pr[= true |
          CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
      |(Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red true]).toReal -
        (Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp red false]).toReal|) :
    CKAScheme.securityAdvantage (SecurityCKA kem hDet leak) adv gp ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp red := by
  rw [kem_ind_cpa_advantage_eq_fixed_branch_dist]
  unfold CKAScheme.securityAdvantage
  rw [CKAScheme.securityExp_toReal_sub_half]
  exact le_trans (abs_half_gap_le_abs _) hGap

private lemma cka_fixed_gap_le_normalized_reduction_raw_gap_pure
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (guess : Bool) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak)
          (pure guess : OracleComp (SecuritySpec leak) Bool) true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak)
          (pure guess : OracleComp (SecuritySpec leak) Bool) false gp]).toReal| ≤
    |(Pr[= true |
        ckaReductionINDCPABranchRaw kem hDet leak
          (pure guess : OracleComp (SecuritySpec leak) Bool) gp true]).toReal -
      (Pr[= true |
        ckaReductionINDCPABranchRaw kem hDet leak
          (pure guess : OracleComp (SecuritySpec leak) Bool) gp false]).toReal| := by
  simp [CKAScheme.securityExpFixedBit, ckaReductionINDCPABranchRaw,
    SecurityCKA, schemeWithLeak, finishChallengeStepRaw]

private lemma cka_fixed_gap_le_normalized_reduction_raw_gap
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (_hgp : AdmissibleParams gp) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
    |(Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaReductionINDCPABranchRaw kem hDet leak adv gp false]).toReal| := by
  rw [securityExpFixedBit_eq_ckaSecurityFixedBranch]
  rw [securityExpFixedBit_eq_ckaSecurityFixedBranch]
  /- Remaining semantic obligation: relate the normalized fixed-bit CKA branch
     to the raw normalized reduction branch. This is now only the protocol-level
     game-hop/cancellation argument over `challengePrefix`; the CKA initialization,
     IND-CPA sampling order, and final Boolean complement have all been factored
     out. -/
  sorry

private lemma cka_fixed_gap_le_normalized_reduction_gap
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
    |(Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp true]).toReal -
      (Pr[= true | ckaReductionINDCPABranch kem hDet leak adv gp false]).toReal| := by
  rw [ckaReductionINDCPABranch_gap_eq_raw_gap]
  exact cka_fixed_gap_le_normalized_reduction_raw_gap kem hDet leak adv gp hgp

private lemma ckaToINDCPAReduction_fixed_gap_dominates
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (_hgp : AdmissibleParams gp) :
    |(Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv true gp]).toReal -
      (Pr[= true |
        CKAScheme.securityExpFixedBit (SecurityCKA kem hDet leak) adv false gp]).toReal| ≤
    |(Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp) true]).toReal -
      (Pr[= true | kem.IND_CPA_Exp ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp) false]).toReal| := by
  rw [ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch
    kem hDet leak adv gp true]
  rw [ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch
    kem hDet leak adv gp false]
  exact cka_fixed_gap_le_normalized_reduction_gap kem hDet leak adv gp _hgp

/-- Existential security-reduction statement for CKA from a KEM.

For every CKA adversary and admissible challenge parameters, there exists an
IND-CPA adversary against the input KEM whose advantage upper-bounds the
CKA security advantage of the constructed protocol.

The statement is intentionally existential: this specification PR records the
proof obligation. A later proof PR should refine the existential witness to a
named concrete reduction.
-/
theorem security_reduces_to_ind_cpa_exists [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    ∃ red : INDCPAReduction kem leak adv gp,
      CKAScheme.securityAdvantage (schemeWithLeak kem hDet leak) adv gp ≤
        kem.IND_CPA_Advantage ProbCompRuntime.probComp red := by
  refine ⟨ckaToINDCPAReduction kem hDet leak adv gp, ?_⟩
  exact cka_securityAdvantage_le_ind_cpa_of_fixed_gap
    kem hDet leak adv gp (ckaToINDCPAReduction kem hDet leak adv gp)
    (ckaToINDCPAReduction_fixed_gap_dominates kem hDet leak adv gp hgp)

end kemCKA
