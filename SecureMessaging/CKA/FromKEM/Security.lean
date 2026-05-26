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
  postChallenge st cStar kStar := do
    match st with
    | .done guess => pure (!guess)
    | .pausedA σ cont =>
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
    | .pausedB σ cont =>
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
  /- Remaining semantic obligation: show that the concrete reduction's fixed
     IND-CPA branch gap dominates the CKA real/random fixed-branch gap. Paths
     that never trigger the challenge oracle must cancel from the branch gap;
     challenge paths are related by the prefix/post-challenge simulation. -/
  sorry

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
