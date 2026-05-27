/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import SecureMessaging.CKA.FromKEM.Security.Basic

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

inductive CKAChallengeStepResult
    {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem)
    (α : Type) where
  | done (a : α)
  | pausedA
      (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) α)
  | pausedB
      (cont : Option (Message C PK × K) → OracleComp (SecuritySpec leak) α)

def CKAChallengeStepResult.map
    {K PK SK C α β : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    {leak : KEMRandLeak kem}
    (f : α → β) :
    CKAChallengeStepResult leak α → CKAChallengeStepResult leak β
  | .done a => .done (f a)
  | .pausedA cont => .pausedA (fun x => f <$> cont x)
  | .pausedB cont => .pausedB (fun x => f <$> cont x)

inductive CKAReductionState
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

inductive PendingChallengeRecv (K PK C : Type) where
  | none
  | aToB (key : K) (nextPk : PK) (msg : Message C PK)
  | bToA (key : K) (nextPk : PK) (msg : Message C PK)

structure PostChallengeState
    (K PK SK C : Type) where
  game : SecurityState K PK SK C
  pending : PendingChallengeRecv K PK C

def liftSecurityImplToPost [SampleableType K] [DecidableEq K]
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

def postChallengeImpl [SampleableType K] [DecidableEq K]
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

def finishChallengeStep [SampleableType K] [DecidableEq K]
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

def finishChallengeStepRaw [SampleableType K] [DecidableEq K]
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

lemma finishChallengeStep_eq_not_map_raw [SampleableType K] [DecidableEq K]
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


end kemCKA
