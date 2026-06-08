/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import SecureMessaging.CKA.FromKEM.Security.Basic

/-!
# CKA from KEM — Post-Challenge Oracle

After the challenge, the reduction no longer holds the decapsulation secret key
for the challenge ciphertext: the challenged sender stores a fresh unrelated
secret key after sending, and the matching receiver deletes the secret key it
used to decapsulate once it reaches the challenge epoch. With `ΔFS = 0` the
remaining state carries no challenge-relevant secret material, so post-challenge
corruptions stay safe [ACD19, Section 4.1.2].

This file is the first Lean layer for that step. It defines the post-challenge
state machine (`PostChallengeState`, `postChallengeImpl`) and the challenge-step
finisher (`finishChallengeStep`), which the later simulation lemmas build on. It
does not yet prove the hidden-state simulation itself.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

variable {K PK SK C : Type}

inductive CKAChallengeStepResult
    {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem)
    (α : Type) where
  | done (a : α)
  | pausedA
      (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) α)
  | pausedB
      (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) α)

def CKAChallengeStepResult.map
    {K PK SK C α β : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    {leak : RandLeak kem}
    (f : α → β) :
    CKAChallengeStepResult leak α → CKAChallengeStepResult leak β
  | .done a => .done (f a)
  | .pausedA cont => .pausedA (fun x => f <$> cont x)
  | .pausedB cont => .pausedB (fun x => f <$> cont x)

inductive CKAReductionState
    {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem) where
  | done (guess : Bool)
  | pausedA
      (σ : SecurityState K PK SK C)
      (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool)
  | pausedB
      (σ : SecurityState K PK SK C)
      (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool)

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
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (securitySpec leak).Domain) :
    StateT (PostChallengeState K PK SK C) ProbComp ((securitySpec leak).Range t) := do
  let ps ← get
  let (out, game') ← (securityImpl kem hDet leak gp false t).run ps.game
  set { ps with game := game' }
  return out

def postChallengeImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams) :
    QueryImpl (securitySpec leak) (StateT (PostChallengeState K PK SK C) ProbComp) :=
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
                (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)
        | _ =>
            liftSecurityImplToPost kem hDet leak gp
              (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)
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
                (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)
        | _ =>
            liftSecurityImplToPost kem hDet leak gp
              (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)
    | other =>
        liftSecurityImplToPost kem hDet leak gp other

lemma securityImpl_recvB_of_decaps_eq [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (g : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (key : K)
    (hstep : CKAScheme.validStep g.lastAction .recvB = true)
    (hdec : hDet.decapsDet sk msg.1 = some key) :
    (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        { g with stB := State.recvReady sk, rhoA := some msg, keyA := some key } =
      pure ((), { g with
        stB := State.sendReady msg.2,
        rhoA := none,
        keyA := none,
        correct := g.correct,
        lastAction := some .recvB,
        tB := g.tB + 1 }) := by
  change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run
        { g with stB := State.recvReady sk, rhoA := some msg, keyA := some key } = _
  simp [CKAScheme.oracleRecvB, scheme, recv, hstep, hdec]

lemma securityImpl_recvA_of_decaps_eq [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (g : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (key : K)
    (hstep : CKAScheme.validStep g.lastAction .recvA = true)
    (hdec : hDet.decapsDet sk msg.1 = some key) :
    (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        { g with stA := State.recvReady sk, rhoB := some msg, keyB := some key } =
      pure ((), { g with
        stA := State.sendReady msg.2,
        rhoB := none,
        keyB := none,
        correct := g.correct,
        lastAction := some .recvA,
        tA := g.tA + 1 }) := by
  change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run
        { g with stA := State.recvReady sk, rhoB := some msg, keyB := some key } = _
  simp [CKAScheme.oracleRecvA, scheme, recv, hstep, hdec]

lemma postChallengeImpl_recvB_aToB_of_valid [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (g : SecurityState K PK SK C)
    (key : K) (nextPk : PK) (msg : Message C PK)
    (hstep : CKAScheme.validStep g.lastAction .recvB = true) :
    (postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        ({ game := g, pending := PendingChallengeRecv.aToB key nextPk msg } :
          PostChallengeState K PK SK C) =
      (let g' : SecurityState K PK SK C := { g with
          stB := State.sendReady nextPk,
          rhoA := none,
          keyA := none,
          correct := g.correct && (g.keyA == some key),
          lastAction := some .recvB,
          tB := g.tB + 1 }
       pure ((), ({ game := g', pending := .none } :
         PostChallengeState K PK SK C))) := by
  simp [postChallengeImpl, hstep, StateT.run_bind, StateT.run_get, StateT.run_set]
  rfl

lemma postChallengeImpl_recvA_bToA_of_valid [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (g : SecurityState K PK SK C)
    (key : K) (nextPk : PK) (msg : Message C PK)
    (hstep : CKAScheme.validStep g.lastAction .recvA = true) :
    (postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        ({ game := g, pending := PendingChallengeRecv.bToA key nextPk msg } :
          PostChallengeState K PK SK C) =
      (let g' : SecurityState K PK SK C := { g with
          stA := State.sendReady nextPk,
          rhoB := none,
          keyB := none,
          correct := g.correct && (g.keyB == some key),
          lastAction := some .recvA,
          tA := g.tA + 1 }
       pure ((), ({ game := g', pending := .none } :
         PostChallengeState K PK SK C))) := by
  simp [postChallengeImpl, hstep, StateT.run_bind, StateT.run_get, StateT.run_set]
  rfl

lemma securityImpl_recvB_eq_project_postChallengeImpl_aToB
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (g : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hstep : CKAScheme.validStep g.lastAction .recvB = true)
    (hdec : hDet.decapsDet sk msg.1 = some realKey) :
    Prod.map id PostChallengeState.game <$>
      (postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        ({ game := { g with rhoA := some msg, keyA := some fakeKey },
           pending := PendingChallengeRecv.aToB fakeKey msg.2 msg } :
          PostChallengeState K PK SK C) =
      (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        { g with stB := State.recvReady sk, rhoA := some msg, keyA := some realKey } := by
  change Prod.map id PostChallengeState.game <$>
      (postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        ({ game := { g with rhoA := some msg, keyA := some fakeKey },
           pending := PendingChallengeRecv.aToB fakeKey msg.2 msg } :
          PostChallengeState K PK SK C) =
    (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run
        { g with stB := State.recvReady sk, rhoA := some msg, keyA := some realKey }
  simp [postChallengeImpl, CKAScheme.oracleRecvB, scheme, recv, hstep, hdec,
    StateT.run_bind, StateT.run_get, StateT.run_set]
  rfl

lemma securityImpl_recvA_eq_project_postChallengeImpl_bToA
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (g : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hstep : CKAScheme.validStep g.lastAction .recvA = true)
    (hdec : hDet.decapsDet sk msg.1 = some realKey) :
    Prod.map id PostChallengeState.game <$>
      (postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        ({ game := { g with rhoB := some msg, keyB := some fakeKey },
           pending := PendingChallengeRecv.bToA fakeKey msg.2 msg } :
          PostChallengeState K PK SK C) =
      (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        { g with stA := State.recvReady sk, rhoB := some msg, keyB := some realKey } := by
  change Prod.map id PostChallengeState.game <$>
      (postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        ({ game := { g with rhoB := some msg, keyB := some fakeKey },
           pending := PendingChallengeRecv.bToA fakeKey msg.2 msg } :
          PostChallengeState K PK SK C) =
    (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run
        { g with stA := State.recvReady sk, rhoB := some msg, keyB := some realKey }
  simp [postChallengeImpl, CKAScheme.oracleRecvA, scheme, recv, hstep, hdec,
    StateT.run_bind, StateT.run_get, StateT.run_set]
  rfl

def finishChallengeStep [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
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
    (leak : RandLeak kem)
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
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (res : CKAChallengeStepResult leak Bool)
    (σ : SecurityState K PK SK C)
    (cStar : C) (kStar : K) :
    finishChallengeStep kem hDet leak gp res σ cStar kStar =
      (! ·) <$> finishChallengeStepRaw kem hDet leak gp res σ cStar kStar := by
  cases res <;> simp [finishChallengeStep, finishChallengeStepRaw]


end kemCKA
