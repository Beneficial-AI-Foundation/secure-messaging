/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import SecureMessaging.CKA.FromKEM.Security.Basic
import ToVCVio.Control.StateT

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

/-- Result of running the adversary up to the first valid challenge query:
either it finished without one (`done`), or it paused at an A- or B-challenge
with the continuation awaiting the challenge answer. -/
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

/-- A paused reduction run together with its game state: the adversary either
finished with a guess, or stands at a challenge query with the current game
state and the continuation. -/
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

/-- The challenge message in flight, if any: after an A-challenge the message
waits for B's receive (`aToB`), and symmetrically for `bToA`. It records the
challenge key, the next public key, and the message itself. -/
inductive PendingChallengeRecv (K PK C : Type) where
  | none
  | aToB (key : K) (nextPk : PK) (msg : Message C PK)
  | bToA (key : K) (nextPk : PK) (msg : Message C PK)

/-- State of the post-challenge oracle implementation: the underlying CKA
game state plus the challenge message still awaiting receipt. -/
structure PostChallengeState
    (K PK SK C : Type) where
  game : SecurityState K PK SK C
  pending : PendingChallengeRecv K PK C

/-- Answer a query with the honest implementation, acting on the `game`
component of the post-challenge state and leaving `pending` unchanged. -/
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

/-- Post-challenge oracle implementation.

The receive of the pending challenge message is answered from the recorded
challenge key and next public key, with no decapsulation — exactly what the
reduction can do without the challenge secret key. Every other query runs the
honest implementation on the `game` component. -/
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

/-- Run reduction for the honest B-receive when decapsulation returns the
sender's recorded key: the receive consumes the message, synchronizes B to
the sender's epoch, and leaves `correct` unchanged. -/
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

/-- Run reduction for the honest A-receive when decapsulation returns the
sender's recorded key, the mirror of `securityImpl_recvB_of_decaps_eq`. -/
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

/-- Run reduction for the intercepted B-receive of the pending `aToB`
challenge message: the state advances as in an honest receive, with the
recorded challenge key standing in for the decapsulated key, and `pending`
clears. -/
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
  simp [postChallengeImpl, hstep, stateT_run]
  rfl

/-- Run reduction for the intercepted A-receive of the pending `bToA`
challenge message, the mirror of `postChallengeImpl_recvB_aToB_of_valid`. -/
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
  simp [postChallengeImpl, hstep, stateT_run]
  rfl

/-- Hidden-state agreement at B's receive of the challenge message.

Projected to the game component, the intercepted receive that replays
`fakeKey` from a state storing `fakeKey` agrees with the honest receive that
decapsulates `realKey` from a state storing `realKey` and the receive secret
`sk`. The key value and the secret key drop out of the resulting game state,
which is what lets the reduction answer post-challenge queries without the
challenge secret. -/
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
    stateT_run]
  rfl

/-- Hidden-state agreement at A's receive of the challenge message, the
mirror of `securityImpl_recvB_eq_project_postChallengeImpl_aToB`. -/
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
    stateT_run]
  rfl

/-- Answer the paused challenge query and finish the game.

For a paused run, draw the next key pair, build the challenge message from
`cStar`, hand `(msg, kStar)` to the continuation, and run it under the
post-challenge implementation. The final guess is negated to account for the
CKA/KEM bit-orientation reversal; `finishChallengeStepRaw` is the un-negated
form. -/
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

/-- `finishChallengeStep` without the final negation. The raw form couples
directly with the IND-CPA experiment; the branch gap absorbs the orientation
difference. -/
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

/-- The negated and raw challenge finishers differ by a final `(! ·)` map. -/
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
