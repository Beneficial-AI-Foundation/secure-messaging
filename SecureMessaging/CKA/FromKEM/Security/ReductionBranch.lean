/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import SecureMessaging.CKA.FromKEM.Security.PostChallenge

/-!
# CKA from KEM — Concrete Reduction Branch

This file builds the KEM IND-CPA adversary from the CKA adversary, following
[ACD19, Section 4.1.2]. The reduction runs in two phases:

* `preChallenge pkStar` initializes the CKA game state, installs `pkStar` at the
  would-be challenge public key, and runs the CKA adversary through
  `challengePrefix` until its first valid challenge query;
* `postChallenge st cStar kStar` injects the KEM challenge ciphertext and key
  through `finishChallengeStep` and continues with `postChallengeImpl`.

`reductionBranchImpl` is a single-pass view of the same reduction, shaped for the
later relational `simulateQ` proofs. This file packages the concrete adversary
`ckaToINDCPAReduction` with its local run lemmas; it does not prove the advantage
bound or the hidden-state simulation.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

variable {K PK SK C : Type}

/-- State of the single-pass reduction branch: the plain game state before
the challenge, the post-challenge state after it. -/
inductive ReductionBranchState (K PK SK C : Type) where
  | pre (game : SecurityState K PK SK C)
  | post (post : PostChallengeState K PK SK C)

/-- Single-pass view of the concrete IND-CPA reduction branch.

While in `.pre`, ordinary queries are handled by the prefix simulator that has
installed `pkStar` at the would-be challenge public key. The first valid
challenge query consumes `(cStar, kStar)`, installs the pending receive override,
and switches to `.post`. All later queries delegate to `postChallengeImpl`.
This is equivalent to the split `preChallenge`/`postChallenge` API, but has the
right shape for relational `simulateQ` reasoning over the adversary. -/
def reductionBranchImpl [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K) :
    QueryImpl (securitySpec leak)
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
                  (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ
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
                  (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ
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

private lemma reductionBranchImpl_post_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (t : (securitySpec leak).Domain)
    (ps : PostChallengeState K PK SK C) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar t).run
        (ReductionBranchState.post ps) =
      (do
        let (out, ps') ← (postChallengeImpl kem hDet leak gp t).run ps
        pure (out, ReductionBranchState.post ps')) := by
  simp [reductionBranchImpl, stateT_run]

/-- Once in `.post`, simulating a whole adversary under `reductionBranchImpl`
is the same as simulating it under `postChallengeImpl`, with the state
re-wrapped. Proved by query induction from the single-query run reduction. -/
lemma reductionBranchImpl_post_simulateQ_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    {α : Type}
    (adv : OracleComp (securitySpec leak) α)
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
      simp only [simulateQ_bind, simulateQ_spec_query, stateT_run]
      rw [reductionBranchImpl_post_run]
      simp only [bind_assoc, pure_bind]
      refine bind_congr (m := ProbComp) fun p => ?_
      simpa using ih p.1 p.2

/-- Run reduction for the due A-challenge: the reduction consumes
`(cStar, kStar)`, builds the challenge message, installs the pending receive,
and switches to the post-challenge state. -/
lemma reductionBranchImpl_pre_challA_run_of_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeA gp σ = true) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
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
  simp [reductionBranchImpl, hWill, stateT_run]

/-- Run reduction for the due B-challenge, the mirror of
`reductionBranchImpl_pre_challA_run_of_will`. -/
lemma reductionBranchImpl_pre_challB_run_of_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeB gp σ = true) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
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
  simp [reductionBranchImpl, hWill, stateT_run]

/-- Run the adversary under the prefix implementation until its first due
challenge query, returning the interrupted continuation
(`pausedA`/`pausedB`), or `done` with the final result if no challenge
occurs. Challenge queries that are not due are answered by the prefix
implementation like any other query. -/
def challengePrefix [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type} :
    OracleComp (securitySpec leak) α →
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
                (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain))
            rec out
      | CKAScheme.ckaSecuritySpec.OChallB =>
          let σ ← get
          if willChallengeB gp σ then
            pure (.pausedB oa)
          else
            let out ←
              (prefixImpl kem hDet leak gp pkStar
                (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain))
            rec out
      | other =>
          let out ← (prefixImpl kem hDet leak gp pkStar other)
          rec out)

/-- The concrete IND-CPA adversary built from the CKA adversary.

`preChallenge pkStar` starts the game — placing `pkStar` directly into the
initial state when the challenge is the very first A-send — and runs the
adversary up to its first due challenge query. `postChallenge` answers that
query with the KEM challenge ciphertext and key and finishes through
`finishChallengeStep`; the final negation aligns the CKA and IND-CPA bit
orientations. -/
def ckaToINDCPAReduction [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) :
    KEMScheme.IND_CPA_Adversary kem where
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


end kemCKA
