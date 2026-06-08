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

inductive ReductionBranchState (K PK SK C : Type) where
  | pre (game : SecurityState K PK SK C)
  | post (post : PostChallengeState K PK SK C)

def reductionBranchInitialState
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

def ckaReductionBranchRun [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let rs0 : ReductionBranchState K PK SK C :=
    reductionBranchInitialState gp pkStar pk0 sk0
  let (guess, _) ←
    (simulateQ (reductionBranchImpl kem hDet leak gp pkStar cStar kStar) adv).run rs0
  pure (!guess)

lemma reductionBranchImpl_post_run [SampleableType K] [DecidableEq K]
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
  simp [reductionBranchImpl, StateT.run_bind, StateT.run_get, StateT.run_set]

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
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [reductionBranchImpl_post_run]
      simp only [bind_assoc, pure_bind]
      refine bind_congr (m := ProbComp) fun p => ?_
      simpa using ih p.1 p.2

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
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

lemma reductionBranchImpl_pre_challA_run_of_not_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeA gp σ = false) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre σ) =
      (do
        let (out, σ') ←
          (prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ
        pure (out, ReductionBranchState.pre σ')) := by
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

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
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

lemma reductionBranchImpl_pre_challB_run_of_not_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeB gp σ = false) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre σ) =
      (do
        let (out, σ') ←
          (prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ
        pure (out, ReductionBranchState.pre σ')) := by
  simp [reductionBranchImpl, hWill, StateT.run_bind, StateT.run_get, StateT.run_set]

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

lemma challengePrefix_pure [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type} (a : α) :
    challengePrefix kem hDet leak gp pkStar (pure a : OracleComp (securitySpec leak) α) =
      pure (.done a) := by
  simp [challengePrefix]

lemma challengePrefix_query_challA [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type}
    (mx : Option (Message C PK × K) → OracleComp (securitySpec leak) α) :
    challengePrefix kem hDet leak gp pkStar
        ((securitySpec leak).query
            (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain) >>= mx) =
      (do
        let σ ← get
        if willChallengeA gp σ then
          pure (.pausedA mx)
        else
          let out ← prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)
          challengePrefix kem hDet leak gp pkStar (mx out)) := by
  simp [challengePrefix]

lemma challengePrefix_query_challB [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type}
    (mx : Option (Message C PK × K) → OracleComp (securitySpec leak) α) :
    challengePrefix kem hDet leak gp pkStar
        ((securitySpec leak).query
            (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain) >>= mx) =
      (do
        let σ ← get
        if willChallengeB gp σ then
          pure (.pausedB mx)
        else
          let out ← prefixImpl kem hDet leak gp pkStar
            (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)
          challengePrefix kem hDet leak gp pkStar (mx out)) := by
  simp [challengePrefix]

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

lemma ckaToINDCPAReduction_pre_post_eq_finish
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
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


end kemCKA
