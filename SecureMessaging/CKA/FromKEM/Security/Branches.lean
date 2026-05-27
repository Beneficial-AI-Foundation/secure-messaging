/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import SecureMessaging.CKA.FromKEM.Security.ReductionBranch

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

lemma probCompRuntime_probOutput_eq {α : Type} (mx : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist mx] = Pr[= x | mx] := by
  rfl

structure INDCPAPrefixState
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) where
  st : red.State
  cStar : C
  kReal : K
  kRand : K

def indCPAPrefix [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp (INDCPAPrefixState kem red) := do
  let (pk, _sk) ← kem.keygen
  let st ← red.preChallenge pk
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  pure { st := st, cStar := cStar, kReal := kReal, kRand := kRand }

def indCPAExpProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) (b : Bool) : ProbComp Bool := do
  let p ← indCPAPrefix kem red
  red.postChallenge p.st p.cStar (if b then p.kReal else p.kRand)


def ckaReductionINDCPABranch [SampleableType K] [DecidableEq K]
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

def ckaReductionINDCPABranchRaw [SampleableType K] [DecidableEq K]
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

def ckaSecurityFixedFromState [SampleableType K] [DecidableEq K]
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

def ckaReductionRawFromState [SampleableType K] [DecidableEq K]
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

def ckaReductionRawSplitFromState [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (adv : Adversary (kem := kem) leak)
    (σ : SecurityState K PK SK C) : ProbComp Bool := do
  let (res, σ') ← (challengePrefix kem hDet leak gp pkStar adv).run σ
  finishChallengeStepRaw kem hDet leak gp res σ' cStar kStar

lemma ckaReductionRawFromState_post_eq
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

lemma ckaReductionRawFromState_query_post_eq
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

lemma ckaReductionRawFromState_query_challA_of_will
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

lemma ckaReductionRawFromState_query_challA_of_not_will
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

lemma ckaReductionRawFromState_query_challB_of_will
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

lemma ckaReductionRawFromState_query_challB_of_not_will
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

lemma ckaReductionRawFromState_pre_eq_split
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (adv : Adversary (kem := kem) leak)
    (σ : SecurityState K PK SK C) :
    ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar adv
        (ReductionBranchState.pre σ) =
      ckaReductionRawSplitFromState kem hDet leak gp pkStar cStar kStar adv σ := by
  induction adv using OracleComp.inductionOn generalizing σ with
  | pure guess =>
      simp only [ckaReductionRawFromState, simulateQ_pure, StateT.run_pure,
        bind_pure_comp, map_pure, ckaReductionRawSplitFromState,
        challengePrefix, construct_pure, finishChallengeStepRaw, pure_bind]
  | query_bind t cont ih =>
      rcases t with
        (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
          uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
      all_goals
        try cases uSendA
        try cases uRecvA
        try cases uSendB
        try cases uRecvB
        try cases uCorrA
        try cases uCorrB
        try cases uRLeakA
        try cases uRLeakB
      all_goals
        try
          simp only [ckaReductionRawFromState, simulateQ_bind, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, reductionBranchImpl,
            bind_pure_comp, map_bind, id_map, bind_assoc, StateT.run_bind,
            StateT.run_get, pure_bind, StateT.run_monadLift, monadLift_self,
            StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            bind_map_left, ckaReductionRawSplitFromState, challengePrefix,
            construct_query_bind]
          refine bind_congr (m := ProbComp) fun a => ?_
          simpa [ckaReductionRawFromState, ckaReductionRawSplitFromState] using
            ih a.1 a.2
      · cases uChallA
        by_cases hWill : willChallengeA gp σ = true
        · trans (do
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
              (cont (some (msg, kStar))) (ReductionBranchState.post ps'))
          · simpa [CKAScheme.ckaSecuritySpec.OChallA] using
              ckaReductionRawFromState_query_challA_of_will
                kem hDet leak gp pkStar cStar kStar σ cont hWill
          · simp only [ckaReductionRawSplitFromState, challengePrefix,
              construct_query_bind, StateT.run_bind, StateT.run_get, pure_bind,
              hWill, ↓reduceIte, StateT.run_pure, finishChallengeStepRaw,
              bind_pure_comp]
            refine bind_congr (m := ProbComp) fun pkNext_skNext => ?_
            let msg : Message C PK := (cStar, pkNext_skNext.1)
            let σ' : SecurityState K PK SK C := { σ with
              stA := State.recvReady pkNext_skNext.2,
              rhoA := some msg,
              keyA := some kStar,
              lastAction := some .challA,
              tA := σ.tA + 1 }
            let ps' : PostChallengeState K PK SK C :=
              { game := σ', pending := .aToB kStar pkNext_skNext.1 msg }
            simpa [msg, σ', ps'] using
              ckaReductionRawFromState_post_eq kem hDet leak gp pkStar cStar kStar
                (cont (some (msg, kStar))) ps'
        · have hWillFalse : willChallengeA gp σ = false :=
            Bool.eq_false_of_not_eq_true hWill
          trans (do
            let (out, σ') ←
              (prefixImpl kem hDet leak gp pkStar
                (CKAScheme.ckaSecuritySpec.OChallA : (SecuritySpec leak).Domain)).run σ
            ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
              (cont out) (ReductionBranchState.pre σ'))
          · simpa [CKAScheme.ckaSecuritySpec.OChallA] using
              ckaReductionRawFromState_query_challA_of_not_will
                kem hDet leak gp pkStar cStar kStar σ cont hWillFalse
          · simp only [ckaReductionRawSplitFromState, challengePrefix,
              construct_query_bind, StateT.run_bind, StateT.run_get, pure_bind,
              hWillFalse, Bool.false_eq_true, ↓reduceIte, bind_assoc]
            refine bind_congr (m := ProbComp) fun out_σ => ?_
            simpa [ckaReductionRawFromState, ckaReductionRawSplitFromState] using
              ih out_σ.1 out_σ.2
      · cases uChallB
        by_cases hWill : willChallengeB gp σ = true
        · trans (do
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
              (cont (some (msg, kStar))) (ReductionBranchState.post ps'))
          · simpa [CKAScheme.ckaSecuritySpec.OChallB] using
              ckaReductionRawFromState_query_challB_of_will
                kem hDet leak gp pkStar cStar kStar σ cont hWill
          · simp only [ckaReductionRawSplitFromState, challengePrefix,
              construct_query_bind, StateT.run_bind, StateT.run_get, pure_bind,
              hWill, ↓reduceIte, StateT.run_pure, finishChallengeStepRaw,
              bind_pure_comp]
            refine bind_congr (m := ProbComp) fun pkNext_skNext => ?_
            let msg : Message C PK := (cStar, pkNext_skNext.1)
            let σ' : SecurityState K PK SK C := { σ with
              stB := State.recvReady pkNext_skNext.2,
              rhoB := some msg,
              keyB := some kStar,
              lastAction := some .challB,
              tB := σ.tB + 1 }
            let ps' : PostChallengeState K PK SK C :=
              { game := σ', pending := .bToA kStar pkNext_skNext.1 msg }
            simpa [msg, σ', ps'] using
              ckaReductionRawFromState_post_eq kem hDet leak gp pkStar cStar kStar
                (cont (some (msg, kStar))) ps'
        · have hWillFalse : willChallengeB gp σ = false :=
            Bool.eq_false_of_not_eq_true hWill
          trans (do
            let (out, σ') ←
              (prefixImpl kem hDet leak gp pkStar
                (CKAScheme.ckaSecuritySpec.OChallB : (SecuritySpec leak).Domain)).run σ
            ckaReductionRawFromState kem hDet leak gp pkStar cStar kStar
              (cont out) (ReductionBranchState.pre σ'))
          · simpa [CKAScheme.ckaSecuritySpec.OChallB] using
              ckaReductionRawFromState_query_challB_of_not_will
                kem hDet leak gp pkStar cStar kStar σ cont hWillFalse
          · simp only [ckaReductionRawSplitFromState, challengePrefix,
              construct_query_bind, StateT.run_bind, StateT.run_get, pure_bind,
              hWillFalse, Bool.false_eq_true, ↓reduceIte, bind_assoc]
            refine bind_congr (m := ProbComp) fun out_σ => ?_
            simpa [ckaReductionRawFromState, ckaReductionRawSplitFromState] using
              ih out_σ.1 out_σ.2

def ckaSecurityFixedBranch [SampleableType K] [DecidableEq K]
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

lemma securityExpFixedBit_eq_ckaSecurityFixedBranch
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

lemma ckaReductionINDCPABranch_eq_not_map_raw [SampleableType K] [DecidableEq K]
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

lemma abs_probOutput_true_not_map_gap_eq (mx my : ProbComp Bool) :
    |(Pr[= true | (! ·) <$> mx]).toReal -
      (Pr[= true | (! ·) <$> my]).toReal| =
    |(Pr[= true | mx]).toReal - (Pr[= true | my]).toReal| := by
  simp [probOutput_false_eq_sub]
  ring_nf
  rw [show -Pr[= true | my].toReal + Pr[= true | mx].toReal =
      Pr[= true | mx].toReal - Pr[= true | my].toReal by ring]
  exact abs_sub_comm (Pr[= true | my].toReal) (Pr[= true | mx].toReal)

lemma ckaReductionINDCPABranch_gap_eq_raw_gap [SampleableType K] [DecidableEq K]
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

lemma indCPAExpProb_ckaToINDCPAReduction_eq_branch
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

def indCPAGameProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let (pk, _sk) ← kem.keygen
  let st ← red.preChallenge pk
  let b ← ($ᵗ Bool)
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← ($ᵗ K)
  let b' ← red.postChallenge st cStar (if b then kReal else kRand)
  return (b == b')

def indCPABranchGameProb [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (red : kem.IND_CPA_Adversary) : ProbComp Bool := do
  let p ← indCPAPrefix kem red
  let b ← ($ᵗ Bool)
  let z ← if b then red.postChallenge p.st p.cStar p.kReal
          else red.postChallenge p.st p.cStar p.kRand
  pure (b == z)

lemma indCPAGameProb_evalDist_eq_branch [SampleableType K]
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

lemma indCPAGameProb_advantage_eq_fixed_dist [SampleableType K]
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

lemma indCPAExpProb_probOutput_true_eq [SampleableType K]
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


lemma ckaToINDCPAReduction_IND_CPA_Exp_probOutput_true_eq_branch
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

lemma kem_ind_cpa_advantage_eq_fixed_branch_dist [SampleableType K]
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


end kemCKA
