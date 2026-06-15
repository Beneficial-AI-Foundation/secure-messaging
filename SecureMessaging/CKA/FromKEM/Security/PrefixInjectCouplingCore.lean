/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectGap
import ToVCVio.ProgramLogic.Relational.Basic
import VCVio.ProgramLogic.Relational.FromUnary

/-!
# CKA from KEM — Injected-Prefix Coupling: shared layer

Shared machinery for coupling `ckaSecurityFixedBranchWithInjectedChallengeKey`
with `ckaReductionINDCPABranchRawKeygenSwapped`: the prefix that pauses both
games at the first challenge query whose guard holds, the factorization of the
injected game through that prefix, run reductions for the modified send
oracles, the state shape maintained by `securityImpl` steps, and the
never-pause lemmas past the challenge epoch.  The party-specific coupling
relations and inductions build on this layer in `PrefixInjectCouplingA` and
`PrefixInjectCouplingB`.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## Challenge queries that do not fire

A challenge query at a state where `willChallengeA`/`willChallengeB` is false is
a full no-op: either the alternation guard rejects it, or the party/epoch gate
on the bumped counter rejects it before any state is written, and in both cases
the challenge bit is never read.  The injecting implementation delegates
challenge queries to `securityImpl`, so these lemmas transfer to it
definitionally. -/

lemma securityImpl_challA_run_of_not_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeA gp σ = false) :
    (securityImpl kem hDet leak gp isRandom
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ =
      pure (none, σ) := by
  change (CKAScheme.oracleChallA gp isRandom (scheme kem hDet leak) ()).run σ = _
  by_cases hvalid : CKAScheme.validStep σ.lastAction .challA = true
  · cases hparty : gp.challengedParty with
    | A =>
        have hne : ¬ σ.tA + 1 = gp.challengeEpoch := by
          simpa [willChallengeA, hvalid, hparty] using hWill
        simp [CKAScheme.oracleChallA, hvalid, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty, hne]
    | B =>
        simp [CKAScheme.oracleChallA, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty]
  · have hvalidFalse : CKAScheme.validStep σ.lastAction .challA = false :=
      Bool.eq_false_of_not_eq_true hvalid
    simp [CKAScheme.oracleChallA, hvalidFalse]

/-- Run reduction for a B-challenge query that is not due, the mirror of
`securityImpl_challA_run_of_not_will`. -/
lemma securityImpl_challB_run_of_not_will [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeB gp σ = false) :
    (securityImpl kem hDet leak gp isRandom
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ =
      pure (none, σ) := by
  change (CKAScheme.oracleChallB gp isRandom (scheme kem hDet leak) ()).run σ = _
  by_cases hvalid : CKAScheme.validStep σ.lastAction .challB = true
  · cases hparty : gp.challengedParty with
    | A =>
        simp [CKAScheme.oracleChallB, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty]
    | B =>
        have hne : ¬ σ.tB + 1 = gp.challengeEpoch := by
          simpa [willChallengeB, hvalid, hparty] using hWill
        simp [CKAScheme.oracleChallB, hvalid, CKAScheme.isChallengeEpoch,
          CKAScheme.GameState.tP, hparty, hne]
  · have hvalidFalse : CKAScheme.validStep σ.lastAction .challB = false :=
      Bool.eq_false_of_not_eq_true hvalid
    simp [CKAScheme.oracleChallB, hvalidFalse]

/-! ## The injected challenge prefix

`injectedChallengePrefix` does for `securityImplWithChallengeKeyPair` what
`challengePrefix` does for `prefixImpl`: it runs the adversary under that
implementation and pauses at the first challenge query whose
`willChallengeA`/`willChallengeB` guard holds.  Before the pause the challenge
bit is never read, so the prefix is used at the fixed bit `false`; the resume
carries the real bit. -/

def injectedChallengePrefix [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
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
              securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar
                (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)
            rec out
      | CKAScheme.ckaSecuritySpec.OChallB =>
          let σ ← get
          if willChallengeB gp σ then
            pure (.pausedB oa)
          else
            let out ←
              securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar
                (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)
            rec out
      | other =>
          let out ←
            securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar other
          rec out)

/-! ## Splitting the injected game

`injectedChallengeResume` completes a split run: a `.done` result returns the
recorded guess, and a paused result performs the challenge query the prefix
paused on, at the real bit, under `securityImplWithChallengeKeyPair`, and
simulates the rest of the run.
The factorization below recovers the full injected game from the bit-`false`
prefix followed by this bit-`b` resume. -/

def injectedChallengeResume [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    (res : CKAChallengeStepResult leak Bool)
    (σ : SecurityState K PK SK C) :
    ProbComp (Bool × SecurityState K PK SK C) :=
  match res with
  | .done g => pure (g, σ)
  | .pausedA cont =>
      (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar
          (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ >>=
        fun x =>
          (simulateQ (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar)
            (cont x.1)).run x.2
  | .pausedB cont =>
      (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar
          (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ >>=
        fun x =>
          (simulateQ (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar)
            (cont x.1)).run x.2

/-- Factor a `securityImplWithChallengeKeyPair` run through the bit-`false` prefix.

Before the pause every oracle step is bit-independent: the only bit-dependent
oracles are the two challenge oracles, and the prefix steps them only at states
where their `willChallengeA`/`willChallengeB` guard is false, where they are
full no-ops.  At the pause both sides perform the same challenge step at the
real bit `b`. -/
private lemma simulateQ_wck_run_eq_injectedChallengePrefix_bind
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (adv : Adversary (kem := kem) leak)
    (σ : SecurityState K PK SK C) :
    (simulateQ (securityImplWithChallengeKeyPair kem hDet leak gp b pkStar skStar) adv).run σ =
      (injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σ >>=
        fun x => injectedChallengeResume kem hDet leak gp b pkStar skStar x.1 x.2 := by
  induction adv using OracleComp.inductionOn generalizing σ with
  | pure g =>
      simp [injectedChallengePrefix, injectedChallengeResume, simulateQ_pure, StateT.run_pure]
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
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, bind_assoc, stateT_run,
            injectedChallengePrefix, construct_query_bind]
          refine bind_congr (m := ProbComp) fun a => ?_
          simpa using ih a.1 a.2
      · -- O-Chall-A
        cases uChallA
        by_cases hWill : willChallengeA gp σ = true
        · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, stateT_run, injectedChallengePrefix,
            construct_query_bind, hWill, ↓reduceIte, injectedChallengeResume]
        · have hWillFalse : willChallengeA gp σ = false :=
            Bool.eq_false_of_not_eq_true hWill
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, bind_assoc, stateT_run,
            injectedChallengePrefix, construct_query_bind, hWillFalse,
            Bool.false_eq_true, ↓reduceIte]
          rw [show (securityImplWithChallengeKeyPair kem hDet leak gp b pkStar skStar
                (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ =
              pure (none, σ) from
            securityImpl_challA_run_of_not_will kem hDet leak gp b σ hWillFalse]
          rw [show (securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar
                (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ =
              pure (none, σ) from
            securityImpl_challA_run_of_not_will kem hDet leak gp false σ hWillFalse]
          simpa using ih none σ
      · -- O-Chall-B
        cases uChallB
        by_cases hWill : willChallengeB gp σ = true
        · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, stateT_run, injectedChallengePrefix,
            construct_query_bind, hWill, ↓reduceIte, injectedChallengeResume]
        · have hWillFalse : willChallengeB gp σ = false :=
            Bool.eq_false_of_not_eq_true hWill
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, bind_assoc, stateT_run,
            injectedChallengePrefix, construct_query_bind, hWillFalse,
            Bool.false_eq_true, ↓reduceIte]
          rw [show (securityImplWithChallengeKeyPair kem hDet leak gp b pkStar skStar
                (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ =
              pure (none, σ) from
            securityImpl_challB_run_of_not_will kem hDet leak gp b σ hWillFalse]
          rw [show (securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar
                (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ =
              pure (none, σ) from
            securityImpl_challB_run_of_not_will kem hDet leak gp false σ hWillFalse]
          simpa using ih none σ

/-- `ckaSecurityFixedBranchWithInjectedChallengeKey` splits at the first
challenge query whose `willChallengeA`/`willChallengeB` guard holds. -/
lemma ckaSecurityFixedBranchWithInjectedChallengeKey_eq_split
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    ckaSecurityFixedBranchWithInjectedChallengeKey kem hDet leak adv gp b =
      (do
        let (pk0, sk0) ← kem.keygen
        let (pkStar, skStar) ← kem.keygen
        let σ0 :=
          CKAScheme.initGameState
            (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
              State.sendReady pkStar
            else
              State.sendReady pk0)
            (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
              State.recvReady skStar
            else
              State.recvReady sk0)
        let (res, σ) ←
          (injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σ0
        Prod.fst <$> injectedChallengeResume kem hDet leak gp b pkStar skStar res σ) := by
  unfold ckaSecurityFixedBranchWithInjectedChallengeKey
  refine bind_congr (m := ProbComp) fun pk0sk0 => ?_
  refine bind_congr (m := ProbComp) fun pkSskS => ?_
  obtain ⟨pk0, sk0⟩ := pk0sk0
  obtain ⟨pkStar, skStar⟩ := pkSskS
  dsimp only
  rw [simulateQ_wck_run_eq_injectedChallengePrefix_bind]
  simp [map_eq_bind_pure_comp, bind_assoc]

/-! ## Run reductions for the reduction-side injecting sends

`prefixImpl` replaces the send oracles by `oracleSendAWithChallengePk` and
`oracleSendBWithChallengePk`.  These run reductions expose their send-ready
normal form, mirroring the existing ones for the key-pair-injecting sends and
for `securityImpl`'s sends. -/

lemma oracleSendAWithChallengePk_run_sendReady
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendA = true)
    (hstA : σ.stA = State.sendReady pk) :
    (oracleSendAWithChallengePk kem gp pkStar ()).run σ =
      (do
        let (c, key) ← kem.encaps pk
        let (pkGenerated, skNext) ← kem.keygen
        let pkNext :=
          if sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } then pkStar
          else pkGenerated
        let msg : Message C PK := (c, pkNext)
        pure (some (msg, key),
          ({ σ with
              tA := σ.tA + 1,
              stA := State.recvReady skNext,
              rhoA := some msg,
              keyA := some key,
              lastAction := some .sendA } : SecurityState K PK SK C))) := by
  simp only [oracleSendAWithChallengePk, hvalid, ↓reduceIte, hstA,
    stateT_run, bind_assoc]

/-- Run reduction for the `pkStar`-embedding B-send oracle on a send-ready
state, the mirror of `oracleSendAWithChallengePk_run_sendReady`. -/
lemma oracleSendBWithChallengePk_run_sendReady
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hvalid : CKAScheme.validStep σ.lastAction .sendB = true)
    (hstB : σ.stB = State.sendReady pk) :
    (oracleSendBWithChallengePk kem gp pkStar ()).run σ =
      (do
        let (c, key) ← kem.encaps pk
        let (pkGenerated, skNext) ← kem.keygen
        let pkNext :=
          if sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } then pkStar
          else pkGenerated
        let msg : Message C PK := (c, pkNext)
        pure (some (msg, key),
          ({ σ with
              tB := σ.tB + 1,
              stB := State.recvReady skNext,
              rhoB := some msg,
              keyB := some key,
              lastAction := some .sendB } : SecurityState K PK SK C))) := by
  simp only [oracleSendBWithChallengePk, hvalid, ↓reduceIte, hstB,
    stateT_run, bind_assoc]

/-! ## A passed challenge stays passed

Once the challenged party's counter has reached the challenge epoch,
`willChallengeA` and `willChallengeB` stay false, and every oracle of the two
prefix implementations keeps the counters non-decreasing. -/

private lemma willChallengeA_eq_false_of_challengePassed
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : challengePassed (K := K) (PK := PK) (SK := SK) (C := C) gp σ) :
    willChallengeA gp σ = false := by
  cases hparty : gp.challengedParty with
  | A =>
      simp only [challengePassed, hparty] at hσ
      have hne : ¬ σ.tA + 1 = gp.challengeEpoch := by omega
      simp [willChallengeA, hparty, hne]
  | B => simp [willChallengeA, hparty]

private lemma willChallengeB_eq_false_of_challengePassed
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : challengePassed (K := K) (PK := PK) (SK := SK) (C := C) gp σ) :
    willChallengeB gp σ = false := by
  cases hparty : gp.challengedParty with
  | A => simp [willChallengeB, hparty]
  | B =>
      simp only [challengePassed, hparty] at hσ
      have hne : ¬ σ.tB + 1 = gp.challengeEpoch := by omega
      simp [willChallengeB, hparty, hne]

/-- The key-pair-injecting implementation keeps both epoch counters
non-decreasing, like `securityImpl`: only the send oracles differ, and they
bump the sender's counter by one. -/
private lemma wck_run_counters_mono [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    (t : (securitySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (z : (securitySpec leak).Range t × SecurityState K PK SK C)
    (hz : z ∈ support
      ((securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar t).run σ)) :
    σ.tA ≤ z.2.tA ∧ σ.tB ≤ z.2.tB := by
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom _ σ z hz
  · -- O-Send-A: the injecting variant differs only in the stored secret
    cases uSendA
    change z ∈ support ((oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ) at hz
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
    · cases hst : σ.stA with
      | sendReady pk =>
          rw [oracleSendAWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σ pk
            hvalid hst] at hz
          vcv_support hz
          obtain rfl := Set.mem_singleton_iff.mp hz
          exact ⟨Nat.le_succ _, le_refl _⟩
      | recvReady sk =>
          simp only [oracleSendAWithChallengeKeyPair, hvalid, ↓reduceIte, hst,
            stateT_run] at hz
          vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      simp only [oracleSendAWithChallengeKeyPair, hvalidFalse, Bool.false_eq_true,
        ↓reduceIte, stateT_run] at hz
      vcv_support
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain) σ z hz
  · -- O-Send-B: mirror of O-Send-A
    cases uSendB
    change z ∈ support ((oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ) at hz
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
    · cases hst : σ.stB with
      | sendReady pk =>
          rw [oracleSendBWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σ pk
            hvalid hst] at hz
          vcv_support hz
          obtain rfl := Set.mem_singleton_iff.mp hz
          exact ⟨le_refl _, Nat.le_succ _⟩
      | recvReady sk =>
          simp only [oracleSendBWithChallengeKeyPair, hvalid, ↓reduceIte, hst,
            stateT_run] at hz
          vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      simp only [oracleSendBWithChallengeKeyPair, hvalidFalse, Bool.false_eq_true,
        ↓reduceIte, stateT_run] at hz
      vcv_support
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp isRandom
      (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain) σ z hz

/-- The reduction prefix implementation keeps both epoch counters
non-decreasing: only its send oracles differ from `securityImpl`'s, and they
bump the sender's counter by one. -/
private lemma prefixImpl_run_counters_mono [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    (t : (securitySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (z : (securitySpec leak).Range t × SecurityState K PK SK C)
    (hz : z ∈ support ((prefixImpl kem hDet leak gp pkStar t).run σ)) :
    σ.tA ≤ z.2.tA ∧ σ.tB ≤ z.2.tB := by
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  · exact securityImpl_run_counters_mono kem hDet leak gp false _ σ z hz
  · -- O-Send-A: the public-key-injecting variant
    cases uSendA
    change z ∈ support ((oracleSendAWithChallengePk kem gp pkStar ()).run σ) at hz
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
    · cases hst : σ.stA with
      | sendReady pk =>
          rw [oracleSendAWithChallengePk_run_sendReady kem gp pkStar σ pk hvalid hst] at hz
          vcv_support hz
          obtain rfl := Set.mem_singleton_iff.mp hz
          exact ⟨Nat.le_succ _, le_refl _⟩
      | recvReady sk =>
          simp only [oracleSendAWithChallengePk, hvalid, ↓reduceIte, hst,
            stateT_run] at hz
          vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      simp only [oracleSendAWithChallengePk, hvalidFalse, Bool.false_eq_true,
        ↓reduceIte, stateT_run] at hz
      vcv_support
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain) σ z hz
  · -- O-Send-B: mirror of O-Send-A
    cases uSendB
    change z ∈ support ((oracleSendBWithChallengePk kem gp pkStar ()).run σ) at hz
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
    · cases hst : σ.stB with
      | sendReady pk =>
          rw [oracleSendBWithChallengePk_run_sendReady kem gp pkStar σ pk hvalid hst] at hz
          vcv_support hz
          obtain rfl := Set.mem_singleton_iff.mp hz
          exact ⟨le_refl _, Nat.le_succ _⟩
      | recvReady sk =>
          simp only [oracleSendBWithChallengePk, hvalid, ↓reduceIte, hst,
            stateT_run] at hz
          vcv_support
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      simp only [oracleSendBWithChallengePk, hvalidFalse, Bool.false_eq_true,
        ↓reduceIte, stateT_run] at hz
      vcv_support
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain) σ z hz
  · exact securityImpl_run_counters_mono kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain) σ z hz

/-- From a state past the challenge epoch, the injected prefix never pauses. -/
lemma injectedChallengePrefix_run_done_of_challengePassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    {α : Type}
    (adv : OracleComp (securitySpec leak) α)
    (σ : SecurityState K PK SK C)
    (z : CKAChallengeStepResult leak α × SecurityState K PK SK C) :
    challengePassed gp σ →
      z ∈ support
        ((injectedChallengePrefix kem hDet leak gp isRandom pkStar skStar adv).run σ) →
      ∃ a, z.1 = CKAChallengeStepResult.done a := by
  induction adv using OracleComp.inductionOn generalizing σ with
  | pure a =>
      intro _ hz
      simp only [injectedChallengePrefix, construct_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      exact ⟨a, by simp [hz]⟩
  | query_bind t cont ih =>
      intro hσ hz
      have hstep : ∀ (u : (securitySpec leak).Range t)
          (σ' : SecurityState K PK SK C),
          ((u, σ') ∈ support
            ((securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar t).run
              σ)) →
          challengePassed gp σ' := by
        intro u σ' hu
        obtain ⟨hA, hB⟩ :=
          wck_run_counters_mono kem hDet leak gp isRandom pkStar skStar t σ (u, σ') hu
        cases hcp : gp.challengedParty
        · simp only [challengePassed, hcp] at hσ ⊢
          exact le_trans hσ hA
        · simp only [challengePassed, hcp] at hσ ⊢
          exact le_trans hσ hB
      have hWillA := willChallengeA_eq_false_of_challengePassed gp σ hσ
      have hWillB := willChallengeB_eq_false_of_challengePassed gp σ hσ
      rcases t with
        (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
          uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
      all_goals
        try cases uSendA
        try cases uRecvA
        try cases uSendB
        try cases uRecvB
        try cases uChallA
        try cases uChallB
        try cases uCorrA
        try cases uCorrB
        try cases uRLeakA
        try cases uRLeakB
      all_goals
        simp only [injectedChallengePrefix, construct_query_bind, stateT_run,
          hWillA, hWillB, Bool.false_eq_true, ↓reduceIte,
          support_bind, Set.mem_iUnion₂] at hz
        obtain ⟨p, hp, hz'⟩ := hz
        exact ih p.1 p.2 (hstep p.1 p.2 hp) hz'

/-- From a state past the challenge epoch, the reduction prefix never pauses. -/
lemma challengePrefix_run_done_of_challengePassed
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    {α : Type}
    (adv : OracleComp (securitySpec leak) α)
    (σ : SecurityState K PK SK C)
    (z : CKAChallengeStepResult leak α × SecurityState K PK SK C) :
    challengePassed gp σ →
      z ∈ support ((challengePrefix kem hDet leak gp pkStar adv).run σ) →
      ∃ a, z.1 = CKAChallengeStepResult.done a := by
  induction adv using OracleComp.inductionOn generalizing σ with
  | pure a =>
      intro _ hz
      simp only [challengePrefix, construct_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      exact ⟨a, by simp [hz]⟩
  | query_bind t cont ih =>
      intro hσ hz
      have hstep : ∀ (u : (securitySpec leak).Range t)
          (σ' : SecurityState K PK SK C),
          ((u, σ') ∈ support ((prefixImpl kem hDet leak gp pkStar t).run σ)) →
          challengePassed gp σ' := by
        intro u σ' hu
        obtain ⟨hA, hB⟩ :=
          prefixImpl_run_counters_mono kem hDet leak gp pkStar t σ (u, σ') hu
        cases hcp : gp.challengedParty
        · simp only [challengePassed, hcp] at hσ ⊢
          exact le_trans hσ hA
        · simp only [challengePassed, hcp] at hσ ⊢
          exact le_trans hσ hB
      have hWillA := willChallengeA_eq_false_of_challengePassed gp σ hσ
      have hWillB := willChallengeB_eq_false_of_challengePassed gp σ hσ
      rcases t with
        (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
          uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
      all_goals
        try cases uSendA
        try cases uRecvA
        try cases uSendB
        try cases uRecvB
        try cases uChallA
        try cases uChallB
        try cases uCorrA
        try cases uCorrB
        try cases uRLeakA
        try cases uRLeakB
      all_goals
        simp only [challengePrefix, construct_query_bind, stateT_run,
          hWillA, hWillB, Bool.false_eq_true, ↓reduceIte,
          support_bind, Set.mem_iUnion₂] at hz
        obtain ⟨p, hp, hz'⟩ := hz
        exact ih p.1 p.2 (hstep p.1 p.2 hp) hz'

/-! ## The state shape maintained by `securityImpl`

Up to the injecting send both split prefixes step the unmodified
`securityImpl`.  `securityShapeInv` records the state shape these steps
maintain: the pending secret keys pair with the public keys they will
decapsulate against, as key-generation support pairs. -/

def securityShapeInv
    (kem : KEMScheme ProbComp K PK SK C)
    (s : SecurityState K PK SK C) : Prop :=
  match s.lastAction with
  | none | some .recvA =>
      ∃ pk sk, (pk, sk) ∈ support kem.keygen ∧
        s.stA = .sendReady pk ∧ s.stB = .recvReady sk ∧
        s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendA =>
      ∃ pk sk c key pk' sk',
        (pk, sk) ∈ support kem.keygen ∧
        (c, key) ∈ support (kem.encaps pk) ∧
        (pk', sk') ∈ support kem.keygen ∧
        s.stA = .recvReady sk' ∧ s.stB = .recvReady sk ∧
        s.rhoA = some (c, pk') ∧ s.rhoB = none ∧
        s.keyA = some key ∧ s.keyB = none
  | some .recvB =>
      ∃ pk sk, (pk, sk) ∈ support kem.keygen ∧
        s.stA = .recvReady sk ∧ s.stB = .sendReady pk ∧
        s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendB =>
      ∃ pk sk c key pk' sk',
        (pk, sk) ∈ support kem.keygen ∧
        (c, key) ∈ support (kem.encaps pk) ∧
        (pk', sk') ∈ support kem.keygen ∧
        s.stA = .recvReady sk ∧ s.stB = .recvReady sk' ∧
        s.rhoA = none ∧ s.rhoB = some (c, pk') ∧
        s.keyA = none ∧ s.keyB = some key
  | some .challA | some .challB => False

/-! ## Supports of the randomness-leaking KEM calls

By `keygen_fst` and `encaps_fst`, `kem.keygen` and `kem.encaps` are the first
components of `keygen_rleak` and `encaps_rleak`, so a support fact for a
leaking call projects to one for the underlying call.  The randomness-leaking
sends preserve the shape invariant through these projections. -/

lemma mem_support_encaps_of_encaps_rleak
    (kem : KEMScheme ProbComp K PK SK C)
    (leak : RandLeak kem)
    {pk : PK} {ck : C × K} {r : leak.EncapsRand}
    (h : (ck, r) ∈ support (leak.encaps_rleak pk)) :
    ck ∈ support (kem.encaps pk) := by
  rw [← leak.encaps_fst pk]
  exact (mem_support_bind_iff _ _ _).2 ⟨(ck, r), h, by simp⟩

/-- Key-generation analogue of `mem_support_encaps_of_encaps_rleak`: a draw
of the leaking key generation projects to a draw of `kem.keygen`. -/
lemma mem_support_keygen_of_keygen_rleak
    (kem : KEMScheme ProbComp K PK SK C)
    (leak : RandLeak kem)
    {ks : PK × SK} {r : leak.KeygenRand}
    (h : (ks, r) ∈ support leak.keygen_rleak) :
    ks ∈ support kem.keygen := by
  rw [← leak.keygen_fst]
  exact (mem_support_bind_iff _ _ _).2 ⟨(ks, r), h, by simp⟩

/-! ## The injecting sends with the guard off

When the inject guard is false on the bumped state, both modified send oracles
run exactly the unmodified send. -/

lemma oracleSendAWithChallengeKeyPair_run_eq_of_not_inject
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK)
    (σ : SecurityState K PK SK C)
    (hg : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = false) :
    (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ =
      (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ := by
  simp only [sendAInjectsChallengeKey] at hg
  rw [show (securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ =
      (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ from rfl]
  by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
  · cases hst : σ.stA with
    | sendReady pk =>
        have hg' : ¬ (gp.challengedParty = CKAScheme.CKAParty.B ∧
            σ.tA + 1 = gp.challengeEpoch - 1) := by
          rintro ⟨h1, h2⟩
          simp [h1, h2] at hg
        simp [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, scheme, send,
          hvalid, hst, sendAInjectsChallengeKey, hg']
    | recvReady sk =>
        simp [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, scheme, send,
          hvalid, hst]
  · simp [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA,
      Bool.eq_false_of_not_eq_true hvalid]

/-- Off the installing send, the injecting B-send agrees with the honest
B-send, the mirror of `oracleSendAWithChallengeKeyPair_run_eq_of_not_inject`. -/
lemma oracleSendBWithChallengeKeyPair_run_eq_of_not_inject
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK)
    (σ : SecurityState K PK SK C)
    (hg : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = false) :
    (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ =
      (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ := by
  simp only [sendBInjectsChallengeKey] at hg
  rw [show (securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ =
      (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ from rfl]
  by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
  · cases hst : σ.stB with
    | sendReady pk =>
        have hg' : ¬ (gp.challengedParty = CKAScheme.CKAParty.A ∧
            σ.tB + 1 = gp.challengeEpoch - 1) := by
          rintro ⟨h1, h2⟩
          simp [h1, h2] at hg
        simp [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, scheme, send,
          hvalid, hst, sendBInjectsChallengeKey, hg']
    | recvReady sk =>
        simp [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, scheme, send,
          hvalid, hst]
  · simp [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB,
      Bool.eq_false_of_not_eq_true hvalid]

/-- Off the installing send, the `pkStar`-embedding A-send agrees with the
honest A-send — the `WithChallengePk` variant of
`oracleSendAWithChallengeKeyPair_run_eq_of_not_inject`. -/
lemma oracleSendAWithChallengePk_run_eq_of_not_inject
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    (σ : SecurityState K PK SK C)
    (hg : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = false) :
    (oracleSendAWithChallengePk kem gp pkStar ()).run σ =
      (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ := by
  simp only [sendAInjectsChallengeKey] at hg
  rw [show (securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ =
      (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ from rfl]
  by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
  · cases hst : σ.stA with
    | sendReady pk =>
        have hg' : ¬ (gp.challengedParty = CKAScheme.CKAParty.B ∧
            σ.tA + 1 = gp.challengeEpoch - 1) := by
          rintro ⟨h1, h2⟩
          simp [h1, h2] at hg
        simp [oracleSendAWithChallengePk, CKAScheme.oracleSendA, scheme, send,
          hvalid, hst, sendAInjectsChallengeKey, hg']
    | recvReady sk =>
        simp [oracleSendAWithChallengePk, CKAScheme.oracleSendA, scheme, send,
          hvalid, hst]
  · simp [oracleSendAWithChallengePk, CKAScheme.oracleSendA,
      Bool.eq_false_of_not_eq_true hvalid]

/-- Off the installing send, the `pkStar`-embedding B-send agrees with the
honest B-send, the mirror of `oracleSendAWithChallengePk_run_eq_of_not_inject`. -/
lemma oracleSendBWithChallengePk_run_eq_of_not_inject
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK)
    (σ : SecurityState K PK SK C)
    (hg : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = false) :
    (oracleSendBWithChallengePk kem gp pkStar ()).run σ =
      (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ := by
  simp only [sendBInjectsChallengeKey] at hg
  rw [show (securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ =
      (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ from rfl]
  by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
  · cases hst : σ.stB with
    | sendReady pk =>
        have hg' : ¬ (gp.challengedParty = CKAScheme.CKAParty.A ∧
            σ.tB + 1 = gp.challengeEpoch - 1) := by
          rintro ⟨h1, h2⟩
          simp [h1, h2] at hg
        simp [oracleSendBWithChallengePk, CKAScheme.oracleSendB, scheme, send,
          hvalid, hst, sendBInjectsChallengeKey, hg']
    | recvReady sk =>
        simp [oracleSendBWithChallengePk, CKAScheme.oracleSendB, scheme, send,
          hvalid, hst]
  · simp [oracleSendBWithChallengePk, CKAScheme.oracleSendB,
      Bool.eq_false_of_not_eq_true hvalid]

end kemCKA
