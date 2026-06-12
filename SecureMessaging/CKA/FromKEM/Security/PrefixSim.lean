/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.HiddenStateSim
import ToVCVio.ProgramLogic.Relational.Basic
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# CKA from KEM — Prefix Simulation

Pre-challenge pieces of the hidden-state simulation. The prepared states
(`preAToBHonestState`, `preAToBReductionState`, and their B-side mirrors) fix
the moment just before the due challenge, with the challenge public key
installed and the reduction not holding its secret key.

The four `chall…_cont_run'_relTriple` lemmas answer the due challenge from
those states and hand the run over to the post-challenge relation: the honest
real-key (`isRandom = false`) and random-key (`isRandom = true`) games match
the reduction's challenge step fed the encapsulated key or an independent
uniform key. `ChallengeBridge` repackages these as probability equalities.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-- Relation used once the raw reduction has switched from prefix mode to the
post-challenge simulator. -/
private def reductionStatePostRel
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps (K := K) (PK := PK) (SK := SK) (C := C) kem)
    (gp : CKAScheme.GameParams) :
    SecurityState K PK SK C → ReductionBranchState K PK SK C → Prop
  | honest, .post post => PostRel kem hDet gp honest post
  | _, .pre _ => False

/-- Honest state immediately before an A-to-B challenge using `pkStar`.

The reduction side stores the same public sender state but does not know
`skStar`; the honest side keeps it in B's receive state. -/
def preAToBHonestState
    (base : SecurityState K PK SK C) (pkStar : PK) (skStar : SK) :
    SecurityState K PK SK C :=
  { base with stA := State.sendReady pkStar, stB := State.recvReady skStar }

/-- Reduction-side projection of `preAToBHonestState`, with the hidden receiver
secret removed. -/
def preAToBReductionState
    (base : SecurityState K PK SK C) (pkStar : PK) :
    SecurityState K PK SK C :=
  { base with stA := State.sendReady pkStar }

/-- Honest state immediately before a B-to-A challenge using `pkStar`. -/
def preBToAHonestState
    (base : SecurityState K PK SK C) (pkStar : PK) (skStar : SK) :
    SecurityState K PK SK C :=
  { base with stB := State.sendReady pkStar, stA := State.recvReady skStar }

/-- Reduction-side projection of `preBToAHonestState`, with the hidden receiver
secret removed. -/
def preBToAReductionState
    (base : SecurityState K PK SK C) (pkStar : PK) :
    SecurityState K PK SK C :=
  { base with stB := State.sendReady pkStar }

private lemma securityImpl_challA_preAToB_real_run
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (pkStar : PK) (skStar : SK)
    (hWill : willChallengeA gp σ = true) :
    (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState σ pkStar skStar) =
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stA := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challA,
          tA := σ.tA + 1 }
        pure (some (msg, realKey), postAToBHonestState base skStar msg realKey)) := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have hvalidAndParty := (Bool.and_eq_true _ _).mp hparts.1
  have hvalid : CKAScheme.validStep σ.lastAction .challA = true := hvalidAndParty.1
  have hparty :
      gp.challengedParty = CKAScheme.CKAParty.A :=
    beq_iff_eq.mp hvalidAndParty.2
  have ht : σ.tA + 1 = gp.challengeEpoch := beq_iff_eq.mp hparts.2
  change (CKAScheme.oracleChallA gp false (scheme kem hDet leak) ()).run
      (preAToBHonestState σ pkStar skStar) = _
  simp [CKAScheme.oracleChallA, scheme, send, preAToBHonestState,
    postAToBHonestState, CKAScheme.isChallengeEpoch, CKAScheme.GameState.tP,
    hvalid, hparty, ht, stateT_run,
    map_eq_bind_pure_comp]
  rfl

private lemma securityImpl_challA_preAToB_random_run
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (pkStar : PK) (skStar : SK)
    (hWill : willChallengeA gp σ = true) :
    (securityImpl kem hDet leak gp true
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState σ pkStar skStar) =
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let (pkNext, skNext) ← kem.keygen
        let outKey ← ($ᵗ K : ProbComp K)
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stA := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challA,
          tA := σ.tA + 1 }
        pure (some (msg, outKey), postAToBHonestState base skStar msg realKey)) := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have hvalidAndParty := (Bool.and_eq_true _ _).mp hparts.1
  have hvalid : CKAScheme.validStep σ.lastAction .challA = true := hvalidAndParty.1
  have hparty :
      gp.challengedParty = CKAScheme.CKAParty.A :=
    beq_iff_eq.mp hvalidAndParty.2
  have ht : σ.tA + 1 = gp.challengeEpoch := beq_iff_eq.mp hparts.2
  change (CKAScheme.oracleChallA gp true (scheme kem hDet leak) ()).run
      (preAToBHonestState σ pkStar skStar) = _
  simp [CKAScheme.oracleChallA, scheme, send, preAToBHonestState,
    postAToBHonestState, CKAScheme.isChallengeEpoch, CKAScheme.GameState.tP,
    hvalid, hparty, ht, stateT_run,
    map_eq_bind_pure_comp]
  rfl

private lemma securityImpl_challB_preBToA_real_run
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (pkStar : PK) (skStar : SK)
    (hWill : willChallengeB gp σ = true) :
    (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState σ pkStar skStar) =
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stB := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challB,
          tB := σ.tB + 1 }
        pure (some (msg, realKey), postBToAHonestState base skStar msg realKey)) := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have hvalidAndParty := (Bool.and_eq_true _ _).mp hparts.1
  have hvalid : CKAScheme.validStep σ.lastAction .challB = true := hvalidAndParty.1
  have hparty :
      gp.challengedParty = CKAScheme.CKAParty.B :=
    beq_iff_eq.mp hvalidAndParty.2
  have ht : σ.tB + 1 = gp.challengeEpoch := beq_iff_eq.mp hparts.2
  change (CKAScheme.oracleChallB gp false (scheme kem hDet leak) ()).run
      (preBToAHonestState σ pkStar skStar) = _
  simp [CKAScheme.oracleChallB, scheme, send, preBToAHonestState,
    postBToAHonestState, CKAScheme.isChallengeEpoch, CKAScheme.GameState.tP,
    hvalid, hparty, ht, stateT_run,
    map_eq_bind_pure_comp]
  rfl

private lemma securityImpl_challB_preBToA_random_run
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (pkStar : PK) (skStar : SK)
    (hWill : willChallengeB gp σ = true) :
    (securityImpl kem hDet leak gp true
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState σ pkStar skStar) =
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let (pkNext, skNext) ← kem.keygen
        let outKey ← ($ᵗ K : ProbComp K)
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stB := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challB,
          tB := σ.tB + 1 }
        pure (some (msg, outKey), postBToAHonestState base skStar msg realKey)) := by
  have hparts := (Bool.and_eq_true _ _).mp hWill
  have hvalidAndParty := (Bool.and_eq_true _ _).mp hparts.1
  have hvalid : CKAScheme.validStep σ.lastAction .challB = true := hvalidAndParty.1
  have hparty :
      gp.challengedParty = CKAScheme.CKAParty.B :=
    beq_iff_eq.mp hvalidAndParty.2
  have ht : σ.tB + 1 = gp.challengeEpoch := beq_iff_eq.mp hparts.2
  change (CKAScheme.oracleChallB gp true (scheme kem hDet leak) ()).run
      (preBToAHonestState σ pkStar skStar) = _
  simp [CKAScheme.oracleChallB, scheme, send, preBToAHonestState,
    postBToAHonestState, CKAScheme.isChallengeEpoch, CKAScheme.GameState.tP,
    hvalid, hparty, ht, stateT_run,
    map_eq_bind_pure_comp]
  rfl

private lemma reductionBranchImpl_challA_preAToB_run_of_will
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (pkStar : PK) (cStar : C) (kStar : K)
    (hWill : willChallengeA gp σ = true) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre (preAToBReductionState σ pkStar)) =
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { preAToBReductionState σ pkStar with
          stA := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challA,
          tA := σ.tA + 1 }
        pure (some (msg, kStar),
          ReductionBranchState.post (postAToBReductionState base msg kStar))) := by
  have hWill' : willChallengeA gp (preAToBReductionState σ pkStar) = true := by
    simpa [preAToBReductionState, willChallengeA] using hWill
  rw [reductionBranchImpl_pre_challA_run_of_will kem hDet leak gp pkStar cStar kStar
    (preAToBReductionState σ pkStar) hWill']
  rfl

private lemma reductionBranchImpl_challB_preBToA_run_of_will
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (pkStar : PK) (cStar : C) (kStar : K)
    (hWill : willChallengeB gp σ = true) :
    (reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre (preBToAReductionState σ pkStar)) =
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { preBToAReductionState σ pkStar with
          stB := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challB,
          tB := σ.tB + 1 }
        pure (some (msg, kStar),
          ReductionBranchState.post (postBToAReductionState base msg kStar))) := by
  have hWill' : willChallengeB gp (preBToAReductionState σ pkStar) = true := by
    simpa [preBToAReductionState, willChallengeB] using hWill
  rw [reductionBranchImpl_pre_challB_run_of_will kem hDet leak gp pkStar cStar kStar
    (preBToAReductionState σ pkStar) hWill']
  rfl

private lemma challA_sampled_keygen_rel
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK} {cStar : C} {realKey fakeKey outKey : K}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (hck : (cStar, realKey) ∈ support (kem.encaps pkStar)) :
    RelTriple
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stA := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challA,
          tA := σ.tA + 1 }
        pure (some (msg, outKey), postAToBHonestState base skStar msg realKey))
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stA := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challA,
          tA := σ.tA + 1 }
        pure (some (msg, outKey),
          ReductionBranchState.post (postAToBReductionState base msg fakeKey)))
      (fun p q => p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2) := by
  refine relTriple_bind (relTriple_refl kem.keygen) ?_
  intro pkNext_skNext pkNext_skNext' hEq
  subst hEq
  apply relTriple_pure_pure
  constructor
  · rfl
  · change PostRel kem hDet gp
      (postAToBHonestState
        ({ σ with
            stA := State.recvReady pkNext_skNext.2,
            lastAction := some CKAScheme.CKAAction.challA,
            tA := σ.tA + 1 } : SecurityState K PK SK C)
        skStar (cStar, pkNext_skNext.1) realKey)
      (postAToBReductionState
        ({ σ with
            stA := State.recvReady pkNext_skNext.2,
            lastAction := some CKAScheme.CKAAction.challA,
            tA := σ.tA + 1 } : SecurityState K PK SK C)
        (cStar, pkNext_skNext.1) fakeKey)
    exact postRel_aToB_after_challA_of_mem_support kem hDet hkem gp hgp σ
      hInv hWill hks (by simpa using hck)

private lemma challA_sampled_reduction_query_rel
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK} {cStar : C} {realKey kStar : K}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (hck : (cStar, realKey) ∈ support (kem.encaps pkStar)) :
    RelTriple
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stA := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challA,
          tA := σ.tA + 1 }
        pure (some (msg, kStar), postAToBHonestState base skStar msg realKey))
      ((reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre (preAToBReductionState σ pkStar)))
      (fun p q => p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2) := by
  rw [reductionBranchImpl_challA_preAToB_run_of_will kem hDet leak gp σ pkStar cStar
    kStar hWill]
  simpa [preAToBReductionState] using
    challA_sampled_keygen_rel kem hDet hkem gp hgp σ (pkStar := pkStar)
      (skStar := skStar) (cStar := cStar) (realKey := realKey) (fakeKey := kStar)
      (outKey := kStar) hInv hWill hks hck

private lemma reductionStatePostRel_run'_relTriple
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    {α : Type}
    (adv : OracleComp (securitySpec leak) α)
    {honest : SecurityState K PK SK C}
    {rs : ReductionBranchState K PK SK C}
    (hrel : reductionStatePostRel kem hDet gp honest rs) :
    RelTriple
      ((simulateQ (securityImpl kem hDet leak gp false) adv).run' honest)
      ((simulateQ (reductionBranchImpl kem hDet leak gp pkStar cStar kStar) adv).run' rs)
      (EqRel α) := by
  cases rs with
  | pre _ =>
      cases hrel
  | post ps =>
      dsimp [reductionStatePostRel] at hrel
      have hpost := postRel_run'_relTriple kem hDet leak gp adv hrel
      rw [StateT.run'_eq]
      rw [StateT.run'_eq]
      rw [reductionBranchImpl_post_simulateQ_run]
      simpa [StateT.run'_eq, map_eq_bind_pure_comp] using hpost

/-- Prepared A-challenge step, real-key case: from
`preAToBHonestState`/`preAToBReductionState`, the honest `isRandom = false`
challenge answer plus honest continuation matches the reduction's challenge
step fed the key encapsulated under `pkStar`, plus its post-challenge
simulation. -/
lemma challA_sampled_reduction_cont_run'_relTriple
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    {α : Type}
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) α) :
    RelTriple
      (((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey
            (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preAToBReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey)
          (cont q.1)).run' q.2)
      (EqRel α) := by
  rw [securityImpl_challA_preAToB_real_run kem hDet leak gp σ pkStar skStar hWill]
  simp only [bind_assoc]
  refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
  intro ck ck' hckRel
  rcases hckRel with ⟨hckEq, hck⟩
  subst hckEq
  rcases ck with ⟨cStar, realKey⟩
  have hstep :=
    challA_sampled_reduction_query_rel kem hDet hkem leak gp hgp σ
      (pkStar := pkStar) (skStar := skStar) (cStar := cStar)
      (realKey := realKey) (kStar := realKey) hInv hWill hks hck
  have hcont :
      ∀ (p : Option (Message C PK × K) × SecurityState K PK SK C)
        (q : Option (Message C PK × K) × ReductionBranchState K PK SK C),
        p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2 →
        RelTriple
          ((simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
          ((simulateQ
            (reductionBranchImpl kem hDet leak gp pkStar cStar realKey)
            (cont q.1)).run' q.2)
          (EqRel α) := by
    intro p q hp
    rcases hp with ⟨hout, hrel⟩
    rw [← hout]
    exact reductionStatePostRel_run'_relTriple kem hDet leak gp pkStar cStar realKey
      (cont p.1) hrel
  simpa only [bind_assoc] using relTriple_bind hstep hcont

/-- Prepared A-challenge step, random-key case: the honest `isRandom = true`
challenge answer plus honest continuation matches the reduction's challenge
step fed an independent uniform key. The random-branch counterpart of
`challA_sampled_reduction_cont_run'_relTriple`. -/
lemma challA_sampled_reduction_random_cont_run'_relTriple
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    {α : Type}
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) α) :
    RelTriple
      (((securityImpl kem hDet leak gp true
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      (do
        let (cStar, _realKey) ← kem.encaps pkStar
        let kRand ← ($ᵗ K : ProbComp K)
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand
            (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preAToBReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand)
          (cont q.1)).run' q.2)
      (EqRel α) := by
  rw [securityImpl_challA_preAToB_random_run kem hDet leak gp σ pkStar skStar hWill]
  simp only [bind_assoc]
  refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
  intro ck ck' hckRel
  rcases hckRel with ⟨hckEq, hck⟩
  subst hckEq
  rcases ck with ⟨cStar, realKey⟩
  let leftAfterSwap : ProbComp α := do
    let outKey ← ($ᵗ K : ProbComp K)
    let p ← do
      let (pkNext, skNext) ← kem.keygen
      let msg : Message C PK := (cStar, pkNext)
      let base : SecurityState K PK SK C := { σ with
        stA := State.recvReady skNext,
        lastAction := some CKAScheme.CKAAction.challA,
        tA := σ.tA + 1 }
      pure (some (msg, outKey), postAToBHonestState base skStar msg realKey)
    (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2
  have hswap : RelTriple
      (do
        let pkNext_skNext ← kem.keygen
        let outKey ← ($ᵗ K : ProbComp K)
        let msg : Message C PK := (cStar, pkNext_skNext.1)
        let base : SecurityState K PK SK C := { σ with
          stA := State.recvReady pkNext_skNext.2,
          lastAction := some CKAScheme.CKAAction.challA,
          tA := σ.tA + 1 }
        let p := (some (msg, outKey), postAToBHonestState base skStar msg realKey)
        (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      leftAfterSwap
      (EqRel α) := by
    simpa [leftAfterSwap, bind_assoc] using
      (relTriple_bind_bind_swap_eqRel
        (oa := kem.keygen) (ob := ($ᵗ K : ProbComp K))
        (f := fun pkNext_skNext outKey =>
          let msg : Message C PK := (cStar, pkNext_skNext.1)
          let base : SecurityState K PK SK C := { σ with
            stA := State.recvReady pkNext_skNext.2,
            lastAction := some CKAScheme.CKAAction.challA,
            tA := σ.tA + 1 }
          let p := (some (msg, outKey), postAToBHonestState base skStar msg realKey)
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2))
  refine relTriple_trans_eqRel_left hswap ?_
  dsimp [leftAfterSwap]
  refine relTriple_bind (relTriple_refl ($ᵗ K : ProbComp K)) ?_
  intro outKey outKey' hout
  subst hout
  have hstep :=
    challA_sampled_reduction_query_rel kem hDet hkem leak gp hgp σ
      (pkStar := pkStar) (skStar := skStar) (cStar := cStar)
      (realKey := realKey) (kStar := outKey) hInv hWill hks hck
  have hcont :
      ∀ (p : Option (Message C PK × K) × SecurityState K PK SK C)
        (q : Option (Message C PK × K) × ReductionBranchState K PK SK C),
        p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2 →
        RelTriple
          ((simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
          ((simulateQ
            (reductionBranchImpl kem hDet leak gp pkStar cStar outKey)
            (cont q.1)).run' q.2)
          (EqRel α) := by
    intro p q hp
    rcases hp with ⟨hout, hrel⟩
    rw [← hout]
    exact reductionStatePostRel_run'_relTriple kem hDet leak gp pkStar cStar outKey
      (cont p.1) hrel
  simpa only [bind_assoc] using relTriple_bind hstep hcont

private lemma challB_sampled_keygen_rel
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK} {cStar : C} {realKey fakeKey outKey : K}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (hck : (cStar, realKey) ∈ support (kem.encaps pkStar)) :
    RelTriple
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stB := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challB,
          tB := σ.tB + 1 }
        pure (some (msg, outKey), postBToAHonestState base skStar msg realKey))
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stB := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challB,
          tB := σ.tB + 1 }
        pure (some (msg, outKey),
          ReductionBranchState.post (postBToAReductionState base msg fakeKey)))
      (fun p q => p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2) := by
  refine relTriple_bind (relTriple_refl kem.keygen) ?_
  intro pkNext_skNext pkNext_skNext' hEq
  subst hEq
  apply relTriple_pure_pure
  constructor
  · rfl
  · change PostRel kem hDet gp
      (postBToAHonestState
        ({ σ with
            stB := State.recvReady pkNext_skNext.2,
            lastAction := some CKAScheme.CKAAction.challB,
            tB := σ.tB + 1 } : SecurityState K PK SK C)
        skStar (cStar, pkNext_skNext.1) realKey)
      (postBToAReductionState
        ({ σ with
            stB := State.recvReady pkNext_skNext.2,
            lastAction := some CKAScheme.CKAAction.challB,
            tB := σ.tB + 1 } : SecurityState K PK SK C)
        (cStar, pkNext_skNext.1) fakeKey)
    exact postRel_bToA_after_challB_of_mem_support kem hDet hkem gp hgp σ
      hInv hWill hks (by simpa using hck)

private lemma challB_sampled_reduction_query_rel
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK} {cStar : C} {realKey kStar : K}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (hck : (cStar, realKey) ∈ support (kem.encaps pkStar)) :
    RelTriple
      (do
        let (pkNext, skNext) ← kem.keygen
        let msg : Message C PK := (cStar, pkNext)
        let base : SecurityState K PK SK C := { σ with
          stB := State.recvReady skNext,
          lastAction := some CKAScheme.CKAAction.challB,
          tB := σ.tB + 1 }
        pure (some (msg, kStar), postBToAHonestState base skStar msg realKey))
      ((reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre (preBToAReductionState σ pkStar)))
      (fun p q => p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2) := by
  rw [reductionBranchImpl_challB_preBToA_run_of_will kem hDet leak gp σ pkStar cStar
    kStar hWill]
  simpa [preBToAReductionState] using
    challB_sampled_keygen_rel kem hDet hkem gp hgp σ (pkStar := pkStar)
      (skStar := skStar) (cStar := cStar) (realKey := realKey) (fakeKey := kStar)
      (outKey := kStar) hInv hWill hks hck

/-- Prepared B-challenge step, real-key case, the mirror of
`challA_sampled_reduction_cont_run'_relTriple`. -/
lemma challB_sampled_reduction_cont_run'_relTriple
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    {α : Type}
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) α) :
    RelTriple
      (((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      (do
        let (cStar, realKey) ← kem.encaps pkStar
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey
            (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preBToAReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar realKey)
          (cont q.1)).run' q.2)
      (EqRel α) := by
  rw [securityImpl_challB_preBToA_real_run kem hDet leak gp σ pkStar skStar hWill]
  simp only [bind_assoc]
  refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
  intro ck ck' hckRel
  rcases hckRel with ⟨hckEq, hck⟩
  subst hckEq
  rcases ck with ⟨cStar, realKey⟩
  have hstep :=
    challB_sampled_reduction_query_rel kem hDet hkem leak gp hgp σ
      (pkStar := pkStar) (skStar := skStar) (cStar := cStar)
      (realKey := realKey) (kStar := realKey) hInv hWill hks hck
  have hcont :
      ∀ (p : Option (Message C PK × K) × SecurityState K PK SK C)
        (q : Option (Message C PK × K) × ReductionBranchState K PK SK C),
        p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2 →
        RelTriple
          ((simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
          ((simulateQ
            (reductionBranchImpl kem hDet leak gp pkStar cStar realKey)
            (cont q.1)).run' q.2)
          (EqRel α) := by
    intro p q hp
    rcases hp with ⟨hout, hrel⟩
    rw [← hout]
    exact reductionStatePostRel_run'_relTriple kem hDet leak gp pkStar cStar realKey
      (cont p.1) hrel
  simpa only [bind_assoc] using relTriple_bind hstep hcont

/-- Prepared B-challenge step, random-key case, the mirror of
`challA_sampled_reduction_random_cont_run'_relTriple`. -/
lemma challB_sampled_reduction_random_cont_run'_relTriple
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar : SK}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    {α : Type}
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) α) :
    RelTriple
      (((securityImpl kem hDet leak gp true
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState σ pkStar skStar)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      (do
        let (cStar, _realKey) ← kem.encaps pkStar
        let kRand ← ($ᵗ K : ProbComp K)
        let q ←
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand
            (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
            (ReductionBranchState.pre (preBToAReductionState σ pkStar))
        (simulateQ
          (reductionBranchImpl kem hDet leak gp pkStar cStar kRand)
          (cont q.1)).run' q.2)
      (EqRel α) := by
  rw [securityImpl_challB_preBToA_random_run kem hDet leak gp σ pkStar skStar hWill]
  simp only [bind_assoc]
  refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
  intro ck ck' hckRel
  rcases hckRel with ⟨hckEq, hck⟩
  subst hckEq
  rcases ck with ⟨cStar, realKey⟩
  let leftAfterSwap : ProbComp α := do
    let outKey ← ($ᵗ K : ProbComp K)
    let p ← do
      let (pkNext, skNext) ← kem.keygen
      let msg : Message C PK := (cStar, pkNext)
      let base : SecurityState K PK SK C := { σ with
        stB := State.recvReady skNext,
        lastAction := some CKAScheme.CKAAction.challB,
        tB := σ.tB + 1 }
      pure (some (msg, outKey), postBToAHonestState base skStar msg realKey)
    (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2
  have hswap : RelTriple
      (do
        let pkNext_skNext ← kem.keygen
        let outKey ← ($ᵗ K : ProbComp K)
        let msg : Message C PK := (cStar, pkNext_skNext.1)
        let base : SecurityState K PK SK C := { σ with
          stB := State.recvReady pkNext_skNext.2,
          lastAction := some CKAScheme.CKAAction.challB,
          tB := σ.tB + 1 }
        let p := (some (msg, outKey), postBToAHonestState base skStar msg realKey)
        (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      leftAfterSwap
      (EqRel α) := by
    simpa [leftAfterSwap, bind_assoc] using
      (relTriple_bind_bind_swap_eqRel
        (oa := kem.keygen) (ob := ($ᵗ K : ProbComp K))
        (f := fun pkNext_skNext outKey =>
          let msg : Message C PK := (cStar, pkNext_skNext.1)
          let base : SecurityState K PK SK C := { σ with
            stB := State.recvReady pkNext_skNext.2,
            lastAction := some CKAScheme.CKAAction.challB,
            tB := σ.tB + 1 }
          let p := (some (msg, outKey), postBToAHonestState base skStar msg realKey)
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2))
  refine relTriple_trans_eqRel_left hswap ?_
  dsimp [leftAfterSwap]
  refine relTriple_bind (relTriple_refl ($ᵗ K : ProbComp K)) ?_
  intro outKey outKey' hout
  subst hout
  have hstep :=
    challB_sampled_reduction_query_rel kem hDet hkem leak gp hgp σ
      (pkStar := pkStar) (skStar := skStar) (cStar := cStar)
      (realKey := realKey) (kStar := outKey) hInv hWill hks hck
  have hcont :
      ∀ (p : Option (Message C PK × K) × SecurityState K PK SK C)
        (q : Option (Message C PK × K) × ReductionBranchState K PK SK C),
        p.1 = q.1 ∧ reductionStatePostRel kem hDet gp p.2 q.2 →
        RelTriple
          ((simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
          ((simulateQ
            (reductionBranchImpl kem hDet leak gp pkStar cStar outKey)
            (cont q.1)).run' q.2)
          (EqRel α) := by
    intro p q hp
    rcases hp with ⟨hout, hrel⟩
    rw [← hout]
    exact reductionStatePostRel_run'_relTriple kem hDet leak gp pkStar cStar outKey
      (cont p.1) hrel
  simpa only [bind_assoc] using relTriple_bind hstep hcont

end kemCKA
