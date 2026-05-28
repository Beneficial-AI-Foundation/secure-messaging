/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.Branches
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# CKA from KEM — Hidden-State Simulation

This file contains the relational invariants used to connect the concrete CKA
fixed-bit games with the IND-CPA reduction branch.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

def postAToBHonestState
    (base : SecurityState K PK SK C) (sk : SK) (msg : Message C PK) (key : K) :
    SecurityState K PK SK C :=
  { base with stB := State.recvReady sk, rhoA := some msg, keyA := some key }

def postAToBReductionState
    (base : SecurityState K PK SK C) (msg : Message C PK) (key : K) :
    PostChallengeState K PK SK C :=
  { game := { base with rhoA := some msg, keyA := some key },
    pending := PendingChallengeRecv.aToB key msg.2 msg }

def postBToAHonestState
    (base : SecurityState K PK SK C) (sk : SK) (msg : Message C PK) (key : K) :
    SecurityState K PK SK C :=
  { base with stA := State.recvReady sk, rhoB := some msg, keyB := some key }

def postBToAReductionState
    (base : SecurityState K PK SK C) (msg : Message C PK) (key : K) :
    PostChallengeState K PK SK C :=
  { game := { base with rhoB := some msg, keyB := some key },
    pending := PendingChallengeRecv.bToA key msg.2 msg }

def noPendingPostState (s : SecurityState K PK SK C) : PostChallengeState K PK SK C :=
  { game := s, pending := PendingChallengeRecv.none }

/-- Relation for the post-challenge A-to-B window.

The honest CKA game still contains the receiver secret key `sk`, while the
reduction-side post-challenge game carries only the public projection plus a
pending receive override.  The two games are observationally equivalent until
the matching `ORecvB`; receiver corruption is blocked by admissibility in the
states where this relation is introduced.
-/
inductive PostAToBRel
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps (K := K) (PK := PK) (SK := SK) (C := C) kem)
    (gp : CKAScheme.GameParams)
    (honest : SecurityState K PK SK C)
    (post : PostChallengeState K PK SK C) : Prop where
  | intro
      (base : SecurityState K PK SK C)
      (sk : SK)
      (msg : Message C PK)
      (realKey fakeKey : K)
      (hhonest : honest = postAToBHonestState base sk msg realKey)
      (hpost : post = postAToBReductionState base msg fakeKey)
      (hdec : hDet.decapsDet sk msg.1 = some realKey)
      (hrecv : CKAScheme.validStep base.lastAction .recvB = true)
      (hblock : CKAScheme.allowCorr gp (postAToBReductionState base msg fakeKey).game .B = false)

/-- Relation for the post-challenge B-to-A window. -/
inductive PostBToARel
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps (K := K) (PK := PK) (SK := SK) (C := C) kem)
    (gp : CKAScheme.GameParams)
    (honest : SecurityState K PK SK C)
    (post : PostChallengeState K PK SK C) : Prop where
  | intro
      (base : SecurityState K PK SK C)
      (sk : SK)
      (msg : Message C PK)
      (realKey fakeKey : K)
      (hhonest : honest = postBToAHonestState base sk msg realKey)
      (hpost : post = postBToAReductionState base msg fakeKey)
      (hdec : hDet.decapsDet sk msg.1 = some realKey)
      (hrecv : CKAScheme.validStep base.lastAction .recvA = true)
      (hblock : CKAScheme.allowCorr gp (postBToAReductionState base msg fakeKey).game .A = false)

/-- Post-challenge relation used by the relational simulator. -/
inductive PostRel
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps (K := K) (PK := PK) (SK := SK) (C := C) kem)
    (gp : CKAScheme.GameParams) :
    SecurityState K PK SK C → PostChallengeState K PK SK C → Prop where
  | none (s : SecurityState K PK SK C) :
      PostRel kem hDet gp s { game := s, pending := .none }
  | aToB {honest : SecurityState K PK SK C} {post : PostChallengeState K PK SK C}
      (h : PostAToBRel kem hDet gp honest post) :
      PostRel kem hDet gp honest post
  | bToA {honest : SecurityState K PK SK C} {post : PostChallengeState K PK SK C}
      (h : PostBToARel kem hDet gp honest post) :
      PostRel kem hDet gp honest post

lemma postRel_aToB_after_challA
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    (skStar skNext : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hdec : hDet.decapsDet skStar msg.1 = some realKey) :
    PostRel kem hDet gp
      (postAToBHonestState
        ({ σ with
            stA := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challA,
            tA := σ.tA + 1 } : SecurityState K PK SK C)
        skStar msg realKey)
      (postAToBReductionState
        ({ σ with
            stA := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challA,
            tA := σ.tA + 1 } : SecurityState K PK SK C)
        msg fakeKey) := by
  let base : SecurityState K PK SK C :=
    { σ with
      stA := State.recvReady skNext,
      lastAction := some CKAScheme.CKAAction.challA,
      tA := σ.tA + 1 }
  have hrecv : CKAScheme.validStep base.lastAction .recvB = true := by
    simp [base, CKAScheme.validStep]
  have hblockBase : CKAScheme.allowCorr gp base .B = false := by
    simpa [base] using
      allowCorr_receiverB_false_after_challA gp hgp σ hInv hWill
  have hblock :
      CKAScheme.allowCorr gp
        (postAToBReductionState base msg fakeKey).game .B = false := by
    simpa [postAToBReductionState] using hblockBase
  exact PostRel.aToB
    (PostAToBRel.intro base skStar msg realKey fakeKey rfl rfl hdec hrecv hblock)

lemma postRel_aToB_after_challA_of_mem_support [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar skNext : SK} {msg : Message C PK} {realKey fakeKey : K}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeA gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (hck : (msg.1, realKey) ∈ support (kem.encaps pkStar)) :
    PostRel kem hDet gp
      (postAToBHonestState
        ({ σ with
            stA := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challA,
            tA := σ.tA + 1 } : SecurityState K PK SK C)
        skStar msg realKey)
      (postAToBReductionState
        ({ σ with
            stA := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challA,
            tA := σ.tA + 1 } : SecurityState K PK SK C)
        msg fakeKey) := by
  exact postRel_aToB_after_challA kem hDet gp hgp σ skStar skNext msg realKey
    fakeKey hInv hWill
    (decapsDet_eq_some_of_mem_support kem hDet hkem hks hck)

lemma postRel_bToA_after_challB
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    (skStar skNext : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hdec : hDet.decapsDet skStar msg.1 = some realKey) :
    PostRel kem hDet gp
      (postBToAHonestState
        ({ σ with
            stB := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challB,
            tB := σ.tB + 1 } : SecurityState K PK SK C)
        skStar msg realKey)
      (postBToAReductionState
        ({ σ with
            stB := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challB,
            tB := σ.tB + 1 } : SecurityState K PK SK C)
        msg fakeKey) := by
  let base : SecurityState K PK SK C :=
    { σ with
      stB := State.recvReady skNext,
      lastAction := some CKAScheme.CKAAction.challB,
      tB := σ.tB + 1 }
  have hrecv : CKAScheme.validStep base.lastAction .recvA = true := by
    simp [base, CKAScheme.validStep]
  have hblockBase : CKAScheme.allowCorr gp base .A = false := by
    simpa [base] using
      allowCorr_receiverA_false_after_challB gp hgp σ hInv hWill
  have hblock :
      CKAScheme.allowCorr gp
        (postBToAReductionState base msg fakeKey).game .A = false := by
    simpa [postBToAReductionState] using hblockBase
  exact PostRel.bToA
    (PostBToARel.intro base skStar msg realKey fakeKey rfl rfl hdec hrecv hblock)

lemma postRel_bToA_after_challB_of_mem_support [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (σ : SecurityState K PK SK C)
    {pkStar : PK} {skStar skNext : SK} {msg : Message C PK} {realKey fakeKey : K}
    (hInv : epochCounterInv σ)
    (hWill : willChallengeB gp σ = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (hck : (msg.1, realKey) ∈ support (kem.encaps pkStar)) :
    PostRel kem hDet gp
      (postBToAHonestState
        ({ σ with
            stB := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challB,
            tB := σ.tB + 1 } : SecurityState K PK SK C)
        skStar msg realKey)
      (postBToAReductionState
        ({ σ with
            stB := State.recvReady skNext,
            lastAction := some CKAScheme.CKAAction.challB,
            tB := σ.tB + 1 } : SecurityState K PK SK C)
        msg fakeKey) := by
  exact postRel_bToA_after_challB kem hDet gp hgp σ skStar skNext msg realKey
    fakeKey hInv hWill
    (decapsDet_eq_some_of_mem_support kem hDet hkem hks hck)

private lemma postRel_attach_none
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (gp : CKAScheme.GameParams)
    {α : Type}
    (mx : ProbComp (α × SecurityState K PK SK C)) :
    RelTriple mx
      ((fun a =>
          (a.1, ({ game := a.2, pending := PendingChallengeRecv.none } :
            PostChallengeState K PK SK C))) <$> mx)
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  let f := fun a : α × SecurityState K PK SK C =>
    (a.1, ({ game := a.2, pending := PendingChallengeRecv.none } :
      PostChallengeState K PK SK C))
  have h : RelTriple (mx >>= fun a => pure a) (mx >>= fun a => pure (f a))
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
    refine relTriple_bind (relTriple_refl mx) ?_
    intro a b hab
    subst hab
    exact relTriple_pure_pure (by simp [f, PostRel.none])
  simpa [f, map_eq_bind_pure_comp] using h

private lemma postRel_attach
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (gp : CKAScheme.GameParams)
    {α : Type}
    (mx : ProbComp α)
    {honest : SecurityState K PK SK C}
    {post : PostChallengeState K PK SK C}
    (hrel : PostRel kem hDet gp honest post) :
    RelTriple
      ((fun a => (a, honest)) <$> mx)
      ((fun a => (a, post)) <$> mx)
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  have h : RelTriple
      (mx >>= fun a => pure (a, honest))
      (mx >>= fun a => pure (a, post))
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
    refine relTriple_bind (relTriple_refl mx) ?_
    intro a b hab
    subst hab
    exact relTriple_pure_pure ⟨rfl, hrel⟩
  simpa [map_eq_bind_pure_comp] using h

private lemma postChallengeImpl_none_run_eq [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (SecuritySpec leak).Domain)
    (s : SecurityState K PK SK C) :
    (postChallengeImpl kem hDet leak gp t).run
        ({ game := s, pending := PendingChallengeRecv.none } :
          PostChallengeState K PK SK C) =
      ((fun a =>
          (a.1, ({ game := a.2, pending := PendingChallengeRecv.none } :
            PostChallengeState K PK SK C))) <$>
        (securityImpl kem hDet leak gp false t).run s) := by
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
    simp [postChallengeImpl, liftSecurityImplToPost, StateT.run_bind, StateT.run_get,
      StateT.run_set]

/-- A post-challenge state with no pending override exactly follows the honest
security implementation, preserving the projected relation. -/
lemma postRel_none_step [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (SecuritySpec leak).Domain)
    (s : SecurityState K PK SK C) :
    RelTriple
      ((securityImpl kem hDet leak gp false t).run s)
      ((postChallengeImpl kem hDet leak gp t).run
        ({ game := s, pending := PendingChallengeRecv.none } :
          PostChallengeState K PK SK C))
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  rw [postChallengeImpl_none_run_eq]
  exact postRel_attach_none (kem := kem) (hDet := hDet) (gp := gp)
    ((securityImpl kem hDet leak gp false t).run s)

lemma securityImpl_postChallenge_none_run'_relTriple
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    {α : Type}
    (adv : OracleComp (SecuritySpec leak) α)
    (s : SecurityState K PK SK C) :
    RelTriple
      ((simulateQ (securityImpl kem hDet leak gp false) adv).run' s)
      ((simulateQ (postChallengeImpl kem hDet leak gp) adv).run' (noPendingPostState s))
      (EqRel α) := by
  refine relTriple_simulateQ_run'_of_query_map_eq
    (securityImpl kem hDet leak gp false)
    (postChallengeImpl kem hDet leak gp)
    noPendingPostState ?_ adv s
  intro t s'
  change
    (Prod.map id noPendingPostState <$> (securityImpl kem hDet leak gp false t).run s') =
      (postChallengeImpl kem hDet leak gp t).run
        ({ game := s', pending := PendingChallengeRecv.none } :
          PostChallengeState K PK SK C)
  rw [postChallengeImpl_none_run_eq]
  rfl

lemma postRel_aToB_recvB_noPending [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvB = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)).run
        (postAToBHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)).run
        (postAToBReductionState base msg fakeKey))
      (fun p q => p.1 = q.1 ∧ q.2 = noPendingPostState p.2) := by
  rw [show postAToBHonestState base sk msg realKey =
      ({ base with stB := State.recvReady sk, rhoA := some msg, keyA := some realKey } :
        SecurityState K PK SK C) by rfl]
  rw [securityImpl_recvB_of_decaps_eq (kem := kem) (hDet := hDet) (leak := leak)
    (gp := gp) (g := base) (sk := sk) (msg := msg) (key := realKey) hrecv hdec]
  have hrecv' : CKAScheme.validStep
      ({ base with rhoA := some msg, keyA := some fakeKey } :
        SecurityState K PK SK C).lastAction .recvB = true := by
    simpa using hrecv
  rw [show postAToBReductionState base msg fakeKey =
      ({ game := ({ base with rhoA := some msg, keyA := some fakeKey } :
          SecurityState K PK SK C),
         pending := PendingChallengeRecv.aToB fakeKey msg.2 msg } :
        PostChallengeState K PK SK C) by rfl]
  rw [postChallengeImpl_recvB_aToB_of_valid (kem := kem) (hDet := hDet) (leak := leak)
    (gp := gp)
    (g := ({ base with rhoA := some msg, keyA := some fakeKey } :
      SecurityState K PK SK C))
    (key := fakeKey) (nextPk := msg.2) (msg := msg) hrecv']
  apply relTriple_pure_pure
  simp [noPendingPostState]

lemma postRel_aToB_recvB [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvB = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)).run
        (postAToBHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)).run
        (postAToBReductionState base msg fakeKey))
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  refine relTriple_post_mono
    (postRel_aToB_recvB_noPending kem hDet leak gp base sk msg realKey fakeKey hdec hrecv) ?_
  intro p q hp
  exact ⟨hp.1, by rw [hp.2]; exact PostRel.none p.2⟩

lemma postRel_aToB_recvB_cont_run'_relTriple [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvB = true)
    {α : Type}
    (cont : Unit → OracleComp (SecuritySpec leak) α) :
    RelTriple
      (((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)).run
        (postAToBHonestState base sk msg realKey)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      (((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (SecuritySpec leak).Domain)).run
        (postAToBReductionState base msg fakeKey)) >>= fun q =>
          (simulateQ (postChallengeImpl kem hDet leak gp) (cont q.1)).run' q.2)
      (EqRel α) := by
  refine relTriple_bind
    (postRel_aToB_recvB_noPending kem hDet leak gp base sk msg realKey fakeKey hdec hrecv) ?_
  intro p q hp
  rcases hp with ⟨hout, hstate⟩
  rw [← hout, hstate]
  exact securityImpl_postChallenge_none_run'_relTriple kem hDet leak gp (cont p.1) p.2

lemma postRel_bToA_recvA_noPending [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvA = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)).run
        (postBToAHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)).run
        (postBToAReductionState base msg fakeKey))
      (fun p q => p.1 = q.1 ∧ q.2 = noPendingPostState p.2) := by
  rw [show postBToAHonestState base sk msg realKey =
      ({ base with stA := State.recvReady sk, rhoB := some msg, keyB := some realKey } :
        SecurityState K PK SK C) by rfl]
  rw [securityImpl_recvA_of_decaps_eq (kem := kem) (hDet := hDet) (leak := leak)
    (gp := gp) (g := base) (sk := sk) (msg := msg) (key := realKey) hrecv hdec]
  have hrecv' : CKAScheme.validStep
      ({ base with rhoB := some msg, keyB := some fakeKey } :
        SecurityState K PK SK C).lastAction .recvA = true := by
    simpa using hrecv
  rw [show postBToAReductionState base msg fakeKey =
      ({ game := ({ base with rhoB := some msg, keyB := some fakeKey } :
          SecurityState K PK SK C),
         pending := PendingChallengeRecv.bToA fakeKey msg.2 msg } :
        PostChallengeState K PK SK C) by rfl]
  rw [postChallengeImpl_recvA_bToA_of_valid (kem := kem) (hDet := hDet) (leak := leak)
    (gp := gp)
    (g := ({ base with rhoB := some msg, keyB := some fakeKey } :
      SecurityState K PK SK C))
    (key := fakeKey) (nextPk := msg.2) (msg := msg) hrecv']
  apply relTriple_pure_pure
  simp [noPendingPostState]

lemma postRel_bToA_recvA [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvA = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)).run
        (postBToAHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)).run
        (postBToAReductionState base msg fakeKey))
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  refine relTriple_post_mono
    (postRel_bToA_recvA_noPending kem hDet leak gp base sk msg realKey fakeKey hdec hrecv) ?_
  intro p q hp
  exact ⟨hp.1, by rw [hp.2]; exact PostRel.none p.2⟩

lemma postRel_bToA_recvA_cont_run'_relTriple [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvA = true)
    {α : Type}
    (cont : Unit → OracleComp (SecuritySpec leak) α) :
    RelTriple
      (((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)).run
        (postBToAHonestState base sk msg realKey)) >>= fun p =>
          (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2)
      (((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (SecuritySpec leak).Domain)).run
        (postBToAReductionState base msg fakeKey)) >>= fun q =>
          (simulateQ (postChallengeImpl kem hDet leak gp) (cont q.1)).run' q.2)
      (EqRel α) := by
  refine relTriple_bind
    (postRel_bToA_recvA_noPending kem hDet leak gp base sk msg realKey fakeKey hdec hrecv) ?_
  intro p q hp
  rcases hp with ⟨hout, hstate⟩
  rw [← hout, hstate]
  exact securityImpl_postChallenge_none_run'_relTriple kem hDet leak gp (cont p.1) p.2

end kemCKA
