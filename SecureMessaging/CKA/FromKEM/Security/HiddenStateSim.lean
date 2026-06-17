/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.Branches
import VCVio.ProgramLogic.Relational.SimulateQ
import ToVCVio.ProgramLogic.Relational.Basic

/-!
# CKA from KEM — Hidden-State Simulation

After the challenge, the honest game and the reduction differ only in hidden
state: the honest receiver still stores the decapsulation secret key and the
real challenge key, while the reduction stores neither and answers the
matching receive from its pending record. This file shows that difference is
unobservable.

`PostRel` relates an honest game state to a reduction post-challenge state in
the A-to-B and B-to-A challenge windows and once the pending receive has
happened. `postRel_step` shows every oracle preserves the relation with equal
outputs — receiver corruption is blocked by admissibility — and
`postRel_run'_relTriple` lifts this to whole adversary runs.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-- Honest-side state in the A-to-B challenge window: the receiver B still
holds the decapsulation secret `sk`, and the challenge message and real key
sit in the A slots. -/
def postAToBHonestState
    (base : SecurityState K PK SK C) (sk : SK) (msg : Message C PK) (key : K) :
    SecurityState K PK SK C :=
  { base with stB := State.recvReady sk, rhoA := some msg, keyA := some key }

/-- Reduction-side state in the A-to-B challenge window: no receiver secret,
the (possibly random) challenge key in the A slots, and the pending receive
override that will answer B's receive. -/
def postAToBReductionState
    (base : SecurityState K PK SK C) (msg : Message C PK) (key : K) :
    PostChallengeState K PK SK C :=
  { game := { base with rhoA := some msg, keyA := some key },
    pending := PendingChallengeRecv.aToB key msg.2 msg }

/-- Honest-side state in the B-to-A challenge window, the mirror of
`postAToBHonestState`. -/
def postBToAHonestState
    (base : SecurityState K PK SK C) (sk : SK) (msg : Message C PK) (key : K) :
    SecurityState K PK SK C :=
  { base with stA := State.recvReady sk, rhoB := some msg, keyB := some key }

/-- Reduction-side state in the B-to-A challenge window, the mirror of
`postAToBReductionState`. -/
def postBToAReductionState
    (base : SecurityState K PK SK C) (msg : Message C PK) (key : K) :
    PostChallengeState K PK SK C :=
  { game := { base with rhoB := some msg, keyB := some key },
    pending := PendingChallengeRecv.bToA key msg.2 msg }

private def noPendingPostState (s : SecurityState K PK SK C) : PostChallengeState K PK SK C :=
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

private lemma postRel_aToB_after_challA
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

/-- Entering the A-to-B window: right after a due A-challenge, the honest and
reduction states are `PostRel`-related. The support memberships supply the
deterministic decapsulation fact through perfect correctness. -/
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

private lemma postRel_bToA_after_challB
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

/-- Entering the B-to-A window, the mirror of
`postRel_aToB_after_challA_of_mem_support`. -/
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
  simpa only [id_map] using
    relTriple_map_map_of_pointwise mx id
      (fun a => (a.1, ({ game := a.2, pending := PendingChallengeRecv.none } :
        PostChallengeState K PK SK C)))
      (R := fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2)
      (fun a => ⟨rfl, PostRel.none a.2⟩)

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
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) :=
  relTriple_map_map_of_pointwise mx (fun a => (a, honest)) (fun a => (a, post))
    (R := fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2)
    (fun _ => ⟨rfl, hrel⟩)

private lemma postChallengeImpl_none_run_eq [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (securitySpec leak).Domain)
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
    simp [postChallengeImpl, liftSecurityImplToPost, stateT_run]

/-- A post-challenge state with no pending override exactly follows the honest
security implementation, preserving the projected relation. -/
private lemma postRel_none_step [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (securitySpec leak).Domain)
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

private lemma postRel_aToB_recvB_noPending [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvB = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        (postAToBHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
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

private lemma postRel_aToB_recvB [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvB = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        (postAToBHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run
        (postAToBReductionState base msg fakeKey))
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  refine relTriple_post_mono
    (postRel_aToB_recvB_noPending kem hDet leak gp base sk msg realKey fakeKey hdec hrecv) ?_
  intro p q hp
  exact ⟨hp.1, by rw [hp.2]; exact PostRel.none p.2⟩

private lemma postRel_bToA_recvA_noPending [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvA = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        (postBToAHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
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

private lemma postRel_bToA_recvA [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (base : SecurityState K PK SK C)
    (sk : SK) (msg : Message C PK) (realKey fakeKey : K)
    (hdec : hDet.decapsDet sk msg.1 = some realKey)
    (hrecv : CKAScheme.validStep base.lastAction .recvA = true) :
    RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        (postBToAHonestState base sk msg realKey))
      ((postChallengeImpl kem hDet leak gp
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run
        (postBToAReductionState base msg fakeKey))
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  refine relTriple_post_mono
    (postRel_bToA_recvA_noPending kem hDet leak gp base sk msg realKey fakeKey hdec hrecv) ?_
  intro p q hp
  exact ⟨hp.1, by rw [hp.2]; exact PostRel.none p.2⟩

private lemma lastAction_of_valid_recvB
    {last : Option CKAScheme.CKAAction}
    (h : CKAScheme.validStep last .recvB = true) :
    last = some .sendA ∨ last = some .challA := by
  cases hlast : last with
  | none =>
      simp [CKAScheme.validStep, hlast] at h
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at h
      · exact Or.inl rfl
      · exact Or.inr rfl

private lemma lastAction_of_valid_recvA
    {last : Option CKAScheme.CKAAction}
    (h : CKAScheme.validStep last .recvA = true) :
    last = some .sendB ∨ last = some .challB := by
  cases hlast : last with
  | none =>
      simp [CKAScheme.validStep, hlast] at h
  | some act =>
      cases act <;> simp [CKAScheme.validStep, hlast] at h
      · exact Or.inl rfl
      · exact Or.inr rfl

private lemma securityImpl_corruptA_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (s : SecurityState K PK SK C) :
    ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run s) =
      pure (if CKAScheme.allowCorr gp s .A then some s.stA else none, s) := by
  change (CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run s = _
  cases hcorr : CKAScheme.allowCorr gp s .A <;>
    simp [CKAScheme.oracleCorruptA, stateT_run, hcorr]

private lemma securityImpl_corruptB_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (s : SecurityState K PK SK C) :
    ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run s) =
      pure (if CKAScheme.allowCorr gp s .B then some s.stB else none, s) := by
  change (CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run s = _
  cases hcorr : CKAScheme.allowCorr gp s .B <;>
    simp [CKAScheme.oracleCorruptB, stateT_run, hcorr]

private lemma postChallengeImpl_corruptA_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (ps : PostChallengeState K PK SK C) :
    ((postChallengeImpl kem hDet leak gp
      (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run ps) =
      pure
        (if CKAScheme.allowCorr gp ps.game .A then some ps.game.stA else none, ps) := by
  have hgame := securityImpl_corruptA_run kem hDet leak gp ps.game
  simp only [postChallengeImpl, liftSecurityImplToPost, stateT_run]
  rw [hgame]
  rfl

private lemma postChallengeImpl_corruptB_run [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (ps : PostChallengeState K PK SK C) :
    ((postChallengeImpl kem hDet leak gp
      (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run ps) =
      pure
        (if CKAScheme.allowCorr gp ps.game .B then some ps.game.stB else none, ps) := by
  have hgame := securityImpl_corruptB_run kem hDet leak gp ps.game
  simp only [postChallengeImpl, liftSecurityImplToPost, stateT_run]
  rw [hgame]
  rfl

/-- One-query preservation of the hidden-state relation: under `PostRel`, the
honest implementation and the post-challenge implementation answer every
oracle with equal outputs and `PostRel`-related successor states. Receiver
corruption, the one query that could see the hidden difference, is blocked by
the recorded `allowCorr = false`. -/
lemma postRel_step [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (t : (securitySpec leak).Domain)
    {honest : SecurityState K PK SK C}
    {post : PostChallengeState K PK SK C}
    (hrel : PostRel kem hDet gp honest post) :
    RelTriple
      ((securityImpl kem hDet leak gp false t).run honest)
      ((postChallengeImpl kem hDet leak gp t).run post)
      (fun p q => p.1 = q.1 ∧ PostRel kem hDet gp p.2 q.2) := by
  induction hrel with
  | none =>
      exact postRel_none_step kem hDet leak gp t _
  | aToB h =>
      rcases h with ⟨base, sk, msg, realKey, fakeKey, hhonest, hpost, hdec, hrecv, hblock⟩
      subst hhonest
      subst hpost
      have hcurrent : PostRel kem hDet gp
          (postAToBHonestState base sk msg realKey)
          (postAToBReductionState base msg fakeKey) :=
        PostRel.aToB
          (PostAToBRel.intro base sk msg realKey fakeKey rfl rfl hdec hrecv hblock)
      have hlastRecv := lastAction_of_valid_recvB hrecv
      have hblockHonest :
          CKAScheme.allowCorr gp (postAToBHonestState base sk msg realKey) .B = false := by
        simpa [postAToBHonestState, postAToBReductionState, CKAScheme.allowCorr,
          CKAScheme.allowCorrPCS, CKAScheme.allowCorrFS] using hblock
      rcases t with
        (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
          uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
      · simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
          CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleUnif, QueryImpl.add,
          QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
          postAToBHonestState, postAToBReductionState, stateT_run] using
          postRel_attach kem hDet gp
            ((securityImpl kem hDet leak gp false
              (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run'
              (postAToBHonestState base sk msg realKey)) hcurrent
      · cases uSendA
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleSendA, QueryImpl.add,
            QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
            postAToBHonestState, postAToBReductionState, send,
            stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run'
                (postAToBHonestState base sk msg realKey)) hcurrent
      · cases uRecvA
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleRecvA, QueryImpl.add,
            QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
            postAToBHonestState, postAToBReductionState, recv,
            stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run'
                (postAToBHonestState base sk msg realKey)) hcurrent
      · cases uSendB
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleSendB, QueryImpl.add,
            QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
            postAToBHonestState, postAToBReductionState, send,
            stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run'
                (postAToBHonestState base sk msg realKey)) hcurrent
      · cases uRecvB
        exact postRel_aToB_recvB kem hDet leak gp base sk msg realKey fakeKey hdec hrecv
      · cases uChallA
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleChallA, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.id',
            postChallengeImpl, liftSecurityImplToPost, postAToBHonestState,
            postAToBReductionState, send, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run'
                (postAToBHonestState base sk msg realKey)) hcurrent
      · cases uChallB
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleChallB, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.id',
            postChallengeImpl, liftSecurityImplToPost, postAToBHonestState,
            postAToBReductionState, send, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run'
                (postAToBHonestState base sk msg realKey)) hcurrent
      · cases uCorrA
        rw [securityImpl_corruptA_run kem hDet leak gp
          (postAToBHonestState base sk msg realKey)]
        rw [postChallengeImpl_corruptA_run kem hDet leak gp
          (postAToBReductionState base msg fakeKey)]
        have hout :
            (if CKAScheme.allowCorr gp (postAToBHonestState base sk msg realKey) .A then
                some (postAToBHonestState base sk msg realKey).stA else none) =
              (if CKAScheme.allowCorr gp (postAToBReductionState base msg fakeKey).game .A then
                some (postAToBReductionState base msg fakeKey).game.stA else none) := by
          simp [postAToBHonestState, postAToBReductionState, CKAScheme.allowCorr,
            CKAScheme.allowCorrPCS, CKAScheme.allowCorrFS]
        exact relTriple_pure_pure ⟨hout, hcurrent⟩
      · cases uCorrB
        rw [securityImpl_corruptB_run kem hDet leak gp
          (postAToBHonestState base sk msg realKey)]
        rw [postChallengeImpl_corruptB_run kem hDet leak gp
          (postAToBReductionState base msg fakeKey)]
        have hleftOut :
            (if CKAScheme.allowCorr gp (postAToBHonestState base sk msg realKey) .B then
                some (postAToBHonestState base sk msg realKey).stB else none) = none := by
          simp [hblockHonest]
        have hrightOut :
            (if CKAScheme.allowCorr gp (postAToBReductionState base msg fakeKey).game .B then
                some (postAToBReductionState base msg fakeKey).game.stB else none) = none := by
          simp [hblock]
        rw [hleftOut, hrightOut]
        exact relTriple_pure_pure ⟨rfl, hcurrent⟩
      · cases uRLeakA
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleSendA_rleak, QueryImpl.add, QueryImpl.liftTarget,
            QueryImpl.id', postChallengeImpl, liftSecurityImplToPost, postAToBHonestState,
            postAToBReductionState, send_rleak, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run'
                (postAToBHonestState base sk msg realKey)) hcurrent
      · cases uRLeakB
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleSendB_rleak, QueryImpl.add, QueryImpl.liftTarget,
            QueryImpl.id', postChallengeImpl, liftSecurityImplToPost, postAToBHonestState,
            postAToBReductionState, send_rleak, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run'
                (postAToBHonestState base sk msg realKey)) hcurrent
  | bToA h =>
      rcases h with ⟨base, sk, msg, realKey, fakeKey, hhonest, hpost, hdec, hrecv, hblock⟩
      subst hhonest
      subst hpost
      have hcurrent : PostRel kem hDet gp
          (postBToAHonestState base sk msg realKey)
          (postBToAReductionState base msg fakeKey) :=
        PostRel.bToA
          (PostBToARel.intro base sk msg realKey fakeKey rfl rfl hdec hrecv hblock)
      have hlastRecv := lastAction_of_valid_recvA hrecv
      have hblockHonest :
          CKAScheme.allowCorr gp (postBToAHonestState base sk msg realKey) .A = false := by
        simpa [postBToAHonestState, postBToAReductionState, CKAScheme.allowCorr,
          CKAScheme.allowCorrPCS, CKAScheme.allowCorrFS] using hblock
      rcases t with
        (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
          uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
      · simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
          CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleUnif, QueryImpl.add,
          QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
          postBToAHonestState, postBToAReductionState, stateT_run] using
          postRel_attach kem hDet gp
            ((securityImpl kem hDet leak gp false
              (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run'
              (postBToAHonestState base sk msg realKey)) hcurrent
      · cases uSendA
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleSendA, QueryImpl.add,
            QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
            postBToAHonestState, postBToAReductionState, send,
            stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run'
                (postBToAHonestState base sk msg realKey)) hcurrent
      · cases uRecvA
        exact postRel_bToA_recvA kem hDet leak gp base sk msg realKey fakeKey hdec hrecv
      · cases uSendB
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleSendB, QueryImpl.add,
            QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
            postBToAHonestState, postBToAReductionState, send,
            stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run'
                (postBToAHonestState base sk msg realKey)) hcurrent
      · cases uRecvB
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.ckaCorrectnessImpl, CKAScheme.oracleRecvB, QueryImpl.add,
            QueryImpl.liftTarget, QueryImpl.id', postChallengeImpl, liftSecurityImplToPost,
            postBToAHonestState, postBToAReductionState, recv,
            stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run'
                (postBToAHonestState base sk msg realKey)) hcurrent
      · cases uChallA
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleChallA, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.id',
            postChallengeImpl, liftSecurityImplToPost, postBToAHonestState,
            postBToAReductionState, send, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run'
                (postBToAHonestState base sk msg realKey)) hcurrent
      · cases uChallB
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleChallB, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.id',
            postChallengeImpl, liftSecurityImplToPost, postBToAHonestState,
            postBToAReductionState, send, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run'
                (postBToAHonestState base sk msg realKey)) hcurrent
      · cases uCorrA
        rw [securityImpl_corruptA_run kem hDet leak gp
          (postBToAHonestState base sk msg realKey)]
        rw [postChallengeImpl_corruptA_run kem hDet leak gp
          (postBToAReductionState base msg fakeKey)]
        have hleftOut :
            (if CKAScheme.allowCorr gp (postBToAHonestState base sk msg realKey) .A then
                some (postBToAHonestState base sk msg realKey).stA else none) = none := by
          simp [hblockHonest]
        have hrightOut :
            (if CKAScheme.allowCorr gp (postBToAReductionState base msg fakeKey).game .A then
                some (postBToAReductionState base msg fakeKey).game.stA else none) = none := by
          simp [hblock]
        rw [hleftOut, hrightOut]
        exact relTriple_pure_pure ⟨rfl, hcurrent⟩
      · cases uCorrB
        rw [securityImpl_corruptB_run kem hDet leak gp
          (postBToAHonestState base sk msg realKey)]
        rw [postChallengeImpl_corruptB_run kem hDet leak gp
          (postBToAReductionState base msg fakeKey)]
        have hout :
            (if CKAScheme.allowCorr gp (postBToAHonestState base sk msg realKey) .B then
                some (postBToAHonestState base sk msg realKey).stB else none) =
              (if CKAScheme.allowCorr gp (postBToAReductionState base msg fakeKey).game .B then
                some (postBToAReductionState base msg fakeKey).game.stB else none) := by
          simp [postBToAHonestState, postBToAReductionState, CKAScheme.allowCorr,
            CKAScheme.allowCorrPCS, CKAScheme.allowCorrFS]
        exact relTriple_pure_pure ⟨hout, hcurrent⟩
      · cases uRLeakA
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleSendA_rleak, QueryImpl.add, QueryImpl.liftTarget,
            QueryImpl.id', postChallengeImpl, liftSecurityImplToPost, postBToAHonestState,
            postBToAReductionState, send_rleak, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run'
                (postBToAHonestState base sk msg realKey)) hcurrent
      · cases uRLeakB
        rcases hlastRecv with hlast | hlast <;>
          simpa [securityImpl, scheme, CKAScheme.ckaSecurityImpl,
            CKAScheme.oracleSendB_rleak, QueryImpl.add, QueryImpl.liftTarget,
            QueryImpl.id', postChallengeImpl, liftSecurityImplToPost, postBToAHonestState,
            postBToAReductionState, send_rleak, stateT_run, hlast, CKAScheme.validStep] using
            postRel_attach kem hDet gp
              ((securityImpl kem hDet leak gp false
                (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run'
                (postBToAHonestState base sk msg realKey)) hcurrent

/-- Whole-run consequence of `postRel_step`: from `PostRel`-related states,
simulating any adversary under the honest and post-challenge implementations
yields outputs related by equality. The probability layer turns this
`RelTriple` into equal output distributions. -/
lemma postRel_run'_relTriple [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    {α : Type}
    (adv : OracleComp (securitySpec leak) α)
    {honest : SecurityState K PK SK C}
    {post : PostChallengeState K PK SK C}
    (hrel : PostRel kem hDet gp honest post) :
    RelTriple
      ((simulateQ (securityImpl kem hDet leak gp false) adv).run' honest)
      ((simulateQ (postChallengeImpl kem hDet leak gp) adv).run' post)
      (EqRel α) := by
  exact relTriple_simulateQ_run'
    (securityImpl kem hDet leak gp false)
    (postChallengeImpl kem hDet leak gp)
    (PostRel kem hDet gp)
    adv
    (by
      intro t s₁ s₂ hs
      exact postRel_step kem hDet leak gp t hs)
    honest post hrel

end kemCKA
