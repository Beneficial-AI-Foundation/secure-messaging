/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromLWE.Construction

/-!
# CKA from the Frodo/LWE Construction — Correctness

This file proves correctness of the Frodo/LWE CKA construction in the abstract
CKA correctness game: `Pr[= true | correctnessExp (scheme p) adv] = 1` for every
correctness adversary.

The argument follows the proven generic KEM correctness stack
(`SecureMessaging.CKA.FromKEM.Correctness`). A reachable invariant pins down, for
each point in the A-first send/receive cycle, the states of both parties, any
pending message, the stored sender key, and the relevant match relation. Each
correctness oracle preserves the invariant, so the final `correct` flag is `true`.
Key agreement at each delivery is supplied by the `Frodo.CKAParams` laws
`sendA_correct` and `sendB_correct`, and the match relation needed for the next
send by `sendA_match_next` and `sendB_match_next`.
-/

open OracleSpec OracleComp ENNReal

namespace lweCKA

open CKAScheme.ckaCorrectnessSpec

/-- Shape of a reachable game state, indexed by the last action.

At each point of the A-first cycle the invariant records both parties' states,
the pending message and stored sender key, and the match relation that the next
delivery or send relies on. After A sends, the support membership of A's send
together with `MatchAB` yields B's key agreement; symmetrically after B sends.
Challenge actions are unreachable in the correctness game, so those cases are
`False`. -/
private def stateShapeInv (p : Frodo.CKAParams ProbComp)
    (s : CKAScheme.GameState (State p) p.Key (Message p)) : Prop :=
  match s.lastAction with
  | none | some .recvA =>
      ∃ common pubAB secAB, p.MatchAB common pubAB secAB ∧
        s.stA = .sendAReady common pubAB ∧ s.stB = .recvBReady common secAB ∧
        s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendA =>
      ∃ common pubAB secAB key pubBA hint secBA randA,
        p.MatchAB common pubAB secAB ∧
        (key, pubBA, hint, secBA, randA) ∈ support (p.sendA common pubAB) ∧
        s.stA = .recvAReady common secBA ∧ s.stB = .recvBReady common secAB ∧
        s.rhoA = some (.fromA pubBA hint) ∧ s.rhoB = none ∧
        s.keyA = some key ∧ s.keyB = none
  | some .recvB =>
      ∃ common pubBA secBA, p.MatchBA common pubBA secBA ∧
        s.stA = .recvAReady common secBA ∧ s.stB = .sendBReady common pubBA ∧
        s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendB =>
      ∃ common pubBA secBA key pubAB hint secAB randB,
        p.MatchBA common pubBA secBA ∧
        (key, pubAB, hint, secAB, randB) ∈ support (p.sendB common pubBA) ∧
        s.stA = .recvAReady common secBA ∧ s.stB = .recvBReady common secAB ∧
        s.rhoA = none ∧ s.rhoB = some (.fromB pubAB hint) ∧
        s.keyA = none ∧ s.keyB = some key
  | some .challA | some .challB => False

/-- Reachable game state: the `correct` flag is still `true` and the state has the
expected shape for its last action. -/
private def reachableInv (p : Frodo.CKAParams ProbComp)
    (s : CKAScheme.GameState (State p) p.Key (Message p)) : Prop :=
  s.correct = true ∧ stateShapeInv p s

private lemma reachableInv_init (p : Frodo.CKAParams ProbComp)
    {common : p.Common} {pubAB : p.PubAB} {secAB : p.SecAB}
    (h : p.MatchAB common pubAB secAB) :
    reachableInv p
      (CKAScheme.initGameState (State.sendAReady common pubAB) (State.recvBReady common secAB)) :=
  ⟨rfl, common, pubAB, secAB, h, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma reachableInv_after_sendA (p : Frodo.CKAParams ProbComp)
    {common : p.Common} {pubAB : p.PubAB} {secAB : p.SecAB}
    {key : p.Key} {pubBA : p.PubBA} {hint : p.Hint} {secBA : p.SecBA} {randA : p.RandA}
    {epA epB : ℕ}
    (hM : p.MatchAB common pubAB secAB)
    (hsend : (key, pubBA, hint, secBA, randA) ∈ support (p.sendA common pubAB)) :
    reachableInv p
      { stA := .recvAReady common secBA, stB := .recvBReady common secAB,
        rhoA := some (.fromA pubBA hint), rhoB := none,
        keyA := some key, keyB := none,
        correct := true, lastAction := some .sendA,
        tA := epA + 1, tB := epB } := by
  refine ⟨rfl, common, pubAB, secAB, key, pubBA, hint, secBA, randA, hM, hsend,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private lemma reachableInv_after_recvB (p : Frodo.CKAParams ProbComp)
    {common : p.Common} {pubBA : p.PubBA} {secBA : p.SecBA}
    {epA epB : ℕ}
    (hM : p.MatchBA common pubBA secBA) :
    reachableInv p
      { stA := .recvAReady common secBA, stB := .sendBReady common pubBA,
        rhoA := none, rhoB := none, keyA := none, keyB := none,
        correct := true, lastAction := some .recvB,
        tA := epA, tB := epB + 1 } := by
  refine ⟨rfl, common, pubBA, secBA, hM, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private lemma reachableInv_after_sendB (p : Frodo.CKAParams ProbComp)
    {common : p.Common} {pubBA : p.PubBA} {secBA : p.SecBA}
    {key : p.Key} {pubAB : p.PubAB} {hint : p.Hint} {secAB : p.SecAB} {randB : p.RandB}
    {epA epB : ℕ}
    (hM : p.MatchBA common pubBA secBA)
    (hsend : (key, pubAB, hint, secAB, randB) ∈ support (p.sendB common pubBA)) :
    reachableInv p
      { stA := .recvAReady common secBA, stB := .recvBReady common secAB,
        rhoA := none, rhoB := some (.fromB pubAB hint),
        keyA := none, keyB := some key,
        correct := true, lastAction := some .sendB,
        tA := epA, tB := epB + 1 } := by
  refine ⟨rfl, common, pubBA, secBA, key, pubAB, hint, secAB, randB, hM, hsend,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private lemma reachableInv_after_recvA (p : Frodo.CKAParams ProbComp)
    {common : p.Common} {pubAB : p.PubAB} {secAB : p.SecAB}
    {epA epB : ℕ}
    (hM : p.MatchAB common pubAB secAB) :
    reachableInv p
      { stA := .sendAReady common pubAB, stB := .recvBReady common secAB,
        rhoA := none, rhoB := none, keyA := none, keyB := none,
        correct := true, lastAction := some .recvA,
        tA := epA + 1, tB := epB } := by
  refine ⟨rfl, common, pubAB, secAB, hM, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private lemma oracleUnif_preserves_reachableInv (p : Frodo.CKAParams ProbComp) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleUnif (State p) p.Key (Message p))
      (reachableInv p) := by
  intro t σ hσ z hz
  have hz' : ∃ y : unifSpec.Range t, (y, σ) = z := by
    simpa [CKAScheme.oracleUnif] using hz
  rcases hz' with ⟨_, rfl⟩
  simpa using hσ

private lemma oracleSendA_preserves_reachableInv (p : Frodo.CKAParams ProbComp) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleSendA (scheme p))
      (reachableInv p) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩
  cases hGuard : CKAScheme.validStep last .sendA
  case false =>
    have : z = (none, ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩) := by
      simpa [CKAScheme.oracleSendA, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this
    exact hσ
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [CKAScheme.validStep] at hGuard
    all_goals (
      rcases (by simpa [reachableInv, stateShapeInv] using hσ) with
        ⟨hcorrect, common, pubAB, secAB, hM, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      rw [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
      have hz' : ∃ key pubBA hint secBA randA,
          (key, pubBA, hint, secBA, randA) ∈ support (p.sendA common pubAB) ∧
          (some (Message.fromA pubBA hint, key),
            { stA := State.recvAReady common secBA, stB := State.recvBReady common secAB,
              rhoA := some (Message.fromA pubBA hint), rhoB := none,
              keyA := some key, keyB := none,
              correct := true, lastAction := some .sendA,
              tA := epA + 1, tB := epB }) = z := by
        simpa [CKAScheme.validStep, lweCKA.scheme, lweCKA.sendA] using hz
      obtain ⟨key, pubBA, hint, secBA, randA, hsend, rfl⟩ := hz'
      exact reachableInv_after_sendA p hM hsend)

private lemma oracleSendB_preserves_reachableInv (p : Frodo.CKAParams ProbComp) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleSendB (scheme p))
      (reachableInv p) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩
  cases hGuard : CKAScheme.validStep last .sendB
  case false =>
    have : z = (none, ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩) := by
      simpa [CKAScheme.oracleSendB, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this
    exact hσ
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [CKAScheme.validStep] at hGuard
    rcases (by simpa [reachableInv, stateShapeInv] using hσ) with
      ⟨hcorrect, common, pubBA, secBA, hM, rfl, rfl, rfl, rfl, rfl, rfl⟩
    subst correct
    rw [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    have hz' : ∃ key pubAB hint secAB randB,
        (key, pubAB, hint, secAB, randB) ∈ support (p.sendB common pubBA) ∧
        (some (Message.fromB pubAB hint, key),
          { stA := State.recvAReady common secBA, stB := State.recvBReady common secAB,
            rhoA := none, rhoB := some (Message.fromB pubAB hint),
            keyA := none, keyB := some key,
            correct := true, lastAction := some .sendB,
            tA := epA, tB := epB + 1 }) = z := by
      simpa [CKAScheme.validStep, lweCKA.scheme, lweCKA.sendB] using hz
    obtain ⟨key, pubAB, hint, secAB, randB, hsend, rfl⟩ := hz'
    exact reachableInv_after_sendB p hM hsend

private lemma oracleRecvB_preserves_reachableInv
    (p : Frodo.CKAParams ProbComp) [DecidableEq p.Key] :
    QueryImpl.PreservesInv
      (CKAScheme.oracleRecvB (scheme p))
      (reachableInv p) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩
  cases hGuard : CKAScheme.validStep last .recvB
  case false =>
    have : z = ((), ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩) := by
      simpa [CKAScheme.oracleRecvB, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this
    exact hσ
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hGuard
    cases action <;> simp [CKAScheme.validStep] at hGuard
    · simp only [reachableInv, stateShapeInv] at hσ
      obtain ⟨hcorrect, common, pubAB, secAB, key, pubBA, hint, secBA, randA,
          hM, hsend, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hσ
      subst correct
      have hrecv : p.recvB common secAB pubBA hint = some key :=
        p.sendA_correct common pubAB secAB hM key pubBA hint secBA randA hsend
      have : z = ((), ⟨State.recvAReady common secBA, State.sendBReady common pubBA,
          none, none, none, none, true, some .recvB, epA, epB + 1⟩) := by
        simpa [CKAScheme.oracleRecvB, CKAScheme.validStep, lweCKA.scheme, lweCKA.recvB, hrecv,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst this
      exact reachableInv_after_recvB p
        (p.sendA_match_next common pubAB key pubBA hint secBA randA hsend)
    · exact False.elim (by simp only [reachableInv, stateShapeInv, and_false] at hσ)

private lemma oracleRecvA_preserves_reachableInv
    (p : Frodo.CKAParams ProbComp) [DecidableEq p.Key] :
    QueryImpl.PreservesInv
      (CKAScheme.oracleRecvA (scheme p))
      (reachableInv p) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩
  cases hGuard : CKAScheme.validStep last .recvA
  case false =>
    have : z = ((), ⟨sA, sB, ρA, ρB, keyA, keyB, correct, last, epA, epB⟩) := by
      simpa [CKAScheme.oracleRecvA, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this
    exact hσ
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hGuard
    cases action <;> simp [CKAScheme.validStep] at hGuard
    · simp only [reachableInv, stateShapeInv] at hσ
      obtain ⟨hcorrect, common, pubBA, secBA, key, pubAB, hint, secAB, randB,
          hM, hsend, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hσ
      subst correct
      have hrecv : p.recvA common secBA pubAB hint = some key :=
        p.sendB_correct common pubBA secBA hM key pubAB hint secAB randB hsend
      have : z = ((), ⟨State.sendAReady common pubAB, State.recvBReady common secAB,
          none, none, none, none, true, some .recvA, epA + 1, epB⟩) := by
        simpa [CKAScheme.oracleRecvA, CKAScheme.validStep, lweCKA.scheme, lweCKA.recvA, hrecv,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst this
      exact reachableInv_after_recvA p
        (p.sendB_match_next common pubBA key pubAB hint secAB randB hsend)
    · exact False.elim (by simp only [reachableInv, stateShapeInv, and_false] at hσ)

private lemma correctnessImpl_preserves (p : Frodo.CKAParams ProbComp) [DecidableEq p.Key] :
    QueryImpl.PreservesInv
      (CKAScheme.ckaCorrectnessImpl (scheme p))
      (reachableInv p) := by
  intro t σ hσ z hz
  match t with
  | OUnif n =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleUnif_preserves_reachableInv p n σ hσ z hz
  | OSendA =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleSendA_preserves_reachableInv p () σ hσ z hz
  | ORecvA =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleRecvA_preserves_reachableInv p () σ hσ z hz
  | OSendB =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleSendB_preserves_reachableInv p () σ hσ z hz
  | ORecvB =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleRecvB_preserves_reachableInv p () σ hσ z hz

/-- One-round agreement for the Frodo/LWE construction.

Sample the setup, run A's send, and run B's receive on the transmitted public key
and hint. The receiver recovers exactly the sender's epoch key; a receive failure
would count as a correctness failure. Agreement is the `sendA_correct` law applied
to the `MatchAB` relation produced by `init_match`. -/
theorem send_recv_agree (p : Frodo.CKAParams ProbComp) [DecidableEq p.Key] :
    Pr[= true |
      do
        let (common, pubAB, secAB) ← p.init
        let (keyS, pubBA, hint, _secBA, _randA) ← p.sendA common pubAB
        match p.recvB common secAB pubBA hint with
        | none => return false
        | some keyR => return decide (keyR = keyS)] = 1 := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨common, pubAB, secAB⟩, hinit, hb⟩ := hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨keyS, pubBA, hint, secBA, randA⟩, hsend, hb⟩ := hb
  have hM := p.init_match common pubAB secAB hinit
  have hrecv := p.sendA_correct common pubAB secAB hM keyS pubBA hint secBA randA hsend
  simpa [hrecv, mem_support_pure_iff] using hb

/-- Correctness of the Frodo/LWE CKA construction in the abstract CKA correctness
game.

For every correctness adversary using the honest send/receive oracles, the game
returns `true` with probability one. Agreement at each delivered epoch follows
from the `Frodo.CKAParams` reconciliation laws; no concrete Frodo matrix algebra
is needed. -/
-- ANCHOR: correctness
theorem correctness (p : Frodo.CKAParams ProbComp) [DecidableEq p.Key]
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) p.Key) :
    Pr[= true | CKAScheme.correctnessExp (scheme p) adv] = 1
-- ANCHOR_END: correctness
    := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  unfold CKAScheme.correctnessExp at hb
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨⟨common, pubAB, secAB⟩, hik, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stA, hstA, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stB, hstB, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨out, hout, hb⟩
  have hik' : (common, pubAB, secAB) ∈ support p.init := by
    simpa [lweCKA.scheme] using hik
  have hM : p.MatchAB common pubAB secAB := p.init_match common pubAB secAB hik'
  have hstA' : stA = State.sendAReady common pubAB := by
    simpa [lweCKA.scheme, lweCKA.initA, mem_support_pure_iff] using hstA
  have hstB' : stB = State.recvBReady common secAB := by
    simpa [lweCKA.scheme, lweCKA.initB, mem_support_pure_iff] using hstB
  subst stA
  subst stB
  have hInv : reachableInv p out.2 :=
    OracleComp.simulateQ_run_preservesInv
      (impl := CKAScheme.ckaCorrectnessImpl (scheme p))
      (Inv := reachableInv p)
      (correctnessImpl_preserves p)
      adv
      (CKAScheme.initGameState (State.sendAReady common pubAB) (State.recvBReady common secAB))
      (reachableInv_init p hM)
      out
      hout
  have hb' : b = out.2.correct := by
    simpa [mem_support_pure_iff] using hb
  exact hb'.trans hInv.1

/-- Correctness of the concrete Frodo/LWE CKA scheme in the CKA correctness game.

A thin specialization of `correctness` to `Frodo.concreteCKAParams p`: agreement
at each epoch is the matrix reconciliation supplied by the `MatrixParams`
reconciliation laws, lifted through the abstract correctness proof. -/
-- ANCHOR: frodoCorrectness
theorem frodoCorrectness (p : Frodo.MatrixParams) [DecidableEq p.Key]
    (adv : CKAScheme.CKACorrectnessAdversary (Message (Frodo.concreteCKAParams p)) p.Key) :
    Pr[= true | CKAScheme.correctnessExp (frodoScheme p) adv] = 1
-- ANCHOR_END: frodoCorrectness
    := by
  letI : DecidableEq (Frodo.concreteCKAParams p).Key := ‹DecidableEq p.Key›
  exact correctness (Frodo.concreteCKAParams p) adv

end lweCKA
