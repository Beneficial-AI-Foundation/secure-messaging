/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Construction

/-!
# CKA from KEM — Correctness Statements

This file states the correctness properties for the generic CKA-from-KEM
construction of [ACD19, Section 4.1.2].

The KEM correctness property is:

```
(pk, sk) ← keygen
(c, k)   ← encaps pk
k'       ← decaps sk c
return k' = some k
```

Perfect correctness means this experiment succeeds with probability exactly 1.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

variable {K PK SK C : Type}

open CKAScheme.ckaCorrectnessSpec

/-- Perfect KEM correctness specialized to deterministic decapsulation.

If `(pk, sk)` can be sampled by key generation and `(c, key)` can be sampled by
encapsulation under `pk`, then the deterministic decapsulation witness recovers
exactly `key` from `sk` and `c`.
-/
lemma decapsDet_eq_some_of_mem_support [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    {pk : PK} {sk : SK} {c : C} {key : K}
    (hks : (pk, sk) ∈ support kem.keygen)
    (hck : (c, key) ∈ support (kem.encaps pk)) :
    hDet.decapsDet sk c = some key := by
  have hsup : support kem.CorrectExp = {true} :=
    (probOutput_eq_one_iff (mx := kem.CorrectExp) (x := true)).mp hkem |>.2
  rw [KEMScheme.CorrectExp] at hsup
  simp only [hDet.decaps_eq, bind_pure_comp, map_pure, support_bind, support_map] at hsup
  have hin : decide (hDet.decapsDet sk c = some key) ∈
      ⋃ x ∈ support kem.keygen,
        (fun a => decide (hDet.decapsDet x.2 a.1 = some a.2)) '' support (kem.encaps x.1) := by
    exact Set.mem_iUnion.2 ⟨(pk, sk), Set.mem_iUnion.2 ⟨hks, ⟨(c, key), hck, rfl⟩⟩⟩
  exact of_decide_eq_true (by simpa [hsup] using hin)

private def stateShapeInv
    (kem : KEMScheme ProbComp K PK SK C)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK)) : Prop :=
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

private def reachableInv
    (kem : KEMScheme ProbComp K PK SK C)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK)) : Prop :=
  s.correct = true ∧ stateShapeInv kem s

private lemma reachableInv_init
    (kem : KEMScheme ProbComp K PK SK C)
    {pk : PK} {sk : SK}
    (hks : (pk, sk) ∈ support kem.keygen) :
    reachableInv kem
      (CKAScheme.initGameState (.sendReady pk) (.recvReady sk)) := by
  simpa [reachableInv, stateShapeInv, CKAScheme.initGameState] using hks

private lemma reachableInv_after_sendA
    (kem : KEMScheme ProbComp K PK SK C)
    {pk : PK} {sk : SK} {c : C} {key : K} {pkNext : PK} {skNext : SK}
    {epA epB : ℕ}
    (hks : (pk, sk) ∈ support kem.keygen)
    (hck : (c, key) ∈ support (kem.encaps pk))
    (hksNext : (pkNext, skNext) ∈ support kem.keygen) :
    reachableInv kem
      { stA := .recvReady skNext, stB := .recvReady sk,
        rhoA := some (c, pkNext), rhoB := none,
        keyA := some key, keyB := none,
        correct := true, lastAction := some .sendA,
        tA := epA + 1, tB := epB } := by
  refine ⟨rfl, pk, sk, c, key, pkNext, skNext, hks, hck, hksNext,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private lemma reachableInv_after_sendB
    (kem : KEMScheme ProbComp K PK SK C)
    {pk : PK} {sk : SK} {c : C} {key : K} {pkNext : PK} {skNext : SK}
    {epA epB : ℕ}
    (hks : (pk, sk) ∈ support kem.keygen)
    (hck : (c, key) ∈ support (kem.encaps pk))
    (hksNext : (pkNext, skNext) ∈ support kem.keygen) :
    reachableInv kem
      { stA := .recvReady sk, stB := .recvReady skNext,
        rhoA := none, rhoB := some (c, pkNext),
        keyA := none, keyB := some key,
        correct := true, lastAction := some .sendB,
        tA := epA, tB := epB + 1 } := by
  refine ⟨rfl, pk, sk, c, key, pkNext, skNext, hks, hck, hksNext,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private lemma reachableInv_after_recvB
    (kem : KEMScheme ProbComp K PK SK C)
    {pk : PK} {sk : SK} {epA epB : ℕ}
    (hks : (pk, sk) ∈ support kem.keygen) :
    reachableInv kem
      { stA := .recvReady sk, stB := .sendReady pk,
        rhoA := none, rhoB := none, keyA := none, keyB := none,
        correct := true, lastAction := some .recvB,
        tA := epA, tB := epB + 1 } := by
  simpa [reachableInv, stateShapeInv] using hks

private lemma reachableInv_after_recvA
    (kem : KEMScheme ProbComp K PK SK C)
    {pk : PK} {sk : SK} {epA epB : ℕ}
    (hks : (pk, sk) ∈ support kem.keygen) :
    reachableInv kem
      { stA := .sendReady pk, stB := .recvReady sk,
        rhoA := none, rhoB := none, keyA := none, keyB := none,
        correct := true, lastAction := some .recvA,
        tA := epA + 1, tB := epB } := by
  simpa [reachableInv, stateShapeInv] using hks

private lemma oracleUnif_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleUnif (State PK SK) K (Message C PK))
      (reachableInv kem) := by
  intro t σ hσ z hz
  have hz' : ∃ y : unifSpec.Range t, (y, σ) = z := by
    simpa [CKAScheme.oracleUnif] using hz
  rcases hz' with ⟨_, rfl⟩
  simpa using hσ

private lemma oracleSendA_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleSendA (scheme kem hDet leak))
      (reachableInv kem) := by
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
        ⟨hcorrect, pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      rw [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
      have hz' : ∃ c key pk' sk',
          (c, key) ∈ support (kem.encaps pk) ∧
          (pk', sk') ∈ support kem.keygen ∧
          (some ((c, pk'), key),
            { stA := State.recvReady sk', stB := State.recvReady sk,
              rhoA := some (c, pk'), rhoB := none,
              keyA := some key, keyB := none,
              correct := true, lastAction := some .sendA,
              tA := epA + 1, tB := epB }) = z := by
        simpa [CKAScheme.validStep, scheme, send] using hz
      obtain ⟨c, key, pk', sk', hck, hks', rfl⟩ := hz'
      exact reachableInv_after_sendA (kem := kem) hks hck hks')

private lemma oracleSendB_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleSendB (scheme kem hDet leak))
      (reachableInv kem) := by
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
      ⟨hcorrect, pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
    subst correct
    rw [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    have hz' : ∃ c key pk' sk',
        (c, key) ∈ support (kem.encaps pk) ∧
        (pk', sk') ∈ support kem.keygen ∧
        (some ((c, pk'), key),
          { stA := State.recvReady sk, stB := State.recvReady sk',
            rhoA := none, rhoB := some (c, pk'),
            keyA := none, keyB := some key,
            correct := true, lastAction := some .sendB,
            tA := epA, tB := epB + 1 }) = z := by
      simpa [CKAScheme.validStep, scheme, send] using hz
    obtain ⟨c, key, pk', sk', hck, hks', rfl⟩ := hz'
    exact reachableInv_after_sendB (kem := kem) hks hck hks'

private lemma oracleRecvB_preserves_reachableInv [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleRecvB (scheme kem hDet leak))
      (reachableInv kem) := by
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
    · rcases (by simpa [reachableInv, stateShapeInv] using hσ) with
        ⟨hcorrect, pk, sk, hks, c, key, hck, pkNext, skNext,
          hksNext, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      have hdec := decapsDet_eq_some_of_mem_support
        (pk := pk) (sk := sk) (c := c) (key := key) kem hDet hkem hks hck
      have : z = ((), ⟨State.recvReady skNext, State.sendReady pkNext,
          none, none, none, none, true, some .recvB, epA, epB + 1⟩) := by
        simpa [CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recv, hdec,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst this
      exact reachableInv_after_recvB (kem := kem) hksNext
    · exact False.elim (by simp only [reachableInv, stateShapeInv, and_false] at hσ)

private lemma oracleRecvA_preserves_reachableInv [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    QueryImpl.PreservesInv
      (CKAScheme.oracleRecvA (scheme kem hDet leak))
      (reachableInv kem) := by
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
    · rcases (by simpa [reachableInv, stateShapeInv] using hσ) with
        ⟨hcorrect, pk, sk, hks, c, key, hck, pkNext, skNext,
          hksNext, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      have hdec := decapsDet_eq_some_of_mem_support
        (pk := pk) (sk := sk) (c := c) (key := key) kem hDet hkem hks hck
      have : z = ((), ⟨State.sendReady pkNext, State.recvReady skNext,
          none, none, none, none, true, some .recvA, epA + 1, epB⟩) := by
        simpa [CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recv, hdec,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst this
      exact reachableInv_after_recvA (kem := kem) hksNext
    · exact False.elim (by simp [reachableInv, stateShapeInv] at hσ)

private lemma correctnessImpl_preserves [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    QueryImpl.PreservesInv
      (CKAScheme.ckaCorrectnessImpl (scheme kem hDet leak))
      (reachableInv kem) := by
  intro t σ hσ z hz
  match t with
  | OUnif n =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleUnif_preserves_reachableInv (kem := kem) n σ hσ z hz
  | OSendA =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleSendA_preserves_reachableInv
          (kem := kem) (hDet := hDet) (leak := leak) () σ hσ z hz
  | ORecvA =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleRecvA_preserves_reachableInv
          (kem := kem) (hDet := hDet) (leak := leak) (hkem := hkem) () σ hσ z hz
  | OSendB =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleSendB_preserves_reachableInv
          (kem := kem) (hDet := hDet) (leak := leak) () σ hσ z hz
  | ORecvB =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleRecvB_preserves_reachableInv
          (kem := kem) (hDet := hDet) (leak := leak) (hkem := hkem) () σ hσ z hz

/-- One-step correctness for the KEM-based CKA construction.

The experiment samples an initial KEM key pair `(pk, sk)`, runs the honest-send
branch of `send` from `sendReady pk` inline — encapsulate under `pk`, then
generate the next key pair — and runs the CKA receive algorithm from
`recvReady sk` on the transmitted message `(c, pkNext)`. The receiver must
recover the sender's epoch key; receive failure counts as a correctness
failure, matching the generic CKA correctness oracle.
-/
theorem send_recv_agree [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    Pr[= true |
      do
        let (pk, sk) ← kem.keygen
        let (c, keyS) ← kem.encaps pk
        let (pkNext, _skNext) ← kem.keygen
        match recv hDet (.recvReady sk) (c, pkNext) with
        | none => return false
        | some (keyR, _) => return decide (keyR = keyS)] = 1 := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨pk, sk⟩, hks, hb⟩ := hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨c, keyS⟩, hck, hb⟩ := hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨pkNext, _skNext⟩, _hksNext, hb⟩ := hb
  have hdec := decapsDet_eq_some_of_mem_support kem hDet hkem hks hck
  simpa [recv, hdec, mem_support_pure_iff] using hb

/-- Correctness of the CKA-from-KEM construction in the existing CKA correctness
game.

For every adversary using only the honest send/receive oracles, the game returns
`true` with probability one under the KEM correctness hypothesis. The statement
is proved for an arbitrary randomness-leak package `leak`: the correctness game
never queries the randomness-leaking send oracles, so correctness is independent
of the choice of `leak`.
-/
-- ANCHOR: correctness
theorem correctness [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : CKAScheme.CKACorrectnessAdversary (Message C PK) K) :
    Pr[= true | CKAScheme.correctnessExp (scheme kem hDet leak) adv] = 1
-- ANCHOR_END: correctness
    := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  unfold CKAScheme.correctnessExp at hb
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨ik, hik, hb⟩
  rcases ik with ⟨pk, sk⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stA, hstA, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stB, hstB, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨out, hout, hb⟩
  have hstA' : stA = State.sendReady pk := by
    simpa [scheme, initA, mem_support_pure_iff] using hstA
  have hstB' : stB = State.recvReady sk := by
    simpa [scheme, initB, mem_support_pure_iff] using hstB
  subst stA
  subst stB
  have hInv : reachableInv kem out.2 := by
    exact OracleComp.simulateQ_run_preservesInv
      (impl := CKAScheme.ckaCorrectnessImpl (scheme kem hDet leak))
      (Inv := reachableInv kem)
      (correctnessImpl_preserves (kem := kem) (hDet := hDet) (leak := leak) (hkem := hkem))
      adv
      (CKAScheme.initGameState (State.sendReady pk) (State.recvReady sk))
      (reachableInv_init (kem := kem) hik)
      out
      hout
  have hb' : b = out.2.correct := by
    simpa [mem_support_pure_iff] using hb
  exact hb'.trans hInv.1

end kemCKA
