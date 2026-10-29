/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromKEM.Construction
import SecureMessaging.KEM.CorrectnessError
import ToVCVio.OracleComp.SimSemantics.StateT.WPBound

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
open OracleComp.ProgramLogic

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
  have h1 : ∀ b ∈ support kem.correctnessExperiment, b = true := by
    rw [← OracleComp.prEvent_eq_one_iff, prEvent_eq_evalDist_singleton]
    exact hkem
  have hin : decide (hDet.decapsDet sk c = some key) ∈ support kem.correctnessExperiment := by
    rw [KEMScheme.correctnessExperiment]
    simp only [hDet.decaps_eq, bind_pure_comp, map_pure, support_bind, support_map]
    exact Set.mem_iUnion.2 ⟨(pk, sk), Set.mem_iUnion.2 ⟨hks, ⟨(c, key), hck, rfl⟩⟩⟩
  exact of_decide_eq_true (h1 _ hin)

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
    Pr{let x ← (do
        let (pk, sk) ← kem.keygen
        let (c, keyS) ← kem.encaps pk
        let (pkNext, _skNext) ← kem.keygen
        match recv hDet (.recvReady sk) (c, pkNext) with
        | none => return false
        | some (keyR, _) => return decide (keyR = keyS))}[x = true] = 1 := by
  rw [OracleComp.prEvent_eq_one_iff]
  intro b hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨pk, sk⟩, hks, hb⟩ := hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨c, keyS⟩, hck, hb⟩ := hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨⟨pkNext, _skNext⟩, _hksNext, hb⟩ := hb
  have hdec := decapsDet_eq_some_of_mem_support kem hDet hkem hks hck
  simpa [recv, hdec, mem_support_pure_iff] using hb

/-! ## The failure potential

Write `δ := kem.correctnessError` and `φ(pk, sk) := keypairFailure kem hDet pk sk`, so that
`δ` is the average of `φ` over key generation. For a remaining send budget `k`, the potential
`failureScore kem hDet k s` of a game state `s` is `1` once the correctness flag is down, and
otherwise

`pend(s) + [k ≠ 0] · (next(s) + (k - 1) · δ)`,

where `pend(s)` is the failure indicator of the pending message, if any, and `next(s)` is `φ`
of the key pair the next send encapsulates under. A send that leaves budget `k` charges the
fresh key pair it generates only when `k ≠ 0`, so a run with at most `q` sends pays for `q` key
pairs, not `q + 1`. -/

/-- The failure indicator of a pending message `(c, _)` with sender key `key`, decapsulated by
the receiver state; `0` when no message is pending. -/
private noncomputable def pendingFailure [DecidableEq K] {kem : KEMScheme ProbComp K PK SK C}
    (hDet : DeterministicDecaps kem) :
    State PK SK → Option (Message C PK) → Option K → ℝ≥0∞
  | .recvReady sk, some (c, _), some key => if hDet.decapsDet sk c = some key then 0 else 1
  | _, _, _ => 0

/-- `φ` of the key pair the next send of the first party encapsulates under: its peer's key pair
`(pk, sk)` if it holds `sendReady pk`, or its own fresh pair `(pk, sk)` if it holds
`recvReady sk` and its pending message carries `pk`. -/
private noncomputable def nextFailure [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem) :
    State PK SK → State PK SK → Option (Message C PK) → ℝ≥0∞
  | .sendReady pk, .recvReady sk, _ => keypairFailure kem hDet pk sk
  | .recvReady sk, _, some (_, pk) => keypairFailure kem hDet pk sk
  | _, _, _ => 0

/-- The budget-indexed failure potential `V_k(s)`. -/
private noncomputable def failureScore [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem) (k : ℕ)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK)) : ℝ≥0∞ :=
  if s.correct then
    pendingFailure hDet s.stB s.rhoA s.keyA + pendingFailure hDet s.stA s.rhoB s.keyB +
      if k = 0 then 0 else
        nextFailure kem hDet s.stA s.stB s.rhoA + nextFailure kem hDet s.stB s.stA s.rhoB +
          ((k - 1 : ℕ) : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
  else 1

/-- The shape of a game state after each kind of action, without support conditions. -/
private def PhaseShape (s : CKAScheme.GameState (State PK SK) K (Message C PK)) : Prop :=
  match s.lastAction with
  | none | some .recvA =>
      ∃ pk sk, s.stA = .sendReady pk ∧ s.stB = .recvReady sk ∧
        s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendA =>
      ∃ sk sk' c key pk', s.stA = .recvReady sk' ∧ s.stB = .recvReady sk ∧
        s.rhoA = some (c, pk') ∧ s.rhoB = none ∧ s.keyA = some key ∧ s.keyB = none
  | some .recvB =>
      ∃ pk sk, s.stA = .recvReady sk ∧ s.stB = .sendReady pk ∧
        s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendB =>
      ∃ sk sk' c key pk', s.stA = .recvReady sk ∧ s.stB = .recvReady sk' ∧
        s.rhoA = none ∧ s.rhoB = some (c, pk') ∧ s.keyA = none ∧ s.keyB = some key
  | some .challA | some .challB => False

/-- The invariant of the potential argument: the flag is down, or the state has its phase
shape. -/
private def ScoreInv (s : CKAScheme.GameState (State PK SK) K (Message C PK)) : Prop :=
  s.correct = false ∨ PhaseShape s

/-! ### Phase shapes at valid steps -/

private lemma phaseShape_sendA {s : CKAScheme.GameState (State PK SK) K (Message C PK)}
    (hs : PhaseShape s) (hv : CKAScheme.validStep s.lastAction .sendA = true) :
    ∃ pk sk, s.stA = .sendReady pk ∧ s.stB = .recvReady sk ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none := by
  unfold PhaseShape at hs
  rcases hl : s.lastAction with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
    rw [hl] at hs hv <;> simp only [CKAScheme.validStep, Bool.false_eq_true] at hv <;> exact hs

private lemma phaseShape_sendB {s : CKAScheme.GameState (State PK SK) K (Message C PK)}
    (hs : PhaseShape s) (hv : CKAScheme.validStep s.lastAction .sendB = true) :
    ∃ pk sk, s.stA = .recvReady sk ∧ s.stB = .sendReady pk ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none := by
  unfold PhaseShape at hs
  rcases hl : s.lastAction with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
    rw [hl] at hs hv <;> simp only [CKAScheme.validStep, Bool.false_eq_true] at hv
  exact hs

private lemma phaseShape_recvB {s : CKAScheme.GameState (State PK SK) K (Message C PK)}
    (hs : PhaseShape s) (hv : CKAScheme.validStep s.lastAction .recvB = true) :
    ∃ sk sk' c key pk', s.stA = .recvReady sk' ∧ s.stB = .recvReady sk ∧
      s.rhoA = some (c, pk') ∧ s.rhoB = none ∧ s.keyA = some key ∧ s.keyB = none := by
  unfold PhaseShape at hs
  rcases hl : s.lastAction with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
    rw [hl] at hs hv <;> simp only [CKAScheme.validStep, Bool.false_eq_true] at hv <;>
    first | exact hs | exact hs.elim

private lemma phaseShape_recvA {s : CKAScheme.GameState (State PK SK) K (Message C PK)}
    (hs : PhaseShape s) (hv : CKAScheme.validStep s.lastAction .recvA = true) :
    ∃ sk sk' c key pk', s.stA = .recvReady sk ∧ s.stB = .recvReady sk' ∧
      s.rhoA = none ∧ s.rhoB = some (c, pk') ∧ s.keyA = none ∧ s.keyB = some key := by
  unfold PhaseShape at hs
  rcases hl : s.lastAction with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
    rw [hl] at hs hv <;> simp only [CKAScheme.validStep, Bool.false_eq_true] at hv <;>
    first | exact hs | exact hs.elim

/-! ### Oracle runs -/

/-- The uniform-randomness oracle leaves the game state unchanged. -/
private lemma oracleUnif_run_snd (n : ℕ)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK)) {z}
    (hz : z ∈ support ((CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run s)) :
    z.2 = s := by
  rw [CKAScheme.oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
  obtain ⟨_, rfl⟩ := hz
  rfl

private lemma oracleUnif_preservesInv
    (Inv : CKAScheme.GameState (State PK SK) K (Message C PK) → Prop) :
    QueryImpl.PreservesInv (CKAScheme.oracleUnif (State PK SK) K (Message C PK)) Inv := by
  intro n s hs z hz
  rw [oracleUnif_run_snd n s hz]
  exact hs

private lemma oracleSendA_run_of_not_valid
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hv : CKAScheme.validStep s.lastAction .sendA = false) :
    (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run s = pure (none, s) := by
  simp [CKAScheme.oracleSendA, hv, StateT.run_bind, StateT.run_get]

private lemma oracleSendB_run_of_not_valid
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hv : CKAScheme.validStep s.lastAction .sendB = false) :
    (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run s = pure (none, s) := by
  simp [CKAScheme.oracleSendB, hv, StateT.run_bind, StateT.run_get]

private lemma oracleRecvA_run_of_not_valid [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hv : CKAScheme.validStep s.lastAction .recvA = false) :
    (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run s = pure ((), s) := by
  simp [CKAScheme.oracleRecvA, hv, StateT.run_bind, StateT.run_get]

private lemma oracleRecvB_run_of_not_valid [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hv : CKAScheme.validStep s.lastAction .recvB = false) :
    (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run s = pure ((), s) := by
  simp [CKAScheme.oracleRecvB, hv, StateT.run_bind, StateT.run_get]

/-- A valid A-send from `sendReady pk`: encapsulate under `pk`, then generate the next key
pair. -/
private lemma oracleSendA_run_sendReady
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK)) {pk : PK}
    (hv : CKAScheme.validStep s.lastAction .sendA = true) (hst : s.stA = .sendReady pk) :
    (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run s =
      kem.encaps pk >>= fun ck => kem.keygen >>= fun kp =>
        pure (some ((ck.1, kp.1), ck.2),
          { s with
            stA := .recvReady kp.2, rhoA := some (ck.1, kp.1), keyA := some ck.2,
            lastAction := some .sendA, tA := s.tA + 1 }) := by
  simp only [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind, hv,
    ↓reduceIte, scheme, send, hst, liftM, StateT.run_monadLift, monadLift_self, bind_assoc,
    StateT.run_set, StateT.run_pure]

/-- A valid B-send from `sendReady pk`: encapsulate under `pk`, then generate the next key
pair. -/
private lemma oracleSendB_run_sendReady
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK)) {pk : PK}
    (hv : CKAScheme.validStep s.lastAction .sendB = true) (hst : s.stB = .sendReady pk) :
    (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run s =
      kem.encaps pk >>= fun ck => kem.keygen >>= fun kp =>
        pure (some ((ck.1, kp.1), ck.2),
          { s with
            stB := .recvReady kp.2, rhoB := some (ck.1, kp.1), keyB := some ck.2,
            lastAction := some .sendB, tB := s.tB + 1 }) := by
  simp only [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind, hv,
    ↓reduceIte, scheme, send, hst, liftM, StateT.run_monadLift, monadLift_self, bind_assoc,
    StateT.run_set, StateT.run_pure]

private lemma oracleRecvA_run_none [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    {sk : SK} {c : C} {pk' : PK}
    (hv : CKAScheme.validStep s.lastAction .recvA = true) (hst : s.stA = .recvReady sk)
    (hrho : s.rhoB = some (c, pk')) (hdec : hDet.decapsDet sk c = none) :
    (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run s =
      pure ((),
        { s with
          rhoB := none, keyB := none, correct := false, lastAction := some .recvA,
          tA := s.tA + 1 }) := by
  simp only [CKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind, hv,
    ↓reduceIte, scheme, recv, hst, hrho, hdec, StateT.run_set]

private lemma oracleRecvA_run_some [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    {sk : SK} {c : C} {pk' : PK} {key' : K}
    (hv : CKAScheme.validStep s.lastAction .recvA = true) (hst : s.stA = .recvReady sk)
    (hrho : s.rhoB = some (c, pk')) (hdec : hDet.decapsDet sk c = some key') :
    (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run s =
      pure ((),
        { s with
          stA := .sendReady pk', rhoB := none, keyB := none,
          correct := s.correct && (s.keyB == some key'), lastAction := some .recvA,
          tA := s.tA + 1 }) := by
  simp only [CKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind, hv,
    ↓reduceIte, scheme, recv, hst, hrho, hdec, StateT.run_set]

private lemma oracleRecvB_run_none [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    {sk : SK} {c : C} {pk' : PK}
    (hv : CKAScheme.validStep s.lastAction .recvB = true) (hst : s.stB = .recvReady sk)
    (hrho : s.rhoA = some (c, pk')) (hdec : hDet.decapsDet sk c = none) :
    (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run s =
      pure ((),
        { s with
          rhoA := none, keyA := none, correct := false, lastAction := some .recvB,
          tB := s.tB + 1 }) := by
  simp only [CKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind, hv,
    ↓reduceIte, scheme, recv, hst, hrho, hdec, StateT.run_set]

private lemma oracleRecvB_run_some [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    {sk : SK} {c : C} {pk' : PK} {key' : K}
    (hv : CKAScheme.validStep s.lastAction .recvB = true) (hst : s.stB = .recvReady sk)
    (hrho : s.rhoA = some (c, pk')) (hdec : hDet.decapsDet sk c = some key') :
    (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run s =
      pure ((),
        { s with
          stB := .sendReady pk', rhoA := none, keyA := none,
          correct := s.correct && (s.keyA == some key'), lastAction := some .recvB,
          tB := s.tB + 1 }) := by
  simp only [CKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind, hv,
    ↓reduceIte, scheme, recv, hst, hrho, hdec, StateT.run_set]

/-! ### Invariants -/

private lemma oracleSendA_correct_false
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleSendA (scheme kem hDet leak))
      (fun s => s.correct = false) := by
  intro _ s hs z hz
  simp only [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_bind, liftM, StateT.run_monadLift, monadLift_self, bind_assoc,
      pure_bind, mem_support_bind_iff] at hz
    obtain ⟨r, -, hz⟩ := hz
    rcases r with _ | ⟨key, ρ, st'⟩
    · simp only [StateT.run_pure, mem_support_pure_iff] at hz
      subst hz
      exact hs
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        mem_support_pure_iff] at hz
      subst hz
      exact hs
  · simp only [StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact hs

private lemma oracleSendB_correct_false
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleSendB (scheme kem hDet leak))
      (fun s => s.correct = false) := by
  intro _ s hs z hz
  simp only [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_bind, liftM, StateT.run_monadLift, monadLift_self, bind_assoc,
      pure_bind, mem_support_bind_iff] at hz
    obtain ⟨r, -, hz⟩ := hz
    rcases r with _ | ⟨key, ρ, st'⟩
    · simp only [StateT.run_pure, mem_support_pure_iff] at hz
      subst hz
      exact hs
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        mem_support_pure_iff] at hz
      subst hz
      exact hs
  · simp only [StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact hs

private lemma oracleRecvA_correct_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvA (scheme kem hDet leak))
      (fun s => s.correct = false) := by
  intro _ s hs z hz
  simp only [CKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · split at hz
    · simp only [StateT.run_pure, mem_support_pure_iff] at hz
      subst hz
      exact hs
    · split at hz
      · simp only [StateT.run_set, mem_support_pure_iff] at hz
        subst hz
        rfl
      · simp only [StateT.run_set, mem_support_pure_iff] at hz
        subst hz
        simp only [hs, Bool.false_and]
  · simp only [StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact hs

private lemma oracleRecvB_correct_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvB (scheme kem hDet leak))
      (fun s => s.correct = false) := by
  intro _ s hs z hz
  simp only [CKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · split at hz
    · simp only [StateT.run_pure, mem_support_pure_iff] at hz
      subst hz
      exact hs
    · split at hz
      · simp only [StateT.run_set, mem_support_pure_iff] at hz
        subst hz
        rfl
      · simp only [StateT.run_set, mem_support_pure_iff] at hz
        subst hz
        simp only [hs, Bool.false_and]
  · simp only [StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact hs

/-- Once the correctness flag is down, it stays down. -/
private lemma correct_false_preserved [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.ckaCorrectnessImpl (scheme kem hDet leak))
      (fun s => s.correct = false) :=
  ((((oracleUnif_preservesInv _).add (oracleSendA_correct_false kem hDet leak)).add
    (oracleRecvA_correct_false kem hDet leak)).add (oracleSendB_correct_false kem hDet leak)).add
    (oracleRecvB_correct_false kem hDet leak)

private lemma scoreInv_init (pk : PK) (sk : SK) :
    ScoreInv (K := K) (PK := PK) (SK := SK) (C := C)
      (CKAScheme.initGameState (State.sendReady pk) (State.recvReady sk)) :=
  Or.inr ⟨pk, sk, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma oracleSendA_scoreInv
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleSendA (scheme kem hDet leak)) ScoreInv := by
  intro _ s hs z hz
  rcases hs with hc | hshape
  · exact Or.inl (oracleSendA_correct_false kem hDet leak () s hc z hz)
  cases hv : CKAScheme.validStep s.lastAction .sendA
  · rw [oracleSendA_run_of_not_valid kem hDet leak s hv, mem_support_pure_iff] at hz
    subst hz
    exact Or.inr hshape
  · obtain ⟨pk, sk, hA, hB, -, hrB, -, hkB⟩ := phaseShape_sendA hshape hv
    rw [oracleSendA_run_sendReady kem hDet leak s hv hA] at hz
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨ck, -, kp, -, rfl⟩ := hz
    exact Or.inr ⟨sk, kp.2, ck.1, ck.2, kp.1, rfl, hB, rfl, hrB, rfl, hkB⟩

private lemma oracleSendB_scoreInv
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleSendB (scheme kem hDet leak)) ScoreInv := by
  intro _ s hs z hz
  rcases hs with hc | hshape
  · exact Or.inl (oracleSendB_correct_false kem hDet leak () s hc z hz)
  cases hv : CKAScheme.validStep s.lastAction .sendB
  · rw [oracleSendB_run_of_not_valid kem hDet leak s hv, mem_support_pure_iff] at hz
    subst hz
    exact Or.inr hshape
  · obtain ⟨pk, sk, hA, hB, hrA, -, hkA, -⟩ := phaseShape_sendB hshape hv
    rw [oracleSendB_run_sendReady kem hDet leak s hv hB] at hz
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨ck, -, kp, -, rfl⟩ := hz
    exact Or.inr ⟨sk, kp.2, ck.1, ck.2, kp.1, hA, rfl, hrA, rfl, hkA, rfl⟩

private lemma oracleRecvA_scoreInv [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvA (scheme kem hDet leak)) ScoreInv := by
  intro _ s hs z hz
  rcases hs with hc | hshape
  · exact Or.inl (oracleRecvA_correct_false kem hDet leak () s hc z hz)
  cases hv : CKAScheme.validStep s.lastAction .recvA
  · rw [oracleRecvA_run_of_not_valid kem hDet leak s hv, mem_support_pure_iff] at hz
    subst hz
    exact Or.inr hshape
  · obtain ⟨sk, sk', c, key, pk', hA, hB, hrA, hrB, hkA, -⟩ := phaseShape_recvA hshape hv
    cases hdec : hDet.decapsDet sk c with
    | none =>
      rw [oracleRecvA_run_none kem hDet leak s hv hA hrB hdec, mem_support_pure_iff] at hz
      subst hz
      exact Or.inl rfl
    | some key' =>
      rw [oracleRecvA_run_some kem hDet leak s hv hA hrB hdec, mem_support_pure_iff] at hz
      subst hz
      exact Or.inr ⟨pk', sk', rfl, hB, hrA, rfl, hkA, rfl⟩

private lemma oracleRecvB_scoreInv [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvB (scheme kem hDet leak)) ScoreInv := by
  intro _ s hs z hz
  rcases hs with hc | hshape
  · exact Or.inl (oracleRecvB_correct_false kem hDet leak () s hc z hz)
  cases hv : CKAScheme.validStep s.lastAction .recvB
  · rw [oracleRecvB_run_of_not_valid kem hDet leak s hv, mem_support_pure_iff] at hz
    subst hz
    exact Or.inr hshape
  · obtain ⟨sk, sk', c, key, pk', hA, hB, hrA, hrB, -, hkB⟩ := phaseShape_recvB hshape hv
    cases hdec : hDet.decapsDet sk c with
    | none =>
      rw [oracleRecvB_run_none kem hDet leak s hv hB hrA hdec, mem_support_pure_iff] at hz
      subst hz
      exact Or.inl rfl
    | some key' =>
      rw [oracleRecvB_run_some kem hDet leak s hv hB hrA hdec, mem_support_pure_iff] at hz
      subst hz
      exact Or.inr ⟨pk', sk', hA, rfl, rfl, hrB, rfl, hkB⟩

private lemma scoreInv_preserved [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    QueryImpl.PreservesInv (CKAScheme.ckaCorrectnessImpl (scheme kem hDet leak))
      (ScoreInv (K := K) (PK := PK) (SK := SK) (C := C)) :=
  ((((oracleUnif_preservesInv _).add (oracleSendA_scoreInv kem hDet leak)).add
    (oracleRecvA_scoreInv kem hDet leak)).add (oracleSendB_scoreInv kem hDet leak)).add
    (oracleRecvB_scoreInv kem hDet leak)

/-! ### One-step bounds -/

private lemma indicator_le_failureScore [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem) (k : ℕ)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK)) :
    (if s.correct then 0 else 1) ≤ failureScore kem hDet k s := by
  unfold failureScore
  split_ifs <;> simp

private lemma failureScore_le_succ [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem) (k : ℕ)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK)) :
    failureScore kem hDet k s ≤ failureScore kem hDet (k + 1) s := by
  unfold failureScore
  by_cases hc : s.correct
  · simp only [hc, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    gcongr
    rcases k with _ | k
    · simp only [↓reduceIte, zero_le]
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      gcongr
      exact Nat.sub_le _ _
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, le_refl]

/-- Averaging the next-send charge over key generation gives `k · δ`. -/
private lemma wp_keygen_nextCharge [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem) (k : ℕ) :
    wp kem.keygen (fun kp => if k = 0 then 0 else keypairFailure kem hDet kp.1 kp.2 +
      ((k - 1 : ℕ) : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp) =
      (k : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  rcases k with _ | k
  · simp only [↓reduceIte, wp_const, Nat.cast_zero, zero_mul]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, wp_add, wp_const, wp_keygen_keypairFailure,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_comm _ _

/-- The exact expected potential after a valid send under `(pk, sk)` that leaves budget `k`. -/
private lemma wp_send_core [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (pk : PK) (sk : SK) (k : ℕ) :
    wp (kem.encaps pk) (fun ck => wp kem.keygen (fun kp =>
      (if hDet.decapsDet sk ck.1 = some ck.2 then 0 else 1) +
        (if k = 0 then 0 else keypairFailure kem hDet kp.1 kp.2 +
          ((k - 1 : ℕ) : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp))) =
      keypairFailure kem hDet pk sk +
        (k : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  simp only [wp_add, wp_const, wp_keygen_nextCharge, wp_encaps_failureIndicator]

/-- Averaging the initial potential over the initial key pair gives `k · δ`. -/
private lemma wp_keygen_failureScore_init [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem) (k : ℕ) :
    wp kem.keygen (fun kp => failureScore kem hDet k
      (CKAScheme.initGameState (State.sendReady kp.1) (State.recvReady kp.2))) =
      (k : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  rw [← wp_keygen_nextCharge kem hDet k]
  refine congrArg _ (funext fun kp => ?_)
  simp [failureScore, CKAScheme.initGameState, pendingFailure, nextFailure]

private lemma oracleSendA_failureScore_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (k : ℕ) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hc : s.correct = true) (hs : PhaseShape s) :
    wp ((CKAScheme.oracleSendA (scheme kem hDet leak) ()).run s)
        (fun z => failureScore kem hDet k z.2) ≤ failureScore kem hDet (k + 1) s := by
  cases hv : CKAScheme.validStep s.lastAction .sendA
  · rw [oracleSendA_run_of_not_valid kem hDet leak s hv, wp_pure]
    exact failureScore_le_succ kem hDet k s
  · obtain ⟨pk, sk, hA, hB, hrA, hrB, hkA, hkB⟩ := phaseShape_sendA hs hv
    rw [oracleSendA_run_sendReady kem hDet leak s hv hA]
    simp only [wp_bind, wp_pure]
    have hold : failureScore kem hDet (k + 1) s = keypairFailure kem hDet pk sk +
        (k : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
      simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure]
    rw [hold, ← wp_send_core kem hDet pk sk k]
    refine le_of_eq (congrArg _ (funext fun ck => congrArg _ (funext fun kp => ?_)))
    simp [failureScore, hc, hB, hrB, hkB, pendingFailure, nextFailure]

private lemma oracleSendB_failureScore_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (k : ℕ) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hc : s.correct = true) (hs : PhaseShape s) :
    wp ((CKAScheme.oracleSendB (scheme kem hDet leak) ()).run s)
        (fun z => failureScore kem hDet k z.2) ≤ failureScore kem hDet (k + 1) s := by
  cases hv : CKAScheme.validStep s.lastAction .sendB
  · rw [oracleSendB_run_of_not_valid kem hDet leak s hv, wp_pure]
    exact failureScore_le_succ kem hDet k s
  · obtain ⟨pk, sk, hA, hB, hrA, hrB, hkA, hkB⟩ := phaseShape_sendB hs hv
    rw [oracleSendB_run_sendReady kem hDet leak s hv hB]
    simp only [wp_bind, wp_pure]
    have hold : failureScore kem hDet (k + 1) s = keypairFailure kem hDet pk sk +
        (k : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
      simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure]
    rw [hold, ← wp_send_core kem hDet pk sk k]
    refine le_of_eq (congrArg _ (funext fun ck => congrArg _ (funext fun kp => ?_)))
    simp [failureScore, hc, hA, hrA, hkA, pendingFailure, nextFailure]

private lemma oracleRecvA_failureScore_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (k : ℕ) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hc : s.correct = true) (hs : PhaseShape s) :
    wp ((CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run s)
        (fun z => failureScore kem hDet k z.2) ≤ failureScore kem hDet k s := by
  cases hv : CKAScheme.validStep s.lastAction .recvA
  · rw [oracleRecvA_run_of_not_valid kem hDet leak s hv, wp_pure]
  · obtain ⟨sk, sk', c, key, pk', hA, hB, hrA, hrB, hkA, hkB⟩ := phaseShape_recvA hs hv
    cases hdec : hDet.decapsDet sk c with
    | none =>
      rw [oracleRecvA_run_none kem hDet leak s hv hA hrB hdec, wp_pure]
      simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure, hdec]
    | some key' =>
      rw [oracleRecvA_run_some kem hDet leak s hv hA hrB hdec, wp_pure]
      by_cases hk : key = key'
      · subst hk
        simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure, hdec]
      · simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure, hdec,
          hk, Ne.symm hk]

private lemma oracleRecvB_failureScore_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (k : ℕ) (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hc : s.correct = true) (hs : PhaseShape s) :
    wp ((CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run s)
        (fun z => failureScore kem hDet k z.2) ≤ failureScore kem hDet k s := by
  cases hv : CKAScheme.validStep s.lastAction .recvB
  · rw [oracleRecvB_run_of_not_valid kem hDet leak s hv, wp_pure]
  · obtain ⟨sk, sk', c, key, pk', hA, hB, hrA, hrB, hkA, hkB⟩ := phaseShape_recvB hs hv
    cases hdec : hDet.decapsDet sk c with
    | none =>
      rw [oracleRecvB_run_none kem hDet leak s hv hB hrA hdec, wp_pure]
      simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure, hdec]
    | some key' =>
      rw [oracleRecvB_run_some kem hDet leak s hv hB hrA hdec, wp_pure]
      by_cases hk : key = key'
      · subst hk
        simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure, hdec]
      · simp [failureScore, hc, hA, hB, hrA, hrB, hkA, hkB, pendingFailure, nextFailure, hdec,
          hk, Ne.symm hk]

/-- One step of the potential argument: a send query uses one unit of budget and any other
query none. -/
private lemma failureScore_step [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (t : (CKAScheme.ckaCorrectnessSpec (Message C PK) K).Domain) (k : ℕ)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK)) (hs : ScoreInv s) :
    wp ((CKAScheme.ckaCorrectnessImpl (scheme kem hDet leak) t).run s)
        (fun z => failureScore kem hDet k z.2) ≤
      failureScore kem hDet (if CKAScheme.isSendQuery t = true then k + 1 else k) s := by
  by_cases hc : s.correct = false
  · refine wp_le_const_of_support _ fun z hz => ?_
    have hz' : z.2.correct = false := correct_false_preserved kem hDet leak t s hc z hz
    simp only [failureScore, hz', hc, Bool.false_eq_true, ↓reduceIte, le_refl]
  have hc' : s.correct = true := by simpa using hc
  have hshape : PhaseShape s := hs.resolve_left hc
  match t with
  | OUnif n =>
      refine wp_le_const_of_support _ fun z hz => ?_
      rw [oracleUnif_run_snd n s hz]
      exact le_rfl
  | OSendA => exact oracleSendA_failureScore_le kem hDet leak k s hc' hshape
  | ORecvA => exact oracleRecvA_failureScore_le kem hDet leak k s hc' hshape
  | OSendB => exact oracleSendB_failureScore_le kem hDet leak k s hc' hshape
  | ORecvB => exact oracleRecvB_failureScore_le kem hDet leak k s hc' hshape

/-- The failure probability of the correctness game is at most the expected final value of any
`V` that bounds the expected failure indicator of the simulation from every initial state. -/
private lemma prEvent_false_le_wp_keygen [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) (adv : CKAScheme.CKACorrectnessAdversary (Message C PK) K)
    (V : CKAScheme.GameState (State PK SK) K (Message C PK) → ℝ≥0∞)
    (hrun : ∀ (pk : PK) (sk : SK),
      wp ((simulateQ (CKAScheme.ckaCorrectnessImpl (scheme kem hDet leak)) adv).run
          (CKAScheme.initGameState (State.sendReady pk) (State.recvReady sk)))
        (fun z => if z.2.correct then 0 else 1) ≤
      V (CKAScheme.initGameState (State.sendReady pk) (State.recvReady sk))) :
    Pr{let x ← CKAScheme.correctnessExp (scheme kem hDet leak) adv}[x = false] ≤
      wp kem.keygen (fun kp =>
        V (CKAScheme.initGameState (State.sendReady kp.1) (State.recvReady kp.2))) := by
  rw [prEvent_eq_wp_propInd]
  simp only [CKAScheme.correctnessExp, scheme, initA, initB, wp_bind, wp_pure]
  refine wp_mono _ fun kp => (wp_mono _ fun z => ?_).trans (hrun kp.1 kp.2)
  by_cases hz : z.2.correct = true <;> simp [hz]

/-- Correctness of the CKA-from-KEM construction for an imperfectly correct KEM.

Assume `kem` has deterministic decapsulation `hDet` and `adv` makes at most `q` `SendA` and
`SendB` queries combined. Then the CKA correctness game fails with probability at most
`q · kem.correctnessError`; no correctness hypothesis on the KEM is needed. Each send
encapsulates under the key pair generated before it, the first under the initial key pair,
and a send that exhausts the remaining budget does not charge its newly generated key pair.
The initial expected potential is `q · δ`; rejected sends still consume the syntactic budget,
and early stopping or rejected sends only leave unused allowance. The bound holds for every
randomness-leak package `leak`, since the correctness game never queries the
randomness-leaking send oracles. -/
-- ANCHOR: correctnessFailureLe
theorem correctness_failure_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : CKAScheme.CKACorrectnessAdversary (Message C PK) K)
    (q : ℕ) (hq : CKAScheme.SendQueryBound adv q) :
    Pr{let x ← CKAScheme.correctnessExp (scheme kem hDet leak) adv}[x = false] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: correctnessFailureLe
    := by
  refine (prEvent_false_le_wp_keygen kem hDet leak adv (failureScore kem hDet q)
    fun pk sk => ?_).trans_eq (wp_keygen_failureScore_init kem hDet q)
  exact OracleComp.wp_simulateQ_run_le_budget _ ScoreInv (failureScore kem hDet)
    (fun t => CKAScheme.isSendQuery t = true) (scoreInv_preserved kem hDet leak)
    (failureScore_step kem hDet leak) (fun s => if s.correct then 0 else 1)
    (fun k s _hs => indicator_le_failureScore kem hDet k s) adv q hq _ (scoreInv_init pk sk)

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
    Pr{let x ← CKAScheme.correctnessExp (scheme kem hDet leak) adv}[x = true] = 1
-- ANCHOR_END: correctness
    := by
  rw [OracleComp.prEvent_eq_one_iff]
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
