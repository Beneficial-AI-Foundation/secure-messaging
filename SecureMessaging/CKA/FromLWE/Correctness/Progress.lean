/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Correctness.HonestRounds
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Tape interpreter progress

This module proves that each correctness query preserves the honest phase, advances the game
counters consistently, and consumes tape entries exactly when a send succeeds.
-/

open OracleComp ENNReal

namespace lweCKA

open CorrectnessInternal

private def TapeProgress
    (p : Params)
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (z : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Range q ×
      (CKAScheme.GameState (State p) (Key p) (Message p) ×
        List (SendACoins p × SendBCoins p))) : Prop :=
  honestPhase p z.2.1 ∧ s.tA ≤ z.2.1.tA ∧ s.tB ≤ z.2.1.tB ∧
    min z.2.1.tA z.2.1.tB = min s.tA s.tB +
      (if (q = CKAScheme.ckaCorrectnessSpec.ORecvA ∧
            CKAScheme.validStep s.lastAction .recvA = true) ∨
          (q = CKAScheme.ckaCorrectnessSpec.ORecvB ∧
            CKAScheme.validStep s.lastAction .recvB = true) then 1 else 0) ∧
    max z.2.1.tA z.2.1.tB = max s.tA s.tB +
      (if (q = CKAScheme.ckaCorrectnessSpec.OSendA ∧
            CKAScheme.validStep s.lastAction .sendA = true) ∨
          (q = CKAScheme.ckaCorrectnessSpec.OSendB ∧
            CKAScheme.validStep s.lastAction .sendB = true) then 1 else 0) ∧
    z.2.2 = (if max s.tA s.tB < max z.2.1.tA z.2.1.tB
      then tape.drop 1 else tape) ∧
    (min z.2.1.tA z.2.1.tB = min s.tA s.tB → z.2.1.correct = s.correct)

namespace CorrectnessInternal

theorem correctnessImpl_sendA_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendA).run s =
      (CKAScheme.oracleSendA cka ()).run s := by
  rfl

theorem correctnessImpl_unif_run
    {p : Params} (n : ℕ)
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka (CKAScheme.ckaCorrectnessSpec.OUnif n)).run s =
      (CKAScheme.oracleUnif (State p) (Key p) (Message p) n).run s := by
  rfl

theorem correctnessImpl_recvA_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvA).run s =
      (CKAScheme.oracleRecvA cka ()).run s := by
  rfl

theorem correctnessImpl_sendB_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendB).run s =
      (CKAScheme.oracleSendB cka ()).run s := by
  rfl

theorem correctnessImpl_recvB_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvB).run s =
      (CKAScheme.oracleRecvB cka ()).run s := by
  rfl

end CorrectnessInternal

private theorem mem_support_StateT_liftM_run_iff
    {A S : Type} (mx : ProbComp A) (s : S) (z : A × S) :
    z ∈ support ((liftM mx : StateT S ProbComp A).run s) ↔
      z.1 ∈ support mx ∧ z.2 = s := by
  rw [StateT.run_monadLift, monadLift_self]
  rw [mem_support_bind_iff]
  constructor
  · rintro ⟨x, hx, hz⟩
    have hz' := eq_of_mem_support_pure hz
    subst z
    exact ⟨hx, rfl⟩
  · rintro ⟨hz, hs⟩
    refine ⟨z.1, hz, ?_⟩
    rw [mem_support_pure_iff]
    exact Prod.ext rfl hs

private theorem eq_of_mem_image_support_StateT_liftM_pure
    {A S B : Type} (x : A) (s : S) (f : A × S → B) {z : B}
    (hz : z ∈ f '' support ((liftM (pure x : ProbComp A) :
      StateT S ProbComp A).run s)) :
    z = f (x, s) := by
  rcases hz with ⟨out, hout, rfl⟩
  have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
  exact congrArg f (Prod.ext (eq_of_mem_support_pure hout'.1) hout'.2)

private theorem tapeCorrectnessImpl_sendA_invalid
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hguard : CKAScheme.validStep s.lastAction .sendA = false) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendA).run (s, tape)),
      z = (none, (s, tape)) := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases tape with _ | ⟨coins, rest⟩
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendA_run,
      CKAScheme.oracleSendA, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    rcases hz with ⟨out, hout, rfl⟩
    have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
    rcases out with ⟨first, outer⟩
    rcases hout' with ⟨hfirst, houter⟩
    simp only at hfirst houter
    subst outer
    have hfirst' := eq_of_mem_support_pure hfirst
    subst first
    simp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendA_run,
      CKAScheme.oracleSendA, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    rcases hz with ⟨out, hout, rfl⟩
    have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
    rcases out with ⟨first, outer⟩
    rcases hout' with ⟨hfirst, houter⟩
    simp only at hfirst houter
    subst outer
    have hfirst' := eq_of_mem_support_pure hfirst
    subst first
    simp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]

private theorem tapeCorrectnessImpl_sendA_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendA).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.OSendA s tape z := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases last with _ | action
  · rcases stA <;> rcases stB <;> simp [honestPhase] at hs
    rcases tape with _ | ⟨coins, rest⟩
    · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
        correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
        liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
        pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte,
        Option.map_some, StateT.run_monadLift, monadLift_self, StateT.run_map,
        StateT.run_set, map_pure, Functor.map_map, support_map] at hz
      rcases hz with ⟨out, hout, rfl⟩
      have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
      rcases out with ⟨first, outer⟩
      change Option (Message p × Key p) ×
        CKAScheme.GameState (State p) (Key p) (Message p) at first
      rcases hout' with ⟨hfirst, houter⟩
      simp only at hfirst houter
      subst outer
      dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA] at hfirst
      rw [support_map] at hfirst
      rcases hfirst with ⟨a, ha, rfl⟩
      simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
    · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
        correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
        liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
        pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
        StateT.run_set, map_pure, support_map] at hz
      rcases hz with ⟨out, hout, rfl⟩
      have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
      rcases out with ⟨first, outer⟩
      change Option (Message p × Key p) ×
        CKAScheme.GameState (State p) (Key p) (Message p) at first
      rcases hout' with ⟨hfirst, houter⟩
      simp only at hfirst houter
      subst outer
      have hfirst' := eq_of_mem_support_pure hfirst
      subst first
      simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
  · cases action
    case recvA =>
      rcases stA <;> rcases stB <;> simp [honestPhase] at hs
      rcases tape with _ | ⟨coins, rest⟩
      · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
          correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
          liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
          pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte,
          Option.map_some, StateT.run_monadLift, monadLift_self, StateT.run_map,
          StateT.run_set, map_pure, Functor.map_map, support_map] at hz
        rcases hz with ⟨out, hout, rfl⟩
        have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
        rcases out with ⟨first, outer⟩
        change Option (Message p × Key p) ×
          CKAScheme.GameState (State p) (Key p) (Message p) at first
        rcases hout' with ⟨hfirst, houter⟩
        simp only at hfirst houter
        subst outer
        dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA] at hfirst
        rw [support_map] at hfirst
        rcases hfirst with ⟨a, ha, rfl⟩
        simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
        omega
      · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
          correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
          liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
          pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
          StateT.run_set, map_pure, support_map] at hz
        rcases hz with ⟨out, hout, rfl⟩
        have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
        rcases out with ⟨first, outer⟩
        change Option (Message p × Key p) ×
          CKAScheme.GameState (State p) (Key p) (Message p) at first
        rcases hout' with ⟨hfirst, houter⟩
        simp only at hfirst houter
        subst outer
        have hfirst' := eq_of_mem_support_pure hfirst
        subst first
        simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
        omega
    case sendA =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .sendA) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case sendB =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .sendB) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case recvB =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .recvB) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case challA =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .challA) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case challB =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .challB) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs

private theorem tapeCorrectnessImpl_recvA_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.ORecvA).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.ORecvA s tape z := by
  intro z hz
  change Unit × (CKAScheme.GameState (State p) (Key p) (Message p) ×
    List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  cases hguard : CKAScheme.validStep last .recvA
  case false =>
    rcases tape with _ | ⟨coins, rest⟩
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvA_run,
        CKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvA_run,
        CKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case sendB =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase, exists_and_left, exists_and_right] at hs
        rcases hs with ⟨ht, hmod, ⟨pub, hint, key, hrho, hkey⟩,
          hrhoA, hkeyA⟩
        rcases pub with ⟨pub, hintValue, hrho⟩
        subst rhoB
        subst rhoA
        subst keyA
        rcases tape with _ | ⟨coins, rest⟩
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvA_run,
            CKAScheme.oracleRecvA, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvA, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvA_run,
            CKAScheme.oracleRecvA, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvA, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
      case challB => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

private theorem tapeCorrectnessImpl_sendB_invalid
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hguard : CKAScheme.validStep s.lastAction .sendB = false) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendB).run (s, tape)),
      z = (none, (s, tape)) := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases tape with _ | ⟨coins, rest⟩
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendB_run,
      CKAScheme.oracleSendB, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
    simpa [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendB] using hz'
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendB_run,
      CKAScheme.oracleSendB, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
    simpa [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendB] using hz'

private theorem tapeCorrectnessImpl_sendB_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendB).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.OSendB s tape z := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  cases hguard : CKAScheme.validStep last .sendB
  case false =>
    have hz' := tapeCorrectnessImpl_sendB_invalid p hp χ
      (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
      tape hguard z hz
    subst z
    simpa [TapeProgress, hguard] using hs
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case recvB =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase] at hs
        rcases tape with _ | ⟨coins, rest⟩
        · simp only [tapeCorrectnessImpl, scheme, sendBrleak, bind_pure_comp,
            correctnessImpl_sendB_run, CKAScheme.oracleSendB, CKAScheme.validStep,
            reduceCtorEq, imp_self, implies_true, liftM_map, bind_map_left,
            eraseCoins, StateT.run_bind, StateT.run_get, pure_bind, liftM_pure,
            lt_sup_iff, sup_lt_iff, ↓reduceIte, Option.map_some,
            StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_set,
            map_pure, Functor.map_map, support_map] at hz
          rcases hz with ⟨out, hout, rfl⟩
          have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
          rcases out with ⟨first, outer⟩
          change Option (Message p × Key p) ×
            CKAScheme.GameState (State p) (Key p) (Message p) at first
          rcases hout' with ⟨hfirst, houter⟩
          simp only at hfirst houter
          subst outer
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.OSendB] at hfirst
          rw [support_map] at hfirst
          rcases hfirst with ⟨b, hb, rfl⟩
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
        · simp only [tapeCorrectnessImpl, scheme, sendBrleak, bind_pure_comp,
            correctnessImpl_sendB_run, CKAScheme.oracleSendB, CKAScheme.validStep,
            reduceCtorEq, imp_self, implies_true, liftM_map, bind_map_left,
            eraseCoins, StateT.run_bind, StateT.run_get, pure_bind, liftM_pure,
            lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map, StateT.run_set,
            map_pure, support_map] at hz
          rcases hz with ⟨out, hout, rfl⟩
          have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
          rcases out with ⟨first, outer⟩
          change Option (Message p × Key p) ×
            CKAScheme.GameState (State p) (Key p) (Message p) at first
          rcases hout' with ⟨hfirst, houter⟩
          simp only at hfirst houter
          subst outer
          have hfirst' := eq_of_mem_support_pure hfirst
          subst first
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
      all_goals simp [CKAScheme.validStep] at hguard

private theorem tapeCorrectnessImpl_recvB_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.ORecvB).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.ORecvB s tape z := by
  intro z hz
  change Unit × (CKAScheme.GameState (State p) (Key p) (Message p) ×
    List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  cases hguard : CKAScheme.validStep last .recvB
  case false =>
    rcases tape with _ | ⟨coins, rest⟩
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvB_run,
        CKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvB_run,
        CKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case sendA =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase, exists_and_left, exists_and_right] at hs
        rcases hs with ⟨ht, hmod, ⟨pub, hint, key, hrho, hkey⟩,
          hrhoB, hkeyB⟩
        rcases pub with ⟨pub, hintValue, hrho⟩
        subst rhoA
        subst rhoB
        subst keyB
        rcases tape with _ | ⟨coins, rest⟩
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvB_run,
            CKAScheme.oracleRecvB, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvB, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvB_run,
            CKAScheme.oracleRecvB, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvB, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
      case challA => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

/-- Each query preserves `honestPhase` and updates the counters according to its send or receive
result. -/
theorem tapeCorrectnessImpl_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ q).run (s, tape)),
      honestPhase p z.2.1 ∧ s.tA ≤ z.2.1.tA ∧ s.tB ≤ z.2.1.tB ∧
      min z.2.1.tA z.2.1.tB = min s.tA s.tB +
        (if (q = CKAScheme.ckaCorrectnessSpec.ORecvA ∧
              CKAScheme.validStep s.lastAction .recvA = true) ∨
            (q = CKAScheme.ckaCorrectnessSpec.ORecvB ∧
              CKAScheme.validStep s.lastAction .recvB = true) then 1 else 0) ∧
      max z.2.1.tA z.2.1.tB = max s.tA s.tB +
        (if (q = CKAScheme.ckaCorrectnessSpec.OSendA ∧
              CKAScheme.validStep s.lastAction .sendA = true) ∨
            (q = CKAScheme.ckaCorrectnessSpec.OSendB ∧
              CKAScheme.validStep s.lastAction .sendB = true) then 1 else 0) ∧
      z.2.2 = (if max s.tA s.tB < max z.2.1.tA z.2.1.tB
        then tape.drop 1 else tape) ∧
      (min z.2.1.tA z.2.1.tB = min s.tA s.tB → z.2.1.correct = s.correct) := by
  intro z hz
  change TapeProgress p q s tape z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  match q with
  | CKAScheme.ckaCorrectnessSpec.OUnif n =>
      rcases tape with _ | ⟨coins, rest⟩
      · simp only [tapeCorrectnessImpl, bind_pure_comp, lt_sup_iff, sup_lt_iff,
          StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_map, StateT.run_set, map_pure,
          Functor.map_map, support_map, Set.mem_image, Prod.exists] at hz
        rcases hz with ⟨a, b, hab, rfl⟩
        have hb : b = CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB := by
          rw [correctnessImpl_unif_run] at hab
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.OUnif] at a hab
          simp only [CKAScheme.oracleUnif, PFunctor.Handler.liftTarget_apply,
            PFunctor.selfMonomial_B, QueryImpl.ofLift_apply, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, support_map, support_liftM,
            OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
            Set.image_univ] at hab
          rcases hab with ⟨_, h⟩
          exact (congrArg Prod.snd h).symm
        subst b
        simpa [TapeProgress] using hs
      · simp only [tapeCorrectnessImpl, bind_pure_comp, lt_sup_iff, sup_lt_iff,
          StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_map, StateT.run_set, map_pure,
          Functor.map_map, support_map, Set.mem_image, Prod.exists] at hz
        rcases hz with ⟨a, b, hab, rfl⟩
        have hb : b = CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB := by
          rw [correctnessImpl_unif_run] at hab
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.OUnif] at a hab
          simp only [CKAScheme.oracleUnif, PFunctor.Handler.liftTarget_apply,
            PFunctor.selfMonomial_B, QueryImpl.ofLift_apply, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, support_map, support_liftM,
            OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
            Set.image_univ] at hab
          rcases hab with ⟨_, h⟩
          exact (congrArg Prod.snd h).symm
        subst b
        simpa [TapeProgress] using hs
  | CKAScheme.ckaCorrectnessSpec.OSendA =>
      exact tapeCorrectnessImpl_sendA_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz
  | CKAScheme.ckaCorrectnessSpec.ORecvA =>
      exact tapeCorrectnessImpl_recvA_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz
  | CKAScheme.ckaCorrectnessSpec.OSendB =>
      exact tapeCorrectnessImpl_sendB_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz
  | CKAScheme.ckaCorrectnessSpec.ORecvB =>
      exact tapeCorrectnessImpl_recvB_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz

namespace CorrectnessInternal

theorem correctnessImpl_preserves_honestPhase
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    QueryImpl.PreservesInv
      (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)) (honestPhase p) := by
  intro q s hs z hz
  have hz' : (z.1, (z.2, ([] : List (SendACoins p × SendBCoins p)))) ∈
      support ((tapeCorrectnessImpl p hp χ q).run
        (s, ([] : List (SendACoins p × SendBCoins p)))) := by
    simpa [tapeCorrectnessImpl] using hz
  exact (tapeCorrectnessImpl_progress p hp χ q s [] hs _ hz').1

end CorrectnessInternal

end lweCKA
