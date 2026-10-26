/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Correctness.Progress
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Tape interpreter distribution equivalence

This module proves that sampling send coins in advance preserves the joint distribution of the
adversary result and final correctness-game state.
-/

open OracleComp ENNReal

namespace lweCKA

open CorrectnessInternal

private theorem tapeCorrectnessImpl_unif_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (n : ℕ)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) :
    (tapeCorrectnessImpl p hp χ
      (CKAScheme.ckaCorrectnessSpec.OUnif n)).run (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          (CKAScheme.ckaCorrectnessSpec.OUnif n)).run s := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_unif_run,
      CKAScheme.oracleUnif] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OUnif] <;>
    simp

private theorem tapeCorrectnessImpl_sendA_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendA = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (s, tape) = pure (none, (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_sendA_run,
      CKAScheme.oracleSendA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendA] <;>
    simp

private theorem tapeCorrectnessImpl_sendB_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendB = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (s, tape) = pure (none, (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_sendB_run,
      CKAScheme.oracleSendB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendB] <;>
    simp

private theorem tapeCorrectnessImpl_recvA_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvA = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (s, tape) = pure ((), (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_recvA_run,
      CKAScheme.oracleRecvA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.ORecvA] <;>
    simp

private theorem tapeCorrectnessImpl_recvB_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvB = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (s, tape) = pure ((), (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_recvB_run,
      CKAScheme.oracleRecvB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.ORecvB] <;>
    simp

private theorem tapeCorrectnessImpl_recvA_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.ORecvA).run s := by
  cases hguard : CKAScheme.validStep s.lastAction .recvA
  case false =>
    rw [tapeCorrectnessImpl_recvA_invalid_run p hp χ s tape hguard]
    simp [correctnessImpl_recvA_run, CKAScheme.oracleRecvA, hguard]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA]
    simp
  case true =>
    rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
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
        cases tape <;>
          simp [tapeCorrectnessImpl, correctnessImpl_recvA_run,
            CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recvA] <;>
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.ORecvA] <;>
          simp
        all_goals omega
      case challB => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

private theorem tapeCorrectnessImpl_recvB_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.ORecvB).run s := by
  cases hguard : CKAScheme.validStep s.lastAction .recvB
  case false =>
    rw [tapeCorrectnessImpl_recvB_invalid_run p hp χ s tape hguard]
    simp [correctnessImpl_recvB_run, CKAScheme.oracleRecvB, hguard]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB]
    simp
  case true =>
    rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
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
        cases tape <;>
          simp [tapeCorrectnessImpl, correctnessImpl_recvB_run,
            CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recvB] <;>
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.ORecvB] <;>
          simp
        all_goals omega
      case challA => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

private theorem evalDist_sample_tape_query_bind_passthrough
    {ι : Type} {spec : OracleSpec ι} {σ θ α : Type}
    (sample : ProbComp θ)
    (impl : QueryImpl spec (StateT (σ × θ) ProbComp))
    (baseMatrix : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (himpl : ∀ param ∈ support sample, (impl t).run (s, param) =
      (fun z => (z.1, (z.2, param))) <$> (baseMatrix t).run s)
    (hpres : ∀ z, z ∈ support ((baseMatrix t).run s) → Inv z.2)
    (hih : ∀ (u : spec.Range t) (s' : σ), Inv s' →
      𝒟[do
        let param ← sample
        let (out, s'', _) ← (simulateQ impl (k u)).run (s', param)
        return (out, s'')] =
      𝒟[(simulateQ baseMatrix (k u)).run s']) :
    𝒟[do
      let param ← sample
      let (out, s', _) ←
        (simulateQ impl (OracleSpec.query t >>= k)).run (s, param)
      return (out, s')] =
      𝒟[(simulateQ baseMatrix (OracleSpec.query t >>= k)).run s] := by
  apply evalDist_ext
  intro y
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
    OracleQuery.input_query, StateT.run_bind, bind_assoc]
  have halign : Pr[= y | do
        let param ← sample
        let step ← (impl t).run (s, param)
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1)] =
      Pr[= y | do
        let param ← sample
        let step ← (baseMatrix t).run s
        let out ← (simulateQ impl (k step.1)).run (step.2, param)
        pure (out.1, out.2.1)] := by
    refine probOutput_bind_congr ?_
    intro param hparam
    rw [himpl param hparam, bind_map_left]
  rw [halign]
  rw [probOutput_bind_bind_swap (mx := sample) (my := (baseMatrix t).run s)
    (f := fun param step => do
      let out ← (simulateQ impl (k step.1)).run (step.2, param)
      pure (out.1, out.2.1)) (z := y)]
  refine probOutput_bind_congr ?_
  intro step hstep
  exact evalDist_ext_iff.mp (hih step.1 step.2 (hpres step hstep)) y

private theorem evalDist_bind_of_evalDist_eq
    {A B : Type} {mx my : ProbComp A} (h : 𝒟[mx] = 𝒟[my])
    (f : A → ProbComp B) : 𝒟[mx >>= f] = 𝒟[my >>= f] := by
  rw [evalDist_bind, evalDist_bind, h]

private theorem evalDist_head_tail_query_bind_consume
    {ι : Type} {spec : OracleSpec ι} {σ η θ α : Type}
    (head : ProbComp η) (tail : ProbComp θ) (combine : η → θ → θ)
    (impl : QueryImpl spec (StateT (σ × θ) ProbComp))
    (baseMatrix : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (hstep : ∀ rest, 𝒟[do
        let h ← head
        (impl t).run (s, combine h rest)] =
      𝒟[(fun z => (z.1, (z.2, rest))) <$> (baseMatrix t).run s])
    (hpres : ∀ z, z ∈ support ((baseMatrix t).run s) → Inv z.2)
    (hih : ∀ (u : spec.Range t) (s' : σ), Inv s' →
      𝒟[do
        let rest ← tail
        let (out, s'', _) ← (simulateQ impl (k u)).run (s', rest)
        return (out, s'')] =
      𝒟[(simulateQ baseMatrix (k u)).run s']) :
    𝒟[do
      let h ← head
      let rest ← tail
      let (out, s', _) ←
        (simulateQ impl (OracleSpec.query t >>= k)).run (s, combine h rest)
      return (out, s')] =
      𝒟[(simulateQ baseMatrix (OracleSpec.query t >>= k)).run s] := by
  apply evalDist_ext
  intro y
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
    OracleQuery.input_query, StateT.run_bind, bind_assoc]
  rw [probOutput_bind_bind_swap (mx := head) (my := tail)
    (f := fun h rest => do
      let step ← (impl t).run (s, combine h rest)
      let out ← (simulateQ impl (k step.1)).run step.2
      pure (out.1, out.2.1)) (z := y)]
  have halign : Pr[= y | do
        let rest ← tail
        let h ← head
        let step ← (impl t).run (s, combine h rest)
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1)] =
      Pr[= y | do
        let rest ← tail
        let step ← (fun z : spec.Range t × σ => (z.1, (z.2, rest))) <$> (baseMatrix t).run s
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1)] := by
    refine probOutput_bind_congr' tail y fun rest => ?_
    simpa only [bind_assoc] using evalDist_ext_iff.mp
      (evalDist_bind_of_evalDist_eq (hstep rest)
      (fun step => do
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1))) y
  rw [halign]
  simp only [bind_map_left]
  rw [probOutput_bind_bind_swap (mx := tail) (my := (baseMatrix t).run s)
    (f := fun rest step => do
      let out ← (simulateQ impl (k step.1)).run (step.2, rest)
      pure (out.1, out.2.1)) (z := y)]
  refine probOutput_bind_congr ?_
  intro step hstep'
  exact evalDist_ext_iff.mp (hih step.1 step.2 (hpres step hstep')) y

private theorem correctnessImpl_sendA_run_for_head (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendA).run s =
      (CKAScheme.oracleSendA cka ()).run s := by
  rfl

private theorem evalDist_tapeCorrectnessImpl_sendA_head
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (rest : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s)
    (hg : CKAScheme.validStep s.lastAction .sendA = true) :
    𝒟[do
      let a ← sampleSendACoins p χ
      let b ← sampleSendBCoins p χ
      (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
        (s, (a, b) :: rest)] =
    𝒟[do
      let z ← (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
        CKAScheme.ckaCorrectnessSpec.OSendA).run s
      pure (z.1, (z.2, rest))] := by
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases last with _ | (_ | _ | _ | _ | _ | _) <;>
    simp [CKAScheme.validStep] at hg
  all_goals
    rcases stA <;> rcases stB <;> simp [honestPhase] at hs
  all_goals
    simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
      correctnessImpl_sendA_run_for_head p, CKAScheme.oracleSendA,
      CKAScheme.validStep,
      liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
      StateT.run_set, map_pure, liftM_bind, Option.map_some, StateT.run_monadLift,
      monadLift_self, Functor.map_map]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
    simp only [pure_bind, bind_map_left]
    simp only [liftM_pure, map_pure]
    have hab : tA = tB := by omega
    subst tB
    simp only [lt_add_iff_pos_right, Order.lt_one_iff, and_self, lt_self_iff_false,
      or_false, ↓reduceIte, bind_pure_comp, liftM_map]
    simp only [← liftM_bind, ← liftM_map]
    simp only [map_eq_bind_pure_comp]
    apply evalDist_bind_congr'
    intro a
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (sampleSendBCoins p χ) (probFailure_eq_zero) _

private theorem correctnessImpl_sendB_run_for_head (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendB).run s =
      (CKAScheme.oracleSendB cka ()).run s := by
  rfl

private theorem evalDist_tapeCorrectnessImpl_sendB_head
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (rest : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s)
    (hg : CKAScheme.validStep s.lastAction .sendB = true) :
    𝒟[do
      let a ← sampleSendACoins p χ
      let b ← sampleSendBCoins p χ
      (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
        (s, (a, b) :: rest)] =
    𝒟[do
      let z ← (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
        CKAScheme.ckaCorrectnessSpec.OSendB).run s
      pure (z.1, (z.2, rest))] := by
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases last with _ | (_ | _ | _ | _ | _ | _) <;>
    simp [CKAScheme.validStep] at hg
  all_goals
    rcases stA <;> rcases stB <;> simp [honestPhase] at hs
  all_goals
    simp only [tapeCorrectnessImpl, scheme, sendBrleak, bind_pure_comp,
      correctnessImpl_sendB_run_for_head p, CKAScheme.oracleSendB,
      CKAScheme.validStep,
      liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
      StateT.run_set, map_pure, liftM_bind, Option.map_some, StateT.run_monadLift,
      monadLift_self, Functor.map_map]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB]
    simp only [pure_bind, bind_map_left]
    simp only [liftM_pure, map_pure]
    have hab : tA = tB := by omega
    subst tB
    simp only [lt_self_iff_false, and_self, lt_add_iff_pos_right, Order.lt_one_iff,
      or_true, ↓reduceIte, bind_pure_comp, liftM_map]
    simp only [← liftM_bind, ← liftM_map]
    simp only [map_eq_bind_pure_comp]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (sampleSendACoins p χ) (probFailure_eq_zero) _

private theorem tapeCorrectnessImpl_sendA_invalid_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendA = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.OSendA).run s := by
  rw [tapeCorrectnessImpl_sendA_invalid_run p hp χ s tape hg]
  simp [correctnessImpl_sendA_run, CKAScheme.oracleSendA, hg]
  dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
  simp

private theorem tapeCorrectnessImpl_sendB_invalid_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendB = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.OSendB).run s := by
  rw [tapeCorrectnessImpl_sendB_invalid_run p hp χ s tape hg]
  simp [correctnessImpl_sendB_run, CKAScheme.oracleSendB, hg]
  dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB]
  simp

/-- Sampling the send tape in advance preserves the joint distribution of the adversary result and
final game state. -/
theorem evalDist_tapeCorrectnessRun
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    {α : Type}
    (oa : OracleComp (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)) α)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (hs : honestPhase p s) (N : ℕ) :
    𝒟[do
      let tape ← OracleComp.drawList (do
        let a ← sampleSendACoins p χ
        let b ← sampleSendBCoins p χ
        return (a, b)) N
      let (out, s', _) ← (simulateQ (tapeCorrectnessImpl p hp χ) oa).run (s, tape)
      return (out, s')] =
      𝒟[(simulateQ (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)) oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s N with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (OracleComp.drawList (do
          let a ← sampleSendACoins p χ
          let b ← sampleSendBCoins p χ
          return (a, b)) N)
        (OracleComp.probFailure_drawList _ _) _
  | query_bind t k ih =>
      match t with
      | CKAScheme.ckaCorrectnessSpec.OUnif n =>
          apply evalDist_sample_tape_query_bind_passthrough
            (Inv := honestPhase p)
          · intro tape _
            exact tapeCorrectnessImpl_unif_run_eq_map p hp χ n s tape
          · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
          · intro u s' hs'
            exact ih u s' hs' N
      | CKAScheme.ckaCorrectnessSpec.OSendA =>
          cases hg : CKAScheme.validStep s.lastAction .sendA
          case false =>
            apply evalDist_sample_tape_query_bind_passthrough
              (Inv := honestPhase p)
            · intro tape _
              exact tapeCorrectnessImpl_sendA_invalid_run_eq_map p hp χ s tape hg
            · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
            · intro u s' hs'
              exact ih u s' hs' N
          case true =>
            cases N with
            | zero =>
                apply evalDist_sample_tape_query_bind_passthrough
                  (Inv := honestPhase p)
                · intro tape htape
                  have hlen := length_of_mem_support_drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) 0 tape htape
                  cases tape with
                  | nil => simp [tapeCorrectnessImpl]
                  | cons _ _ => simp at hlen
                · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
                · intro u s' hs'
                  exact ih u s' hs' 0
            | succ N =>
                rw [OracleComp.drawList]
                simp only [bind_assoc, pure_bind]
                have hrun := evalDist_head_tail_query_bind_consume
                  (head := do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b))
                  (tail := OracleComp.drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) N)
                  (combine := List.cons) (impl := tapeCorrectnessImpl p hp χ)
                  (baseMatrix := CKAScheme.ckaCorrectnessImpl (scheme p hp χ))
                  (Inv := honestPhase p) (s := s)
                  (t := CKAScheme.ckaCorrectnessSpec.OSendA) (k := k)
                  (hstep := fun rest => by
                    simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp,
                      Function.comp_def] using
                      evalDist_tapeCorrectnessImpl_sendA_head p hp χ s rest hs hg)
                  (hpres := correctnessImpl_preserves_honestPhase p hp χ _ s hs)
                  (hih := fun u s' hs' => ih u s' hs' N)
                simpa only [bind_assoc, pure_bind] using hrun
      | CKAScheme.ckaCorrectnessSpec.ORecvA =>
          apply evalDist_sample_tape_query_bind_passthrough
            (Inv := honestPhase p)
          · intro tape _
            exact tapeCorrectnessImpl_recvA_run_eq_map p hp χ s tape hs
          · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
          · intro u s' hs'
            exact ih u s' hs' N
      | CKAScheme.ckaCorrectnessSpec.OSendB =>
          cases hg : CKAScheme.validStep s.lastAction .sendB
          case false =>
            apply evalDist_sample_tape_query_bind_passthrough
              (Inv := honestPhase p)
            · intro tape _
              exact tapeCorrectnessImpl_sendB_invalid_run_eq_map p hp χ s tape hg
            · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
            · intro u s' hs'
              exact ih u s' hs' N
          case true =>
            cases N with
            | zero =>
                apply evalDist_sample_tape_query_bind_passthrough
                  (Inv := honestPhase p)
                · intro tape htape
                  have hlen := length_of_mem_support_drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) 0 tape htape
                  cases tape with
                  | nil => simp [tapeCorrectnessImpl]
                  | cons _ _ => simp at hlen
                · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
                · intro u s' hs'
                  exact ih u s' hs' 0
            | succ N =>
                rw [OracleComp.drawList]
                simp only [bind_assoc, pure_bind]
                have hrun := evalDist_head_tail_query_bind_consume
                  (head := do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b))
                  (tail := OracleComp.drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) N)
                  (combine := List.cons) (impl := tapeCorrectnessImpl p hp χ)
                  (baseMatrix := CKAScheme.ckaCorrectnessImpl (scheme p hp χ))
                  (Inv := honestPhase p) (s := s)
                  (t := CKAScheme.ckaCorrectnessSpec.OSendB) (k := k)
                  (hstep := fun rest => by
                    simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp,
                      Function.comp_def] using
                      evalDist_tapeCorrectnessImpl_sendB_head p hp χ s rest hs hg)
                  (hpres := correctnessImpl_preserves_honestPhase p hp χ _ s hs)
                  (hih := fun u s' hs' => ih u s' hs' N)
                simpa only [bind_assoc, pure_bind] using hrun
      | CKAScheme.ckaCorrectnessSpec.ORecvB =>
          apply evalDist_sample_tape_query_bind_passthrough
            (Inv := honestPhase p)
          · intro tape _
            exact tapeCorrectnessImpl_recvB_run_eq_map p hp χ s tape hs
          · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
          · intro u s' hs'
            exact ih u s' hs' N

end lweCKA
