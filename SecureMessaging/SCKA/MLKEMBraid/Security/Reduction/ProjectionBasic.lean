/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Simulator
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Basic
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import ToVCVio.OracleComp.EvalDist

/-!
# Simulator views and elementary query projections

The view masks the selected secret positions, relabels its epoch key and erases its ghost
records. Step comparisons retain the joint response and successor state, including answers
dropped by exposure stopping. No analytical bad-event estimate is needed here.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- An output key with the key of the selected epoch `e` replaced by `v`. -/
def relabelKey (e : ℕ) (v : P.EpochKey) : Option (ℕ × P.EpochKey) → Option (ℕ × P.EpochKey)
  | none => none
  | some (t, k) => some (t, if t = e then v else k)

/-- A key table with the key of the selected epoch `e` replaced by `v`. -/
def relabel (e : ℕ) (v : P.EpochKey) (keys : ℕ → Option P.EpochKey) : ℕ → Option P.EpochKey :=
  fun t => if t = e then (keys t).map fun _ => v else keys t

/-- Ghost records with the records of the selected epoch `e` erased. -/
def eraseAt (e : ℕ) (T : ℕ → EpochTranscript P) : ℕ → EpochTranscript P :=
  fun t => if t = e then { keypair := none, encaps1 := none } else T t

/-- The simulator game of a trace game: masked states and relabelled keys at `e`. -/
def simGameOf (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) : SimGame P :=
  { stA := maskState e g.stA, stB := maskState e g.stB
    keyA := relabel e v g.keyA, keyB := relabel e v g.keyB
    msgA := g.msgA, msgB := g.msgB, nA := g.nA, nB := g.nB
    exposed := g.exposed, challenged := g.challenged }

/-- The simulator state of a trace state. -/
def simOf (e : ℕ) (v : P.EpochKey) (s : TraceState P) : SimState P :=
  { game := simGameOf e v s.game, transcript := eraseAt e s.transcript }

section SimView

/-- The simulator's party state is the masked trace party state. -/
theorem simGameOf_stateAt (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit)
    (party : Bool) : (simGameOf e v g).stateAt party = maskState e (g.stateAt party) := by
  cases party <;> rfl

/-- The game of the simulator view. -/
theorem simOf_game (e : ℕ) (v : P.EpochKey) (s : TraceState P) :
    (simOf e v s).game = simGameOf e v s.game := rfl

/-- The records of the simulator view. -/
theorem simOf_transcript (e : ℕ) (v : P.EpochKey) (s : TraceState P) :
    (simOf e v s).transcript = eraseAt e s.transcript := rfl

/-- The exposed epochs of the simulator view. -/
theorem simGameOf_exposed (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) :
    (simGameOf e v g).exposed = g.exposed := rfl

/-- The challenged epochs of the simulator view. -/
theorem simGameOf_challenged (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) :
    (simGameOf e v g).challenged = g.challenged := rfl

/-- Relabelling commutes with recording a key. -/
theorem relabel_update (e : ℕ) (v : P.EpochKey) (keys : ℕ → Option P.EpochKey) (t : ℕ)
    (k : P.EpochKey) :
    relabel e v (Function.update keys t (some k)) =
      Function.update (relabel e v keys) t (some (if t = e then v else k)) := by
  funext u
  by_cases hu : u = t
  · subst hu
    by_cases he : u = e <;> simp [relabel, he]
  · simp [relabel, hu]

/-- Relabelling keeps the epoch of an output key. -/
theorem relabelKey_map_fst (e : ℕ) (v : P.EpochKey) (key : Option (ℕ × P.EpochKey)) :
    (relabelKey e v key).map Prod.fst = key.map Prod.fst := by
  rcases key with _ | ⟨t, k⟩ <;> rfl

/-- Erasing `e` commutes with recording a key pair of another epoch. -/
theorem eraseAt_update_keypair (e t : ℕ) (ht : t ≠ e) (T : ℕ → EpochTranscript P)
    (x : P.PK × P.SK) :
    Function.update (eraseAt e T) t { (eraseAt e T t) with keypair := some x } =
      eraseAt e (Function.update T t { (T t) with keypair := some x }) := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp [eraseAt, ht]
  · simp [eraseAt, hu]

/-- Erasing `e` commutes with recording a first-stage encapsulation of another epoch. -/
theorem eraseAt_update_encaps1 (e t : ℕ) (ht : t ≠ e) (T : ℕ → EpochTranscript P)
    (x : P.inc.St × P.inc.C₁ × P.K) :
    Function.update (eraseAt e T) t { (eraseAt e T t) with encaps1 := some x } =
      eraseAt e (Function.update T t { (T t) with encaps1 := some x }) := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp [eraseAt, ht]
  · simp [eraseAt, hu]

/-- Erasing `e` forgets every record of `e`. -/
theorem eraseAt_update_self (e : ℕ) (T : ℕ → EpochTranscript P) (r : EpochTranscript P) :
    eraseAt e (Function.update T e r) = eraseAt e T := by
  funext u
  by_cases hu : u = e
  · simp [eraseAt, hu]
  · simp [eraseAt, hu]

/-- `maskState` keeps an ordinary state. -/
theorem maskState_eq_inl {e : ℕ} {st st' : State P Unit} (h : maskState e st = .inl st') :
    st' = st := by
  cases st <;> simp only [maskState] at h <;> (try split_ifs at h) <;> simp_all

/-- The exposure footprint of a masked view is that of the state. -/
theorem simVuln_maskState (e : ℕ) (st : State P Unit) : simVuln e (maskState e st) = vuln st := by
  cases st <;> simp only [maskState] <;> (try split_ifs) <;> simp_all [simVuln, vuln, State.epoch]

/-- A masked state sends its next chunk deterministically. -/
theorem send_masked (hMac : P.Mac = Unit) {e : ℕ} {st : State P Unit} {m : Masked P}
    (hm : maskState e st = .inr m) :
    ∃ R : SendResult P Unit, MLKEMBraid.send P (auth P hMac) st = pure R ∧
      R.msg = (maskedSend e m).1 ∧ R.sendingEpoch = e - 1 ∧ R.outputKey = none ∧
      maskState e R.state = .inr (maskedSend e m).2 := by
  cases st with
  | keysUnsampled t a => simp [maskState] at hm
  | noHeaderReceived t a dec => simp [maskState] at hm
  | headerReceived t a hdr dec => simp [maskState] at hm
  | ct2Sampled t a enc => simp [maskState] at hm
  | keysSampled t a sk vec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | headerSent t a sk dec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ct1Received t a sk ct1 enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ekSentCt1Received t a sk ct1 dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ct1Sampled t a hdr es ct1 enc dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ekReceivedCt1Sampled t a es ct1 hdr vec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ct1Acknowledged t a hdr es ct1 dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm

/-- Lifted uniform randomness keeps any state. -/
theorem liftTarget_unif_run {σ : Type} (t : ℕ) (s : σ) :
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)) t).run s =
      (fun a => (a, s)) <$> (QueryImpl.ofLift unifSpec ProbComp) t := by
  simp [StateT.run_monadLift, map_eq_bind_pure_comp]

variable [DecidableEq P.EpochKey]

/-- The simulator game of a trace send update. -/
theorem simGameOf_sendUpdate (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit)
    (party : Bool) (r : SendResult P Unit) (X : Finset ℕ) :
    simGameOf e v { sendUpdate g party r with exposed := X } =
      { (simGameOf e v g).sendUpdate party (relabelKey e v r.outputKey) r.msg r.sendingEpoch
          (maskState e r.state) with exposed := X } := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨t, k⟩ <;>
    simp [simGameOf, sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hk,
      SimGame.sendUpdate, keyUpdate, relabelKey, relabel_update]

/-- The simulator game of a trace receive update. -/
theorem simGameOf_recvUpdate (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit)
    (party : Bool) (tsnd trcv : ℕ) (key : Option (ℕ × P.EpochKey)) (st : State P Unit) :
    simGameOf e v (recvUpdate g party tsnd ⟨trcv, key, st⟩ trcv) =
      (simGameOf e v g).recvUpdate party (relabelKey e v key) (maskState e st) := by
  cases party <;> rcases key with _ | ⟨t, k⟩ <;>
    simp [simGameOf, recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate,
      SimGame.recvUpdate, keyUpdate, relabelKey, relabel_update]

end SimView

/-- One simulator query from the simulator view of a trace state agrees with one trace query, up
to answers dropped because `e` became exposed. -/
def StepSim (e : ℕ) (v : P.EpochKey) {α : Type} (oS : ProbComp (α × SimState P))
    (oT : ProbComp (α × TraceState P)) : Prop :=
  ((fun w => (if simStop e w.2 then none else some w.1, w.2)) <$> oS) =ᵈ
      (fun w => (if targetStop e w.2 then none else some w.1, simOf e v w.2)) <$> oT

section Step

variable {e : ℕ} {v : P.EpochKey}

/-- Exact agreement gives `StepSim`. -/
theorem StepSim.of_eq {α : Type} {oS : ProbComp (α × SimState P)}
    {oT : ProbComp (α × TraceState P)} (h : oS =ᵈ Prod.map id (simOf e v) <$> oT) :
    StepSim e v oS oT := by
  unfold StepSim
  refine (h.map _).trans ?_
  rw [Functor.map_map]
  exact .rfl

/-- A deterministic step that exposes `e` on both sides gives `StepSim`. -/
theorem StepSim.pure_stop {α : Type} (a b : α) (s' : TraceState P)
    (hstop : targetStop e s' = true) :
    StepSim e v (pure (a, simOf e v s')) (pure (b, s')) := by
  have hS : simStop e (simOf e v s') = true := hstop
  unfold StepSim
  simp [hS, hstop]

/-- `StepSim` combines over a sum of oracle implementations. -/
theorem stepSim_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (Inv : TraceState P → Prop)
    {i₁ : QueryImpl spec₁ (StateT (SimState P) ProbComp)}
    {i₂ : QueryImpl spec₂ (StateT (SimState P) ProbComp)}
    {j₁ : QueryImpl spec₁ (StateT (TraceState P) ProbComp)}
    {j₂ : QueryImpl spec₂ (StateT (TraceState P) ProbComp)}
    (h₁ : ∀ t s, Inv s → StepSim e v ((i₁ t).run (simOf e v s)) ((j₁ t).run s))
    (h₂ : ∀ t s, Inv s → StepSim e v ((i₂ t).run (simOf e v s)) ((j₂ t).run s)) :
    ∀ t s, Inv s → StepSim e v (((i₁ + i₂) t).run (simOf e v s)) (((j₁ + j₂) t).run s)
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

/-- `StepSim` is the per-query hypothesis of the stopped state-map comparison. -/
theorem stopOnState_simOf {ι : Type} {spec : OracleSpec ι}
    (S : QueryImpl spec (StateT (SimState P) ProbComp))
    (G : QueryImpl spec (StateT (TraceState P) ProbComp)) (q : spec.Domain) (s : TraceState P)
    (h : StepSim e v ((S q).run (simOf e v s)) ((G q).run s)) :
    ((stopOnState S (simStop e) q).run).run (simOf e v s) =ᵈ
        Prod.map id (simOf e v) <$> ((stopOnState G (targetStop e) q).run).run s := by
  rw [OracleComp.stopOnState_run_eq_map, OracleComp.stopOnState_run_eq_map, Functor.map_map]
  exact h

/-- Exact agreement survives a map of the answers. -/
theorem exact_mapAnswer {α β : Type} {oS : ProbComp (α × SimState P)}
    {oT : ProbComp (α × TraceState P)} (f : α → β)
    (h : oS =ᵈ Prod.map id (simOf e v) <$> oT) :
    ((fun w => (f w.1, w.2)) <$> oS) =ᵈ
        Prod.map id (simOf e v) <$> ((fun w => (f w.1, w.2)) <$> oT) := by
  refine (h.map _).trans ?_
  rw [Functor.map_map, Functor.map_map]
  exact .rfl

end Step

section Queries

variable {e : ℕ} {v : P.EpochKey}

/-- The uniform-randomness query of the trace game. -/
theorem traceUnif_run (t : ℕ) (s : TraceState P) :
    (traceUnif P t).run s = (fun a => (a, s)) <$> (QueryImpl.ofLift unifSpec ProbComp) t := by
  rw [show traceUnif P t = liftGame (SCKAScheme.oracleUnif (State P Unit) (State P Unit)
      P.EpochKey (Message P.Sym) t) from rfl, liftGame_run, SCKAScheme.oracleUnif,
    liftTarget_unif_run, Functor.map_map]

/-- The uniform-randomness query agrees. -/
theorem unif_step (t : ℕ) (s : TraceState P) :
    StepSim e v ((simUnif P t).run (simOf e v s)) ((traceUnif P t).run s) :=
  StepSim.of_eq (by
    rw [show (simUnif P t).run (simOf e v s) = _ from liftTarget_unif_run t (simOf e v s),
      traceUnif_run, Functor.map_map]
    rfl)

/-- A corruption of A on the game state. -/
theorem oracleCorruptA_run (V : State P Unit → Finset ℕ) (g : MLKEMBraid.GameState P Unit) :
    (SCKAScheme.oracleCorruptA V (State P Unit) P.EpochKey (Message P.Sym) ()).run g =
      if V g.stA ∩ g.challenged ≠ ∅ then pure (none, g)
      else pure (some g.stA, { g with exposed := g.exposed ∪ V g.stA }) :=
  SCKAScheme.oracleCorruptA_run V g

/-- A corruption of B on the game state. -/
theorem oracleCorruptB_run (V : State P Unit → Finset ℕ) (g : MLKEMBraid.GameState P Unit) :
    (SCKAScheme.oracleCorruptB V (State P Unit) P.EpochKey (Message P.Sym) ()).run g =
      if V g.stB ∩ g.challenged ≠ ∅ then pure (none, g)
      else pure (some g.stB, { g with exposed := g.exposed ∪ V g.stB }) :=
  SCKAScheme.oracleCorruptB_run V g

/-- A corruption of A agrees; a masked state exposes `e`, which stops both runs. -/
theorem corruptA_step (s : TraceState P) :
    StepSim e v ((simCorrupt P e true ()).run (simOf e v s)) ((traceCorruptA P ()).run s) := by
  have hT : (traceCorruptA P ()).run s = (fun z => (z.1, { s with game := z.2 })) <$>
      (SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym) ()).run
        s.game := rfl
  have hS : (simCorrupt P e true ()).run (simOf e v s) =
      if simVuln e (maskState e s.game.stA) ∩ s.game.challenged ≠ ∅ then
        pure (none, simOf e v s)
      else pure (unmask (maskState e s.game.stA), { simOf e v s with game :=
        { (simOf e v s).game with
          exposed := s.game.exposed ∪ simVuln e (maskState e s.game.stA) } }) := rfl
  rw [hT, oracleCorruptA_run, hS, simVuln_maskState]
  by_cases hc : vuln s.game.stA ∩ s.game.challenged = ∅
  · rw [ite_eq_right (not_not.mpr hc), ite_eq_right (not_not.mpr hc), map_pure]
    rcases hm : maskState e s.game.stA with st' | m
    · have h := maskState_eq_inl hm
      subst h
      exact StepSim.of_eq (by rw [map_pure]; rfl)
    · have he : vuln s.game.stA = {e} := by
        rw [← simVuln_maskState e s.game.stA, hm]
        rfl
      exact StepSim.pure_stop (s' := { s with game :=
        { s.game with exposed := s.game.exposed ∪ vuln s.game.stA } }) _ _
        (by simp [targetStop, he])
  · rw [ite_eq_left hc, ite_eq_left hc, map_pure]
    exact StepSim.of_eq (by rw [map_pure]; rfl)

/-- A corruption of B agrees; a masked state exposes `e`, which stops both runs. -/
theorem corruptB_step (s : TraceState P) :
    StepSim e v ((simCorrupt P e false ()).run (simOf e v s)) ((traceCorruptB P ()).run s) := by
  have hT : (traceCorruptB P ()).run s = (fun z => (z.1, { s with game := z.2 })) <$>
      (SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym) ()).run
        s.game := rfl
  have hS : (simCorrupt P e false ()).run (simOf e v s) =
      if simVuln e (maskState e s.game.stB) ∩ s.game.challenged ≠ ∅ then
        pure (none, simOf e v s)
      else pure (unmask (maskState e s.game.stB), { simOf e v s with game :=
        { (simOf e v s).game with
          exposed := s.game.exposed ∪ simVuln e (maskState e s.game.stB) } }) := rfl
  rw [hT, oracleCorruptB_run, hS, simVuln_maskState]
  by_cases hc : vuln s.game.stB ∩ s.game.challenged = ∅
  · rw [ite_eq_right (not_not.mpr hc), ite_eq_right (not_not.mpr hc), map_pure]
    rcases hm : maskState e s.game.stB with st' | m
    · have h := maskState_eq_inl hm
      subst h
      exact StepSim.of_eq (by rw [map_pure]; rfl)
    · have he : vuln s.game.stB = {e} := by
        rw [← simVuln_maskState e s.game.stB, hm]
        rfl
      exact StepSim.pure_stop (s' := { s with game :=
        { s.game with exposed := s.game.exposed ∪ vuln s.game.stB } }) _ _
        (by simp [targetStop, he])
  · rw [ite_eq_left hc, ite_eq_left hc, map_pure]
    exact StepSim.of_eq (by rw [map_pure]; rfl)

/-- The available key in the simulator view. -/
theorem simLookup_simGameOf (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) (t : ℕ) :
    simLookup (simGameOf e v g) t =
      if t = e then (lookupKey g t).map (fun _ => v) else lookupKey g t := by
  by_cases ht : t = e
  · subst ht
    cases hA : g.keyA t <;> cases hB : g.keyB t <;>
      simp [simLookup, lookupKey, simGameOf, relabel, hA, hB]
  · simp only [simLookup, lookupKey, simGameOf, relabel, ite_eq_right ht]
    rfl

/-- The challenge query agrees, given the installed value or the key of `e`. -/
theorem challenge_step [SampleableType P.K] [SampleableType P.EpochKey]
    (xo : Option P.EpochKey) (t : ℕ) (s : TraceState P)
    (hxo : ∀ x, xo = some x → x = v)
    (hkey : xo = none → ∀ kk, lookupKey s.game e = some kk → kk = v) :
    StepSim e v
      ((simChallenge P (fun t => if t < e then .uniform else .real) t).run (simOf e v s))
      ((traceChallengeAt P (fun t => if t < e then .uniform else .real) e xo t).run s) := by
  apply StepSim.of_eq
  change simChallenge P _ t (simOf e v s) =ᵈ
      Prod.map id (simOf e v) <$> traceChallengeAt P _ e xo t s
  simp only [simChallenge, traceChallengeAt, simOf_game, simGameOf_exposed,
    simGameOf_challenged, simLookup_simGameOf]
  by_cases hex : t ∈ s.game.exposed ∨ t ∈ s.game.challenged
  · rw [ite_eq_left hex, ite_eq_left hex, map_pure]
    rfl
  · rw [ite_eq_right hex, ite_eq_right hex]
    by_cases ht : t = e
    · subst ht
      rw [ite_eq_left rfl]
      cases hk : lookupKey s.game t with
      | none =>
          simp only [Option.map_none, map_pure]
          rfl
      | some kk =>
          simp only [Option.map_some, lt_irrefl, ite_false]
          cases xo with
          | none =>
              obtain rfl := hkey rfl kk hk
              simp only [challengeValue, map_pure]
              rfl
          | some x =>
              obtain rfl := hxo x rfl
              simp only [↓reduceIte, challengeValue, map_pure]
              rfl
    · rw [ite_eq_right ht]
      cases hk : lookupKey s.game t with
      | none =>
          simp only [map_pure]
          rfl
      | some kk =>
          cases xo with
          | none =>
              simp only [Functor.map_map]
              rfl
          | some x =>
              simp only [ite_eq_right ht, Functor.map_map]
              rfl

end Queries

section Sends

variable (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A send edge from an ordinary state that does not sample at `e` keeps the state ordinary and
the key unrelabelled. -/
theorem ghost_succ {e : ℕ} {v v' : P.EpochKey} {ch : Challenge P} {st : State P Unit}
    {r : SendResult P Unit} (hedge : SendEdge (auth P hMac) st r)
    (hm : maskState e st = .inl st) (hT : targetSend P hMac e ch v' st = none) :
    maskState e r.state = .inl r.state ∧ relabelKey e v r.outputKey = r.outputKey := by
  cases hedge <;> simp_all [maskState, relabelKey, targetSend]

variable [DecidableEq P.EpochKey]

/-- No sample is installed outside the sampling states of `e`. -/
theorem installedSample_eq_none (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (s : TraceState P) (party : Bool)
    (h1 : ∀ a, s.game.stateAt party ≠ .keysUnsampled e a)
    (h2 : ∀ a hdr dec, s.game.stateAt party ≠ .headerReceived e a hdr dec) :
    installedSample P hMac e kp ec s party = none := by
  unfold installedSample
  cases hst : s.game.stateAt party with
  | keysUnsampled t a =>
      have ht : t ≠ e := fun h => h1 a (by rw [hst, h])
      rcases kp with _ | ⟨pk, sk⟩
      · rfl
      · simp only [ite_eq_right ht]
  | headerReceived t a hdr dec =>
      have ht : t ≠ e := fun h => h2 a hdr dec (by rw [hst, h])
      rcases ec with _ | ⟨es, ct1, k⟩
      · rfl
      · simp only [ite_eq_right ht]
  | _ => rfl

/-- The trace send of a masked state. -/
theorem traceSend_masked (party leaking : Bool) (s : TraceState P) {e : ℕ} {m : Masked P}
    (hm : maskState e (s.game.stateAt party) = .inr m) {R : SendResult P Unit}
    (hR : MLKEMBraid.send P (auth P hMac) (s.game.stateAt party) = pure R) :
    traceSend P hMac irl party leaking s =
      pure (some (R.sendingEpoch, R.outputKey.map Prod.fst, R.msg, SendRand.none),
        { game := { sendUpdate s.game party R with exposed := s.game.exposed },
          transcript := s.transcript, bad := s.bad }) := by
  have h1 : ∀ t a, s.game.stateAt party ≠ .keysUnsampled t a := fun t a h => by
    rw [h] at hm
    simp [maskState] at hm
  have h2 : ∀ t a hdr dec, s.game.stateAt party ≠ .headerReceived t a hdr dec :=
    fun t a hdr dec h => by
      rw [h] at hm
      simp [maskState] at hm
  simp only [traceSend, sampledSend_of_noSample hMac irl s party h1 h2, hR, map_pure]
  simp [exposure, sendExposure]

/-- The send of a masked state agrees. -/
theorem sendStep_masked (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    {m : Masked P} (hm : maskState e (s.game.stateAt party) = .inr m) :
    (simSend P hMac irl e ch party leaking).run (simOf e v s) =ᵈ
        Prod.map id (simOf e v) <$> (traceSendAt P hMac irl e kp ec party leaking).run s := by
  obtain ⟨R, hR, hmsg, hep, hkey, hst⟩ := send_masked hMac hm
  have hI : installedSample P hMac e kp ec s party = none :=
    installedSample_eq_none hMac e kp ec s party
      (fun a h => by rw [h] at hm; simp [maskState] at hm)
      (fun a hdr dec h => by rw [h] at hm; simp [maskState] at hm)
  have hT : (traceSendAt P hMac irl e kp ec party leaking).run s =
      traceSend P hMac irl party leaking s := by
    change traceSendAt P hMac irl e kp ec party leaking s = _
    simp only [traceSendAt, hI]
  have hS : (simOf e v s).game.stateAt party = .inr m := by
    rw [simOf_game, simGameOf_stateAt, hm]
  rw [hT, traceSend_masked hMac irl party leaking s hm hR, map_pure]
  refine ToVCVio.evalDistEq_of_eq ?_
  change simSend P hMac irl e ch party leaking (simOf e v s) = _
  simp only [simSend, hS]
  congr 1
  simp only [Prod.map, id, simOf, simGameOf_sendUpdate, hmsg, hep, hkey, hst, relabelKey,
    Option.map_none]
  cases party <;> rfl

/-- The ghost sample of an ordinary state is the trace sample with `e` erased. -/
theorem ghostSample_eq (e : ℕ) (s : TraceState P) (party : Bool)
    (h1 : ∀ a, s.game.stateAt party ≠ .keysUnsampled e a)
    (h2 : ∀ a hdr dec, s.game.stateAt party ≠ .headerReceived e a hdr dec) :
    ghostSample P hMac irl (eraseAt e s.transcript) (s.game.stateAt party) =
      (fun w => (w.1, eraseAt e w.2.1)) <$> sampledSend P hMac irl s party := by
  cases hst : s.game.stateAt party with
  | keysUnsampled t a =>
      have ht : t ≠ e := fun h => h1 a (by rw [hst, h])
      rw [sampledSend_eq_keygen hMac irl s party hst, Functor.map_map]
      simp only [ghostSample]
      refine congrArg (· <$> irl.keygenRleak) (funext fun x => ?_)
      simp only [eraseAt_update_keypair e t ht]
  | headerReceived t a hdr dec =>
      have ht : t ≠ e := fun h => h2 a hdr dec (by rw [hst, h])
      rw [sampledSend_eq_encaps1 hMac irl s party hst, Functor.map_map]
      simp only [ghostSample]
      refine congrArg (· <$> irl.encaps1Rleak hdr) (funext fun x => ?_)
      simp only [eraseAt_update_encaps1 e t ht]
  | _ =>
      simp only [ghostSample, sampledSend, hst, MLKEMBraid.sendRleak, Functor.map_map]

end Sends

end MLKEMBraid.NoAuth
