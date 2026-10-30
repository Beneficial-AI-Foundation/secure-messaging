/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.EvalDist.BoolDist
import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant
import ToVCVio.OracleComp.SimSemantics.StateT.QueryImplAdd

/-!
# Trace invariants and instrumentation erasure

The trace invariant separates repaired payload consistency from actual decapsulation agreement.
Real and repaired queries agree before the absorbing bad event. Erasing real instrumentation
gives the unchanged explicit-policy game as a term equality, with no codec-correctness premise.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- The invariant of a trace game: in the repaired game, or before the bad event in the real game,
the repaired transcript invariant holds, with decapsulation agreement in the real game; exposed and
challenged epochs stay disjoint. -/
def TraceInv (hMac : P.Mac = Unit) (repair : Bool) (s : TraceState P) : Prop :=
  ((repair = true ∨ s.bad = false) →
    RepairInv hMac s.transcript s.game ∧ (repair = false → DecapsGood s.transcript)) ∧
  s.game.exposed ∩ s.game.challenged = ∅

/-- One query step keeps `TraceInv` when it keeps the bad flag set, keeps the repaired invariant
and decapsulation agreement before the bad event, and keeps disjointness. -/
private theorem TraceInv.step {hMac : P.Mac = Unit} {repair : Bool} {s z : TraceState P}
    (hs : TraceInv hMac repair s) (hbad : s.bad = true → z.bad = true)
    (hstep : RepairInv hMac s.transcript s.game → (repair = false → DecapsGood s.transcript) →
      RepairInv hMac z.transcript z.game ∧
        (DecapsGood s.transcript → z.bad = false → DecapsGood z.transcript))
    (hdisj : z.game.exposed ∩ z.game.challenged = ∅) :
    TraceInv hMac repair z := by
  refine ⟨fun hz => ?_, hdisj⟩
  have hs' : repair = true ∨ s.bad = false := by
    rcases hz with h | h
    · exact Or.inl h
    · right
      cases hb : s.bad
      · rfl
      · have := hbad hb
        rw [h] at this
        cases this
  obtain ⟨hR, hG⟩ := hs.1 hs'
  obtain ⟨hR', hG'⟩ := hstep hR hG
  refine ⟨hR', fun hrep => hG' (hG hrep) ?_⟩
  rcases hz with h | h
  · rw [h] at hrep
    cases hrep
  · exact h

/-- The initial trace state satisfies `TraceInv` for either game. -/
theorem traceInv_init (hMac : P.Mac = Unit) (repair : Bool) :
    TraceInv hMac repair
      { game := SCKAScheme.initGameState (MLKEMBraid.initA P (auth P hMac) ())
          (MLKEMBraid.initB P (auth P hMac) ())
        transcript := fun _ => { keypair := none, encaps1 := none }
        bad := false } :=
  ⟨fun _ => ⟨RepairInv.of_transcriptConsistent
      (transcriptConsistent_initGameState (auth P hMac) ()),
    fun _ _ _ _ _ _ _ hk _ => by cases hk⟩, by simp [SCKAScheme.initGameState]⟩

section Preservation

variable (hMac : P.Mac = Unit)

/-- The uniform-randomness query preserves `TraceInv`. -/
theorem traceUnif_preservesInv (repair : Bool) :
    QueryImpl.PreservesInv (traceUnif P) (TraceInv hMac repair) := by
  intro t s hs z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleUnif (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) t) hz
  have hw' : w.2 = s.game :=
    SCKAScheme.oracleUnif_preservesInv (fun g => g = s.game) t s.game rfl w hw
  change TraceInv hMac repair { s with game := w.2 }
  rw [hw']
  exact hs

/-- A corruption of A preserves `TraceInv`. -/
theorem traceCorruptA_preservesInv (repair : Bool) :
    QueryImpl.PreservesInv (traceCorruptA P) (TraceInv hMac repair) := by
  intro t s hs z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
  cases t
  change TraceInv hMac repair { s with game := w.2 }
  rcases mem_support_oracleCorruptA hw with hw | ⟨hV, hw⟩
  · rw [hw]
    exact hs
  · rw [hw]
    refine TraceInv.step hs (fun hb => hb) (fun hR _ => ⟨hR.setFlags _ _, fun hg _ => hg⟩) ?_
    change (s.game.exposed ∪ vuln s.game.stA) ∩ s.game.challenged = ∅
    rw [Finset.union_inter_distrib_right, Finset.union_eq_empty]
    exact ⟨hs.2, hV⟩

/-- A corruption of B preserves `TraceInv`. -/
theorem traceCorruptB_preservesInv (repair : Bool) :
    QueryImpl.PreservesInv (traceCorruptB P) (TraceInv hMac repair) := by
  intro t s hs z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
  cases t
  change TraceInv hMac repair { s with game := w.2 }
  rcases mem_support_oracleCorruptB hw with hw | ⟨hV, hw⟩
  · rw [hw]
    exact hs
  · rw [hw]
    refine TraceInv.step hs (fun hb => hb) (fun hR _ => ⟨hR.setFlags _ _, fun hg _ => hg⟩) ?_
    change (s.game.exposed ∪ vuln s.game.stB) ∩ s.game.challenged = ∅
    rw [Finset.union_inter_distrib_right, Finset.union_eq_empty]
    exact ⟨hs.2, hV⟩

/-- A challenge preserves `TraceInv`. -/
theorem traceChallenge_preservesInv [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) (repair : Bool) :
    QueryImpl.PreservesInv (traceChallenge P mode) (TraceInv hMac repair) := by
  intro e s hs z hz
  rcases mem_support_traceChallenge hz with hz | ⟨hex, hz⟩
  · rw [hz]
    exact hs
  · rw [hz]
    refine TraceInv.step hs (fun hb => hb) (fun hR _ => ⟨hR.setFlags _ _, fun hg _ => hg⟩) ?_
    change s.game.exposed ∩ insert e s.game.challenged = ∅
    rw [Finset.inter_insert_of_notMem hex]
    exact hs.2

variable [DecidableEq P.EpochKey] (irl : P.kem.IncrementalRandLeak P.inc)

/-- A trace send preserves `TraceInv`. -/
theorem traceSend_traceInv (party leaking repair : Bool) (s : TraceState P)
    (hs : TraceInv hMac repair s)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) : TraceInv hMac repair z.2 :=
  TraceInv.step hs (fun hb => traceSend_bad hMac irl hb hz)
    (fun hR _ => traceSend_preserves hMac irl party leaking s hR hz)
    (traceSend_disjoint hMac irl hs.2 hz)

/-- The outcomes of an ordinary send are those of the trace send with the coins hidden. -/
theorem mem_support_tracePlain {party : Bool} {t : Unit} {s : TraceState P}
    {z : Option (ℕ × Option ℕ × Message P.Sym) × TraceState P}
    (hz : z ∈ support ((tracePlain P hMac irl party t).run s)) :
    ∃ w ∈ support ((traceSend P hMac irl party false).run s),
      z = (w.1.map fun x => (x.1, x.2.1, x.2.2.1), w.2) := by
  change z ∈ support (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSend P hMac irl party false).run s) at hz
  rw [StateT.run_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- An ordinary send preserves `TraceInv`. -/
theorem tracePlain_preservesInv (party repair : Bool) :
    QueryImpl.PreservesInv (tracePlain P hMac irl party) (TraceInv hMac repair) := by
  intro t s hs z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
  exact traceSend_traceInv hMac irl party false repair s hs hw

/-- A leaking send preserves `TraceInv`. -/
theorem traceLeak_preservesInv (party repair : Bool) :
    QueryImpl.PreservesInv (traceLeak P hMac irl party) (TraceInv hMac repair) :=
  fun _ s hs _ hz => traceSend_traceInv hMac irl party true repair s hs hz

variable [DecidableEq P.Sym]

/-- A trace receive preserves `TraceInv`. -/
theorem traceReceive_preservesInv
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (repair party : Bool) :
    QueryImpl.PreservesInv (traceReceive P hMac irl repair party) (TraceInv hMac repair) := by
  intro n s hs z hz
  have hz' := hz
  rw [traceReceive_run] at hz'
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz'
  refine TraceInv.step hs (fun hb => hb) (fun hR hG => ?_) ?_
  · obtain ⟨h1, h2, -⟩ := (traceReceive_outcome hMac irl hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct repair party n s hR hG).2 _ hz
    exact ⟨h1, fun hg _ => h2 ▸ hg⟩
  · change w.2.exposed ∩ w.2.challenged = ∅
    cases party
    · rw [ite_eq_right Bool.false_ne_true] at hw
      obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvB_flags _ hw
      rw [h1, h2]
      exact hs.2
    · rw [ite_eq_left rfl] at hw
      obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvA_flags _ hw
      rw [h1, h2]
      exact hs.2

variable [SampleableType P.K] [SampleableType P.EpochKey]

/-- Every query of a trace game preserves `TraceInv`. -/
theorem traceImpl_preservesInv
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (repair : Bool) (mode : ℕ → Mode) :
    QueryImpl.PreservesInv (traceImpl P hMac irl repair mode) (TraceInv hMac repair) :=
  ((((((((((traceUnif_preservesInv hMac repair).add
    (tracePlain_preservesInv hMac irl true repair)).add
    (tracePlain_preservesInv hMac irl false repair)).add
    (traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct
      repair true)).add
    (traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct
      repair false)).add
    (traceLeak_preservesInv hMac irl true repair)).add
    (traceLeak_preservesInv hMac irl false repair)).add
    (traceChallenge_preservesInv hMac mode repair)).add
    (traceCorruptA_preservesInv hMac repair)).add
    (traceCorruptB_preservesInv hMac repair))

/-- Before the bad event, the real and repaired trace games answer every query identically. -/
theorem traceImpl_real_eq_repaired
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (mode : ℕ → Mode) :
    ∀ t s, (TraceInv hMac false s ∧ s.bad = false) →
      (traceImpl P hMac irl false mode t).run s = (traceImpl P hMac irl true mode t).run s := by
  have hR : ∀ (party : Bool) n (s : TraceState P), (TraceInv hMac false s ∧ s.bad = false) →
      (traceReceive P hMac irl false party n).run s =
        (traceReceive P hMac irl true party n).run s := fun party n s hs =>
    (traceReceive_outcome hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct false party n s
      (hs.1.1 (Or.inr hs.2)).1 (hs.1.1 (Or.inr hs.2)).2).1
  exact queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _
    (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (hR true)) (hR false)) (fun _ _ _ => rfl))
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl)

/-- No query of a trace game clears the bad flag. -/
theorem traceImpl_bad_mono (repair : Bool) (mode : ℕ → Mode) :
    QueryImpl.PreservesInv (traceImpl P hMac irl repair mode) (fun s => s.bad = true) := by
  have hlift : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (MLKEMBraid.GameState P Unit) ProbComp)),
      QueryImpl.PreservesInv (fun t => liftGame (c t)) (fun s : TraceState P => s.bad = true) := by
    intro ι spec c t s hs z hz
    obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
    exact hs
  refine ((((((((((hlift _).add ?_).add ?_).add ?_).add ?_).add ?_).add ?_).add ?_).add
    (hlift _)).add (hlift _))
  · intro t s hs z hz
    obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
    exact traceSend_bad hMac irl hs hw
  · intro t s hs z hz
    obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
    exact traceSend_bad hMac irl hs hw
  · intro n s hs z hz
    rw [traceReceive_run] at hz
    obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
    exact hs
  · intro n s hs z hz
    rw [traceReceive_run] at hz
    obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
    exact hs
  · exact fun _ s hs _ hz => traceSend_bad hMac irl hs hz
  · exact fun _ s hs _ hz => traceSend_bad hMac irl hs hz
  · intro e s hs z hz
    rcases mem_support_traceChallenge hz with hz | ⟨-, hz⟩ <;> rw [hz] <;> exact hs

end Preservation

section Erasure

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym] (hMac : P.Mac = Unit)
  (irl : P.kem.IncrementalRandLeak P.inc)

omit [DecidableEq P.Sym] in
/-- A non-leaking send records the update of `sendUpdate` with the exposed epochs unchanged. -/
private theorem sendUpdate_with_exposed (g : MLKEMBraid.GameState P Unit) (party : Bool)
    (r : SendResult P Unit) :
    { sendUpdate g party r with exposed := g.exposed } = sendUpdate g party r := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨e, k⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hk]

/-- Projecting an ordinary trace send gives the scheme's send oracle. -/
private theorem tracePlain_map (party : Bool) (t : Unit) (s : TraceState P) :
    Prod.map id TraceState.game <$> (tracePlain P hMac irl party t).run s =
      (oracleSend (auth P hMac) irl (pure ()) party ()).run s.game := by
  rw [oracleSend_run_eq (auth P hMac) irl (pure ()) s.game party, send_eq_map_sendRleak P irl,
    ← sampledSend_erase P hMac irl s party]
  change Prod.map id TraceState.game <$> ((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSend P hMac irl party false).run s = _
  rw [StateT.run_map]
  change Prod.map id TraceState.game <$> ((fun p => _) <$> traceSend P hMac irl party false s) = _
  simp only [traceSend, Functor.map_map]
  refine congrArg (fun f => f <$> sampledSend P hMac irl s party) (funext fun w => ?_)
  simp [sendUpdate_with_exposed]

/-- The explicit-policy leaking send of A on the no-authentication scheme. -/
private theorem oracleSendArleak_run (g : MLKEMBraid.GameState P Unit) :
    (SCKAScheme.ExposurePolicy.oracleSendArleak (exposure P irl).send (scheme P hMac irl) ()).run
        g =
      (fun out : SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand =>
        if (exposure P irl).send g.stA out.1.state out.2 ∩ g.challenged ≠ ∅ then (none, g)
        else (some (out.1.sendingEpoch, out.1.outputKey.map Prod.fst, out.1.msg, out.2),
          { sendUpdate g true out.1 with
            exposed := g.exposed ∪ (exposure P irl).send g.stA out.1.state out.2 })) <$>
        MLKEMBraid.sendRleak P irl (auth P hMac) g.stA := by
  simp only [SCKAScheme.ExposurePolicy.oracleSendArleak, StateT.run_bind, StateT.run_get,
    pure_bind, StateT.run_monadLift, monadLift_self, scheme, MLKEMBraid.scheme, bind_assoc,
    map_eq_bind_pure_comp]
  refine bind_congr fun out => ?_
  rcases out with ⟨r, rand⟩
  simp only [Function.comp_apply]
  split_ifs with hc
  · simp [StateT.run_pure]
  · rcases hk : r.outputKey with _ | ⟨tI, key⟩ <;>
      simp [hk, sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.knownPrefix, StateT.run_set]

/-- The explicit-policy leaking send of B on the no-authentication scheme. -/
private theorem oracleSendBrleak_run (g : MLKEMBraid.GameState P Unit) :
    (SCKAScheme.ExposurePolicy.oracleSendBrleak (exposure P irl).send (scheme P hMac irl) ()).run
        g =
      (fun out : SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand =>
        if (exposure P irl).send g.stB out.1.state out.2 ∩ g.challenged ≠ ∅ then (none, g)
        else (some (out.1.sendingEpoch, out.1.outputKey.map Prod.fst, out.1.msg, out.2),
          { sendUpdate g false out.1 with
            exposed := g.exposed ∪ (exposure P irl).send g.stB out.1.state out.2 })) <$>
        MLKEMBraid.sendRleak P irl (auth P hMac) g.stB := by
  simp only [SCKAScheme.ExposurePolicy.oracleSendBrleak, StateT.run_bind, StateT.run_get,
    pure_bind, StateT.run_monadLift, monadLift_self, scheme, MLKEMBraid.scheme, bind_assoc,
    map_eq_bind_pure_comp]
  refine bind_congr fun out => ?_
  rcases out with ⟨r, rand⟩
  simp only [Function.comp_apply]
  split_ifs with hc
  · simp [StateT.run_pure]
  · rcases hk : r.outputKey with _ | ⟨tI, key⟩ <;>
      simp [hk, sendUpdate, SCKAScheme.sendBUpdate, SCKAScheme.knownPrefix, StateT.run_set]

/-- Projecting a leaking trace send of A gives the explicit-policy leaking send. -/
private theorem traceLeakA_map (t : Unit) (s : TraceState P) :
    Prod.map id TraceState.game <$> (traceLeak P hMac irl true t).run s =
      (SCKAScheme.ExposurePolicy.oracleSendArleak (exposure P irl).send (scheme P hMac irl)
        t).run s.game := by
  cases t
  rw [oracleSendArleak_run hMac irl s.game,
    show s.game.stA = s.game.stateAt true from rfl, ← sampledSend_erase P hMac irl s true]
  change Prod.map id TraceState.game <$> traceSend P hMac irl true true s = _
  simp only [traceSend, Functor.map_map]
  refine congrArg (fun f => f <$> sampledSend P hMac irl s true) (funext fun w => ?_)
  by_cases hc : (exposure P irl).send s.game.stA w.1.1.state w.1.2 ∩ s.game.challenged = ∅
  · simp [hc, GameState.stateAt]
  · simp [hc, GameState.stateAt]

/-- Projecting a leaking trace send of B gives the explicit-policy leaking send. -/
private theorem traceLeakB_map (t : Unit) (s : TraceState P) :
    Prod.map id TraceState.game <$> (traceLeak P hMac irl false t).run s =
      (SCKAScheme.ExposurePolicy.oracleSendBrleak (exposure P irl).send (scheme P hMac irl)
        t).run s.game := by
  cases t
  rw [oracleSendBrleak_run hMac irl s.game,
    show s.game.stB = s.game.stateAt false from rfl, ← sampledSend_erase P hMac irl s false]
  change Prod.map id TraceState.game <$> traceSend P hMac irl false true s = _
  simp only [traceSend, Functor.map_map]
  refine congrArg (fun f => f <$> sampledSend P hMac irl s false) (funext fun w => ?_)
  by_cases hc : (exposure P irl).send s.game.stB w.1.1.state w.1.2 ∩ s.game.challenged = ∅
  · simp [hc, GameState.stateAt]
  · simp [hc, GameState.stateAt]

omit [DecidableEq P.EpochKey] [DecidableEq P.Sym] in
/-- Projecting the challenge of the real trace game for bit `b` gives the challenge oracle. -/
private theorem traceChallenge_map [SampleableType P.K] [SampleableType P.EpochKey] (b : Bool)
    (e : ℕ) (s : TraceState P) :
    Prod.map id TraceState.game <$>
        (traceChallenge P (fun _ => if b then .uniform else .real) e).run s =
      (SCKAScheme.oracleChall b (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) e).run
        s.game := by
  change Prod.map id TraceState.game <$> traceChallenge P _ e s = _
  simp only [traceChallenge, SCKAScheme.oracleChall, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hex : e ∈ s.game.exposed ∨ e ∈ s.game.challenged
  · rw [ite_eq_left hex, ite_eq_left hex]
    simp [StateT.run_pure]
  · rw [ite_eq_right hex, ite_eq_right hex]
    cases hA : s.game.keyA e with
    | some k =>
        have hk : lookupKey s.game e = some k := by simp [lookupKey, hA]
        rw [hk]
        cases b <;> simp [challengeValue, StateT.run_bind, StateT.run_set,
          StateT.run_monadLift]
    | none =>
        cases hB : s.game.keyB e with
        | none =>
            have hk : lookupKey s.game e = none := by simp [lookupKey, hA, hB]
            rw [hk]
            simp [StateT.run_pure]
        | some k =>
            have hk : lookupKey s.game e = some k := by simp [lookupKey, hA, hB]
            rw [hk]
            cases b <;> simp [challengeValue, StateT.run_bind, StateT.run_set,
              StateT.run_monadLift]

/-- Each query of the real trace game projects to the explicit-policy game query. -/
private theorem traceImpl_real_map [SampleableType P.K] [SampleableType P.EpochKey] (b : Bool) :
    ∀ t s, Prod.map id TraceState.game <$>
        (traceImpl P hMac irl false (fun _ => if b then .uniform else .real) t).run s =
      (SCKAScheme.ExposurePolicy.sckaSecurityImpl b (exposure P irl) (exposure P irl)
        (scheme P hMac irl) t).run (TraceState.game s) :=
  queryMap_add _ (queryMap_add _ (queryMap_add _ (queryMap_add _ (queryMap_add _
    (queryMap_add _ (queryMap_add _ (queryMap_add _ (queryMap_add _
      (fun _ s => map_game_liftGame _ s)
      (fun t s => tracePlain_map hMac irl true t s))
      (fun t s => tracePlain_map hMac irl false t s))
      (fun n s => by rw [traceReceive_run, map_game_liftGame, ite_eq_left rfl]; rfl))
      (fun n s => by
        rw [traceReceive_run, map_game_liftGame, ite_eq_right Bool.false_ne_true]
        rfl))
      (fun t s => traceLeakA_map hMac irl t s))
      (fun t s => traceLeakB_map hMac irl t s))
      (fun e s => traceChallenge_map b e s))
      (fun _ s => map_game_liftGame _ s))
      (fun _ s => map_game_liftGame _ s)

end Erasure

/-- **`run_erase`**: projecting the real trace run to its game state gives the explicit-policy
security game of either fixed bit, as a term equality and without code-correctness assumptions. -/
theorem run_erase (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (b : Bool) :
    Prod.map id TraceState.game <$>
        run P hMac irl false (fun _ => if b then .uniform else .real) A =
      (simulateQ (SCKAScheme.ExposurePolicy.sckaSecurityImpl b (exposure P irl) (exposure P irl)
        (scheme P hMac irl)) A).run
        (SCKAScheme.initGameState (MLKEMBraid.initA P (auth P hMac) ())
          (MLKEMBraid.initB P (auth P hMac) ())) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ TraceState.game
    (traceImpl_real_map hMac irl b) A _

/-- **`repaired_trace_invariant`**: every supported result of a repaired trace run satisfies the
fields of `TranscriptConsistent` for its own transcript, with only the final actual-decapsulation
implication of `encaps` removed, together with exposure/challenge disjointness. -/
theorem repaired_trace_invariant (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (mode : ℕ → Mode) (A : Adversary P irl)
    (z : Bool × TraceState P) (hz : z ∈ support (run P hMac irl true mode A)) :
    z.2.game.correct = true ∧ ControlInv z.2.game ∧ StatePairInv z.2.game ∧
      (z.2.transcript 0).keypair = none ∧ (z.2.transcript 0).encaps1 = none ∧
      (∀ e pk sk, (z.2.transcript e).keypair = some (pk, sk) →
        0 < e ∧ e ≤ (if e % 2 = 1 then z.2.game.stA else z.2.game.stB).epoch) ∧
      (∀ e encapsState ct1 key, (z.2.transcript e).encaps1 = some (encapsState, ct1, key) →
        0 < e ∧ e ≤ (if e % 2 = 1 then z.2.game.stB else z.2.game.stA).completedEpoch ∧
          ∃ pk sk, (z.2.transcript e).keypair = some (pk, sk)) ∧
      LocalPayloadInv (auth P hMac) () z.2.transcript z.2.game.stA ∧
      LocalPayloadInv (auth P hMac) () z.2.transcript z.2.game.stB ∧
      (∀ (party : Bool) n msg tsnd,
        (if party then z.2.game.msgA else z.2.game.msgB) n = some (msg, tsnd) →
          MessagePayloadInv (auth P hMac) () z.2.transcript msg) ∧
      (∀ (party : Bool) e, (if party then z.2.game.keyA else z.2.game.keyB) e =
        if 0 < e ∧ e ≤ (if party then z.2.game.stA else z.2.game.stB).completedEpoch then
          (z.2.transcript e).encaps1.map (fun (_, _, key) => P.kdfOK key e)
        else none) ∧
      z.2.game.exposed ∩ z.2.game.challenged = ∅ := by
  have hinv := simulateQ_run_preservesInv (traceImpl P hMac irl true mode) (TraceInv hMac true)
    (traceImpl_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct true mode)
    A _ (traceInv_init hMac true) z hz
  obtain ⟨h, -⟩ := hinv.1 (Or.inl rfl)
  exact ⟨h.correct, h.control, h.statePair, h.keypair_zero, h.encaps_zero, h.keypair, h.encaps,
    h.localA, h.localB, h.messages, h.keys, hinv.2⟩

/-- **`real_trace_before_bad`**: every supported result of a real trace run whose bad flag is
false is transcript consistent, keeps exposure/challenge disjointness, and decapsulates every
recorded encapsulation to its derived key. -/
theorem real_trace_before_bad (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (mode : ℕ → Mode) (A : Adversary P irl)
    (z : Bool × TraceState P) (hz : z ∈ support (run P hMac irl false mode A))
    (hbad : z.2.bad = false) :
    TranscriptConsistent (auth P hMac) () z.2.transcript z.2.game ∧
      z.2.game.exposed ∩ z.2.game.challenged = ∅ ∧
      ∀ e pk sk encapsState ct1 key, (z.2.transcript e).keypair = some (pk, sk) →
        (z.2.transcript e).encaps1 = some (encapsState, ct1, key) →
        decapsEpochKey e pk sk encapsState ct1 = some (P.kdfOK key e) := by
  have hinv := simulateQ_run_preservesInv (traceImpl P hMac irl false mode) (TraceInv hMac false)
    (traceImpl_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct false mode)
    A _ (traceInv_init hMac false) z hz
  obtain ⟨hR, hG⟩ := hinv.1 (Or.inr hbad)
  exact ⟨hR.transcriptConsistent (hG rfl), hinv.2, hG rfl⟩

/-- **`fixed_repaired_gap_le`**: the actual explicit-policy game of a fixed bit and the repaired
trace game of the same bit differ by at most the probability of the bad event. -/
theorem fixed_repaired_gap_le (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (b : Bool) :
    (𝒟[fixed P hMac irl A b].boolDist
        𝒟[Prod.fst <$> run P hMac irl true (fun _ => if b then .uniform else .real) A]).toReal ≤
      (Pr{let z ← run P hMac irl false (fun _ => if b then .uniform else .real) A}[z.2.bad =
          true]).toReal := by
  have hfixed : fixed P hMac irl A b =
      Prod.fst <$> run P hMac irl false (fun _ => if b then .uniform else .real) A := by
    unfold fixed
    rw [StateT.run'_eq, ← run_erase P hMac irl A b, Functor.map_map]
    rfl
  rw [ToVCVio.toReal_boolDist_evalDist, hfixed]
  simp only [Functor.map_map]
  exact abs_prEvent_simulateQ_run_sub_le_bad_of_inv
    (traceImpl P hMac irl false (fun _ => if b then .uniform else .real))
    (traceImpl P hMac irl true (fun _ => if b then .uniform else .real))
    (TraceInv hMac false) (fun s => s.bad = true)
    (traceImpl_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct false _)
    (traceImpl_bad_mono hMac irl false _)
    (fun t s hs hb => traceImpl_real_eq_repaired hMac irl hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct _ t s ⟨hs, by simpa using hb⟩)
    A (fun x => x = true) _ (traceInv_init hMac false)

end MLKEMBraid.NoAuth
