/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant
import SecureMessaging.KEM.IncrementalKEM.Correctness
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import ToVCVio.OracleComp.SimSemantics.StateT.PreservesInv
import ToVCVio.OracleComp.SimSemantics.StateT.ExpectedPayoffBound
import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant
import ToVCVio.OracleComp.QueryTracking.StateBudget
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# Trace-game invariants, erasure and the bad event

`TraceInv hMac repair` is the invariant of a trace game: in the repaired game, or before the bad
event in the real game, the repaired transcript invariant holds (with decapsulation agreement in
the real game), and exposed and challenged epochs stay disjoint. Every query preserves it.

The bad event is bounded with the score `badScore`: one after the bad event, and otherwise the
total decapsulation risk of key pairs sampled but not yet encapsulated against. Key generation
raises the expected score by the KEM correctness error; first-stage encapsulation converts the
retained pair's conditional risk into the probability of the bad flag; no other query changes it.

The endpoint hybrids use the produced-epoch bound: every first-stage encapsulated epoch is at most
the number of accepted sends, which the send budget bounds along every adaptive run.

The last sections provide the installed trace games of the reductions in `Reduction`:
`traceImplAt` is the repaired trace game in which an eligible challenge of the selected epoch
answers a supplied value, and in which that epoch's key pair and first-stage sample may be
installed instead of sampled. They contain the exposure/challenge flag discipline of every query,
the signed-gap stop at the exposure of the selected epoch (`signedGap_stop`), the installation of
the challenge value (`stoppedRun_chalSample`), the once-used-sample combinator
(`optionRun_install`), and the per-send projections used by the installations of the selected
key pair and first-stage sample.

## Main results

- `run_erase`: projecting the real trace run to its game state gives the explicit-policy game.
- `repaired_trace_invariant`: every supported repaired run satisfies the repaired invariant and
  exposure/challenge disjointness.
- `real_trace_before_bad`: every supported real run with a false bad flag satisfies full
  transcript consistency, disjointness and decapsulation agreement for all records.
- `hybrid_endpoints`: the first and last repaired hybrids have the distributions of the repaired
  real-key and uniform-key games.
- `badEvent_le`: the bad event has probability at most `qS` times the KEM correctness error.
- `fixed_repaired_gap_le`: the actual fixed-bit game and the repaired game differ by at most the
  bad-event probability.
- `security_correctness_error_le`: the security-interface correctness flag fails with probability
  at most `qS` times the KEM correctness error.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-! ### Query-wise facts over sums of oracles -/

/-- Query-wise projection equalities combine over a sum of oracle implementations. -/
theorem queryMap_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ τ : Type} (proj : σ → τ)
    {i₁ : QueryImpl spec₁ (StateT σ ProbComp)} {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    {j₁ : QueryImpl spec₁ (StateT τ ProbComp)} {j₂ : QueryImpl spec₂ (StateT τ ProbComp)}
    (h₁ : ∀ t s, Prod.map id proj <$> (i₁ t).run s = (j₁ t).run (proj s))
    (h₂ : ∀ t s, Prod.map id proj <$> (i₂ t).run s = (j₂ t).run (proj s)) :
    ∀ t s, Prod.map id proj <$> ((i₁ + i₂) t).run s = ((j₁ + j₂) t).run (proj s)
  | .inl t, s => h₁ t s
  | .inr t, s => h₂ t s

/-- Query-wise equalities on states satisfying `Inv` combine over a sum of implementations. -/
theorem queryEq_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}
    (Inv : σ → Prop) {i₁ j₁ : QueryImpl spec₁ (StateT σ ProbComp)}
    {i₂ j₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (h₁ : ∀ t s, Inv s → (i₁ t).run s = (j₁ t).run s)
    (h₂ : ∀ t s, Inv s → (i₂ t).run s = (j₂ t).run s) :
    ∀ t s, Inv s → ((i₁ + i₂) t).run s = ((j₁ + j₂) t).run s
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

/-- Query-wise expected-score bounds combine over a sum of implementations, charging `ε` exactly
on the queries selected by `Sum.elim p₁ p₂`. -/
theorem payoff_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}
    (Inv : σ → Prop) (score : σ → ℝ≥0∞) (ε : ℝ≥0∞)
    {i₁ : QueryImpl spec₁ (StateT σ ProbComp)} {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (p₁ : ι₁ → Bool) (p₂ : ι₂ → Bool)
    (h₁ : ∀ t s, Inv s → expectedPayoff ((i₁ t).run s) (fun z => score z.2) ≤
      score s + if p₁ t then ε else 0)
    (h₂ : ∀ t s, Inv s → expectedPayoff ((i₂ t).run s) (fun z => score z.2) ≤
      score s + if p₂ t then ε else 0) :
    ∀ t s, Inv s → expectedPayoff (((i₁ + i₂) t).run s) (fun z => score z.2) ≤
      score s + if Sum.elim p₁ p₂ t then ε else 0
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

/-- Query-wise counter bounds combine over a sum of implementations: the counter never decreases,
and it increases by at most one exactly on the queries selected by `Sum.elim p₁ p₂`. -/
theorem countStep_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}
    (count : σ → ℕ)
    {i₁ : QueryImpl spec₁ (StateT σ ProbComp)} {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (p₁ : ι₁ → Bool) (p₂ : ι₂ → Bool)
    (h₁ : ∀ t s z, z ∈ support ((i₁ t).run s) →
      count s ≤ count z.2 ∧ count z.2 ≤ count s + if p₁ t then 1 else 0)
    (h₂ : ∀ t s z, z ∈ support ((i₂ t).run s) →
      count s ≤ count z.2 ∧ count z.2 ≤ count s + if p₂ t then 1 else 0) :
    ∀ t s z, z ∈ support (((i₁ + i₂) t).run s) →
      count s ≤ count z.2 ∧ count z.2 ≤ count s + if Sum.elim p₁ p₂ t then 1 else 0
  | .inl t, s, z, hz => h₁ t s z hz
  | .inr t, s, z, hz => h₂ t s z hz

/-! ### The trace invariant -/

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

/-! ### Supports of the non-protocol queries -/

/-- A corruption of A reveals A's state, or is refused without a state change. -/
theorem mem_support_oracleCorruptA {V : State P Unit → Finset ℕ}
    {g : MLKEMBraid.GameState P Unit} {w : Option (State P Unit) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleCorruptA V (State P Unit) P.EpochKey
      (Message P.Sym) ()).run g)) :
    w.2 = g ∨ (V g.stA ∩ g.challenged = ∅ ∧ w.2 = { g with exposed := g.exposed ∪ V g.stA }) := by
  simp only [SCKAScheme.oracleCorruptA, StateT.run_bind, StateT.run_get, pure_bind] at hw
  split_ifs at hw with hc
  · left
    simp only [StateT.run_pure, mem_support_pure_iff] at hw
    rw [hw]
  · right
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      mem_support_pure_iff] at hw
    exact ⟨not_not.mp hc, by rw [hw]⟩

/-- The version of `mem_support_oracleCorruptA` for B. -/
theorem mem_support_oracleCorruptB {V : State P Unit → Finset ℕ}
    {g : MLKEMBraid.GameState P Unit} {w : Option (State P Unit) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleCorruptB V (State P Unit) P.EpochKey
      (Message P.Sym) ()).run g)) :
    w.2 = g ∨ (V g.stB ∩ g.challenged = ∅ ∧ w.2 = { g with exposed := g.exposed ∪ V g.stB }) := by
  simp only [SCKAScheme.oracleCorruptB, StateT.run_bind, StateT.run_get, pure_bind] at hw
  split_ifs at hw with hc
  · left
    simp only [StateT.run_pure, mem_support_pure_iff] at hw
    rw [hw]
  · right
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      mem_support_pure_iff] at hw
    exact ⟨not_not.mp hc, by rw [hw]⟩

/-- A challenge leaves the state unchanged, or adds an unexposed epoch to the challenged set. -/
theorem mem_support_traceChallenge [SampleableType P.K] [SampleableType P.EpochKey]
    {mode : ℕ → Mode} {e : ℕ} {s : TraceState P} {z : Option P.EpochKey × TraceState P}
    (hz : z ∈ support ((traceChallenge P mode e).run s)) :
    z.2 = s ∨ (e ∉ s.game.exposed ∧
      z.2 = { s with game := { s.game with challenged := insert e s.game.challenged } }) := by
  change z ∈ support (traceChallenge P mode e s) at hz
  simp only [traceChallenge] at hz
  split_ifs at hz with hex
  · left
    rw [mem_support_pure_iff] at hz
    rw [hz]
  · cases hk : lookupKey s.game e with
    | none =>
        simp only [hk, mem_support_pure_iff] at hz
        left
        rw [hz]
    | some k =>
        simp only [hk, support_map] at hz
        obtain ⟨out, -, rfl⟩ := hz
        exact Or.inr ⟨fun h => hex (Or.inl h), rfl⟩

/-- A receive oracle keeps the exposed and challenged epochs and the send counters. -/
private theorem oracleRecvA_flags {IK Rand : Type} [DecidableEq P.EpochKey]
    (scka : SCKAScheme ProbComp IK (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) Rand)
    {n : ℕ} {g : MLKEMBraid.GameState P Unit}
    {w : Option (ℕ × Option ℕ) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleRecvA scka n).run g)) :
    w.2.exposed = g.exposed ∧ w.2.challenged = g.challenged ∧ w.2.nA = g.nA ∧ w.2.nB = g.nB := by
  rcases hm : g.msgB n with _ | ⟨ρ, tsnd⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl, rfl, rfl⟩
  rcases hr : scka.recvA g.stA ρ with _ | ⟨keyOpt, trcv, st'⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    rcases keyOpt with _ | ⟨tI, key⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The version of `oracleRecvA_flags` for B. -/
private theorem oracleRecvB_flags {IK Rand : Type} [DecidableEq P.EpochKey]
    (scka : SCKAScheme ProbComp IK (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) Rand)
    {n : ℕ} {g : MLKEMBraid.GameState P Unit}
    {w : Option (ℕ × Option ℕ) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleRecvB scka n).run g)) :
    w.2.exposed = g.exposed ∧ w.2.challenged = g.challenged ∧ w.2.nA = g.nA ∧ w.2.nB = g.nB := by
  rcases hm : g.msgA n with _ | ⟨ρ, tsnd⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl, rfl, rfl⟩
  rcases hr : scka.recvB g.stB ρ with _ | ⟨keyOpt, trcv, st'⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    rcases keyOpt with _ | ⟨tI, key⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### Preservation of the trace invariant -/

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
    · rw [if_neg Bool.false_ne_true] at hw
      obtain ⟨h1, h2, -, -⟩ := oracleRecvB_flags _ hw
      rw [h1, h2]
      exact hs.2
    · rw [if_pos rfl] at hw
      obtain ⟨h1, h2, -, -⟩ := oracleRecvA_flags _ hw
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

/-! ### Erasure of the real trace game -/

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
  · rw [if_pos hex, if_pos hex]
    simp [StateT.run_pure]
  · rw [if_neg hex, if_neg hex]
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
      (fun n s => by rw [traceReceive_run, map_game_liftGame, if_pos rfl]; rfl))
      (fun n s => by rw [traceReceive_run, map_game_liftGame, if_neg Bool.false_ne_true]; rfl))
      (fun t s => traceLeakA_map hMac irl t s))
      (fun t s => traceLeakB_map hMac irl t s))
      (fun e s => traceChallenge_map b e s))
      (fun _ s => map_game_liftGame _ s))
      (fun _ s => map_game_liftGame _ s)

end Erasure

/-! ### Public results on the trace games -/

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
    (fixed P hMac irl A b).boolDistAdvantage
        (Prod.fst <$> run P hMac irl true (fun _ => if b then .uniform else .real) A) ≤
      (Pr[fun z => z.2.bad = true |
        run P hMac irl false (fun _ => if b then .uniform else .real) A]).toReal := by
  have hfixed : fixed P hMac irl A b =
      Prod.fst <$> run P hMac irl false (fun _ => if b then .uniform else .real) A := by
    unfold fixed
    rw [StateT.run'_eq, ← run_erase P hMac irl A b, Functor.map_map]
    rfl
  unfold ProbComp.boolDistAdvantage
  rw [hfixed, probOutput_fst_map_eq_probEvent, probOutput_fst_map_eq_probEvent]
  exact abs_probEvent_simulateQ_run_sub_le_bad_of_inv
    (traceImpl P hMac irl false (fun _ => if b then .uniform else .real))
    (traceImpl P hMac irl true (fun _ => if b then .uniform else .real))
    (TraceInv hMac false) (fun s => s.bad = true)
    (traceImpl_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct false _)
    (traceImpl_bad_mono hMac irl false _)
    (fun t s hs hb => traceImpl_real_eq_repaired hMac irl hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct _ t s ⟨hs, by simpa using hb⟩)
    A (fun x => x = true) _ (traceInv_init hMac false)

/-! ### The bad-event bound -/

section BadEventBound

/-- The send predicate in the nesting of `traceImpl`'s components. -/
private def sendElim (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc) :
    (Spec P irl).Domain → Bool :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim
    (fun _ => false) (fun _ => true)) (fun _ => true)) (fun _ => false)) (fun _ => false))
    (fun _ => true)) (fun _ => true)) (fun _ => false)) (fun _ => false)) (fun _ => false)

/-- `isSendQuery` selects the four send components of `traceImpl`. -/
private theorem isSendQuery_eq_sendElim (irl : P.kem.IncrementalRandLeak P.inc) :
    ∀ t : (Spec P irl).Domain, isSendQuery t = sendElim P irl t
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inr _))))) => rfl
  | .inl (.inl (.inl (.inl (.inr _)))) => rfl
  | .inl (.inl (.inl (.inr _))) => rfl
  | .inl (.inl (.inr _)) => rfl
  | .inl (.inr _) => rfl
  | .inr _ => rfl

/-- Updating one summand of an `ℝ≥0∞`-valued series. -/
private theorem tsum_update_add (f : ℕ → ℝ≥0∞) (e : ℕ) (v : ℝ≥0∞) :
    (∑' t, Function.update f e v t) + f e = (∑' t, f t) + v := by
  have h : ∀ t, Function.update f e v t + (Pi.single e (f e) : ℕ → ℝ≥0∞) t =
      f t + (Pi.single e v : ℕ → ℝ≥0∞) t := by
    intro t
    by_cases ht : t = e
    · subst ht
      simp [add_comm]
    · simp [Function.update_of_ne ht, Pi.single_eq_of_ne ht]
  calc (∑' t, Function.update f e v t) + f e
      = (∑' t, Function.update f e v t) + ∑' t, (Pi.single e (f e) : ℕ → ℝ≥0∞) t := by
        rw [tsum_pi_single]
    _ = ∑' t, (Function.update f e v t + (Pi.single e (f e) : ℕ → ℝ≥0∞) t) :=
        ENNReal.tsum_add.symm
    _ = ∑' t, (f t + (Pi.single e v : ℕ → ℝ≥0∞) t) := tsum_congr h
    _ = (∑' t, f t) + ∑' t, (Pi.single e v : ℕ → ℝ≥0∞) t := ENNReal.tsum_add
    _ = (∑' t, f t) + v := by rw [tsum_pi_single]

variable [DecidableEq P.K]

/-- The decapsulation-failure risk of an epoch record whose key pair is sampled but not yet
encapsulated against; zero otherwise. -/
noncomputable def pendingRisk (r : EpochTranscript P) : ℝ≥0∞ :=
  match r.keypair, r.encaps1 with
  | some (pk, sk), none => P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk
  | _, _ => 0

/-- The total pending decapsulation risk of a transcript. -/
noncomputable def pendingPotential (T : ℕ → EpochTranscript P) : ℝ≥0∞ :=
  ∑' e, pendingRisk (T e)

/-- The bad-event score: one after the bad event, the pending risk before it. -/
noncomputable def badScore (s : TraceState P) : ℝ≥0∞ :=
  if s.bad then 1 else pendingPotential s.transcript

/-- Replacing one epoch record changes the pending potential by the difference of their risks. -/
theorem pendingPotential_update (T : ℕ → EpochTranscript P) (e : ℕ) (r : EpochTranscript P) :
    pendingPotential (Function.update T e r) + pendingRisk (T e) =
      pendingPotential T + pendingRisk r := by
  have h : (fun t => pendingRisk (Function.update T e r t)) =
      Function.update (fun t => pendingRisk (T t)) e (pendingRisk r) := by
    funext t
    exact Function.apply_update (fun _ => pendingRisk) T e r t
  unfold pendingPotential
  rw [h]
  exact tsum_update_add _ e _

/-- A query whose outcomes keep the transcript and bad flag does not raise the expected score. -/
private theorem payoff_le_of_support {α : Type} (X : ProbComp (α × TraceState P))
    (s : TraceState P) (h : ∀ z ∈ support X, z.2.transcript = s.transcript ∧ z.2.bad = s.bad) :
    expectedPayoff X (fun z => badScore z.2) ≤ badScore s :=
  expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun z hz => by
    obtain ⟨h1, h2⟩ := h z hz
    simp [badScore, h1, h2]

variable (hMac : P.Mac = Unit) [DecidableEq P.EpochKey] (irl : P.kem.IncrementalRandLeak P.inc)

omit [DecidableEq P.K] in
/-- The coin tag and ghost records of a key-generation sample. -/
private theorem obs_sampledSend_keysUnsampled (s : TraceState P) (party : Bool) {e : ℕ}
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled e a) :
    (fun w => (w.1.2, w.2)) <$> sampledSend P hMac irl s party =
      (fun x : (P.PK × P.SK) × irl.KeygenRand => (SendRand.keygen x.2,
        Function.update s.transcript e { (s.transcript e) with keypair := some x.1 }, s.bad)) <$>
        irl.keygenRleak := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp, bind_assoc]
  exact bind_congr fun x => by
    obtain ⟨⟨pk, sk⟩, rand⟩ := x
    simp only [pure_bind, Function.comp_apply]

omit [DecidableEq P.K] in
/-- The coin tag, ghost records and bad flag of a first-stage encapsulation sample. -/
private theorem obs_sampledSend_headerReceived (s : TraceState P) (party : Bool) {e : ℕ}
    {a : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) :
    (fun w => (w.1.2, w.2)) <$> sampledSend P hMac irl s party =
      (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand => (SendRand.encaps1 x.2,
        Function.update s.transcript e { (s.transcript e) with encaps1 := some x.1 },
        match (s.transcript e).keypair with
        | none => s.bad
        | some (pk, sk) => s.bad || decide (decapsEpochKey (P := P) e pk sk x.1.1 x.1.2.1 ≠
            some (P.kdfOK x.1.2.2 e)))) <$> irl.encaps1Rleak hdr := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp, bind_assoc]
  exact bind_congr fun x => by
    obtain ⟨⟨es, ct1, k⟩, rand⟩ := x
    simp only [pure_bind, Function.comp_apply]
    try rfl

omit [DecidableEq P.K] in
/-- A send that samples nothing keeps the ghost records and the bad flag. -/
private theorem obs_sampledSend_steady (s : TraceState P) (party : Bool)
    (hsteady : (s.game.stateAt party).SendsNoSample) :
    ∀ w ∈ support (sampledSend P hMac irl s party), w.2 = (s.transcript, s.bad) := by
  intro w hw
  cases hst : s.game.stateAt party <;> rw [hst] at hsteady
  case keysUnsampled => exact False.elim hsteady
  case headerReceived => exact False.elim hsteady
  all_goals
    simp only [sampledSend, hst, support_map, Set.mem_image] at hw
    obtain ⟨out, -, rfl⟩ := hw
    rfl

/-- A trace send raises the expected bad-event score by at most the KEM correctness error. -/
theorem traceSend_payoff (party leaking : Bool) (s : TraceState P)
    (hs : TraceInv hMac false s) :
    expectedPayoff ((traceSend P hMac irl party leaking).run s) (fun z => badScore z.2) ≤
      badScore s + P.kem.correctnessError ProbCompRuntime.probComp := by
  cases hb : s.bad
  · obtain ⟨hR, -⟩ := hs.1 (Or.inr hb)
    have hscore : badScore s = pendingPotential s.transcript := by simp [badScore, hb]
    rw [hscore]
    let R : SendRand irl.KeygenRand irl.Encaps1Rand → Bool := fun tag =>
      leaking && decide ((exposure P irl).send (s.game.stateAt party) (s.game.stateAt party) tag ∩
        s.game.challenged ≠ ∅)
    let H : SendRand irl.KeygenRand irl.Encaps1Rand × (ℕ → EpochTranscript P) × Bool → ℝ≥0∞ :=
      fun o => if R o.1 then pendingPotential s.transcript
        else if o.2.2 then 1 else pendingPotential o.2.1
    have hpay : expectedPayoff ((traceSend P hMac irl party leaking).run s)
        (fun z => badScore z.2) =
        expectedPayoff ((fun w => (w.1.2, w.2)) <$> sampledSend P hMac irl s party) H := by
      change expectedPayoff (traceSend P hMac irl party leaking s) _ = _
      simp only [traceSend]
      rw [expectedPayoff_map, expectedPayoff_map]
      congr 1
      funext w
      have hx : (leaking && decide ((exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2 ∩
          s.game.challenged ≠ ∅)) = R w.1.2 := rfl
      rw [hx]
      simp only [H]
      by_cases hc : R w.1.2 = true
      · rw [if_pos hc, if_pos hc]
        simp [badScore, hb]
      · rw [if_neg hc, if_neg hc]
        rfl
    rw [hpay]
    cases hst : s.game.stateAt party
    case keysUnsampled e a =>
      have hRe : ∀ r, R (SendRand.keygen r) =
          (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) := by
        intro r
        simp only [R, hst]
        rfl
      have hL := hR.local party
      rw [hst] at hL
      obtain ⟨-, h1, h2⟩ := hL
      rw [obs_sampledSend_keysUnsampled hMac irl s party hst, expectedPayoff_map]
      by_cases hRk : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · refine le_trans (expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
          fun x _ => le_of_eq ?_) le_self_add
        simp only [H]
        rw [hRe x.2, if_pos hRk]
      · have hstep : ∀ x : (P.PK × P.SK) × irl.KeygenRand,
            H (SendRand.keygen x.2,
              Function.update s.transcript e { (s.transcript e) with keypair := some x.1 }, s.bad)
              = P.inc.decapsFailureProb (P.inc.toHeader x.1.1) (P.inc.toVector x.1.1) x.1.2 +
                pendingPotential s.transcript := by
          rintro ⟨⟨pk, sk⟩, rand⟩
          have hu := pendingPotential_update s.transcript e
            { (s.transcript e) with keypair := some (pk, sk) }
          have h0 : pendingRisk (s.transcript e) = 0 := by simp [pendingRisk, h1, h2]
          have hr : pendingRisk { (s.transcript e) with keypair := some (pk, sk) } =
              P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
            simp [pendingRisk, h2]
          rw [h0, hr, add_zero] at hu
          simp only [H]
          rw [hRe rand, if_neg hRk, hb, if_neg Bool.false_ne_true, hu, add_comm]
        have hkg : expectedPayoff irl.keygenRleak (fun x : (P.PK × P.SK) × irl.KeygenRand =>
            P.inc.decapsFailureProb (P.inc.toHeader x.1.1) (P.inc.toVector x.1.1) x.1.2) =
            P.kem.correctnessError ProbCompRuntime.probComp := by
          rw [← P.inc.expectedPayoff_keygen_decapsFailureProb, ← irl.keygen_fst, bind_pure_comp,
            expectedPayoff_map]
          try rfl
        refine le_trans (expectedPayoff_mono _ _ _ fun x => le_of_eq (hstep x)) ?_
        refine le_trans (expectedPayoff_add_const_le _ _ _) ?_
        rw [hkg]
        exact le_of_eq (add_comm _ _)
    case headerReceived e a hdr dec =>
      obtain ⟨pk, sk, -, -, hkpT, -, hhdr⟩ := hR.peer_of_headerReceived party hst
      subst hhdr
      have hRe : ∀ r, R (SendRand.encaps1 r) =
          (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) := by
        intro r
        simp only [R, hst]
        rfl
      have hL := hR.local party
      rw [hst] at hL
      have hc0 : (s.transcript e).encaps1 = none := hL.2.1
      have hrisk : pendingRisk (s.transcript e) =
          P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
        simp [pendingRisk, hkpT, hc0]
      obtain ⟨c, hc, hupd⟩ : ∃ c : ℝ≥0∞,
          c + P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk =
            pendingPotential s.transcript ∧
          ∀ x : P.inc.St × P.inc.C₁ × P.K, pendingPotential
            (Function.update s.transcript e { (s.transcript e) with encaps1 := some x }) = c := by
        refine ⟨∑' t, Function.update (fun t => pendingRisk (s.transcript t)) e 0 t, ?_,
          fun x => ?_⟩
        · have h := tsum_update_add (fun t => pendingRisk (s.transcript t)) e 0
          simp only [add_zero] at h
          rw [hrisk] at h
          exact h
        · refine tsum_congr fun t => ?_
          have h0 : pendingRisk { (s.transcript e) with encaps1 := some x } = 0 := by
            simp [pendingRisk, hkpT]
          rw [Function.apply_update (fun _ => pendingRisk) s.transcript e _ t, h0]
      rw [obs_sampledSend_headerReceived hMac irl s party hst, expectedPayoff_map]
      by_cases hRk : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · refine le_trans (expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
          fun x _ => le_of_eq ?_) le_self_add
        simp only [H]
        rw [hRe x.2, if_pos hRk]
      · have hfp : expectedPayoff (irl.encaps1Rleak (P.inc.toHeader pk))
            (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
              if P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
                P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
              then 0 else 1) =
            P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
          rw [P.inc.decapsFailureProb_eq_expectedPayoff P.hDet P.hEnc2, ← irl.encaps1_fst,
            bind_pure_comp, expectedPayoff_map]
          try rfl
        refine le_trans (expectedPayoff_mono _ _
          (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
            (if P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
              P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
            then 0 else 1) + c) fun x => ?_) ?_
        · simp only [H]
          rw [hRe x.2, if_neg hRk, hupd x.1]
          simp only [hkpT, hb, Bool.false_or]
          by_cases hfail : P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
              P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
          · have hk : decapsEpochKey (P := P) e pk sk x.1.1 x.1.2.1 = some (P.kdfOK x.1.2.2 e) :=
              congrArg (Option.map fun k => P.kdfOK k e) hfail
            have hnot : ¬ (decide (decapsEpochKey (P := P) e pk sk x.1.1 x.1.2.1 ≠
                some (P.kdfOK x.1.2.2 e)) = true) := fun h => of_decide_eq_true h hk
            rw [if_neg hnot, if_pos hfail, zero_add]
          · rw [if_neg hfail]
            split_ifs
            · exact le_self_add
            · exact le_add_self
        · refine le_trans (expectedPayoff_add_const_le _ _ _) ?_
          rw [hfp, add_comm _ c, hc]
          exact le_self_add
    all_goals
      have hsteady : (s.game.stateAt party).SendsNoSample := by
        rw [hst]
        trivial
      refine le_trans (expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
        fun o ho => ?_) le_self_add
      rw [support_map] at ho
      obtain ⟨w, hw, rfl⟩ := ho
      have hw2 := obs_sampledSend_steady hMac irl s party hsteady w hw
      simp only [H, hw2, hb, Bool.false_eq_true, ↓reduceIte]
      by_cases hc : R w.1.2 = true <;> simp [hc]
  · refine le_trans ?_ le_self_add
    refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun z hz => ?_
    simp [badScore, traceSend_bad hMac irl hb hz, hb]

variable [DecidableEq P.Sym] [SampleableType P.K] [SampleableType P.EpochKey]

/-- One query of the real trace game raises the expected bad-event score by at most the KEM
correctness error for a send, and not at all for any other query. -/
theorem traceImpl_payoff (mode : ℕ → Mode) :
    ∀ t s, TraceInv hMac false s →
      expectedPayoff ((traceImpl P hMac irl false mode t).run s) (fun z => badScore z.2) ≤
        badScore s + if isSendQuery t = true then
          P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
  intro t s hs
  rw [isSendQuery_eq_sendElim irl t]
  have hzero : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P) ProbComp)),
      (∀ t s, ∀ z ∈ support ((c t).run s), z.2.transcript = s.transcript ∧ z.2.bad = s.bad) →
      ∀ t s, TraceInv hMac false s → expectedPayoff ((c t).run s) (fun z => badScore z.2) ≤
        badScore s + if (fun _ => false) t then
          P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
    intro ι spec c hc t s _
    simpa using payoff_le_of_support _ s (hc t s)
  have hsend : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P) ProbComp)),
      (∀ t s, TraceInv hMac false s → expectedPayoff ((c t).run s) (fun z => badScore z.2) ≤
        badScore s + P.kem.correctnessError ProbCompRuntime.probComp) →
      ∀ t s, TraceInv hMac false s → expectedPayoff ((c t).run s) (fun z => badScore z.2) ≤
        badScore s + if (fun _ => true) t then
          P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
    intro ι spec c hc t s hs
    simpa using hc t s hs
  have hlift : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (MLKEMBraid.GameState P Unit) ProbComp)),
      ∀ t (s : TraceState P), ∀ z ∈ support ((liftGame (c t)).run s),
        z.2.transcript = s.transcript ∧ z.2.bad = s.bad := by
    intro ι spec c t s z hz
    obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
    exact ⟨rfl, rfl⟩
  have hplain : ∀ party, ∀ t s, TraceInv hMac false s →
      expectedPayoff ((tracePlain P hMac irl party t).run s) (fun z => badScore z.2) ≤
        badScore s + P.kem.correctnessError ProbCompRuntime.probComp := by
    intro party t s hs
    change expectedPayoff (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
      traceSend P hMac irl party false).run s) _ ≤ _
    rw [StateT.run_map, expectedPayoff_map]
    exact traceSend_payoff hMac irl party false s hs
  exact payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _
    (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _
      (payoff_add _ _ _ _ _
        (hzero (traceUnif P) fun t s => hlift _ t s)
        (hsend _ (hplain true)))
        (hsend _ (hplain false)))
        (hzero _ fun n s z hz => by
          rw [traceReceive_run] at hz
          obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
          exact ⟨rfl, rfl⟩))
        (hzero _ fun n s z hz => by
          rw [traceReceive_run] at hz
          obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
          exact ⟨rfl, rfl⟩))
        (hsend _ fun _ s hs => traceSend_payoff hMac irl true true s hs))
        (hsend _ fun _ s hs => traceSend_payoff hMac irl false true s hs))
        (hzero _ fun e s z hz => by
          rcases mem_support_traceChallenge hz with hz | ⟨-, hz⟩ <;> rw [hz] <;>
            exact ⟨rfl, rfl⟩))
        (hzero (traceCorruptA P) fun t s => hlift _ t s))
        (hzero (traceCorruptB P) fun t s => hlift _ t s) t s hs

end BadEventBound

/-- **`badEvent_le`**: in the real trace game of either bit, the bad event has probability at most
`qS` times the KEM correctness error. Key generation charges the KEM's average failure; the
retained pair's conditional risk is consumed at first-stage encapsulation. -/
theorem badEvent_le (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) (b : Bool) :
    Pr[fun z => z.2.bad = true |
        run P hMac irl false (fun _ => if b then .uniform else .real) A] ≤
      (qS : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp := by
  have hE := expectedPayoff_simulateQ_run_le
    (traceImpl P hMac irl false (fun _ => if b then .uniform else .real))
    (TraceInv hMac false) badScore (fun t => isSendQuery t = true)
    (P.kem.correctnessError ProbCompRuntime.probComp)
    (traceImpl_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct false _)
    (traceImpl_payoff hMac irl _) A qS hqS _ (traceInv_init hMac false)
  have h0 : badScore (P := P)
      { game := SCKAScheme.initGameState (MLKEMBraid.initA P (auth P hMac) ())
          (MLKEMBraid.initB P (auth P hMac) ())
        transcript := fun _ => { keypair := none, encaps1 := none }
        bad := false } = 0 := by
    simp [badScore, pendingPotential, pendingRisk]
  calc Pr[fun z => z.2.bad = true |
        run P hMac irl false (fun _ => if b then .uniform else .real) A]
      ≤ expectedPayoff (run P hMac irl false (fun _ => if b then .uniform else .real) A)
          (fun z => badScore z.2) :=
        probEvent_le_expectedPayoff _ _ _ fun z hz => by simp [badScore, hz]
    _ ≤ _ := hE
    _ = (qS : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp := by
        rw [h0, zero_add]

/-- **`security_correctness_error_le`**: on the full security interface of either bit, the
correctness flag fails with probability at most `qS` times the KEM correctness error. -/
theorem security_correctness_error_le (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) (b : Bool) :
    Pr[fun z => z.2.game.correct = false |
        run P hMac irl false (fun _ => if b then .uniform else .real) A] ≤
      (qS : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp := by
  refine le_trans (probEvent_mono fun z hz hc => ?_)
    (badEvent_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS b)
  by_contra hb
  have hcor := (real_trace_before_bad P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct
    _ A z hz (by simpa using hb)).1.correct
  rw [hc] at hcor
  cases hcor

/-! ### Endpoint hybrids -/

section Endpoints

variable (hMac : P.Mac = Unit)

/-- The number of accepted sends of both parties. -/
private def sendCount (s : TraceState P) : ℕ := s.game.nA + s.game.nB

/-- The produced-epoch bound: every first-stage encapsulated epoch is at most the number of
accepted sends. -/
private def SendBound (s : TraceState P) : Prop :=
  ∀ e, (s.transcript e).encaps1 ≠ none → e ≤ sendCount s

/-- The initial trace state satisfies the produced-epoch bound. -/
private theorem sendBound_init :
    SendBound (P := P)
      { game := SCKAScheme.initGameState (MLKEMBraid.initA P (auth P hMac) ())
          (MLKEMBraid.initB P (auth P hMac) ())
        transcript := fun _ => { keypair := none, encaps1 := none }
        bad := false } :=
  fun _ he => absurd rfl he

/-- A key held by a party is for a positive epoch with a recorded first-stage encapsulation. -/
private theorem encaps1_of_key {T : ℕ → EpochTranscript P} {g : MLKEMBraid.GameState P Unit}
    (h : RepairInv hMac T g) (party : Bool) {e : ℕ} (hk : g.keysAt party e ≠ none) :
    0 < e ∧ (T e).encaps1 ≠ none := by
  change (if party then g.keyA else g.keyB) e ≠ none at hk
  rw [h.keys party e] at hk
  by_cases hc : 0 < e ∧ e ≤ (if party then g.stA else g.stB).completedEpoch
  · rw [if_pos hc] at hk
    exact ⟨hc.1, fun h0 => hk (by simp [h0])⟩
  · rw [if_neg hc] at hk
    exact absurd rfl hk

/-- An available challenge key is held by one of the parties. -/
private theorem keysAt_of_lookupKey {g : MLKEMBraid.GameState P Unit} {e : ℕ}
    (hk : lookupKey g e ≠ none) : ∃ party, g.keysAt party e ≠ none := by
  cases hA : g.keyA e with
  | some k => exact ⟨true, by simp [GameState.keysAt, hA]⟩
  | none =>
      refine ⟨false, ?_⟩
      simpa [lookupKey, GameState.keysAt, hA] using hk

/-- The uniform-randomness query keeps the ghost records and the send counters. -/
private theorem traceUnif_frame : ∀ t s z, z ∈ support ((traceUnif P t).run s) →
    z.2.transcript = s.transcript ∧ sendCount z.2 = sendCount s := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleUnif (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) t) hz
  have hw' : w.2 = s.game :=
    SCKAScheme.oracleUnif_preservesInv (fun g => g = s.game) t s.game rfl w hw
  exact ⟨rfl, by simp only [sendCount, hw']⟩

/-- A corruption of A keeps the ghost records and the send counters. -/
private theorem traceCorruptA_frame : ∀ t s z, z ∈ support ((traceCorruptA P t).run s) →
    z.2.transcript = s.transcript ∧ sendCount z.2 = sendCount s := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
  cases t
  refine ⟨rfl, ?_⟩
  rcases mem_support_oracleCorruptA hw with hw | ⟨-, hw⟩ <;> simp only [sendCount, hw]

/-- A corruption of B keeps the ghost records and the send counters. -/
private theorem traceCorruptB_frame : ∀ t s z, z ∈ support ((traceCorruptB P t).run s) →
    z.2.transcript = s.transcript ∧ sendCount z.2 = sendCount s := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
  cases t
  refine ⟨rfl, ?_⟩
  rcases mem_support_oracleCorruptB hw with hw | ⟨-, hw⟩ <;> simp only [sendCount, hw]

/-- A challenge keeps the ghost records and the send counters. -/
private theorem traceChallenge_frame [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) : ∀ e s z, z ∈ support ((traceChallenge P mode e).run s) →
      z.2.transcript = s.transcript ∧ sendCount z.2 = sendCount s := by
  intro e s z hz
  rcases mem_support_traceChallenge hz with hz | ⟨-, hz⟩ <;> rw [hz] <;> exact ⟨rfl, rfl⟩

/-- Two challenge modes give the same trace challenge where they agree on an available epoch. -/
private theorem traceChallenge_mode_eq [SampleableType P.K] [SampleableType P.EpochKey]
    (m m' : ℕ → Mode) (e : ℕ) (s : TraceState P)
    (h : lookupKey s.game e ≠ none → m e = m' e) :
    (traceChallenge P m e).run s = (traceChallenge P m' e).run s := by
  change traceChallenge P m e s = traceChallenge P m' e s
  cases hk : lookupKey s.game e with
  | none => simp only [traceChallenge, hk]
  | some k => simp only [traceChallenge, hk, h (by rw [hk]; exact Option.some_ne_none k)]

variable [DecidableEq P.EpochKey] (irl : P.kem.IncrementalRandLeak P.inc)

/-- An accepted send increments the number of accepted sends. -/
private theorem sendUpdate_count (g : MLKEMBraid.GameState P Unit) (party : Bool)
    (r : SendResult P Unit) :
    (sendUpdate g party r).nA + (sendUpdate g party r).nB = g.nA + g.nB + 1 := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨e, k⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hk] <;> omega

/-- A trace send is refused without a counter change, or increments the counter. -/
private theorem traceSend_count {party leaking : Bool} {s : TraceState P}
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) :
    sendCount z.2 = sendCount s ∨ sendCount z.2 = sendCount s + 1 := by
  rcases mem_support_traceSend hMac irl hz with hz | ⟨w, -, -, hz⟩
  · left
    rw [hz]
  · right
    rw [hz]
    exact sendUpdate_count s.game party w.1.1

/-- The first-stage records of a send sample are unchanged, except for a first-stage
encapsulation from `headerReceived`, which records its epoch. -/
private theorem sampledSend_encaps1 (s : TraceState P) (party : Bool)
    {w : (SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P) × Bool}
    (hw : w ∈ support (sampledSend P hMac irl s party)) :
    (∀ t, (w.2.1 t).encaps1 = (s.transcript t).encaps1) ∨
      ∃ e a hdr dec x, s.game.stateAt party = .headerReceived e a hdr dec ∧
        w.2.1 = Function.update s.transcript e { (s.transcript e) with encaps1 := some x } := by
  have hmem : (w.1.2, w.2) ∈
      support ((fun w => (w.1.2, w.2)) <$> sampledSend P hMac irl s party) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ hw
  cases hst : s.game.stateAt party
  case keysUnsampled e a =>
    rw [obs_sampledSend_keysUnsampled hMac irl s party hst, support_map] at hmem
    obtain ⟨x, -, hx⟩ := hmem
    left
    intro t
    rw [← (Prod.mk.inj hx).2]
    by_cases ht : t = e
    · rw [ht]
      simp
    · simp [Function.update_of_ne ht]
  case headerReceived e a hdr dec =>
    rw [obs_sampledSend_headerReceived hMac irl s party hst, support_map] at hmem
    obtain ⟨x, -, hx⟩ := hmem
    right
    exact ⟨e, a, hdr, dec, x.1, rfl, by rw [← (Prod.mk.inj hx).2]⟩
  all_goals
    have hsteady : (s.game.stateAt party).SendsNoSample := by
      rw [hst]
      trivial
    left
    intro t
    rw [obs_sampledSend_steady hMac irl s party hsteady w hw]

/-- A trace send preserves the produced-epoch bound: a first-stage encapsulation at epoch `e`
follows keys for every earlier epoch, hence `e - 1` earlier accepted sends. -/
private theorem traceSend_sendBound (party leaking : Bool) (s : TraceState P)
    (hR : RepairInv hMac s.transcript s.game) (hB : SendBound s)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) : SendBound z.2 := by
  rcases mem_support_traceSend hMac irl hz with hz' | ⟨w, hw, -, hz'⟩
  · rw [hz']
    exact hB
  have hcount : sendCount z.2 = sendCount s + 1 := by
    rw [hz']
    exact sendUpdate_count s.game party w.1.1
  have hT : z.2.transcript = w.2.1 := by rw [hz']
  intro t ht
  rw [hcount]
  rw [hT] at ht
  rcases sampledSend_encaps1 hMac irl s party hw with hsame | ⟨e, a, hdr, dec, x, hst, hw2⟩
  · rw [hsame t] at ht
    exact (hB t ht).trans (Nat.le_succ _)
  · rw [hw2] at ht
    by_cases hte : t = e
    · rw [hte]
      by_cases he1 : e ≤ 1
      · omega
      · have hpre := (hR.control.send_prefix party).2 (e - 1) (by omega)
          (by rw [hst]; exact le_rfl)
        obtain ⟨-, hT1⟩ := encaps1_of_key hMac hR party hpre
        have := hB (e - 1) hT1
        omega
    · rw [Function.update_of_ne hte] at ht
      exact (hB t ht).trans (Nat.le_succ _)

variable [DecidableEq P.Sym]

/-- A trace receive keeps the ghost records and the send counters. -/
private theorem traceReceive_frame (repair party : Bool) :
    ∀ n s z, z ∈ support ((traceReceive P hMac irl repair party n).run s) →
      z.2.transcript = s.transcript ∧ sendCount z.2 = sendCount s := by
  intro n s z hz
  rw [traceReceive_run] at hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz
  refine ⟨rfl, ?_⟩
  cases party
  · rw [if_neg Bool.false_ne_true] at hw
    obtain ⟨-, -, h1, h2⟩ := oracleRecvB_flags _ hw
    simp only [sendCount, h1, h2]
  · rw [if_pos rfl] at hw
    obtain ⟨-, -, h1, h2⟩ := oracleRecvA_flags _ hw
    simp only [sendCount, h1, h2]

variable [SampleableType P.K] [SampleableType P.EpochKey]

/-- Two trace games with the same repair flag answer every query identically on states where
their modes agree at every available challenge epoch. -/
private theorem traceImpl_mode_eq (repair : Bool) (m m' : ℕ → Mode) (Q : TraceState P → Prop)
    (h : ∀ e s, Q s → lookupKey s.game e ≠ none → m e = m' e) :
    ∀ t s, Q s →
      (traceImpl P hMac irl repair m t).run s = (traceImpl P hMac irl repair m' t).run s :=
  queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _
    (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl))
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl))
      (fun e s hs => traceChallenge_mode_eq m m' e s (h e s hs)))
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl)

/-- The send counter never decreases, and increases by at most one exactly on sends. -/
private theorem traceImpl_count (repair : Bool) (mode : ℕ → Mode) :
    ∀ t s z, z ∈ support ((traceImpl P hMac irl repair mode t).run s) →
      sendCount s ≤ sendCount z.2 ∧
        sendCount z.2 ≤ sendCount s + if isSendQuery t = true then 1 else 0 := by
  intro t s z hz
  rw [isSendQuery_eq_sendElim irl t]
  have hzero : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P) ProbComp)),
      (∀ t s z, z ∈ support ((c t).run s) →
        z.2.transcript = s.transcript ∧ sendCount z.2 = sendCount s) →
      ∀ t s z, z ∈ support ((c t).run s) → sendCount s ≤ sendCount z.2 ∧
        sendCount z.2 ≤ sendCount s + if (fun _ => false) t then 1 else 0 := by
    intro ι spec c hc t s z hz
    rw [(hc t s z hz).2]
    simp
  have hone : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P) ProbComp)),
      (∀ t s z, z ∈ support ((c t).run s) →
        sendCount z.2 = sendCount s ∨ sendCount z.2 = sendCount s + 1) →
      ∀ t s z, z ∈ support ((c t).run s) → sendCount s ≤ sendCount z.2 ∧
        sendCount z.2 ≤ sendCount s + if (fun _ => true) t then 1 else 0 := by
    intro ι spec c hc t s z hz
    rcases hc t s z hz with h | h <;> rw [h] <;> simp
  exact countStep_add _ _ _ (countStep_add _ _ _ (countStep_add _ _ _ (countStep_add _ _ _
    (countStep_add _ _ _ (countStep_add _ _ _ (countStep_add _ _ _ (countStep_add _ _ _
      (countStep_add _ _ _
        (hzero _ traceUnif_frame)
        (hone _ fun t s z hz => by
          obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
          exact traceSend_count hMac irl hw))
        (hone _ fun t s z hz => by
          obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
          exact traceSend_count hMac irl hw))
        (hzero _ (traceReceive_frame hMac irl repair true)))
        (hzero _ (traceReceive_frame hMac irl repair false)))
        (hone _ fun _ s z hz => by exact traceSend_count hMac irl hz))
        (hone _ fun _ s z hz => by exact traceSend_count hMac irl hz))
        (hzero _ (traceChallenge_frame mode)))
        (hzero _ traceCorruptA_frame))
        (hzero _ traceCorruptB_frame) t s z hz

/-- Every query of a repaired trace game preserves `TraceInv` and the produced-epoch bound. -/
private theorem traceImpl_sendBound
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (mode : ℕ → Mode) :
    QueryImpl.PreservesInv (traceImpl P hMac irl true mode)
      (fun s => TraceInv hMac true s ∧ SendBound s) := by
  have hframe : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P) ProbComp)),
      QueryImpl.PreservesInv c (TraceInv hMac true) →
      (∀ t s z, z ∈ support ((c t).run s) →
        z.2.transcript = s.transcript ∧ sendCount z.2 = sendCount s) →
      QueryImpl.PreservesInv c (fun s => TraceInv hMac true s ∧ SendBound s) := by
    intro ι spec c hc hf t s hs z hz
    obtain ⟨hT, hC⟩ := hf t s z hz
    refine ⟨hc t s hs.1 z hz, fun e he => ?_⟩
    rw [hT] at he
    rw [hC]
    exact hs.2 e he
  have hsend : ∀ (party leaking : Bool) (s : TraceState P), TraceInv hMac true s ∧ SendBound s →
      ∀ z ∈ support ((traceSend P hMac irl party leaking).run s),
        TraceInv hMac true z.2 ∧ SendBound z.2 := fun party leaking s hs z hz =>
    ⟨traceSend_traceInv hMac irl party leaking true s hs.1 hz,
      traceSend_sendBound hMac irl party leaking s (hs.1.1 (Or.inl rfl)).1 hs.2 hz⟩
  refine ((((((((((hframe _ (traceUnif_preservesInv hMac true) traceUnif_frame).add ?_).add
    ?_).add (hframe _ (traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct true true) (traceReceive_frame hMac irl true true))).add
    (hframe _ (traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct true false) (traceReceive_frame hMac irl true false))).add ?_).add ?_).add
    (hframe _ (traceChallenge_preservesInv hMac mode true) (traceChallenge_frame mode))).add
    (hframe _ (traceCorruptA_preservesInv hMac true) traceCorruptA_frame)).add
    (hframe _ (traceCorruptB_preservesInv hMac true) traceCorruptB_frame))
  · intro t s hs z hz
    obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
    exact hsend true false s hs w hw
  · intro t s hs z hz
    obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
    exact hsend false false s hs w hw
  · exact fun _ s hs z hz => hsend true true s hs z hz
  · exact fun _ s hs z hz => hsend false true s hs z hz

/-- Two repaired trace runs whose modes agree on every positive epoch up to the send budget have
the same output distribution. The modes differ only at challenges, every available challenge key
is for a positive encapsulated epoch, and the produced-epoch bound and the send budget bound that
epoch by `qS` along every adaptive run. -/
private theorem run_mode_evalDist_eq
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) (m m' : ℕ → Mode)
    (hm : ∀ e, 0 < e → e ≤ qS → m e = m' e) :
    𝒟[Prod.fst <$> run P hMac irl true m A] = 𝒟[Prod.fst <$> run P hMac irl true m' A] := by
  have hbad : Pr[fun z => qS < sendCount z.2 | run P hMac irl true m A] = 0 := by
    rw [probEvent_eq_zero_iff]
    intro z hz
    have hle := stateCounter_simulateQ_run_le (traceImpl P hMac irl true m) sendCount
      (fun t => isSendQuery t = true)
      (fun t s z hz => (traceImpl_count hMac irl true m t s z hz).2) A qS hqS _ z hz
    have h0 : z.2.game.nA + z.2.game.nB ≤ qS := by
      simpa [sendCount, SCKAScheme.initGameState] using hle
    exact not_lt.mpr h0
  refine evalDist_ext fun x => ?_
  rw [probOutput_fst_map_eq_probEvent, probOutput_fst_map_eq_probEvent]
  have habs := abs_probEvent_simulateQ_run_sub_le_bad_of_inv
    (traceImpl P hMac irl true m) (traceImpl P hMac irl true m')
    (fun s => TraceInv hMac true s ∧ SendBound s) (fun s => qS < sendCount s)
    (traceImpl_sendBound hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct m)
    (fun t s hs z hz => lt_of_lt_of_le hs (traceImpl_count hMac irl true m t s z hz).1)
    (fun t s hs hb => traceImpl_mode_eq hMac irl true m m'
      (fun s => (TraceInv hMac true s ∧ SendBound s) ∧ ¬ qS < sendCount s)
      (fun e s hs hk => by
        obtain ⟨party, hp⟩ := keysAt_of_lookupKey hk
        obtain ⟨hpos, hT⟩ := encaps1_of_key hMac (hs.1.1.1 (Or.inl rfl)).1 party hp
        exact hm e hpos ((hs.1.2 e hT).trans (not_lt.mp hs.2)))
      t s ⟨hs, hb⟩)
    A (fun y => y = x) _ ⟨traceInv_init hMac true, sendBound_init hMac⟩
  change |(Pr[fun z => z.1 = x | run P hMac irl true m A]).toReal -
      (Pr[fun z => z.1 = x | run P hMac irl true m' A]).toReal| ≤
    (Pr[fun z => qS < sendCount z.2 | run P hMac irl true m A]).toReal at habs
  rw [hbad, ENNReal.toReal_zero, abs_nonpos_iff, sub_eq_zero] at habs
  exact (ENNReal.toReal_eq_toReal_iff' probEvent_ne_top probEvent_ne_top).mp habs

end Endpoints

/-- **`hybrid_endpoints`**: the repaired hybrid with no uniform epochs has the distribution of the
repaired real-key game, and the hybrid with uniform keys through epoch `qS` has the distribution of
the repaired uniform-key game. Every available challenge key is for a positive epoch at most the
number of accepted sends, which the send budget bounds along every adaptive run. -/
theorem hybrid_endpoints (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) :
    𝒟[hybrid P hMac irl A 0] =
        𝒟[Prod.fst <$> run P hMac irl true (fun _ => if false then .uniform else .real) A] ∧
      𝒟[hybrid P hMac irl A qS] =
        𝒟[Prod.fst <$> run P hMac irl true (fun _ => if true then .uniform else .real) A] :=
  ⟨run_mode_evalDist_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS _ _
      fun _ he _ => by simp [Nat.not_le.mpr he],
    run_mode_evalDist_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS _ _
      fun _ _ he => by simp [he]⟩

/-! ### Combinators over sums of oracles -/

/-- Query-wise step relations combine over a sum of oracle implementations. -/
theorem relStep_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}
    (R : σ → σ → Prop) {i₁ : QueryImpl spec₁ (StateT σ ProbComp)}
    {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (h₁ : ∀ t s z, z ∈ support ((i₁ t).run s) → R s z.2)
    (h₂ : ∀ t s z, z ∈ support ((i₂ t).run s) → R s z.2) :
    ∀ t s z, z ∈ support (((i₁ + i₂) t).run s) → R s z.2
  | .inl t, s, z, hz => h₁ t s z hz
  | .inr t, s, z, hz => h₂ t s z hz

/-- Query-wise equality, or commitment of both outcomes, combine over a sum of implementations. -/
theorem queryEqOr_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}
    (Inv C : σ → Prop) {i₁ j₁ : QueryImpl spec₁ (StateT σ ProbComp)}
    {i₂ j₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (h₁ : ∀ t s, Inv s → (i₁ t).run s = (j₁ t).run s ∨
      ((∀ z ∈ support ((i₁ t).run s), C z.2) ∧ ∀ z ∈ support ((j₁ t).run s), C z.2))
    (h₂ : ∀ t s, Inv s → (i₂ t).run s = (j₂ t).run s ∨
      ((∀ z ∈ support ((i₂ t).run s), C z.2) ∧ ∀ z ∈ support ((j₂ t).run s), C z.2)) :
    ∀ t s, Inv s → ((i₁ + i₂) t).run s = ((j₁ + j₂) t).run s ∨
      ((∀ z ∈ support (((i₁ + i₂) t).run s), C z.2) ∧
        ∀ z ∈ support (((j₁ + j₂) t).run s), C z.2)
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

/-- Sampling a value and discarding it does not change the distribution of a computation. -/
theorem evalDist_bind_ignore {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] :=
  evalDist_ext fun y => by
    rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- A stopped oracle step: the oracle step with the answer dropped where `stop` holds. -/
theorem stopOnState_run {ι σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool) (t : spec.Domain) (s : σ) :
    ((stopOnState impl stop t).run).run s =
      (fun w => (if stop w.2 then none else some w.1, w.2)) <$> (impl t).run s := by
  change ((impl t).run s >>= fun w => pure (if stop w.2 then none else some w.1, w.2)) = _
  rw [map_eq_bind_pure_comp]
  rfl

/-- An outcome of a stopped oracle has the next state of an outcome of the oracle. -/
theorem mem_support_stopOnState {ι σ : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT σ ProbComp)} {stop : σ → Bool} {t : spec.Domain} {s : σ}
    {z : Option (spec.Range t) × σ}
    (hz : z ∈ support (((stopOnState impl stop t).run).run s)) :
    ∃ w ∈ support ((impl t).run s), z = (if stop w.2 then none else some w.1, w.2) := by
  rw [stopOnState_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- A stopped oracle step depends only on the oracle's step. -/
private theorem stopOnState_run_congr {ι σ : Type} {spec : OracleSpec ι}
    {impl impl' : QueryImpl spec (StateT σ ProbComp)} (stop : σ → Bool) {t : spec.Domain} {s : σ}
    (h : (impl t).run s = (impl' t).run s) :
    ((stopOnState impl stop t).run).run s = ((stopOnState impl' stop t).run).run s := by
  rw [stopOnState_run, stopOnState_run, h]

/-! ### The literal initial trace state and the stop at the selected epoch -/

/-- The literal initial state of the trace games. -/
def initTrace (P : Parameters ProbComp) (hMac : P.Mac = Unit) : TraceState P :=
  { game := SCKAScheme.initGameState (MLKEMBraid.initA P (auth P hMac) ())
      (MLKEMBraid.initB P (auth P hMac) ())
    transcript := fun _ => { keypair := none, encaps1 := none }
    bad := false }

/-- Stop when the selected epoch `e` is exposed. -/
def targetStop (e : ℕ) (s : TraceState P) : Bool :=
  decide (e ∈ s.game.exposed)

/-- The selected epoch `e` is challenged and unexposed. -/
def Committed (e : ℕ) (s : TraceState P) : Prop :=
  e ∈ s.game.challenged ∧ e ∉ s.game.exposed

/-! ### Installed trace games -/

/-- The key-generation send of epoch `t` with the key pair `(pk, sk)`: the result of the
key-generation branch of `sendRleak`. -/
def keygenStep (P : Parameters ProbComp) (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (pk : P.PK)
    (sk : P.SK) : SendResult P Unit :=
  let hdr := P.inc.toHeader pk
  let (chunk, enc) :=
    (EncoderState.init P.ecpHdr (hdr, (auth P hMac).macHeader a t hdr)).nextChunk
  { msg := { epoch := t, type := .hdr, data := some chunk }
    sendingEpoch := t - 1, outputKey := none
    state := .keysSampled t a sk (P.inc.toVector pk) enc }

/-- The first-stage encapsulation send of epoch `t` with the sample `(es, ct1, k)`: the result of
the first-stage encapsulation branch of `sendRleak`. -/
def encaps1Step (P : Parameters ProbComp) (hMac : P.Mac = Unit) (t : ℕ) (a : Unit)
    (hdr : P.inc.PKheader) (dec : DecoderState P.inc.PKvector P.Sym) (es : P.inc.St)
    (ct1 : P.inc.C₁) (k : P.K) : SendResult P Unit :=
  let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
  { msg := { epoch := t, type := .ct1, data := some chunk }
    sendingEpoch := t - 1, outputKey := some (t, P.kdfOK k t)
    state := .ct1Sampled t ((auth P hMac).update a t (P.kdfOK k t)) hdr es ct1 enc dec }

/-- The bad flag after a first-stage encapsulation sample `c` of epoch `t`. -/
def encaps1Bad [DecidableEq P.EpochKey] (s : TraceState P) (t : ℕ)
    (c : P.inc.St × P.inc.C₁ × P.K) : Bool :=
  match (s.transcript t).keypair with
  | none => s.bad
  | some (pk, sk) => s.bad || decide (decapsEpochKey (P := P) t pk sk c.1 c.2.1 ≠
      some (P.kdfOK c.2.2 t))

/-- The sample of a key-generation send. -/
theorem sampledSend_eq_keygen [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (s : TraceState P) (party : Bool) {t : ℕ}
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled t a) :
    sampledSend P hMac irl s party = (fun x : (P.PK × P.SK) × irl.KeygenRand =>
      ((keygenStep P hMac t a x.1.1 x.1.2, SendRand.keygen x.2),
        Function.update s.transcript t { (s.transcript t) with keypair := some x.1 }, s.bad)) <$>
      irl.keygenRleak := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp]
  exact bind_congr fun x => by obtain ⟨⟨pk, sk⟩, rand⟩ := x; rfl

/-- The sample of a first-stage encapsulation send. -/
theorem sampledSend_eq_encaps1 [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (s : TraceState P) (party : Bool) {t : ℕ}
    {a : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived t a hdr dec) :
    sampledSend P hMac irl s party = (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
      ((encaps1Step P hMac t a hdr dec x.1.1 x.1.2.1 x.1.2.2, SendRand.encaps1 x.2),
        Function.update s.transcript t { (s.transcript t) with encaps1 := some x.1 },
        encaps1Bad s t x.1)) <$> irl.encaps1Rleak hdr := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp]
  exact bind_congr fun x => by obtain ⟨⟨es, ct1, k⟩, rand⟩ := x; rfl

/-- The installed sample of `party`: a key generation of epoch `e` with an installed key pair, or
a first-stage encapsulation of epoch `e` with an installed sample, with its ghost records and the
bad flag of the same sample. -/
def installedSample (P : Parameters ProbComp) [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (e : ℕ) (kp : Option (P.PK × P.SK)) (ec : Option (P.inc.St × P.inc.C₁ × P.K))
    (s : TraceState P) (party : Bool) :
    Option (SendResult P Unit × (ℕ → EpochTranscript P) × Bool) :=
  match s.game.stateAt party, kp, ec with
  | .keysUnsampled t a, some (pk, sk), _ =>
      if t = e then some (keygenStep P hMac t a pk sk,
        Function.update s.transcript t { (s.transcript t) with keypair := some (pk, sk) }, s.bad)
      else none
  | .headerReceived t a hdr dec, _, some (es, ct1, k) =>
      if t = e then some (encaps1Step P hMac t a hdr dec es ct1 k,
        Function.update s.transcript t { (s.transcript t) with encaps1 := some (es, ct1, k) },
        encaps1Bad s t (es, ct1, k))
      else none
  | _, _, _ => none

/-- Without installed samples nothing is installed. -/
theorem installedSample_none [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (e : ℕ)
    (s : TraceState P) (party : Bool) : installedSample P hMac e none none s party = none := by
  rcases hst : s.game.stateAt party <;> simp [installedSample, hst]

/-- A send of `party` in the installed trace game. An installed sample replaces sampling; a leaking
installed sample is refused as in `traceSend`, or else accepted only to expose `e`, without coins.
Every other send is `traceSend`. -/
def traceSendAt (P : Parameters ProbComp) [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) :
    StateT (TraceState P) ProbComp
      (Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand)) :=
  fun s => match installedSample P hMac e kp ec s party with
    | none => traceSend P hMac irl party leaking s
    | some (r, T, b) =>
        if leaking && decide ({e} ∩ s.game.challenged ≠ ∅) then pure (none, s)
        else pure (if leaking then none
            else some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg, SendRand.none),
          { game := { sendUpdate s.game party r with
              exposed := if leaking then s.game.exposed ∪ {e} else s.game.exposed },
            transcript := T, bad := b })

/-- The ordinary send oracle of `party` in the installed trace game. -/
def tracePlainAt (P : Parameters ProbComp) [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym))
      (StateT (TraceState P) ProbComp) :=
  fun _ => (fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSendAt P hMac irl e kp ec party false

/-- The leaking send oracle of `party` in the installed trace game. -/
def traceLeakAt (P : Parameters ProbComp) [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym ×
      SendRand irl.KeygenRand irl.Encaps1Rand)) (StateT (TraceState P) ProbComp) :=
  fun _ => traceSendAt P hMac irl e kp ec party true

/-- The challenge oracle in which an eligible challenge of epoch `e` answers `x` if it is given;
every other challenge follows `mode`. -/
def traceChallengeAt (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) (e : ℕ) (x : Option P.EpochKey) :
    QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (TraceState P) ProbComp) :=
  fun t s =>
    if t ∈ s.game.exposed ∨ t ∈ s.game.challenged then pure (none, s)
    else match lookupKey s.game t with
      | none => pure (none, s)
      | some k => (fun out => (some out, { s with game :=
          { s.game with challenged := insert t s.game.challenged } })) <$>
          (match x with
            | some v => if t = e then pure v else challengeValue P (mode t) t k
            | none => challengeValue P (mode t) t k)

/-- The repaired trace game with installed samples `kp`, `ec` at epoch `e` and installed
challenge value `x` for an eligible challenge of `e`. -/
def traceImplAt (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ)
    (kp : Option (P.PK × P.SK)) (ec : Option (P.inc.St × P.inc.C₁ × P.K))
    (x : Option P.EpochKey) (mode : ℕ → Mode) :
    QueryImpl (Spec P irl) (StateT (TraceState P) ProbComp) :=
  traceUnif P + tracePlainAt P hMac irl e kp ec true + tracePlainAt P hMac irl e kp ec false +
    traceReceive P hMac irl true true + traceReceive P hMac irl true false +
    traceLeakAt P hMac irl e kp ec true + traceLeakAt P hMac irl e kp ec false +
    traceChallengeAt P mode e x + traceCorruptA P + traceCorruptB P

section InstalledLemmas

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- Without installed samples the installed send is `traceSend`. -/
theorem traceSendAt_none (e : ℕ) (party leaking : Bool) :
    traceSendAt P hMac irl e none none party leaking = traceSend P hMac irl party leaking := by
  funext s
  simp only [traceSendAt, installedSample_none]

/-- Without installed samples the installed ordinary send is `tracePlain`. -/
theorem tracePlainAt_none (e : ℕ) (party : Bool) :
    tracePlainAt P hMac irl e none none party = tracePlain P hMac irl party := by
  funext t
  simp only [tracePlainAt, tracePlain, traceSendAt_none]

/-- Without installed samples the installed leaking send is `traceLeak`. -/
theorem traceLeakAt_none (e : ℕ) (party : Bool) :
    traceLeakAt P hMac irl e none none party = traceLeak P hMac irl party := by
  funext t
  simp only [traceLeakAt, traceLeak, traceSendAt_none]

variable [SampleableType P.K] [SampleableType P.EpochKey]

omit [DecidableEq P.EpochKey] in
/-- Without an installed challenge value the installed challenge is `traceChallenge`. -/
theorem traceChallengeAt_none (mode : ℕ → Mode) (e : ℕ) :
    traceChallengeAt P mode e none = traceChallenge P mode := rfl

omit [DecidableEq P.EpochKey] in
/-- With an installed challenge value, the mode at `e` is irrelevant. -/
theorem traceChallengeAt_congr (m m' : ℕ → Mode) (e : ℕ) (x : P.EpochKey)
    (h : ∀ t, t ≠ e → m t = m' t) :
    traceChallengeAt P m e (some x) = traceChallengeAt P m' e (some x) := by
  funext t s
  by_cases ht : t = e
  · simp only [traceChallengeAt, if_pos ht]
  · simp only [traceChallengeAt, if_neg ht, h t ht]

variable [DecidableEq P.Sym]

/-- Without installed samples or challenge value the installed game is the repaired trace game. -/
theorem traceImplAt_none (e : ℕ) (mode : ℕ → Mode) :
    traceImplAt P hMac irl e none none none mode = traceImpl P hMac irl true mode := by
  simp only [traceImplAt, traceImpl, tracePlainAt_none, traceLeakAt_none, traceChallengeAt_none]
  rfl

/-- With an installed challenge value, the mode at `e` is irrelevant. -/
theorem traceImplAt_congr (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (x : P.EpochKey) (m m' : ℕ → Mode)
    (h : ∀ t, t ≠ e → m t = m' t) :
    traceImplAt P hMac irl e kp ec (some x) m = traceImplAt P hMac irl e kp ec (some x) m' := by
  unfold traceImplAt
  rw [traceChallengeAt_congr m m' e x h]

end InstalledLemmas

/-! ### Exposure and challenge flags of one query -/

/-- One query never shrinks the exposed or challenged epochs and never exposes an epoch that is
already challenged. -/
structure FlagStep (s s' : TraceState P) : Prop where
  /-- Exposed epochs only grow. -/
  exposed : s.game.exposed ⊆ s'.game.exposed
  /-- Challenged epochs only grow. -/
  challenged : s.game.challenged ⊆ s'.game.challenged
  /-- A challenged epoch is never newly exposed. -/
  fresh : ∀ t, t ∈ s.game.challenged → t ∈ s'.game.exposed → t ∈ s.game.exposed

/-- No state change is a flag step. -/
theorem FlagStep.refl (s : TraceState P) : FlagStep s s :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ h => h⟩

/-- A receive oracle keeps the exposed and challenged epochs. -/
private theorem recvA_flags {IK Rand : Type} [DecidableEq P.EpochKey]
    (scka : SCKAScheme ProbComp IK (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) Rand)
    {n : ℕ} {g : MLKEMBraid.GameState P Unit}
    {w : Option (ℕ × Option ℕ) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleRecvA scka n).run g)) :
    w.2.exposed = g.exposed ∧ w.2.challenged = g.challenged := by
  rcases hm : g.msgB n with _ | ⟨ρ, tsnd⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl⟩
  rcases hr : scka.recvA g.stA ρ with _ | ⟨keyOpt, trcv, st'⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    rcases keyOpt with _ | ⟨tI, key⟩ <;> exact ⟨rfl, rfl⟩

/-- The version of `recvA_flags` for B. -/
private theorem recvB_flags {IK Rand : Type} [DecidableEq P.EpochKey]
    (scka : SCKAScheme ProbComp IK (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) Rand)
    {n : ℕ} {g : MLKEMBraid.GameState P Unit}
    {w : Option (ℕ × Option ℕ) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleRecvB scka n).run g)) :
    w.2.exposed = g.exposed ∧ w.2.challenged = g.challenged := by
  rcases hm : g.msgA n with _ | ⟨ρ, tsnd⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl⟩
  rcases hr : scka.recvB g.stB ρ with _ | ⟨keyOpt, trcv, st'⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    exact ⟨rfl, rfl⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hm hr, mem_support_pure_iff] at hw
    subst hw
    rcases keyOpt with _ | ⟨tI, key⟩ <;> exact ⟨rfl, rfl⟩

section FlagSteps

/-- The uniform-randomness query is a flag step. -/
theorem traceUnif_flagStep :
    ∀ t s z, z ∈ support ((traceUnif P t).run s) → FlagStep s z.2 := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleUnif (State P Unit) (State P Unit) P.EpochKey (Message P.Sym) t) hz
  have hw' : w.2 = s.game :=
    SCKAScheme.oracleUnif_preservesInv (fun g => g = s.game) t s.game rfl w hw
  change FlagStep s { s with game := w.2 }
  rw [hw']
  exact FlagStep.refl s

/-- A corruption of A is a flag step. -/
theorem traceCorruptA_flagStep :
    ∀ t s z, z ∈ support ((traceCorruptA P t).run s) → FlagStep s z.2 := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
  cases t
  change FlagStep s { s with game := w.2 }
  rcases mem_support_oracleCorruptA hw with hw | ⟨hV, hw⟩
  · rw [hw]
    exact FlagStep.refl s
  · rw [hw]
    refine ⟨Finset.subset_union_left, Finset.Subset.refl _, fun u hu hmem => ?_⟩
    rcases Finset.mem_union.mp hmem with h | h
    · exact h
    · exact absurd (Finset.mem_inter.mpr ⟨h, hu⟩) (by rw [hV]; exact Finset.notMem_empty u)

/-- A corruption of B is a flag step. -/
theorem traceCorruptB_flagStep :
    ∀ t s z, z ∈ support ((traceCorruptB P t).run s) → FlagStep s z.2 := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
  cases t
  change FlagStep s { s with game := w.2 }
  rcases mem_support_oracleCorruptB hw with hw | ⟨hV, hw⟩
  · rw [hw]
    exact FlagStep.refl s
  · rw [hw]
    refine ⟨Finset.subset_union_left, Finset.Subset.refl _, fun u hu hmem => ?_⟩
    rcases Finset.mem_union.mp hmem with h | h
    · exact h
    · exact absurd (Finset.mem_inter.mpr ⟨h, hu⟩) (by rw [hV]; exact Finset.notMem_empty u)

/-- A challenge is a flag step. -/
theorem traceChallenge_flagStep [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) : ∀ t s z, z ∈ support ((traceChallenge P mode t).run s) →
      FlagStep s z.2 := by
  intro t s z hz
  rcases mem_support_traceChallenge hz with hz | ⟨-, hz⟩
  · rw [hz]
    exact FlagStep.refl s
  · rw [hz]
    exact ⟨Finset.Subset.refl _, Finset.subset_insert _ _, fun _ _ h => h⟩

/-- An installed challenge leaves the state unchanged, or adds an unexposed epoch to the
challenged set. -/
theorem mem_support_traceChallengeAt [SampleableType P.K] [SampleableType P.EpochKey]
    {mode : ℕ → Mode} {e : ℕ} {x : Option P.EpochKey} {t : ℕ} {s : TraceState P}
    {z : Option P.EpochKey × TraceState P}
    (hz : z ∈ support ((traceChallengeAt P mode e x t).run s)) :
    z.2 = s ∨ (t ∉ s.game.exposed ∧
      z.2 = { s with game := { s.game with challenged := insert t s.game.challenged } }) := by
  change z ∈ support (traceChallengeAt P mode e x t s) at hz
  by_cases hex : t ∈ s.game.exposed ∨ t ∈ s.game.challenged
  · left
    simp only [traceChallengeAt, if_pos hex, mem_support_pure_iff] at hz
    rw [hz]
  · cases hk : lookupKey s.game t with
    | none =>
        simp only [traceChallengeAt, if_neg hex, hk, mem_support_pure_iff] at hz
        left
        rw [hz]
    | some k =>
        simp only [traceChallengeAt, if_neg hex, hk, support_map] at hz
        obtain ⟨out, -, rfl⟩ := hz
        exact Or.inr ⟨fun h => hex (Or.inl h), rfl⟩

/-- An installed challenge is a flag step. -/
theorem traceChallengeAt_flagStep [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) (e : ℕ) (x : Option P.EpochKey) :
    ∀ t s z, z ∈ support ((traceChallengeAt P mode e x t).run s) → FlagStep s z.2 := by
  intro t s z hz
  rcases mem_support_traceChallengeAt hz with hz | ⟨-, hz⟩
  · rw [hz]
    exact FlagStep.refl s
  · rw [hz]
    exact ⟨Finset.Subset.refl _, Finset.subset_insert _ _, fun _ _ h => h⟩

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A trace send is a flag step. -/
theorem traceSend_flagStep {party leaking : Bool} {s : TraceState P}
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) : FlagStep s z.2 := by
  rcases mem_support_traceSend hMac irl hz with hz | ⟨w, -, hX, hz⟩
  · rw [hz]
    exact FlagStep.refl s
  · rw [hz]
    obtain ⟨-, hC⟩ := sendUpdate_flags s.game party w.1.1
    cases leaking
    · exact ⟨Finset.Subset.refl _, subset_of_eq hC.symm, fun _ _ h => h⟩
    · have hX' := hX rfl
      refine ⟨Finset.subset_union_left, subset_of_eq hC.symm, fun u hu hmem => ?_⟩
      rcases Finset.mem_union.mp hmem with h | h
      · exact h
      · exact absurd (Finset.mem_inter.mpr ⟨h, hu⟩) (by rw [hX']; exact Finset.notMem_empty u)

/-- An installed trace send is a flag step. -/
theorem traceSendAt_flagStep (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) {party leaking : Bool} {s : TraceState P}
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSendAt P hMac irl e kp ec party leaking).run s)) :
    FlagStep s z.2 := by
  change z ∈ support (traceSendAt P hMac irl e kp ec party leaking s) at hz
  rcases hI : installedSample P hMac e kp ec s party with _ | ⟨r, T, b⟩
  · simp only [traceSendAt, hI] at hz
    exact traceSend_flagStep hMac irl hz
  · simp only [traceSendAt, hI] at hz
    by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
    · rw [if_pos hc, mem_support_pure_iff] at hz
      rw [hz]
      exact FlagStep.refl s
    · rw [if_neg hc, mem_support_pure_iff] at hz
      rw [hz]
      obtain ⟨-, hC⟩ := sendUpdate_flags s.game party r
      cases leaking
      · exact ⟨Finset.Subset.refl _, subset_of_eq hC.symm, fun _ _ h => h⟩
      · have hdisj : {e} ∩ s.game.challenged = ∅ := by
          by_contra hne
          exact hc (by simp [hne])
        refine ⟨Finset.subset_union_left, subset_of_eq hC.symm, fun u hu hmem => ?_⟩
        rcases Finset.mem_union.mp hmem with h | h
        · exact h
        · exact absurd (Finset.mem_inter.mpr ⟨h, hu⟩)
            (by rw [hdisj]; exact Finset.notMem_empty u)

/-- An ordinary send is a flag step. -/
theorem tracePlain_flagStep (party : Bool) :
    ∀ t s z, z ∈ support ((tracePlain P hMac irl party t).run s) → FlagStep s z.2 := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain hMac irl hz
  exact traceSend_flagStep hMac irl hw

/-- An installed ordinary send is a flag step. -/
theorem tracePlainAt_flagStep (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party : Bool) :
    ∀ t s z, z ∈ support ((tracePlainAt P hMac irl e kp ec party t).run s) → FlagStep s z.2 := by
  intro t s z hz
  change z ∈ support (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSendAt P hMac irl e kp ec party false).run s) at hz
  rw [StateT.run_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact traceSendAt_flagStep hMac irl e kp ec hw

variable [DecidableEq P.Sym]

/-- A trace receive is a flag step. -/
theorem traceReceive_flagStep (repair party : Bool) :
    ∀ n s z, z ∈ support ((traceReceive P hMac irl repair party n).run s) → FlagStep s z.2 := by
  intro n s z hz
  rw [traceReceive_run] at hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz
  change FlagStep s { s with game := w.2 }
  cases party
  · rw [if_neg Bool.false_ne_true] at hw
    obtain ⟨h1, h2⟩ := recvB_flags _ hw
    exact ⟨subset_of_eq h1.symm, subset_of_eq h2.symm, fun _ _ h => h1 ▸ h⟩
  · rw [if_pos rfl] at hw
    obtain ⟨h1, h2⟩ := recvA_flags _ hw
    exact ⟨subset_of_eq h1.symm, subset_of_eq h2.symm, fun _ _ h => h1 ▸ h⟩

variable [SampleableType P.K] [SampleableType P.EpochKey]

/-- Every query of a trace game is a flag step. -/
theorem traceImpl_flagStep (repair : Bool) (mode : ℕ → Mode) :
    ∀ t s z, z ∈ support ((traceImpl P hMac irl repair mode t).run s) → FlagStep s z.2 :=
  relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
    (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
      traceUnif_flagStep (tracePlain_flagStep hMac irl true))
      (tracePlain_flagStep hMac irl false))
      (traceReceive_flagStep hMac irl repair true))
      (traceReceive_flagStep hMac irl repair false))
      (fun _ _ _ hz => traceSend_flagStep hMac irl hz))
      (fun _ _ _ hz => traceSend_flagStep hMac irl hz))
      (traceChallenge_flagStep mode)) traceCorruptA_flagStep) traceCorruptB_flagStep

/-- Every query of an installed trace game is a flag step. -/
theorem traceImplAt_flagStep (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (x : Option P.EpochKey) (mode : ℕ → Mode) :
    ∀ t s z, z ∈ support ((traceImplAt P hMac irl e kp ec x mode t).run s) → FlagStep s z.2 :=
  relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
    (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
      traceUnif_flagStep (tracePlainAt_flagStep hMac irl e kp ec true))
      (tracePlainAt_flagStep hMac irl e kp ec false))
      (traceReceive_flagStep hMac irl true true))
      (traceReceive_flagStep hMac irl true false))
      (fun _ _ _ hz => traceSendAt_flagStep hMac irl e kp ec hz))
      (fun _ _ _ hz => traceSendAt_flagStep hMac irl e kp ec hz))
      (traceChallengeAt_flagStep mode e x)) traceCorruptA_flagStep) traceCorruptB_flagStep

end FlagSteps

/-! ### Stopping at the exposure of the selected epoch -/

section Stopping

variable [SampleableType P.K] [SampleableType P.EpochKey]

/-- Two challenge modes agreeing off `e` answer every challenge identically, except an eligible
challenge of `e`, after which both commit to `e`. -/
theorem traceChallenge_eq_or (m m' : ℕ → Mode) (e : ℕ) (hm : ∀ t, t ≠ e → m t = m' t) :
    ∀ t (s : TraceState P), True → (traceChallenge P m t).run s = (traceChallenge P m' t).run s ∨
      ((∀ z ∈ support ((traceChallenge P m t).run s), Committed e z.2) ∧
        ∀ z ∈ support ((traceChallenge P m' t).run s), Committed e z.2) := by
  intro t s _
  by_cases ht : t = e
  · subst ht
    by_cases hex : t ∈ s.game.exposed ∨ t ∈ s.game.challenged
    · left
      change traceChallenge P m t s = traceChallenge P m' t s
      simp only [traceChallenge, if_pos hex]
    · cases hk : lookupKey s.game t with
      | none =>
          left
          change traceChallenge P m t s = traceChallenge P m' t s
          simp only [traceChallenge, if_neg hex, hk]
      | some k =>
          right
          have hc : ∀ mm : ℕ → Mode, ∀ z ∈ support ((traceChallenge P mm t).run s),
              Committed t z.2 := by
            intro mm z hz
            change z ∈ support (traceChallenge P mm t s) at hz
            simp only [traceChallenge, if_neg hex, hk, support_map] at hz
            obtain ⟨out, -, rfl⟩ := hz
            exact ⟨Finset.mem_insert_self t _, fun h => hex (Or.inl h)⟩
          exact ⟨hc m, hc m'⟩
  · left
    change traceChallenge P m t s = traceChallenge P m' t s
    simp only [traceChallenge, hm t ht]

/-- Once `e` is exposed, two challenge modes agreeing off `e` answer every challenge identically. -/
theorem traceChallenge_eq_of_exposed (m m' : ℕ → Mode) (e : ℕ)
    (hm : ∀ t, t ≠ e → m t = m' t) :
    ∀ t (s : TraceState P), e ∈ s.game.exposed →
      (traceChallenge P m t).run s = (traceChallenge P m' t).run s := by
  intro t s hs
  change traceChallenge P m t s = traceChallenge P m' t s
  by_cases ht : t = e
  · subst ht
    simp only [traceChallenge, if_pos (Or.inl hs)]
  · simp only [traceChallenge, hm t ht]

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym] (hMac : P.Mac = Unit)
  (irl : P.kem.IncrementalRandLeak P.inc)

/-- Two repaired trace games whose modes agree off `e` answer every query identically, except an
eligible challenge of `e`, after which both commit to `e`. -/
theorem traceImpl_eq_or (m m' : ℕ → Mode) (e : ℕ) (hm : ∀ t, t ≠ e → m t = m' t) :
    ∀ t s, True → (traceImpl P hMac irl true m t).run s = (traceImpl P hMac irl true m' t).run s ∨
      ((∀ z ∈ support ((traceImpl P hMac irl true m t).run s), Committed e z.2) ∧
        ∀ z ∈ support ((traceImpl P hMac irl true m' t).run s), Committed e z.2) :=
  queryEqOr_add _ _ (queryEqOr_add _ _ (queryEqOr_add _ _ (queryEqOr_add _ _
    (queryEqOr_add _ _ (queryEqOr_add _ _ (queryEqOr_add _ _ (queryEqOr_add _ _
      (queryEqOr_add _ _ (fun _ _ _ => Or.inl rfl) (fun _ _ _ => Or.inl rfl))
      (fun _ _ _ => Or.inl rfl)) (fun _ _ _ => Or.inl rfl)) (fun _ _ _ => Or.inl rfl))
      (fun _ _ _ => Or.inl rfl)) (fun _ _ _ => Or.inl rfl))
      (traceChallenge_eq_or m m' e hm)) (fun _ _ _ => Or.inl rfl)) (fun _ _ _ => Or.inl rfl)

/-- Once `e` is exposed, two repaired trace games whose modes agree off `e` answer every query
identically. -/
theorem traceImpl_eq_of_exposed (m m' : ℕ → Mode) (e : ℕ) (hm : ∀ t, t ≠ e → m t = m' t) :
    ∀ t s, e ∈ s.game.exposed →
      (traceImpl P hMac irl true m t).run s = (traceImpl P hMac irl true m' t).run s :=
  queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _
    (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl))
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl))
      (traceChallenge_eq_of_exposed m m' e hm)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl)

/-- From a state where `e` is exposed, two repaired trace games whose modes agree off `e` accept
with the same probability. -/
theorem probOutput_run_eq_of_exposed (m m' : ℕ → Mode) (e : ℕ)
    (hm : ∀ t, t ≠ e → m t = m' t) (s : TraceState P) (hs : targetStop e s = true)
    (oa : OracleComp (Spec P irl) Bool) :
    Pr[= true | (simulateQ (traceImpl P hMac irl true m) oa).run' s] =
      Pr[= true | (simulateQ (traceImpl P hMac irl true m') oa).run' s] := by
  have hs' : e ∈ s.game.exposed := by simpa [targetStop] using hs
  have h := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (traceImpl P hMac irl true m) (traceImpl P hMac irl true m')
    (fun s => e ∈ s.game.exposed) id
    (fun t s hs z hz => (traceImpl_flagStep hMac irl true m t s z hz).exposed hs)
    (fun t s hs => by
      rw [traceImpl_eq_of_exposed hMac irl m m' e hm t s hs, Prod.map_id, id_map]
      rfl) oa s hs'
  rw [StateT.run'_eq, StateT.run'_eq,
    show (simulateQ (traceImpl P hMac irl true m') oa).run s =
      Prod.map id id <$> (simulateQ (traceImpl P hMac irl true m) oa).run s from h.symm,
    Prod.map_id, id_map]

/-- **Signed-gap stop.** Two repaired trace games whose modes agree off `e` have the same signed
gap of acceptance probabilities as their runs stopped with `false` when `e` becomes exposed. -/
theorem signedGap_stop (m m' : ℕ → Mode) (e : ℕ) (hm : ∀ t, t ≠ e → m t = m' t)
    (A : Adversary P irl) :
    (Pr[= true | Prod.fst <$> run P hMac irl true m A]).toReal -
        (Pr[= true | Prod.fst <$> run P hMac irl true m' A]).toReal =
      (Pr[= true | stoppedRun (traceImpl P hMac irl true m) (targetStop e) A
          (initTrace P hMac)]).toReal -
        (Pr[= true | stoppedRun (traceImpl P hMac irl true m') (targetStop e) A
          (initTrace P hMac)]).toReal := by
  have hC : ∀ mode : ℕ → Mode,
      QueryImpl.PreservesInv (traceImpl P hMac irl true mode) (Committed e) :=
    fun mode t s hs z hz =>
      ⟨(traceImpl_flagStep hMac irl true mode t s z hz).challenged hs.1,
        fun hexp => hs.2 ((traceImpl_flagStep hMac irl true mode t s z hz).fresh e hs.1 hexp)⟩
  have h := signed_gap_stoppedRun_eq (traceImpl P hMac irl true m) (traceImpl P hMac irl true m')
    (fun _ => True) (Committed e) (targetStop e) (fun _ _ _ _ _ => trivial) (hC m) (hC m')
    (fun s hs => by simp [targetStop, hs.2]) (traceImpl_eq_or hMac irl m m' e hm)
    (fun s _ hs oa => probOutput_run_eq_of_exposed hMac irl m m' e hm s hs oa)
    A (initTrace P hMac) trivial
  rw [StateT.run'_eq, StateT.run'_eq] at h
  exact h

end Stopping

/-! ### Installing the challenge value -/

section ChallengeSample

/-- The eligible challenge of epoch `e`: unexposed, unchallenged, with an available key. -/
def chalHit {irl : P.kem.IncrementalRandLeak P.inc} (e : ℕ) :
    (Spec P irl).Domain → TraceState P → Bool
  | .inl (.inl (.inr t)), s => decide (t = e ∧ e ∉ s.game.exposed ∧ e ∉ s.game.challenged ∧
      (lookupKey s.game e).isSome = true)
  | _, _ => false

variable [SampleableType P.K] [SampleableType P.EpochKey]

/-- Off an eligible challenge of `e`, the installed challenge value is unused. -/
theorem traceChallengeAt_offHit (mode : ℕ → Mode) (e : ℕ) (x : P.EpochKey) (t : ℕ)
    (s : TraceState P)
    (h : ¬ (t = e ∧ e ∉ s.game.exposed ∧ e ∉ s.game.challenged ∧
      (lookupKey s.game e).isSome = true)) :
    (traceChallengeAt P mode e (some x) t).run s = (traceChallengeAt P mode e none t).run s := by
  change traceChallengeAt P mode e (some x) t s = traceChallengeAt P mode e none t s
  by_cases hex : t ∈ s.game.exposed ∨ t ∈ s.game.challenged
  · simp only [traceChallengeAt, if_pos hex]
  · cases hk : lookupKey s.game t with
    | none => simp only [traceChallengeAt, if_neg hex, hk]
    | some k =>
        have hte : t ≠ e := by
          intro hte
          subst hte
          exact h ⟨rfl, fun h' => hex (Or.inl h'), fun h' => hex (Or.inr h'), by simp [hk]⟩
        simp only [traceChallengeAt, if_neg hex, hk, if_neg hte]

/-- An eligible challenge of `e` answers the installed value, or the mode's value, and commits
`e`. -/
theorem traceChallengeAt_hit (mode : ℕ → Mode) (e : ℕ) (x : Option P.EpochKey)
    (s : TraceState P) (hex : ¬ (e ∈ s.game.exposed ∨ e ∈ s.game.challenged)) {k : P.EpochKey}
    (hk : lookupKey s.game e = some k) :
    (traceChallengeAt P mode e x e).run s =
      (fun out => (some out, { s with game :=
        { s.game with challenged := insert e s.game.challenged } })) <$>
        (match x with
          | some v => pure v
          | none => challengeValue P (mode e) e k) := by
  change traceChallengeAt P mode e x e s = _
  cases x <;> simp only [traceChallengeAt, if_neg hex, hk, ↓reduceIte]

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym] (hMac : P.Mac = Unit)
  (irl : P.kem.IncrementalRandLeak P.inc)

/-- Off an eligible challenge of `e`, the installed challenge value is unused. -/
theorem traceImplAt_offHit (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (mode : ℕ → Mode) (x : P.EpochKey) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), chalHit e q s = false →
      (traceImplAt P hMac irl e kp ec (some x) mode q).run s =
        (traceImplAt P hMac irl e kp ec none mode q).run s
  | .inl (.inl (.inl _)), _, _ => rfl
  | .inl (.inl (.inr t)), s, h => traceChallengeAt_offHit mode e x t s (of_decide_eq_false h)
  | .inl (.inr _), _, _ => rfl
  | .inr _, _, _ => rfl

/-- The per-query step of `sampleEachQuery` for the installed challenge value. -/
private theorem chalSample_step (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (mode : ℕ → Mode) (sample : ProbComp P.EpochKey)
    (hsample : ∀ k, challengeValue P (mode e) e k = sample)
    (q : (Spec P irl).Domain) (s : TraceState P) :
    𝒟[((stopOnState (traceImplAt P hMac irl e kp ec none mode) (targetStop e) q).run).run s] =
      𝒟[Prod.map id id <$> ((sampleEachQuery sample fun x =>
        stopOnState (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e)) q).run.run
          s] := by
  rw [sampleEachQuery_run, Prod.map_id, id_map]
  by_cases hq : chalHit e q s = true
  · rcases q with ((q | t) | q) | q
    · exact absurd hq (by simp [chalHit])
    · obtain ⟨rfl, hexp, hch, hk⟩ := of_decide_eq_true hq
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
      have hex : ¬ (t ∈ s.game.exposed ∨ t ∈ s.game.challenged) := fun h => h.elim hexp hch
      change 𝒟[((stopOnState (traceChallengeAt P mode t none) (targetStop t) t).run).run s] =
        𝒟[sample >>= fun x =>
          ((stopOnState (traceChallengeAt P mode t (some x)) (targetStop t) t).run).run s]
      simp only [stopOnState_run, traceChallengeAt_hit mode t _ s hex hk, hsample,
        Functor.map_map, map_pure, bind_pure_comp]
    · exact absurd hq (by simp [chalHit])
    · exact absurd hq (by simp [chalHit])
  · have hq' : chalHit e q s = false := by simpa using hq
    have heq : ∀ x, ((stopOnState (traceImplAt P hMac irl e kp ec (some x) mode)
        (targetStop e) q).run).run s =
        ((stopOnState (traceImplAt P hMac irl e kp ec none mode) (targetStop e) q).run).run s :=
      fun x => stopOnState_run_congr _ (traceImplAt_offHit hMac irl e kp ec mode x q s hq')
    simp only [heq]
    exact (evalDist_bind_ignore sample _).symm

/-- **Installing the challenge value.** Sampling the challenge value of `e` once before the run
and installing it is the same as sampling it at the eligible challenge of `e`. -/
theorem stoppedRun_chalSample (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (mode : ℕ → Mode) (sample : ProbComp P.EpochKey)
    (hsample : ∀ k, challengeValue P (mode e) e k = sample) (A : Adversary P irl)
    (s : TraceState P) :
    Pr[= true | sample >>= fun x =>
        stoppedRun (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e) A s] =
      Pr[= true | stoppedRun (traceImplAt P hMac irl e kp ec none mode) (targetStop e) A s] := by
  have hU := optionRun_sample_once_eq_sampleEachQuery sample
    (fun x => stopOnState (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e))
    (fun _ => True) (fun s => e ∈ s.game.challenged) (chalHit e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun x _ q s _ hu z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact (traceImplAt_flagStep hMac irl e kp ec (some x) mode q s w hw).challenged hu)
    (fun q s _ hq x _ x' _ => by
      rw [stopOnState_run_congr _ (traceImplAt_offHit hMac irl e kp ec mode x q s hq),
        stopOnState_run_congr _ (traceImplAt_offHit hMac irl e kp ec mode x' q s hq)])
    (fun q s _ hu => by
      rcases q with ((q | t) | q) | q
      · rfl
      · exact decide_eq_false fun h => h.2.2.1 hu
      · rfl
      · rfl)
    (fun x _ q s _ hq z hz _ => by
      rcases q with ((q | t) | q) | q
      · exact absurd hq (by simp [chalHit])
      · obtain ⟨rfl, hexp, hch, hk⟩ := of_decide_eq_true hq
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
        obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
        change w ∈ support ((traceChallengeAt P mode t (some x) t).run s) at hw
        rw [traceChallengeAt_hit mode t (some x) s (fun h => h.elim hexp hch) hk,
          support_map] at hw
        obtain ⟨out, -, rfl⟩ := hw
        exact Finset.mem_insert_self t _
      · exact absurd hq (by simp [chalHit])
      · exact absurd hq (by simp [chalHit]))
    A s trivial
  have hS := probOutput_optionRun_eq_of_state_map
    (sampleEachQuery sample fun x =>
      stopOnState (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e))
    (stopOnState (traceImplAt P hMac irl e kp ec none mode) (targetStop e)) id (fun _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun q s _ => chalSample_step hMac irl e kp ec mode sample hsample q s) A s trivial
  exact hU.trans hS.symm

end ChallengeSample

/-! ### Installing a sample used once -/

section Generic

/-- Sampling a value and discarding it does not change the probability of an output. -/
theorem probOutput_bind_const' {α β : Type} (mx : ProbComp α) (my : ProbComp β) (y : β) :
    Pr[= y | mx >>= fun _ => my] = Pr[= y | my] := by
  rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- An independent sample commutes past two dependent ones. -/
theorem probOutput_swap3 {α β γ δ : Type} (mx : ProbComp α) (my : α → ProbComp β)
    (mz : ProbComp γ) (f : α → β → γ → ProbComp δ) (y : δ) :
    Pr[= y | mx >>= fun a => my a >>= fun b => mz >>= fun c => f a b c] =
      Pr[= y | mz >>= fun c => mx >>= fun a => my a >>= fun b => f a b c] :=
  (probOutput_bind_congr fun a _ =>
      probOutput_bind_bind_swap (my a) mz (fun b c => f a b c) y).trans
    (probOutput_bind_bind_swap mx mz (fun a c => my a >>= fun b => f a b c) y)

/-- Stopping preserves agreement of one step in distribution. -/
theorem stopped_congr {ι σ : Type} {spec : OracleSpec ι}
    {I L : QueryImpl spec (StateT σ ProbComp)} (stop : σ → Bool) (q : spec.Domain) (s : σ)
    (h : 𝒟[(I q).run s] = 𝒟[(L q).run s]) :
    𝒟[((stopOnState I stop q).run).run s] = 𝒟[((stopOnState L stop q).run).run s] := by
  rw [stopOnState_run, stopOnState_run, evalDist_map, evalDist_map, h]

/-- Stopping commutes with sampling before one step. -/
theorem stopped_bind {ι σ α : Type} {spec : OracleSpec ι} (sample : ProbComp α)
    {I : α → QueryImpl spec (StateT σ ProbComp)} {L : QueryImpl spec (StateT σ ProbComp)}
    (stop : σ → Bool) (q : spec.Domain) (s : σ)
    (h : 𝒟[(L q).run s] = 𝒟[sample >>= fun a => (I a q).run s]) :
    𝒟[((stopOnState L stop q).run).run s] =
      𝒟[sample >>= fun a => ((stopOnState (I a) stop q).run).run s] := by
  simp only [stopOnState_run]
  rw [evalDist_map, h, ← evalDist_map, map_bind]

/-- **Installing a sample used once.** If an implementation `L` samples at its first hit query,
and `I a` uses an installed sample `a` instead, then sampling `a` once before the run is the same
as running `L`. -/
theorem optionRun_install {ι σ α : Type} {spec : OracleSpec ι} (sample : ProbComp α)
    (I : α → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (L : QueryImpl spec (OptionT (StateT σ ProbComp))) (Inv used : σ → Prop)
    (hit : spec.Domain → σ → Bool)
    (hpres : ∀ a ∈ support sample, ∀ t s, Inv s →
      ∀ z ∈ support (((I a t).run).run s), z.1.isSome → Inv z.2)
    (hused : ∀ a ∈ support sample, ∀ t s, Inv s → used s →
      ∀ z ∈ support (((I a t).run).run s), z.1.isSome → used z.2)
    (hnohit : ∀ t s, Inv s → used s → hit t s = false)
    (hfirst : ∀ a ∈ support sample, ∀ t s, Inv s → hit t s = true →
      ∀ z ∈ support (((I a t).run).run s), z.1.isSome → used z.2)
    (hoff : ∀ t s, Inv s → hit t s = false → ∀ a ∈ support sample,
      𝒟[((I a t).run).run s] = 𝒟[((L t).run).run s])
    (hon : ∀ t s, Inv s → hit t s = true →
      𝒟[((L t).run).run s] = 𝒟[sample >>= fun a => ((I a t).run).run s])
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | sample >>= fun a => optionRun (I a) oa s] = Pr[= true | optionRun L oa s] := by
  have hU := optionRun_sample_once_eq_sampleEachQuery sample I Inv used hit hpres hused
    (fun t s hs hh a ha a' ha' => (hoff t s hs hh a ha).trans (hoff t s hs hh a' ha').symm)
    hnohit hfirst oa s hs
  have hS := probOutput_optionRun_eq_of_state_map (sampleEachQuery sample I) L id Inv
    (fun t s hs z hz hsome => by
      rw [sampleEachQuery_run, mem_support_bind_iff] at hz
      obtain ⟨a, ha, hz⟩ := hz
      exact hpres a ha t s hs z hz hsome)
    (fun t s hs => by
      rw [sampleEachQuery_run, Prod.map_id, id_map]
      cases hh : hit t s
      · rw [evalDist_bind_congr (ob₂ := fun _ => ((L t).run).run s)
          (fun a ha => hoff t s hs hh a ha)]
        exact (evalDist_bind_ignore sample _).symm
      · exact hon t s hs hh)
    oa s hs
  exact hU.trans hS.symm

end Generic

/-! ### Key generation and first-stage encapsulation as projections -/

section Projections

variable (irl : P.kem.IncrementalRandLeak P.inc)

/-- Key generation is the first component of the leaking key generation. -/
theorem keygen_eq_map : P.kem.keygen = Prod.fst <$> irl.keygenRleak := by
  rw [← irl.keygen_fst, map_eq_bind_pure_comp]
  rfl

/-- First-stage encapsulation is the first component of its leaking version. -/
theorem encaps1_eq_map (hdr : P.inc.PKheader) :
    P.inc.encaps1 hdr = Prod.fst <$> irl.encaps1Rleak hdr := by
  rw [← irl.encaps1_fst hdr, map_eq_bind_pure_comp]
  rfl

/-- Encapsulation is the first stage followed by the deterministic second stage. -/
theorem encaps_eq_map (pk : P.PK) :
    P.kem.encaps pk = (fun c : P.inc.St × P.inc.C₁ × P.K =>
      (P.inc.splitC.symm (c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader pk)
        (P.inc.toVector pk)), c.2.2)) <$> P.inc.encaps1 (P.inc.toHeader pk) := by
  rw [P.inc.encaps_eq_stagedEncaps pk, KEMScheme.IncrementalStructure.stagedEncaps,
    map_eq_bind_pure_comp]
  refine bind_congr fun c => ?_
  obtain ⟨es, c1, k⟩ := c
  simp [P.hEnc2.encaps2_eq]

end Projections

/-! ### Sampling sends and their hits -/

/-- Whether a state generates the key pair of epoch `e`. -/
def isKeygenAt (e : ℕ) : State P Unit → Bool
  | .keysUnsampled t _ => decide (t = e)
  | _ => false

/-- Whether a state runs the first-stage encapsulation of epoch `e`. -/
def isEncaps1At (e : ℕ) : State P Unit → Bool
  | .headerReceived t _ _ _ => decide (t = e)
  | _ => false

/-- A send query of a state passing `test`, unless it is a refused leaking send of `e`. -/
def sendHit {irl : P.kem.IncrementalRandLeak P.inc} (test : State P Unit → Bool) (e : ℕ) :
    (Spec P irl).Domain → TraceState P → Bool
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))), s => test (s.game.stateAt true)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))), s => test (s.game.stateAt false)
  | .inl (.inl (.inl (.inl (.inr _)))), s =>
      test (s.game.stateAt true) && !decide ({e} ∩ s.game.challenged ≠ ∅)
  | .inl (.inl (.inl (.inr _))), s =>
      test (s.game.stateAt false) && !decide ({e} ∩ s.game.challenged ≠ ∅)
  | _, _ => false

/-- The queries other than the four sends. -/
def NonSend {irl : P.kem.IncrementalRandLeak P.inc} : (Spec P irl).Domain → Prop
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))) => False
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))) => False
  | .inl (.inl (.inl (.inl (.inr _)))) => False
  | .inl (.inl (.inl (.inr _))) => False
  | _ => True

section Hits

variable {irl : P.kem.IncrementalRandLeak P.inc}

/-- Key generation of `e` is the state `keysUnsampled e`. -/
theorem isKeygenAt_eq_true {e : ℕ} {st : State P Unit} (h : isKeygenAt e st = true) :
    ∃ a, st = .keysUnsampled e a := by
  cases st with
  | keysUnsampled t a =>
      obtain rfl : t = e := of_decide_eq_true h
      exact ⟨a, rfl⟩
  | _ => cases h

/-- First-stage encapsulation of `e` is the state `headerReceived e`. -/
theorem isEncaps1At_eq_true {e : ℕ} {st : State P Unit} (h : isEncaps1At e st = true) :
    ∃ a hdr dec, st = .headerReceived e a hdr dec := by
  cases st with
  | headerReceived t a hdr dec =>
      obtain rfl : t = e := of_decide_eq_true h
      exact ⟨a, hdr, dec, rfl⟩
  | _ => cases h

/-- No query hits if no party passes `test`. -/
theorem sendHit_false {test : State P Unit → Bool} {e : ℕ} {s : TraceState P}
    (h : ∀ p, test (s.game.stateAt p) = false) :
    ∀ q : (Spec P irl).Domain, sendHit test e q s = false
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))) => h true
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))) => h false
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inr _))))) => rfl
  | .inl (.inl (.inl (.inl (.inr _)))) => by simp [sendHit, h true]
  | .inl (.inl (.inl (.inr _))) => by simp [sendHit, h false]
  | .inl (.inl (.inr _)) => rfl
  | .inl (.inr _) => rfl
  | .inr _ => rfl

end Hits

/-! ### Evolution of the records of the selected epoch -/

/-- One query keeps the records, or records a key pair or a first-stage encapsulation of one
epoch; at `e`, an installed sample is the one recorded. -/
def TranscriptStep (e : ℕ) (kp : Option (P.PK × P.SK)) (ec : Option (P.inc.St × P.inc.C₁ × P.K))
    (s s' : TraceState P) : Prop :=
  s'.transcript = s.transcript ∨
    (∃ t x, s'.transcript = Function.update s.transcript t
        { (s.transcript t) with keypair := some x } ∧ (t = e → ∀ x0, kp = some x0 → x = x0)) ∨
    (∃ t c, s'.transcript = Function.update s.transcript t
        { (s.transcript t) with encaps1 := some c } ∧ (t = e → ∀ c0, ec = some c0 → c = c0))

section TranscriptSteps

variable {e : ℕ} {kp : Option (P.PK × P.SK)} {ec : Option (P.inc.St × P.inc.C₁ × P.K)}
  {s s' : TraceState P}

/-- The records of `e` after one query. -/
theorem TranscriptStep.at_e (h : TranscriptStep e kp ec s s') :
    ((s'.transcript e).keypair = (s.transcript e).keypair ∨
      ∃ x, (s'.transcript e).keypair = some x ∧ ∀ x0, kp = some x0 → x = x0) ∧
    ((s'.transcript e).encaps1 = (s.transcript e).encaps1 ∨
      ∃ c, (s'.transcript e).encaps1 = some c ∧ ∀ c0, ec = some c0 → c = c0) := by
  rcases h with h | ⟨t, x, h, hx⟩ | ⟨t, c, h, hc⟩
  · rw [h]
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  · rw [h]
    by_cases ht : e = t
    · subst ht
      rw [Function.update_self]
      exact ⟨Or.inr ⟨x, rfl, hx rfl⟩, Or.inl rfl⟩
    · rw [Function.update_of_ne ht]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  · rw [h]
    by_cases ht : e = t
    · subst ht
      rw [Function.update_self]
      exact ⟨Or.inl rfl, Or.inr ⟨c, rfl, hc rfl⟩⟩
    · rw [Function.update_of_ne ht]
      exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- A recorded key pair of `e` stays recorded. -/
theorem TranscriptStep.keypair_ne (h : TranscriptStep e kp ec s s')
    (hs : (s.transcript e).keypair ≠ none) : (s'.transcript e).keypair ≠ none := by
  rcases h.at_e.1 with h1 | ⟨x, h1, -⟩
  · rwa [h1]
  · rw [h1]
    exact Option.some_ne_none x

/-- A recorded first-stage encapsulation of `e` stays recorded. -/
theorem TranscriptStep.encaps1_ne (h : TranscriptStep e kp ec s s')
    (hs : (s.transcript e).encaps1 ≠ none) : (s'.transcript e).encaps1 ≠ none := by
  rcases h.at_e.2 with h1 | ⟨c, h1, -⟩
  · rwa [h1]
  · rw [h1]
    exact Option.some_ne_none c

/-- The key pair of `e` stays unrecorded or the installed one. -/
theorem TranscriptStep.keypairAt (h : TranscriptStep e kp ec s s')
    (hs : ∀ x, kp = some x → (s.transcript e).keypair = none ∨ (s.transcript e).keypair = some x) :
    ∀ x, kp = some x →
      (s'.transcript e).keypair = none ∨ (s'.transcript e).keypair = some x := by
  intro x hx
  rcases h.at_e.1 with h1 | ⟨y, h1, hy⟩
  · rw [h1]
    exact hs x hx
  · rw [h1, hy x hx]
    exact Or.inr rfl

/-- The first-stage encapsulation of `e` stays unrecorded or the installed one. -/
theorem TranscriptStep.encapsAt (h : TranscriptStep e kp ec s s')
    (hs : ∀ c, ec = some c → (s.transcript e).encaps1 = none ∨ (s.transcript e).encaps1 = some c) :
    ∀ c, ec = some c →
      (s'.transcript e).encaps1 = none ∨ (s'.transcript e).encaps1 = some c := by
  intro c hc
  rcases h.at_e.2 with h1 | ⟨y, h1, hy⟩
  · rw [h1]
    exact hs c hc
  · rw [h1, hy c hc]
    exact Or.inr rfl

end TranscriptSteps

/-! ### Header and first-stage chunks, and sends that sample nothing -/

/-- The first header chunk and encoder of epoch `t` for the public key `pk`. -/
def hdrChunk (P : Parameters ProbComp) (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (pk : P.PK) :
    (ℕ × P.Sym) × EncoderState (P.inc.PKheader × P.Mac) P.Sym :=
  (EncoderState.init P.ecpHdr
    (P.inc.toHeader pk, (auth P hMac).macHeader a t (P.inc.toHeader pk))).nextChunk

/-- The first `ct₁` chunk and encoder for `ct1`. -/
def ct1Chunk (P : Parameters ProbComp) (ct1 : P.inc.C₁) :
    (ℕ × P.Sym) × EncoderState P.inc.C₁ P.Sym :=
  (EncoderState.init P.ecpCt1 ct1).nextChunk

/-- The key-generation send in terms of `hdrChunk`. -/
theorem keygenStep_eq (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (pk : P.PK) (sk : P.SK) :
    keygenStep P hMac t a pk sk =
      { msg := { epoch := t, type := .hdr, data := some (hdrChunk P hMac t a pk).1 }
        sendingEpoch := t - 1, outputKey := none
        state := .keysSampled t a sk (P.inc.toVector pk) (hdrChunk P hMac t a pk).2 } := rfl

/-- The first-stage encapsulation send in terms of `ct1Chunk`. -/
theorem encaps1Step_eq (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (hdr : P.inc.PKheader)
    (dec : DecoderState P.inc.PKvector P.Sym) (es : P.inc.St) (ct1 : P.inc.C₁) (k : P.K) :
    encaps1Step P hMac t a hdr dec es ct1 k =
      { msg := { epoch := t, type := .ct1, data := some (ct1Chunk P ct1).1 }
        sendingEpoch := t - 1, outputKey := some (t, P.kdfOK k t)
        state := .ct1Sampled t ((auth P hMac).update a t (P.kdfOK k t)) hdr es ct1
          (ct1Chunk P ct1).2 dec } := rfl

section NoSample

variable (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A send from a state that does not sample is `send` without coins. -/
theorem sendRleak_of_noSample {st : State P Unit} (h1 : ∀ t a, st ≠ .keysUnsampled t a)
    (h2 : ∀ t a hdr dec, st ≠ .headerReceived t a hdr dec) :
    MLKEMBraid.sendRleak P irl (auth P hMac) st =
      (fun r => (r, SendRand.none)) <$> MLKEMBraid.send P (auth P hMac) st := by
  cases st with
  | keysUnsampled t a => exact absurd rfl (h1 t a)
  | headerReceived t a hdr dec => exact absurd rfl (h2 t a hdr dec)
  | _ => rfl

variable [DecidableEq P.EpochKey]

/-- The sample of a send that samples nothing. -/
theorem sampledSend_of_noSample (s : TraceState P) (party : Bool)
    (h1 : ∀ t a, s.game.stateAt party ≠ .keysUnsampled t a)
    (h2 : ∀ t a hdr dec, s.game.stateAt party ≠ .headerReceived t a hdr dec) :
    sampledSend P hMac irl s party = (fun r => ((r, SendRand.none), s.transcript, s.bad)) <$>
      MLKEMBraid.send P (auth P hMac) (s.game.stateAt party) := by
  have hS : sampledSend P hMac irl s party = (fun out => (out, s.transcript, s.bad)) <$>
      MLKEMBraid.sendRleak P irl (auth P hMac) (s.game.stateAt party) := by
    cases hst : s.game.stateAt party with
    | keysUnsampled t a => exact absurd hst (h1 t a)
    | headerReceived t a hdr dec => exact absurd hst (h2 t a hdr dec)
    | _ => simp only [sampledSend, hst]
  rw [hS, sendRleak_of_noSample hMac irl h1 h2, Functor.map_map]

end NoSample

/-! ### Sends at the selected epoch -/

/-- The state after the key-generation send of `e` with the key pair `x`. -/
def keygenState [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (s : TraceState P)
    (party leaking : Bool) (e : ℕ) (a : Unit) (x : P.PK × P.SK) : TraceState P :=
  { game := { sendUpdate s.game party (keygenStep P hMac e a x.1 x.2) with
      exposed := if leaking then s.game.exposed ∪ {e} else s.game.exposed }
    transcript := Function.update s.transcript e { (s.transcript e) with keypair := some x }
    bad := s.bad }

/-- The state after the first-stage encapsulation send of `e` with the sample `c`. -/
def encaps1State [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (s : TraceState P)
    (party leaking : Bool) (e : ℕ) (a : Unit) (hdr : P.inc.PKheader)
    (dec : DecoderState P.inc.PKvector P.Sym) (c : P.inc.St × P.inc.C₁ × P.K) : TraceState P :=
  { game := { sendUpdate s.game party (encaps1Step P hMac e a hdr dec c.1 c.2.1 c.2.2) with
      exposed := if leaking then s.game.exposed ∪ {e} else s.game.exposed }
    transcript := Function.update s.transcript e { (s.transcript e) with encaps1 := some c }
    bad := encaps1Bad s e c }

section TargetSends

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- The lazy key-generation send of `e`. -/
theorem traceSend_keygen_run {s : TraceState P} {party : Bool} (leaking : Bool) {e : ℕ}
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled e a) :
    (traceSend P hMac irl party leaking).run s =
      (fun y : (P.PK × P.SK) × irl.KeygenRand =>
        if leaking && decide ({e} ∩ s.game.challenged ≠ ∅) then (none, s)
        else (some (e - 1, none, (keygenStep P hMac e a y.1.1 y.1.2).msg, SendRand.keygen y.2),
          keygenState hMac s party leaking e a y.1)) <$> irl.keygenRleak := by
  change traceSend P hMac irl party leaking s = _
  simp only [traceSend, sampledSend_eq_keygen hMac irl s party hst, Functor.map_map]
  congr 1
  funext y
  simp [exposure, sendExposure, hst, State.epoch, keygenState, keygenStep_eq]

/-- The installed key-generation send of `e`. -/
theorem traceSendAt_keygen_run {s : TraceState P} {party : Bool} (leaking : Bool) {e : ℕ}
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled e a) (x : P.PK × P.SK)
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) :
    (traceSendAt P hMac irl e (some x) ec party leaking).run s =
      if leaking && decide ({e} ∩ s.game.challenged ≠ ∅) then pure (none, s)
      else pure (if leaking then none
          else some (e - 1, none, (keygenStep P hMac e a x.1 x.2).msg, SendRand.none),
        keygenState hMac s party leaking e a x) := by
  have hI : installedSample P hMac e (some x) ec s party =
      some (keygenStep P hMac e a x.1 x.2,
        Function.update s.transcript e { (s.transcript e) with keypair := some x }, s.bad) := by
    obtain ⟨pk, sk⟩ := x
    simp [installedSample, hst]
  change traceSendAt P hMac irl e (some x) ec party leaking s = _
  simp only [traceSendAt, hI]
  rfl

/-- The lazy first-stage encapsulation send of `e`. -/
theorem traceSend_encaps1_run {s : TraceState P} {party : Bool} (leaking : Bool) {e : ℕ}
    {a : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) :
    (traceSend P hMac irl party leaking).run s =
      (fun y : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        if leaking && decide ({e} ∩ s.game.challenged ≠ ∅) then (none, s)
        else (some (e - 1, some e, (encaps1Step P hMac e a hdr dec y.1.1 y.1.2.1 y.1.2.2).msg,
            SendRand.encaps1 y.2),
          encaps1State hMac s party leaking e a hdr dec y.1)) <$> irl.encaps1Rleak hdr := by
  change traceSend P hMac irl party leaking s = _
  simp only [traceSend, sampledSend_eq_encaps1 hMac irl s party hst, Functor.map_map]
  congr 1
  funext y
  simp [exposure, sendExposure, hst, State.epoch, encaps1State, encaps1Step_eq]

/-- The installed first-stage encapsulation send of `e`. -/
theorem traceSendAt_encaps1_run {s : TraceState P} {party : Bool} (leaking : Bool) {e : ℕ}
    {a : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) (kp : Option (P.PK × P.SK))
    (c : P.inc.St × P.inc.C₁ × P.K) :
    (traceSendAt P hMac irl e kp (some c) party leaking).run s =
      if leaking && decide ({e} ∩ s.game.challenged ≠ ∅) then pure (none, s)
      else pure (if leaking then none
          else some (e - 1, some e, (encaps1Step P hMac e a hdr dec c.1 c.2.1 c.2.2).msg,
            SendRand.none),
        encaps1State hMac s party leaking e a hdr dec c) := by
  have hI : installedSample P hMac e kp (some c) s party =
      some (encaps1Step P hMac e a hdr dec c.1 c.2.1 c.2.2,
        Function.update s.transcript e { (s.transcript e) with encaps1 := some c },
        encaps1Bad s e c) := by
    obtain ⟨es, ct1, k⟩ := c
    simp [installedSample, hst]
  change traceSendAt P hMac irl e kp (some c) party leaking s = _
  simp only [traceSendAt, hI]
  rfl

/-- A non-refused installed key-generation send of `e` records the installed key pair. -/
theorem traceSendAt_keygen_records {s : TraceState P} {party leaking : Bool} {e : ℕ} {a : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a) (x : P.PK × P.SK)
    (hc : ¬ (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSendAt P hMac irl e (some x) none party leaking).run s)) :
    (z.2.transcript e).keypair ≠ none := by
  rw [traceSendAt_keygen_run hMac irl leaking hst x none, if_neg hc, mem_support_pure_iff] at hz
  rw [hz]
  simp [keygenState]

/-- A non-refused installed first-stage encapsulation send of `e` records the installed sample. -/
theorem traceSendAt_encaps1_records {s : TraceState P} {party leaking : Bool} {e : ℕ} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) (kp : Option (P.PK × P.SK))
    (c : P.inc.St × P.inc.C₁ × P.K)
    (hc : ¬ (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSendAt P hMac irl e kp (some c) party leaking).run s)) :
    (z.2.transcript e).encaps1 ≠ none := by
  rw [traceSendAt_encaps1_run hMac irl leaking hst kp c, if_neg hc, mem_support_pure_iff] at hz
  rw [hz]
  simp [encaps1State]

/-- The installed samples that apply. -/
theorem installedSample_some {e : ℕ} {kp : Option (P.PK × P.SK)}
    {ec : Option (P.inc.St × P.inc.C₁ × P.K)} {s : TraceState P} {party : Bool}
    {r : SendResult P Unit} {T : ℕ → EpochTranscript P} {b : Bool}
    (h : installedSample P hMac e kp ec s party = some (r, T, b)) :
    (∃ a x, kp = some x ∧ s.game.stateAt party = .keysUnsampled e a) ∨
      (∃ a hdr dec c, ec = some c ∧ s.game.stateAt party = .headerReceived e a hdr dec) := by
  unfold installedSample at h
  cases hst : s.game.stateAt party with
  | keysUnsampled t a =>
      rw [hst] at h
      rcases kp with _ | ⟨pk, sk⟩
      · simp at h
      · by_cases ht : t = e
        · subst ht
          exact Or.inl ⟨a, (pk, sk), rfl, rfl⟩
        · simp [ht] at h
  | headerReceived t a hdr dec =>
      rw [hst] at h
      rcases ec with _ | ⟨es, ct1, k⟩
      · rcases kp with _ | ⟨pk, sk⟩ <;> simp at h
      · by_cases ht : t = e
        · subst ht
          exact Or.inr ⟨a, hdr, dec, (es, ct1, k), rfl, rfl⟩
        · rcases kp with _ | ⟨pk, sk⟩ <;> simp [ht] at h
  | _ =>
      rw [hst] at h
      rcases kp with _ | ⟨pk, sk⟩ <;> rcases ec with _ | ⟨es, ct1, k⟩ <;> simp at h

/-- The outcomes of an installed ordinary send are those of the installed send. -/
theorem mem_support_tracePlainAt {e : ℕ} {kp : Option (P.PK × P.SK)}
    {ec : Option (P.inc.St × P.inc.C₁ × P.K)} {party : Bool} {t : Unit} {s : TraceState P}
    {z : Option (ℕ × Option ℕ × Message P.Sym) × TraceState P}
    (hz : z ∈ support ((tracePlainAt P hMac irl e kp ec party t).run s)) :
    ∃ w ∈ support ((traceSendAt P hMac irl e kp ec party false).run s),
      z = (w.1.map fun x => (x.1, x.2.1, x.2.2.1), w.2) := by
  change z ∈ support (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSendAt P hMac irl e kp ec party false).run s) at hz
  rw [StateT.run_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- An installed send keeps the trace invariant of the repaired game. -/
theorem traceSendAt_traceInv (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    (hs : TraceInv hMac true s) (hkp : ∀ x, kp = some x → x ∈ support P.kem.keygen)
    (hec : ∀ c a hdr dec, ec = some c → s.game.stateAt party = .headerReceived e a hdr dec →
      c ∈ support (P.inc.encaps1 hdr))
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSendAt P hMac irl e kp ec party leaking).run s)) :
    TraceInv hMac true z.2 := by
  rcases hI : installedSample P hMac e kp ec s party with _ | ⟨r, T, b⟩
  · change z ∈ support (traceSendAt P hMac irl e kp ec party leaking s) at hz
    simp only [traceSendAt, hI] at hz
    exact traceSend_traceInv hMac irl party leaking true s hs hz
  · rcases installedSample_some hMac hI with ⟨a, x, rfl, hst⟩ | ⟨a, hdr, dec, c, rfl, hst⟩
    · rw [traceSendAt_keygen_run hMac irl leaking hst x ec] at hz
      by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · rw [if_pos hc, mem_support_pure_iff] at hz
        rw [hz]
        exact hs
      · rw [if_neg hc, mem_support_pure_iff] at hz
        rw [hz]
        obtain ⟨rand, hrand⟩ : ∃ rand, (x, rand) ∈ support irl.keygenRleak := by
          have hx := hkp x rfl
          rw [keygen_eq_map irl, support_map] at hx
          obtain ⟨⟨x', rand⟩, hm, rfl⟩ := hx
          exact ⟨rand, hm⟩
        have hlazy : (some (e - 1, none, (keygenStep P hMac e a x.1 x.2).msg,
            SendRand.keygen rand), keygenState hMac s party leaking e a x) ∈
            support ((traceSend P hMac irl party leaking).run s) := by
          rw [traceSend_keygen_run hMac irl leaking hst, support_map]
          exact ⟨(x, rand), hrand, by simp only [if_neg hc]⟩
        have hinv := traceSend_traceInv hMac irl party leaking true s hs hlazy
        exact hinv
    · rw [traceSendAt_encaps1_run hMac irl leaking hst kp c] at hz
      by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · rw [if_pos hc, mem_support_pure_iff] at hz
        rw [hz]
        exact hs
      · rw [if_neg hc, mem_support_pure_iff] at hz
        rw [hz]
        obtain ⟨rand, hrand⟩ : ∃ rand, (c, rand) ∈ support (irl.encaps1Rleak hdr) := by
          have hc' := hec c a hdr dec rfl hst
          rw [encaps1_eq_map irl, support_map] at hc'
          obtain ⟨⟨c', rand⟩, hm, rfl⟩ := hc'
          exact ⟨rand, hm⟩
        have hlazy : (some (e - 1, some e, (encaps1Step P hMac e a hdr dec c.1 c.2.1 c.2.2).msg,
            SendRand.encaps1 rand), encaps1State hMac s party leaking e a hdr dec c) ∈
            support ((traceSend P hMac irl party leaking).run s) := by
          rw [traceSend_encaps1_run hMac irl leaking hst, support_map]
          exact ⟨(c, rand), hrand, by simp only [if_neg hc]⟩
        have hinv := traceSend_traceInv hMac irl party leaking true s hs hlazy
        exact hinv

/-- An installed send records at most one sample, the installed one at `e`. -/
theorem traceSendAt_transcriptStep (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSendAt P hMac irl e kp ec party leaking).run s)) :
    TranscriptStep e kp ec s z.2 := by
  rcases hI : installedSample P hMac e kp ec s party with _ | ⟨r, T, b⟩
  · change z ∈ support (traceSendAt P hMac irl e kp ec party leaking s) at hz
    simp only [traceSendAt, hI] at hz
    rcases mem_support_traceSend hMac irl hz with hzs | ⟨w, hw, -, hzw⟩
    · exact Or.inl (by rw [hzs])
    · rw [hzw]
      cases hst : s.game.stateAt party with
      | keysUnsampled t a =>
          rw [sampledSend_eq_keygen hMac irl s party hst, support_map] at hw
          obtain ⟨y, -, rfl⟩ := hw
          refine Or.inr (Or.inl ⟨t, y.1, rfl, fun ht x0 hx0 => ?_⟩)
          subst ht hx0
          simp [installedSample, hst] at hI
      | headerReceived t a hdr dec =>
          rw [sampledSend_eq_encaps1 hMac irl s party hst, support_map] at hw
          obtain ⟨y, -, rfl⟩ := hw
          refine Or.inr (Or.inr ⟨t, y.1, rfl, fun ht c0 hc0 => ?_⟩)
          subst ht hc0
          rcases kp with _ | ⟨pk, sk⟩ <;> simp [installedSample, hst] at hI
      | _ =>
          rw [sampledSend_of_noSample hMac irl s party
            (fun _ _ h => by rw [hst] at h; cases h)
            (fun _ _ _ _ h => by rw [hst] at h; cases h), support_map] at hw
          obtain ⟨y, -, rfl⟩ := hw
          exact Or.inl rfl
  · rcases installedSample_some hMac hI with ⟨a, x, rfl, hst⟩ | ⟨a, hdr, dec, c, rfl, hst⟩
    · rw [traceSendAt_keygen_run hMac irl leaking hst x ec] at hz
      by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · rw [if_pos hc, mem_support_pure_iff] at hz
        exact Or.inl (by rw [hz])
      · rw [if_neg hc, mem_support_pure_iff] at hz
        rw [hz]
        exact Or.inr (Or.inl ⟨e, x, rfl, fun _ x0 h => Option.some.inj h⟩)
    · rw [traceSendAt_encaps1_run hMac irl leaking hst kp c] at hz
      by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · rw [if_pos hc, mem_support_pure_iff] at hz
        exact Or.inl (by rw [hz])
      · rw [if_neg hc, mem_support_pure_iff] at hz
        rw [hz]
        exact Or.inr (Or.inr ⟨e, c, rfl, fun _ c0 h => Option.some.inj h⟩)

/-- Off the key generation of `e`, installing a key pair does not change a send. -/
theorem traceSendAt_kp_off (e : ℕ) (x : P.PK × P.SK) (party leaking : Bool) (s : TraceState P)
    (h : isKeygenAt e (s.game.stateAt party) = false) :
    (traceSendAt P hMac irl e (some x) none party leaking).run s =
      (traceSendAt P hMac irl e none none party leaking).run s := by
  have hI : installedSample P hMac e (some x) none s party = none := by
    unfold installedSample
    cases hst : s.game.stateAt party with
    | keysUnsampled t a =>
        rw [hst] at h
        have ht : t ≠ e := by simpa [isKeygenAt] using h
        obtain ⟨pk, sk⟩ := x
        simp [ht]
    | _ => rfl
  change traceSendAt P hMac irl e (some x) none party leaking s =
    traceSendAt P hMac irl e none none party leaking s
  simp only [traceSendAt, hI, installedSample_none]

/-- Off the first-stage encapsulation of `e`, installing a sample does not change a send. -/
theorem traceSendAt_ec_off (e : ℕ) (kp : Option (P.PK × P.SK)) (c : P.inc.St × P.inc.C₁ × P.K)
    (party leaking : Bool) (s : TraceState P) (h : isEncaps1At e (s.game.stateAt party) = false) :
    (traceSendAt P hMac irl e kp (some c) party leaking).run s =
      (traceSendAt P hMac irl e kp none party leaking).run s := by
  have hI : installedSample P hMac e kp (some c) s party =
      installedSample P hMac e kp none s party := by
    unfold installedSample
    cases hst : s.game.stateAt party with
    | keysUnsampled t a => rcases kp with _ | ⟨pk, sk⟩ <;> rfl
    | headerReceived t a hdr dec =>
        rw [hst] at h
        have ht : t ≠ e := by simpa [isEncaps1At] using h
        obtain ⟨es, ct1, k⟩ := c
        rcases kp with _ | ⟨pk, sk⟩ <;> simp [ht]
    | _ => rfl
  change traceSendAt P hMac irl e kp (some c) party leaking s =
    traceSendAt P hMac irl e kp none party leaking s
  simp only [traceSendAt, hI]

/-- With no installed first-stage sample, the first-stage encapsulation of `e` is lazy. -/
theorem traceSendAt_hdr_lazy (e : ℕ) (kp : Option (P.PK × P.SK)) (party leaking : Bool)
    (s : TraceState P) {a : Unit} {hdr : P.inc.PKheader}
    {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) :
    (traceSendAt P hMac irl e kp none party leaking).run s =
      (traceSend P hMac irl party leaking).run s := by
  have hI : installedSample P hMac e kp none s party = none := by
    unfold installedSample
    rw [hst]
  change traceSendAt P hMac irl e kp none party leaking s = _
  simp only [traceSendAt, hI]
  rfl

end TargetSends

end MLKEMBraid.NoAuth
