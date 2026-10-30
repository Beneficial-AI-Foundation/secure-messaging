/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Basic
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import ToVCVio.OracleComp.QueryTracking.OneUseSampling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import ToVCVio.OracleComp.SimSemantics.StateT.QueryImplAdd

/-!
# Stopping at exposure and installing the challenge value

The sets of exposed and challenged epochs only grow, and a challenged epoch is never exposed
later. From these facts alone, this module proves two results. Stopping two games at the first
exposure of `e` keeps the difference of their acceptance probabilities (`signedGap_stop`).
Sampling the challenge value of `e` once before the run gives the same distribution as sampling
it at the challenge (`stoppedRun_chalSample`).
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

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
    simp only [traceChallengeAt, ite_eq_left hex, mem_support_pure_iff] at hz
    rw [hz]
  · cases hk : lookupKey s.game t with
    | none =>
        simp only [traceChallengeAt, ite_eq_right hex, hk, mem_support_pure_iff] at hz
        left
        rw [hz]
    | some k =>
        simp only [traceChallengeAt, ite_eq_right hex, hk, support_map] at hz
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
    · rw [ite_eq_left hc, mem_support_pure_iff] at hz
      rw [hz]
      exact FlagStep.refl s
    · rw [ite_eq_right hc, mem_support_pure_iff] at hz
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
  change z ∈ support (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSend P hMac irl party false).run s) at hz
  rw [StateT.run_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact traceSend_flagStep hMac irl hw

/-- An installed ordinary send is a flag step. -/
theorem tracePlainAt_flagStep (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party : Bool) :
    ∀ t s z, z ∈ support ((tracePlainAt P hMac irl e kp ec party t).run s) → FlagStep s z.2 := by
  intro t s z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
  exact traceSendAt_flagStep hMac irl e kp ec hw

variable [DecidableEq P.Sym]

/-- A trace receive is a flag step. -/
theorem traceReceive_flagStep (repair party : Bool) :
    ∀ n s z, z ∈ support ((traceReceive P hMac irl repair party n).run s) → FlagStep s z.2 := by
  intro n s z hz
  change z ∈ support ((liftGame (if party then
    SCKAScheme.oracleRecvA (recvScheme P hMac irl repair s.transcript) n
    else SCKAScheme.oracleRecvB (recvScheme P hMac irl repair s.transcript) n)).run s) at hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz
  change FlagStep s { s with game := w.2 }
  cases party
  · rw [ite_eq_right Bool.false_ne_true] at hw
    obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvB_flags _ hw
    exact ⟨subset_of_eq h1.symm, subset_of_eq h2.symm, fun _ _ h => h1 ▸ h⟩
  · rw [ite_eq_left rfl] at hw
    obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvA_flags _ hw
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
      simp only [traceChallenge, ite_eq_left hex]
    · cases hk : lookupKey s.game t with
      | none =>
          left
          change traceChallenge P m t s = traceChallenge P m' t s
          simp only [traceChallenge, ite_eq_right hex, hk]
      | some k =>
          right
          have hc : ∀ mm : ℕ → Mode, ∀ z ∈ support ((traceChallenge P mm t).run s),
              Committed t z.2 := by
            intro mm z hz
            change z ∈ support (traceChallenge P mm t s) at hz
            simp only [traceChallenge, ite_eq_right hex, hk, support_map] at hz
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
    simp only [traceChallenge, ite_eq_left (Or.inl hs)]
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
      (traceImpl P hMac irl true m t).run s = (traceImpl P hMac irl true m' t).run s := by
  intro t s hs
  rcases t with (((((((((t | t) | t) | t) | t) | t) | t) | t) | t) | t) <;>
    first | rfl | exact traceChallenge_eq_of_exposed m m' e hm _ s hs

/-- From a state where `e` is exposed, two repaired trace games whose modes agree off `e` accept
with the same probability. -/
theorem probOutput_run_eq_of_exposed (m m' : ℕ → Mode) (e : ℕ)
    (hm : ∀ t, t ≠ e → m t = m' t) (s : TraceState P) (hs : targetStop e s = true)
    (oa : OracleComp (Spec P irl) Bool) :
    Pr{let x ← (simulateQ (traceImpl P hMac irl true m) oa).run' s}[x = true] =
      Pr{let x ← (simulateQ (traceImpl P hMac irl true m') oa).run' s}[x = true] := by
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
    (Pr{let x ← Prod.fst <$> run P hMac irl true m A}[x = true]).toReal -
        (Pr{let x ← Prod.fst <$> run P hMac irl true m' A}[x = true]).toReal =
      (Pr{let x ← (stoppedRun (traceImpl P hMac irl true m) (targetStop e) A
          (initTrace P hMac))}[x = true]).toReal -
        (Pr{let x ← (stoppedRun (traceImpl P hMac irl true m') (targetStop e) A
          (initTrace P hMac))}[x = true]).toReal := by
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

/-- A stopped oracle step depends only on the oracle's step. -/
private theorem stopOnState_run_congr {ι σ : Type} {spec : OracleSpec ι}
    {impl impl' : QueryImpl spec (StateT σ ProbComp)} (stop : σ → Bool) {t : spec.Domain} {s : σ}
    (h : (impl t).run s = (impl' t).run s) :
    ((stopOnState impl stop t).run).run s = ((stopOnState impl' stop t).run).run s := by
  rw [OracleComp.stopOnState_run_eq_map, OracleComp.stopOnState_run_eq_map, h]

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
  · simp only [traceChallengeAt, ite_eq_left hex]
  · cases hk : lookupKey s.game t with
    | none => simp only [traceChallengeAt, ite_eq_right hex, hk]
    | some k =>
        have hte : t ≠ e := by
          intro hte
          subst hte
          exact h ⟨rfl, fun h' => hex (Or.inl h'), fun h' => hex (Or.inr h'), by simp [hk]⟩
        simp only [traceChallengeAt, ite_eq_right hex, hk, ite_eq_right hte]

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
  cases x <;> simp only [traceChallengeAt, ite_eq_right hex, hk, ↓reduceIte]

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
    ((stopOnState (traceImplAt P hMac irl e kp ec none mode) (targetStop e) q).run).run s =ᵈ
        Prod.map id id <$> ((sampleEachQuery sample fun x =>
        stopOnState (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e)) q).run.run
          s := by
  rw [sampleEachQuery_run, Prod.map_id, id_map]
  by_cases hq : chalHit e q s = true
  · rcases q with ((q | t) | q) | q
    · exact absurd hq (by simp [chalHit])
    · obtain ⟨rfl, hexp, hch, hk⟩ := of_decide_eq_true hq
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
      have hex : ¬ (t ∈ s.game.exposed ∨ t ∈ s.game.challenged) := fun h => h.elim hexp hch
      change ((stopOnState (traceChallengeAt P mode t none) (targetStop t) t).run).run s =ᵈ
          sample >>= fun x =>
          ((stopOnState (traceChallengeAt P mode t (some x)) (targetStop t) t).run).run s
      simp only [OracleComp.stopOnState_run_eq_map, traceChallengeAt_hit mode t _ s hex hk, hsample,
        Functor.map_map, map_pure, bind_pure_comp, EvalDistEq.refl]
    · exact absurd hq (by simp [chalHit])
    · exact absurd hq (by simp [chalHit])
  · have hq' : chalHit e q s = false := by simpa using hq
    have heq : ∀ x, ((stopOnState (traceImplAt P hMac irl e kp ec (some x) mode)
        (targetStop e) q).run).run s =
        ((stopOnState (traceImplAt P hMac irl e kp ec none mode) (targetStop e) q).run).run s :=
      fun x => stopOnState_run_congr _ (traceImplAt_offHit hMac irl e kp ec mode x q s hq')
    simp only [heq]
    exact (EvalDistEq.bind_const _ _).symm

/-- **Installing the challenge value.** Sampling the challenge value of `e` once before the run
and installing it is the same as sampling it at the eligible challenge of `e`. -/
theorem stoppedRun_chalSample (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (mode : ℕ → Mode) (sample : ProbComp P.EpochKey)
    (hsample : ∀ k, challengeValue P (mode e) e k = sample) (A : Adversary P irl)
    (s : TraceState P) :
    Pr{let y ← do
        let x ← sample
        stoppedRun (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e) A s}[y = true] =
      Pr{let x ← stoppedRun (traceImplAt P hMac irl e kp ec none mode) (targetStop e) A s}[x = true]
          := by
  have hU := optionRun_sample_once_eq_sampleEachQuery sample
    (fun x => stopOnState (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e))
    (fun _ => True) (fun s => e ∈ s.game.challenged) (chalHit e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun x _ q s _ hu z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
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
        obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
        change w ∈ support ((traceChallengeAt P mode t (some x) t).run s) at hw
        rw [traceChallengeAt_hit mode t (some x) s (fun h => h.elim hexp hch) hk,
          support_map] at hw
        obtain ⟨out, -, rfl⟩ := hw
        exact Finset.mem_insert_self t _
      · exact absurd hq (by simp [chalHit])
      · exact absurd hq (by simp [chalHit]))
    A s trivial
  have hS := prEvent_optionRun_eq_of_state_map
    (sampleEachQuery sample fun x =>
      stopOnState (traceImplAt P hMac irl e kp ec (some x) mode) (targetStop e))
    (stopOnState (traceImplAt P hMac irl e kp ec none mode) (targetStop e)) id (fun _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun q s _ => chalSample_step hMac irl e kp ec mode sample hsample q s) A s trivial
  exact hU.trans hS.symm

end ChallengeSample

end MLKEMBraid.NoAuth
