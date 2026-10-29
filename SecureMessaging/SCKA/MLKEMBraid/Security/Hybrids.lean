/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Trace
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling

/-!
# Numerical-epoch hybrid endpoints

Every available challenge key belongs to a positive recorded encapsulation epoch. The
produced-epoch invariant bounds it by accepted sends, and the pathwise budget bounds those
sends along adaptive runs. This identifies the repaired endpoint distributions without
importing analytical bad-event risk estimates.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

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
  · rw [ite_eq_left hc] at hk
    exact ⟨hc.1, fun h0 => hk (by simp [h0])⟩
  · rw [ite_eq_right hc] at hk
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
  cases hst : s.game.stateAt party
  case keysUnsampled e a =>
    rw [sampledSend_eq_keygen hMac irl s party hst, support_map] at hw
    obtain ⟨x, -, rfl⟩ := hw
    left
    intro t
    by_cases ht : t = e
    · rw [ht]
      simp
    · simp [Function.update_of_ne ht]
  case headerReceived e a hdr dec =>
    rw [sampledSend_eq_encaps1 hMac irl s party hst, support_map] at hw
    obtain ⟨x, -, rfl⟩ := hw
    exact Or.inr ⟨e, a, hdr, dec, x.1, rfl, rfl⟩
  all_goals
    rw [sampledSend_of_noSample hMac irl s party (by simp [hst]) (by simp [hst]),
      support_map] at hw
    obtain ⟨r, -, rfl⟩ := hw
    exact Or.inl fun _ => rfl

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
  · rw [ite_eq_right Bool.false_ne_true] at hw
    obtain ⟨-, -, h1, h2⟩ := SCKAScheme.oracleRecvB_flags _ hw
    simp only [sendCount, h1, h2]
  · rw [ite_eq_left rfl] at hw
    obtain ⟨-, -, h1, h2⟩ := SCKAScheme.oracleRecvA_flags _ hw
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
    Prod.fst <$> run P hMac irl true m A =ᵈ Prod.fst <$> run P hMac irl true m' A := by
  have hbad : Pr{let z ← run P hMac irl true m A}[qS < sendCount z.2] = 0 := by
    rw [prEvent_eq_zero_iff]
    intro z hz
    have hle := IsQueryBoundP.cost_le_of_mem_support_run_simulateQ
      (impl := traceImpl P hMac irl true m) sendCount
      (fun t ht s z hz => by simpa [ht] using (traceImpl_count hMac irl true m t s z hz).2)
      (fun t ht s z hz => by simpa [ht] using (traceImpl_count hMac irl true m t s z hz).2)
      hqS _ z hz
    have h0 : z.2.game.nA + z.2.game.nB ≤ qS := by
      simpa [sendCount, SCKAScheme.initGameState] using hle
    exact not_lt.mpr h0
  refine evalDistEq_of_forall_prEvent_eq_output fun x => ?_
  simp only [Functor.map_map]
  have habs := abs_prEvent_simulateQ_run_sub_le_bad_of_inv
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
  change |(Pr{let z ← run P hMac irl true m A}[z.1 = x]).toReal -
      (Pr{let z ← run P hMac irl true m' A}[z.1 = x]).toReal| ≤
    (Pr{let z ← run P hMac irl true m A}[qS < sendCount z.2]).toReal at habs
  rw [hbad, ENNReal.toReal_zero, abs_nonpos_iff, sub_eq_zero] at habs
  exact (ENNReal.toReal_eq_toReal_iff' (prEvent_ne_top _) (prEvent_ne_top _)).mp habs

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
    hybrid P hMac irl A 0 =ᵈ
        Prod.fst <$> run P hMac irl true (fun _ => if false then .uniform else .real) A ∧
      hybrid P hMac irl A qS =ᵈ
          Prod.fst <$> run P hMac irl true (fun _ => if true then .uniform else .real) A :=
  ⟨run_mode_evalDist_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS _ _
      fun _ he _ => by simp [Nat.not_le.mpr he],
    run_mode_evalDist_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS _ _
      fun _ _ he => by simp [he]⟩

end MLKEMBraid.NoAuth
