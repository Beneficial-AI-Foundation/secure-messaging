/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Trace
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import SecureMessaging.KEM.IncrementalKEM.Correctness
import ToVCVio.ProgramLogic.Unary.WP
import ToVCVio.OracleComp.SimSemantics.StateT.WPBound
import ToVCVio.OracleComp.SimSemantics.StateT.QueryImplAdd

/-!
# Conditional decapsulation risk and the bad-event bound

Key generation adds its mean failure risk. A retained key pair carries its own conditional
risk until first-stage encapsulation consumes it. The score and drift argument below do not
replace that conditional quantity by the fresh-key mean at an adaptive state.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming
open OracleComp.ProgramLogic

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- Adding a constant to every payoff raises the expected payoff by at most that constant. -/
private theorem wp_add_const_le {α : Type} (oa : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    wp oa (fun a => f a + c) ≤ wp oa f + c :=
  le_of_eq (by rw [wp_add, wp_const])

section BadEventBound

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
    wp X (fun z => badScore z.2) ≤ badScore s :=
  wp_le_const_of_support _ fun z hz => by
    obtain ⟨h1, h2⟩ := h z hz
    simp [badScore, h1, h2]

variable (hMac : P.Mac = Unit) [DecidableEq P.EpochKey] (irl : P.kem.IncrementalRandLeak P.inc)

omit [DecidableEq P.K] in
/-- The coin tag and records of a key-generation sample. -/
private theorem obs_sampledSend_keysUnsampled (s : TraceState P) (party : Bool) {e : ℕ}
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled e a) :
    (fun w => (w.1.2, w.2)) <$> sampledSend P hMac irl s party =
      (fun x : (P.PK × P.SK) × irl.KeygenRand => (SendRand.keygen x.2,
        Function.update s.transcript e { (s.transcript e) with keypair := some x.1 }, s.bad)) <$>
        irl.keygenRleak := by
  rw [sampledSend_eq_keygen hMac irl s party hst, Functor.map_map]

omit [DecidableEq P.K] in
/-- The coin tag, records and bad flag of a first-stage encapsulation sample. -/
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
  rw [sampledSend_eq_encaps1 hMac irl s party hst, Functor.map_map]
  rfl

omit [DecidableEq P.K] in
/-- A send that samples nothing keeps the records and the bad flag. -/
private theorem obs_sampledSend_steady (s : TraceState P) (party : Bool)
    (hsteady : (s.game.stateAt party).SendsNoSample) :
    ∀ w ∈ support (sampledSend P hMac irl s party), w.2 = (s.transcript, s.bad) := by
  have h1 : ∀ t a, s.game.stateAt party ≠ .keysUnsampled t a := by
    intro t a hh
    rw [hh] at hsteady
    exact hsteady
  have h2 : ∀ t a hdr dec, s.game.stateAt party ≠ .headerReceived t a hdr dec := by
    intro t a hdr dec hh
    rw [hh] at hsteady
    exact hsteady
  intro w hw
  rw [sampledSend_of_noSample hMac irl s party h1 h2, support_map] at hw
  obtain ⟨r, -, rfl⟩ := hw
  rfl

/-- A trace send raises the expected bad-event score by at most the KEM correctness error. -/
theorem traceSend_payoff (party leaking : Bool) (s : TraceState P)
    (hs : TraceInv hMac false s) :
    wp ((traceSend P hMac irl party leaking).run s) (fun z => badScore z.2) ≤
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
    have hpay : wp ((traceSend P hMac irl party leaking).run s)
        (fun z => badScore z.2) =
        wp ((fun w => (w.1.2, w.2)) <$> sampledSend P hMac irl s party) H := by
      change wp (traceSend P hMac irl party leaking s) _ = _
      simp only [traceSend]
      rw [wp_map, wp_map]
      congr 1
      funext w
      simp only [Function.comp_apply]
      have hx : (leaking && decide ((exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2 ∩
          s.game.challenged ≠ ∅)) = R w.1.2 := rfl
      rw [hx]
      simp only [H]
      by_cases hc : R w.1.2 = true
      · rw [ite_eq_left hc, ite_eq_left hc]
        simp [badScore, hb]
      · rw [ite_eq_right hc, ite_eq_right hc]
        rfl
    rw [hpay]
    cases hst : s.game.stateAt party
    case keysUnsampled e a =>
      have hRe : ∀ r, R (SendRand.keygen r) =
          (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) := by
        intro r
        simp only [R, hst]
        rfl
      have hL := hR.local _ party
      rw [hst] at hL
      obtain ⟨-, h1, h2⟩ := hL
      rw [obs_sampledSend_keysUnsampled hMac irl s party hst, wp_map]
      by_cases hRk : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · refine le_trans (wp_le_const_of_support _
          fun x _ => le_of_eq ?_) le_self_add
        simp only [H, Function.comp_apply]
        rw [hRe x.2, ite_eq_left hRk]
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
          rw [hRe rand, ite_eq_right hRk, hb, ite_eq_right Bool.false_ne_true, hu, add_comm]
        have hkg : wp irl.keygenRleak (fun x : (P.PK × P.SK) × irl.KeygenRand =>
            P.inc.decapsFailureProb (P.inc.toHeader x.1.1) (P.inc.toVector x.1.1) x.1.2) =
            P.kem.correctnessError ProbCompRuntime.probComp := by
          rw [← P.inc.wp_keygen_decapsFailureProb, ← irl.keygen_fst, bind_pure_comp,
            wp_map]
          try rfl
        refine le_trans (wp_mono _ fun x => le_of_eq (hstep x)) ?_
        refine le_trans (wp_add_const_le _ _ _) ?_
        rw [hkg]
        exact le_of_eq (add_comm _ _)
    case headerReceived e a hdr dec =>
      obtain ⟨pk, sk, -, -, hkpT, -, hhdr⟩ := peer_keysSampled_of_headerReceived _ hR party hst
      subst hhdr
      have hRe : ∀ r, R (SendRand.encaps1 r) =
          (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) := by
        intro r
        simp only [R, hst]
        rfl
      have hL := hR.local _ party
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
      rw [obs_sampledSend_headerReceived hMac irl s party hst, wp_map]
      by_cases hRk : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · refine le_trans (wp_le_const_of_support _
          fun x _ => le_of_eq ?_) le_self_add
        simp only [H, Function.comp_apply]
        rw [hRe x.2, ite_eq_left hRk]
      · have hfp : wp (irl.encaps1Rleak (P.inc.toHeader pk))
            (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
              if P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
                P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
              then 0 else 1) =
            P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
          rw [P.inc.decapsFailureProb_eq_wp P.hDet P.hEnc2, ← irl.encaps1_fst,
            bind_pure_comp, wp_map]
          try rfl
        refine le_trans (wp_mono _ (post' :=
          fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
            (if P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
              P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
            then 0 else 1) + c) fun x => ?_) ?_
        · simp only [H, Function.comp_apply]
          rw [hRe x.2, ite_eq_right hRk, hupd x.1]
          simp only [hkpT, hb, Bool.false_or]
          by_cases hfail : P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
              P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
          · have hk : decapsEpochKey (P := P) e pk sk x.1.1 x.1.2.1 = some (P.kdfOK x.1.2.2 e) :=
              congrArg (Option.map fun k => P.kdfOK k e) hfail
            have hnot : ¬ (decide (decapsEpochKey (P := P) e pk sk x.1.1 x.1.2.1 ≠
                some (P.kdfOK x.1.2.2 e)) = true) := fun h => of_decide_eq_true h hk
            rw [ite_eq_right hnot, ite_eq_left hfail, zero_add]
          · rw [ite_eq_right hfail]
            split_ifs
            · exact le_self_add
            · exact le_add_self
        · refine le_trans (wp_add_const_le _ _ _) ?_
          rw [hfp, add_comm _ c, hc]
          exact le_self_add
    all_goals
      have hsteady : (s.game.stateAt party).SendsNoSample := by
        rw [hst]
        trivial
      refine le_trans (wp_le_const_of_support _
        fun o ho => ?_) le_self_add
      rw [support_map] at ho
      obtain ⟨w, hw, rfl⟩ := ho
      have hw2 := obs_sampledSend_steady hMac irl s party hsteady w hw
      simp only [H, hw2, hb, Bool.false_eq_true, ↓reduceIte]
      by_cases hc : R w.1.2 = true <;> simp [hc]
  · refine le_trans ?_ le_self_add
    refine wp_le_const_of_support _ fun z hz => ?_
    simp [badScore, traceSend_bad hMac irl hb hz, hb]

variable [DecidableEq P.Sym] [SampleableType P.K] [SampleableType P.EpochKey]

/-- One query of the real trace game raises the expected bad-event score by at most the KEM
correctness error for a send, and not at all for any other query. -/
theorem traceImpl_payoff (mode : ℕ → Mode) :
    ∀ t s, TraceInv hMac false s →
      wp ((traceImpl P hMac irl false mode t).run s) (fun z => badScore z.2) ≤
        badScore s + if isSendQuery t = true then
          P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
  intro t s hs
  rw [isSendQuery_eq_sendElim irl t]
  have hzero : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P) ProbComp)),
      (∀ t s, ∀ z ∈ support ((c t).run s), z.2.transcript = s.transcript ∧ z.2.bad = s.bad) →
      ∀ t s, TraceInv hMac false s → wp ((c t).run s) (fun z => badScore z.2) ≤
        badScore s + if (fun _ => false) t then
          P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
    intro ι spec c hc t s _
    simpa using payoff_le_of_support _ s (hc t s)
  have hsend : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P) ProbComp)),
      (∀ t s, TraceInv hMac false s → wp ((c t).run s) (fun z => badScore z.2) ≤
        badScore s + P.kem.correctnessError ProbCompRuntime.probComp) →
      ∀ t s, TraceInv hMac false s → wp ((c t).run s) (fun z => badScore z.2) ≤
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
      wp ((tracePlain P hMac irl party t).run s) (fun z => badScore z.2) ≤
        badScore s + P.kem.correctnessError ProbCompRuntime.probComp := by
    intro party t s hs
    change wp (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
      traceSend P hMac irl party false).run s) _ ≤ _
    rw [StateT.run_map, wp_map]
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
`qS` times the KEM correctness error. -/
theorem badEvent_le (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) (b : Bool) :
    Pr{let z ← run P hMac irl false (fun _ => if b then .uniform else .real) A}[z.2.bad = true] ≤
      (qS : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp := by
  -- Key generation charges the average failure of the KEM. The conditional risk of the retained
  -- key pair is consumed at first-stage encapsulation.
  have hE := wp_simulateQ_run_le
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
  calc Pr{let z ← run P hMac irl false (fun _ => if b then .uniform else .real) A}[z.2.bad = true]
      ≤ wp (run P hMac irl false (fun _ => if b then .uniform else .real) A)
          (fun z => badScore z.2) :=
        prEvent_le_wp _ _ _ fun z hz => by simp [badScore, hz]
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
    Pr{let z ← run P hMac irl false (fun _ => if b then .uniform else
        .real) A}[z.2.game.correct = false] ≤
      (qS : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp := by
  refine le_trans (prEvent_mono_of_support _ _ _ fun z hz hc => ?_)
    (badEvent_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS b)
  by_contra hb
  have hcor := (real_trace_before_bad P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct
    _ A z hz (by simpa using hb)).1.correct
  rw [hc] at hcor
  cases hcor

end MLKEMBraid.NoAuth
