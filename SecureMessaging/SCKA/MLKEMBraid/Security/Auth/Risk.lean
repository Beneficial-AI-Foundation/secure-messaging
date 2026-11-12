/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Trace.Inv
public import SecureMessaging.SCKA.MLKEMBraid.Security.Risk
public import ToVCVio.ProgramLogic.Unary.WP
public import ToVCVio.OracleComp.SimSemantics.StateT.WPBound

/-!
# The bad-event bound of the real trace game

The real trace game sets its bad flag at a first-stage encapsulation whose decapsulation with the
recorded key pair would not give the derived epoch key. This module bounds the probability of
this event by `qS · ε`, where `qS` bounds the number of sends and `ε` is the correctness error of
the KEM (`badEvent_le`).

The proof uses a score. After the bad event the score `badScore` is one. Before it, the score is
the pending risk of the records: for each epoch with a recorded key pair and no recorded
encapsulation, the decapsulation-failure probability of that key pair. A key-generation send adds,
in expectation, the mean failure probability of a fresh key pair, which is `ε`. A first-stage
encapsulation removes the conditional risk of the retained key pair, and that risk bounds the
probability that the send sets the bad flag. The argument never replaces the conditional risk of
a retained key pair by the mean over fresh key pairs. Every other query leaves the score unchanged.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming
open OracleComp.ProgramLogic

namespace MLKEMBraid.Auth

open Braid

variable {P : Parameters ProbComp} {Root MacKey : Type}

/-- The bad-event score of a trace state: `1` after the bad event, and before it the pending
decapsulation risk of the records (`Braid.NoAuth.pendingPotential`). -/
noncomputable def badScore {AS : Type} [DecidableEq P.K] (s : TraceState P AS) : ENNReal :=
  if s.bad then 1 else NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript)

/-- Let the game state of the real game agree with the records, and let the bad flag be false.
From `keysUnsampled`, the key-generation send raises the expected score by at most the KEM
correctness error: it adds the mean decapsulation-failure probability of a fresh key pair. -/
theorem traceSend_payoff_keygen [DecidableEq P.K] [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (ik : P.EpochKey) (leaking : Bool) (s : TraceState P (Root × MacKey)) (party : Bool)
    (hR : RepairInv S (Installed.empty (irl := irl)) Modes.real ik s.transcript s.game)
    (hb : s.bad = false) {e : ℕ} {a : Root × MacKey}
    (hst : s.game.stateAt party = .keysUnsampled e a) :
    wp ((fun w => (w.1.2, w.2)) <$> sampledSend S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) s party)
      (fun o => if (leaking && decide ((exposureAt P irl (Root × MacKey)).rleak
          (s.game.stateAt party) o.1 ∩ s.game.challenged ≠ ∅)) then
          NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript)
        else if o.2.2 then 1 else NoAuth.pendingPotential (EpochRecord.toTranscript ∘ o.2.1)) ≤
      NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript) +
        P.kem.correctnessError ProbCompRuntime.probComp := by
  let R : SendRand irl.KeygenRand irl.Encaps1Rand → Bool := fun tag =>
    leaking && decide ((exposureAt P irl (Root × MacKey)).rleak (s.game.stateAt party) tag ∩
      s.game.challenged ≠ ∅)
  let H : SendRand irl.KeygenRand irl.Encaps1Rand × (ℕ → EpochRecord P (Root × MacKey)) × Bool →
      ENNReal := fun o =>
    if R o.1 then NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript)
    else if o.2.2 then 1 else NoAuth.pendingPotential (EpochRecord.toTranscript ∘ o.2.1)
  change wp ((fun w => (w.1.2, w.2)) <$> sampledSend S.toRatcheted irl Installed.empty
    (installedRules S (Installed.empty (irl := irl)) Modes.real) s party) H ≤ _
  have hRe : ∀ r, R (SendRand.keygen r) =
      (leaking && decide ({e, e + 1} ∩ s.game.challenged ≠ ∅)) := by
    intro r
    simp only [R, hst]
    rfl
  have hL := hR.local party
  rw [hst] at hL
  obtain ⟨-, h1, h2⟩ := hL
  have h1' : (s.transcript e).keypair = none := h1
  have h2' : (s.transcript e).encaps1 = none := h2
  rw [sampledSend_eq_keygen S.toRatcheted irl Installed.empty _ s party hst rfl, Functor.map_map,
    wp_map]
  by_cases hRk : (leaking && decide ({e, e + 1} ∩ s.game.challenged ≠ ∅)) = true
  · refine le_trans (wp_le_const_of_support _ fun x _ => le_of_eq ?_) le_self_add
    simp only [H, Function.comp_apply]
    rw [hRe x.2, ite_eq_left hRk]
  · have hstep : ∀ x : (P.PK × P.SK) × irl.KeygenRand,
        H (SendRand.keygen x.2,
          Function.update s.transcript e { (s.transcript e) with keypair := some x.1 }, s.bad) =
          P.inc.decapsFailureProb (P.inc.toHeader x.1.1) (P.inc.toVector x.1.1) x.1.2 +
            NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript) := by
      rintro ⟨⟨pk, sk⟩, rand⟩
      have hu := NoAuth.pendingPotential_update (EpochRecord.toTranscript ∘ s.transcript) e
        (EpochRecord.toTranscript { (s.transcript e) with keypair := some (pk, sk) })
      have h0 : NoAuth.pendingRisk ((EpochRecord.toTranscript ∘ s.transcript) e) = 0 := by
        simp [NoAuth.pendingRisk, EpochRecord.toTranscript, h1', h2']
      have hr : NoAuth.pendingRisk (EpochRecord.toTranscript
          { (s.transcript e) with keypair := some (pk, sk) }) =
          P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
        simp [NoAuth.pendingRisk, EpochRecord.toTranscript, h2']
      rw [h0, hr, add_zero] at hu
      simp only [H]
      rw [hRe rand, ite_eq_right hRk, hb, ite_eq_right Bool.false_ne_true, Function.comp_update,
        hu, add_comm]
    have hkg : wp irl.keygenRleak (fun x : (P.PK × P.SK) × irl.KeygenRand =>
        P.inc.decapsFailureProb (P.inc.toHeader x.1.1) (P.inc.toVector x.1.1) x.1.2) =
        P.kem.correctnessError ProbCompRuntime.probComp := by
      rw [← P.inc.wp_keygen_decapsFailureProb, ← irl.keygen_fst, bind_pure_comp, wp_map]
      try rfl
    refine le_trans (wp_mono _ fun x => le_of_eq (hstep x)) ?_
    rw [wp_add, wp_const, hkg, add_comm]

/-- Let the game state of the real game agree with the records, and let the bad flag be false.
From `headerReceived`, the first-stage encapsulation send raises the expected score by at most the
KEM correctness error: the conditional risk of the retained key pair, which the send removes from
the score, bounds the probability that the send sets the bad flag. -/
theorem traceSend_payoff_encaps1 [DecidableEq P.K] [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (ik : P.EpochKey) (leaking : Bool) (s : TraceState P (Root × MacKey)) (party : Bool)
    (hR : RepairInv S (Installed.empty (irl := irl)) Modes.real ik s.transcript s.game)
    (hb : s.bad = false) {e : ℕ} {a : Root × MacKey} {hdr : P.inc.PKheader} {dec : P.decEk.D}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) :
    wp ((fun w => (w.1.2, w.2)) <$> sampledSend S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) s party)
      (fun o => if (leaking && decide ((exposureAt P irl (Root × MacKey)).rleak
          (s.game.stateAt party) o.1 ∩ s.game.challenged ≠ ∅)) then
          NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript)
        else if o.2.2 then 1 else NoAuth.pendingPotential (EpochRecord.toTranscript ∘ o.2.1)) ≤
      NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript) +
        P.kem.correctnessError ProbCompRuntime.probComp := by
  let R : SendRand irl.KeygenRand irl.Encaps1Rand → Bool := fun tag =>
    leaking && decide ((exposureAt P irl (Root × MacKey)).rleak (s.game.stateAt party) tag ∩
      s.game.challenged ≠ ∅)
  let H : SendRand irl.KeygenRand irl.Encaps1Rand × (ℕ → EpochRecord P (Root × MacKey)) × Bool →
      ENNReal := fun o =>
    if R o.1 then NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript)
    else if o.2.2 then 1 else NoAuth.pendingPotential (EpochRecord.toTranscript ∘ o.2.1)
  change wp ((fun w => (w.1.2, w.2)) <$> sampledSend S.toRatcheted irl Installed.empty
    (installedRules S (Installed.empty (irl := irl)) Modes.real) s party) H ≤ _
  have hL := hR.local party
  rw [hst] at hL
  obtain ⟨-, hc0, pk, sk, hkpT, hhdr, -⟩ := hL
  subst hhdr
  have hc0' : (s.transcript e).encaps1 = none := hc0
  have hkpT' : (s.transcript e).keypair = some (pk, sk) := hkpT
  have hRe : ∀ r, R (SendRand.encaps1 r) =
      (leaking && decide ({e, e + 1} ∩ s.game.challenged ≠ ∅)) := by
    intro r
    simp only [R, hst]
    rfl
  have hrisk : NoAuth.pendingRisk ((EpochRecord.toTranscript ∘ s.transcript) e) =
      P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
    simp [NoAuth.pendingRisk, EpochRecord.toTranscript, hkpT', hc0']
  obtain ⟨c, hc, hupd⟩ : ∃ c : ENNReal,
      c + P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk =
        NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript) ∧
      ∀ (x : P.inc.St × P.inc.C₁ × P.K) key pair, NoAuth.pendingPotential
        (EpochRecord.toTranscript ∘ Function.update s.transcript e
          { (s.transcript e) with encaps1 := some x, key := some key, pair := some pair }) = c := by
    refine ⟨NoAuth.pendingPotential (Function.update (EpochRecord.toTranscript ∘ s.transcript) e
      { keypair := none, encaps1 := none }), ?_, fun x key pair => ?_⟩
    · have hu := NoAuth.pendingPotential_update (EpochRecord.toTranscript ∘ s.transcript) e
        { keypair := none, encaps1 := none }
      rw [hrisk] at hu
      simp only [NoAuth.pendingRisk, add_zero] at hu
      exact hu
    · rw [Function.comp_update]
      refine tsum_congr fun t => ?_
      by_cases ht : t = e
      · subst ht
        simp [NoAuth.pendingRisk, EpochRecord.toTranscript]
      · rw [Function.update_of_ne ht, Function.update_of_ne ht]
  have hkey : ∀ k, (installedRules S (Installed.empty (irl := irl)) Modes.real).key e k =
      pure (P.kdfOK k e) := fun _ => rfl
  have hpair : ∀ prev x,
      (installedRules S (Installed.empty (irl := irl)) Modes.real).pair e prev x =
        pure (S.F e prev.1 x) := fun _ _ => rfl
  rw [sampledSend_eq_encaps1 S.toRatcheted irl Installed.empty _ s party hst rfl]
  simp only [hkey, hpair, map_pure, bind_pure_comp, Functor.map_map]
  rw [wp_map]
  by_cases hRk : (leaking && decide ({e, e + 1} ∩ s.game.challenged ≠ ∅)) = true
  · refine le_trans (wp_le_const_of_support _ fun x _ => le_of_eq ?_) le_self_add
    simp only [H, Function.comp_apply]
    rw [hRe x.2, ite_eq_left hRk]
  · have hfp : wp (irl.encaps1Rleak (P.inc.toHeader pk))
        (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
          if P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
            P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
          then 0 else 1) =
        P.inc.decapsFailureProb (P.inc.toHeader pk) (P.inc.toVector pk) sk := by
      rw [P.inc.decapsFailureProb_eq_wp P.hDet P.hEnc2, ← irl.encaps1_fst, bind_pure_comp, wp_map]
      try rfl
    refine le_trans (wp_mono _ (post' :=
      fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        (if P.hDet.decapsDet sk (P.inc.splitC.symm (x.1.2.1,
          P.hEnc2.encaps2Det x.1.1 (P.inc.toHeader pk) (P.inc.toVector pk))) = some x.1.2.2
        then 0 else 1) + c) fun x => ?_) ?_
    · simp only [H, Function.comp_apply]
      rw [hRe x.2, ite_eq_right hRk, hupd x.1]
      simp only [encaps1Bad, hkpT', hb, Bool.false_or]
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
    · rw [wp_add, wp_const, hfp, add_comm _ c, hc]
      exact le_self_add

/-- Under `TraceInv` of the real game, a trace send raises the expected score by at most the KEM
correctness error. -/
theorem traceSend_payoff [DecidableEq P.K] [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (ik : P.EpochKey) (party leaking : Bool) (s : TraceState P (Root × MacKey))
    (hs : TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s) :
    wp ((traceSend S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party leaking).run s)
      (fun z => badScore z.2) ≤
      badScore s + P.kem.correctnessError ProbCompRuntime.probComp := by
  cases hb : s.bad
  · obtain ⟨hR, -⟩ := hs.1 (Or.inr hb)
    have hscore : badScore s =
        NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript) := by
      simp [badScore, hb]
    rw [hscore]
    let R : SendRand irl.KeygenRand irl.Encaps1Rand → Bool := fun tag =>
      leaking && decide ((exposureAt P irl (Root × MacKey)).rleak (s.game.stateAt party) tag ∩
        s.game.challenged ≠ ∅)
    let H : SendRand irl.KeygenRand irl.Encaps1Rand × (ℕ → EpochRecord P (Root × MacKey)) × Bool →
        ENNReal := fun o =>
      if R o.1 then NoAuth.pendingPotential (EpochRecord.toTranscript ∘ s.transcript)
      else if o.2.2 then 1 else NoAuth.pendingPotential (EpochRecord.toTranscript ∘ o.2.1)
    have hpay : wp ((traceSend S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party leaking).run s)
        (fun z => badScore z.2) =
        wp ((fun w => (w.1.2, w.2)) <$> sampledSend S.toRatcheted irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) s party) H := by
      change wp (traceSend S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party leaking s) _ = _
      simp only [traceSend]
      rw [wp_map, wp_map]
      congr 1
      funext w
      simp only [Function.comp_apply]
      have hx : (leaking && decide ((exposureAt P irl (Root × MacKey)).rleak
          (s.game.stateAt party) w.1.2 ∩ s.game.challenged ≠ ∅)) = R w.1.2 := rfl
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
      exact traceSend_payoff_keygen S irl ik leaking s party hR hb hst
    case headerReceived e a hdr dec =>
      exact traceSend_payoff_encaps1 S irl ik leaking s party hR hb hst
    all_goals
      refine le_trans (wp_le_const_of_support _ fun o ho => ?_) le_self_add
      rw [sampledSend_of_noSample S.toRatcheted irl Installed.empty _ s party (by simp [hst])
        (by simp [hst]), Functor.map_map, support_map] at ho
      obtain ⟨r, -, rfl⟩ := ho
      simp only [H, hb, Bool.false_eq_true, ↓reduceIte]
      by_cases hc : R SendRand.none = true <;> simp [hc]
  · refine le_trans ?_ le_self_add
    refine wp_le_const_of_support _ fun z hz => ?_
    simp [badScore, traceSend_bad S.toRatcheted irl Installed.empty _ hb hz, hb]

/-- Under `TraceInv` of the real game, one query of the real trace game raises the expected score by
at most the KEM correctness error for a send, and not at all for any other query. -/
theorem traceImpl_payoff [DecidableEq P.K] [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (ik : P.EpochKey) (modes : Modes) :
    ∀ t s, TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s →
      wp ((traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) modes false t).run s)
        (fun z => badScore z.2) ≤
        badScore s + if SCKAScheme.sckaSecuritySpec.isSendQuery t = true then
          P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
  intro t s hs
  rw [isSendQuery_eq_sendElim P Root MacKey irl t]
  have hzero : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P (Root × MacKey)) ProbComp)),
      (∀ t s, ∀ z ∈ support ((c t).run s), z.2.transcript = s.transcript ∧ z.2.bad = s.bad) →
      ∀ t s, TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s →
        wp ((c t).run s) (fun z => badScore z.2) ≤
          badScore s + if (fun _ => false) t then
            P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
    intro ι spec c hc t s _
    have h : wp ((c t).run s) (fun z => badScore z.2) ≤ badScore s :=
      wp_le_const_of_support _ fun z hz => by
        obtain ⟨h1, h2⟩ := hc t s z hz
        simp [badScore, h1, h2]
    simpa using h
  have hsend : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (TraceState P (Root × MacKey)) ProbComp)),
      (∀ t s, TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s →
        wp ((c t).run s) (fun z => badScore z.2) ≤
          badScore s + P.kem.correctnessError ProbCompRuntime.probComp) →
      ∀ t s, TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s →
        wp ((c t).run s) (fun z => badScore z.2) ≤
          badScore s + if (fun _ => true) t then
            P.kem.correctnessError ProbCompRuntime.probComp else 0 := by
    intro ι spec c hc t s hs
    simpa using hc t s hs
  have hlift : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (GameState P (Root × MacKey)) ProbComp)),
      ∀ t (s : TraceState P (Root × MacKey)), ∀ z ∈ support ((liftGame (c t)).run s),
        z.2.transcript = s.transcript ∧ z.2.bad = s.bad := by
    intro ι spec c t s z hz
    obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
    exact ⟨rfl, rfl⟩
  have hplain : ∀ party, ∀ t s, TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s →
      wp ((tracePlain S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party t).run s)
        (fun z => badScore z.2) ≤
        badScore s + P.kem.correctnessError ProbCompRuntime.probComp := by
    intro party t s hs
    change wp (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
      traceSend S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party false).run s) _ ≤ _
    rw [StateT.run_map, wp_map]
    exact traceSend_payoff S irl ik party false s hs
  have hcorrupt : ∀ party : Bool, ∀ t (s : TraceState P (Root × MacKey)),
      ∀ z ∈ support (((if party then traceCorruptA (AS := Root × MacKey) (MacKey := MacKey) irl some
        else traceCorruptB (AS := Root × MacKey) (MacKey := MacKey) irl some) t).run s),
        z.2.transcript = s.transcript ∧ z.2.bad = s.bad := by
    intro party t s z hz
    cases party
    · rw [ite_eq_right Bool.false_ne_true] at hz
      change z ∈ support (traceCorruptB irl some t s) at hz
      simp only [traceCorruptB] at hz
      split_ifs at hz <;> rw [mem_support_pure_iff] at hz <;> rw [hz] <;> exact ⟨rfl, rfl⟩
    · rw [ite_eq_left rfl] at hz
      change z ∈ support (traceCorruptA irl some t s) at hz
      simp only [traceCorruptA] at hz
      split_ifs at hz <;> rw [mem_support_pure_iff] at hz <;> rw [hz] <;> exact ⟨rfl, rfl⟩
  exact payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _
    (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _ (payoff_add _ _ _ _ _
      (payoff_add _ _ _ _ _
        (hzero (traceUnif P (Root × MacKey)) fun t s => hlift _ t s)
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
        (hsend _ fun _ s hs => traceSend_payoff S irl ik true true s hs))
        (hsend _ fun _ s hs => traceSend_payoff S irl ik false true s hs))
        (hzero _ fun e s z hz => by
          rcases mem_support_traceChallenge hz with hz | ⟨-, hz⟩ <;> rw [hz] <;>
            exact ⟨rfl, rfl⟩))
        (hzero _ (hcorrupt true)))
        (hzero _ (hcorrupt false)) t s hs

/-- Let the four stream decoders be sound, and let `A` make at most `qS` sends. Then in the real
trace game with the bit `b` the bad flag is set with probability at most `qS` times the KEM
correctness error. -/
theorem badEvent_le [DecidableEq P.K] [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (A : Adversary P S irl) (qS : ℕ) (hqS : SendQueryBound A qS) (b : Bool) :
    Pr{let z ← run S.toRatcheted some S irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false
        A}[z.2.bad = true] ≤
      (qS : ENNReal) * P.kem.correctnessError ProbCompRuntime.probComp := by
  have hinit : (installedRules S (Installed.empty (irl := irl)) Modes.real).initPair =
      (fun ik => S.F 1 S.initRoot ik) <$> ($ᵗ P.EpochKey) := rfl
  have hrun : run S.toRatcheted some S irl Installed.empty
      (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false A =
      ($ᵗ P.EpochKey) >>= fun ik => (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false)
        A).run (initTrace P (S.F 1 S.initRoot ik)) := by
    simp only [run, hinit, bind_map_left]
  -- Key generation charges the average failure of the KEM. The conditional risk of the retained
  -- key pair is consumed at first-stage encapsulation.
  have hE : ∀ ik : P.EpochKey,
      wp ((simulateQ (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false)
          A).run (initTrace P (S.F 1 S.initRoot ik))) (fun z => badScore z.2) ≤
        badScore (initTrace P (S.F 1 S.initRoot ik)) +
          (qS : ENNReal) * P.kem.correctnessError ProbCompRuntime.probComp := fun ik =>
    wp_simulateQ_run_le
      (traceImpl S.toRatcheted some irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false)
      (TraceInv S Installed.empty Modes.real ik false) badScore
      (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
      (P.kem.correctnessError ProbCompRuntime.probComp)
      (traceImpl_real_preservesInv S irl ik hHdrSound hEkSound hCt1Sound hCt2Sound _)
      (traceImpl_payoff S irl ik _) A qS hqS _
      (traceInv_init S Installed.empty Modes.real ik false _ fun _ h => by cases h)
  have h0 : ∀ a0 : Root × MacKey, badScore (initTrace P a0) = 0 := fun a0 => by
    simp [initTrace, badScore, NoAuth.pendingPotential, NoAuth.pendingRisk,
      EpochRecord.toTranscript]
  refine (prEvent_le_wp _ _ (fun z => badScore z.2) fun z hz => by simp [badScore, hz]).trans ?_
  rw [hrun, wp_bind]
  refine le_trans (wp_mono _ (post' := fun _ =>
    (qS : ENNReal) * P.kem.correctnessError ProbCompRuntime.probComp) fun ik => (hE ik).trans ?_)
    (le_of_eq (wp_const _ _))
  rw [h0, zero_add]

end MLKEMBraid.Auth
