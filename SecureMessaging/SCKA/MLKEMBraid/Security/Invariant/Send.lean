/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Basic
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import SecureMessaging.SCKA.MLKEMBraid.Correctness.SendInvariant

/-!
# Sends preserve the repaired invariant

The send lemmas of `Correctness.SendInvariant` hold for `TranscriptInv` with any condition on
decapsulation, so they apply to the repaired invariant `RepairInv`. A send that generates a key
pair or runs the first stage of encapsulation adds its sample to the transcript. The repaired
invariant holds after every send of the trace game. Decapsulation agreement holds after the send
while the bad flag stays false.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A committed trace send keeps the repaired invariant for its extended transcript, and keeps
decapsulation agreement whenever its bad flag stays false. -/
theorem traceSend_preserves (party leaking : Bool) (s : TraceState P)
    (h : RepairInv hMac s.transcript s.game)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) :
    RepairInv hMac z.2.transcript z.2.game ∧
      (DecapsGood s.transcript → z.2.bad = false → DecapsGood z.2.transcript) := by
  classical
  rcases mem_support_traceSend hMac irl hz with hz | ⟨⟨⟨r, rand⟩, T', bad'⟩, hw, -, hz⟩
  · rw [hz]
    exact ⟨h, fun hg _ => hg⟩
  rw [hz]
  dsimp only
  have hCPgen : ∀ r', r' ∈ support (send P (auth P hMac) (s.game.stateAt party)) →
      ControlInv (sendUpdate s.game party r') ∧ StatePairInv (sendUpdate s.game party r') := by
    intro r' hr'
    cases party
    · exact correctnessImpl_preserves_controlInv_statePairInv (auth P hMac) irl (pure ())
        (OSendB (Rho := Message P.Sym)) s.game ⟨h.control, h.statePair⟩ _
        ((mem_support_oracleSend_run_iff (auth P hMac) irl (pure ()) s.game false _).2
          ⟨r', hr', rfl⟩)
    · exact correctnessImpl_preserves_controlInv_statePairInv (auth P hMac) irl (pure ())
        (OSendA (Rho := Message P.Sym)) s.game ⟨h.control, h.statePair⟩ _
        ((mem_support_oracleSend_run_iff (auth P hMac) irl (pure ()) s.game true _).2
          ⟨r', hr', rfl⟩)
  obtain ⟨htcur, hkeys⟩ := h.control.send_prefix party
  cases hst : s.game.stateAt party with
  | keysUnsampled e a =>
      rw [sampledSend_eq_keygen hMac irl s party hst, support_map] at hw
      obtain ⟨⟨⟨pk, sk⟩, rand₀⟩, hkr, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      have hkg : (pk, sk) ∈ support P.kem.keygen := by
        rw [keygen_eq_map irl, support_map]
        exact ⟨_, hkr, rfl⟩
      have hr : keygenStep P hMac e a pk sk ∈
          support (send P (auth P hMac) (s.game.stateAt party)) := by
        rw [hst, mem_support_send_iff]
        exact .keygen e a pk sk hkg
      rw [hst] at htcur hkeys
      simp only [State.epoch] at htcur hkeys
      have hflag : (sendUpdate s.game party (keygenStep P hMac e a pk sk)).correct = true := by
        rw [sendUpdate_correct]
        simp only [keygenStep, Bool.and_eq_true]
        exact ⟨⟨h.correct, decide_eq_true htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
      have hsucc := sendUpdate_eq_successor_of_correct s.game party _ h.correct hflag
      have hCP := hCPgen _ hr
      rw [hsucc] at hCP ⊢
      refine ⟨RepairInv.setFlags
        (send_keysUnsampled_transcript (auth P hMac) h party hst pk sk hCP) _ _, fun hg _ => ?_⟩
      have hc0 : (s.transcript e).encaps1 = none := by
        have hL := h.local _ party
        rw [hst] at hL
        exact hL.2.2
      intro e' pk' sk' es ct1 key hk hc
      by_cases he : e' = e
      · subst e'
        simp [Function.update_self, hc0] at hc
      · rw [Function.update_of_ne he] at hk hc
        exact hg e' pk' sk' es ct1 key hk hc
  | headerReceived e a hdr dec =>
      rw [sampledSend_eq_encaps1 hMac irl s party hst, support_map] at hw
      obtain ⟨⟨⟨es, ct1, k⟩, rand₀⟩, hkr, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      have hek : (es, ct1, k) ∈ support (P.inc.encaps1 hdr) := by
        rw [encaps1_eq_map irl, support_map]
        exact ⟨_, hkr, rfl⟩
      have hr : encaps1Step P hMac e a hdr dec es ct1 k ∈
          support (send P (auth P hMac) (s.game.stateAt party)) := by
        rw [hst, mem_support_send_iff]
        exact .encaps1 e a hdr dec es ct1 k hek
      obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ := peer_keysSampled_of_headerReceived _ h party hst
      rw [hst] at htcur hkeys
      simp only [State.epoch] at htcur hkeys
      have hnone : ∀ who, s.game.keysAt who e = none := by
        intro who
        have hprefix := h.control.epochKnowledge.keyPrefix.keys who e
        by_contra hne
        obtain ⟨hpos', hbound⟩ := hprefix.1 hne
        rcases Bool.eq_or_eq_not who party with rfl | rfl
        · rw [hst] at hbound
          simp only [State.completedEpoch, State.epoch] at hbound
          omega
        · rw [hpeer] at hbound
          simp only [State.completedEpoch, State.epoch] at hbound
          omega
      have hflag : (sendUpdate s.game party (encaps1Step P hMac e a hdr dec es ct1 k)).correct =
          true := by
        rw [sendUpdate_correct]
        simp only [encaps1Step, Bool.and_eq_true]
        exact ⟨⟨⟨⟨h.correct, decide_eq_true htcur⟩, by simp [hnone]⟩, by simp [hnone]⟩,
          SCKAScheme.knownPrefix_update_some (SCKAScheme.knownPrefix_eq_true hkeys) e _⟩
      have hsucc := sendUpdate_eq_successor_of_correct s.game party _ h.correct hflag
      have hCP := hCPgen _ hr
      rw [hsucc] at hCP ⊢
      refine ⟨RepairInv.setFlags
        (send_headerReceived_transcript (auth P hMac) h party hst es ct1 k hCP) _ _,
        fun hg hbad => ?_⟩
      simp only [encaps1Bad, hkpT, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not] at hbad
      obtain ⟨-, hdk⟩ := hbad
      intro e' pk' sk' es' ct1' key' hk hc
      by_cases he : e' = e
      · subst e'
        simp only [Function.update_self] at hk hc
        rw [hkpT] at hk
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk)
        obtain ⟨rfl, rfl, rfl⟩ : es = es' ∧ ct1 = ct1' ∧ k = key' := by simpa using hc
        exact hdk
      · rw [Function.update_of_ne he] at hk hc
        exact hg e' pk' sk' es' ct1' key' hk hc
  | _ =>
      have hsteady : (s.game.stateAt party).SendsNoSample := by rw [hst]; trivial
      rw [sampledSend_of_noSample hMac irl s party (by simp [hst]) (by simp [hst]),
        support_map] at hw
      obtain ⟨out, hout, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨hrEq, -⟩, hTEq, hBEq⟩ := heq
      rw [hrEq] at hout
      subst T'
      subst bad'
      have hr : r ∈ support (send P (auth P hMac) (s.game.stateAt party)) := hout
      have hedge := (mem_support_send_iff (auth P hMac)).mp hr
      have hkey : r.outputKey = none := hedge.outputKey_eq_none fun e a hdr dec h' => by
        rw [h'] at hsteady
        exact hsteady
      have hflag : (sendUpdate s.game party r).correct = true := by
        rw [sendUpdate_correct, hkey, hedge.sendingEpoch_eq]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨h.correct, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
      have hsucc := sendUpdate_eq_successor_of_correct s.game party _ h.correct hflag
      have hCP := hCPgen _ hr
      rw [hsucc] at hCP ⊢
      exact ⟨RepairInv.setFlags
        (send_existing_transcript (auth P hMac) h party hr hsteady hCP) _ _, fun hg _ => hg⟩

end MLKEMBraid.NoAuth
