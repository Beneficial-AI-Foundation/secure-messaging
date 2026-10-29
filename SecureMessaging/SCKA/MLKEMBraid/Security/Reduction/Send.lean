/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.ProjectionBasic
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Basic

/-!
# Joint send projections of the masked simulator

Target key generation and first-stage encapsulation use the supplied challenge. Other sends
preserve the ordinary projection, and masked sends retain their observable chunks. The equalities
compare entire response/state distributions before deriving stopped-query comparisons.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}
variable (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) [DecidableEq P.EpochKey]

/-- The key-generation send of `e` agrees. -/
theorem sendStep_keygen (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (sk : P.SK)
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled e a) :
    (simSend P hMac irl e ch party leaking).run (simOf e v s) =ᵈ Prod.map id (simOf e v) <$>
        (traceSendAt P hMac irl e (some (ch.pk, sk)) ec party leaking).run s := by
  rw [traceSendAt_keygen_run hMac irl leaking hst (ch.pk, sk) ec]
  have hS : (simOf e v s).game.stateAt party = .inl (.keysUnsampled e a) := by
    rw [simOf_game, simGameOf_stateAt, hst]
    rfl
  refine ToVCVio.evalDistEq_of_eq ?_
  change simSend P hMac irl e ch party leaking (simOf e v s) = _
  simp only [simSend, hS, targetSend, ↓reduceIte]
  by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
  · have hc' : (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [ite_eq_left hc', ite_eq_left hc, map_pure]
    rfl
  · have hc' : ¬ (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [ite_eq_right hc', ite_eq_right hc, map_pure]
    congr 1
    simp only [Prod.map, id, simOf, simGameOf_sendUpdate, keygenState, keygenStep_eq,
      eraseAt_update_self, relabelKey, Option.map_none, maskState, ↓reduceIte, simGameOf_exposed]

/-- The first-stage encapsulation send of `e` agrees. -/
theorem sendStep_encaps1 (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (kp : Option (P.PK × P.SK)) (es : P.inc.St) (k : P.K) (party leaking : Bool)
    (s : TraceState P) {a : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) :
    (simSend P hMac irl e ch party leaking).run (simOf e v s) =ᵈ Prod.map id (simOf e v) <$>
        (traceSendAt P hMac irl e kp (some (es, ch.ct1, k)) party leaking).run s := by
  rw [traceSendAt_encaps1_run hMac irl leaking hst kp (es, ch.ct1, k)]
  have hS : (simOf e v s).game.stateAt party = .inl (.headerReceived e a hdr dec) := by
    rw [simOf_game, simGameOf_stateAt, hst]
    rfl
  refine ToVCVio.evalDistEq_of_eq ?_
  change simSend P hMac irl e ch party leaking (simOf e v s) = _
  simp only [simSend, hS, targetSend, ↓reduceIte, hv]
  by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
  · have hc' : (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [ite_eq_left hc', ite_eq_left hc, map_pure]
    rfl
  · have hc' : ¬ (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [ite_eq_right hc', ite_eq_right hc, map_pure]
    congr 1
    simp only [Prod.map, id, simOf, simGameOf_sendUpdate, encaps1State, encaps1Step_eq,
      eraseAt_update_self, relabelKey, Option.map_some, maskState, ↓reduceIte, simGameOf_exposed]

/-- A send of an ordinary state that samples nothing installed agrees. -/
theorem sendStep_ghost (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    (hm : maskState e (s.game.stateAt party) = .inl (s.game.stateAt party))
    (hT : targetSend P hMac e ch (P.kdfOK ch.key e) (s.game.stateAt party) = none) :
    (simSend P hMac irl e ch party leaking).run (simOf e v s) =ᵈ
        Prod.map id (simOf e v) <$> (traceSendAt P hMac irl e kp ec party leaking).run s := by
  have h1 : ∀ a, s.game.stateAt party ≠ .keysUnsampled e a := fun a h => by
    rw [h] at hT
    simp [targetSend] at hT
  have h2 : ∀ a hdr dec, s.game.stateAt party ≠ .headerReceived e a hdr dec :=
    fun a hdr dec h => by
      rw [h] at hT
      simp [targetSend] at hT
  have hI := installedSample_eq_none hMac e kp ec s party h1 h2
  have hTr : (traceSendAt P hMac irl e kp ec party leaking).run s =
      traceSend P hMac irl party leaking s := by
    change traceSendAt P hMac irl e kp ec party leaking s = _
    simp only [traceSendAt, hI]
  have hS : (simGameOf e v s.game).stateAt party = .inl (s.game.stateAt party) := by
    rw [simGameOf_stateAt, hm]
  rw [hTr]
  change simSend P hMac irl e ch party leaking (simOf e v s) =ᵈ _
  simp only [simSend, simOf_game, hS, hT, simOf_transcript,
    ghostSample_eq hMac irl e s party h1 h2, traceSend, Functor.map_map]
  apply evalDist_map_congr_support
  intro w hw
  have hedge : SendEdge (auth P hMac) (s.game.stateAt party) w.1.1 := by
    refine (mem_support_send_iff (auth P hMac)).mp ?_
    have h1' : w.1 ∈ support
        (MLKEMBraid.sendRleak P irl (auth P hMac) (s.game.stateAt party)) := by
      rw [← sampledSend_erase P hMac irl s party, support_map]
      exact ⟨w, hw, rfl⟩
    rw [send_eq_map_sendRleak P irl, support_map]
    exact ⟨w.1, h1', rfl⟩
  obtain ⟨hmw, hkw⟩ := ghost_succ hMac (v := v) hedge hm hT
  simp only [apply_ite (Prod.map id (simOf e v))]
  refine if_congr Iff.rfl rfl ?_
  simp only [Prod.map, id, simOf, simGameOf_sendUpdate, hmw, hkw, simGameOf_exposed]

/-- Every send agrees, with the challenge key pair and first-stage sample installed. -/
theorem sendStep (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (sk : P.SK) (es : P.inc.St) (k : P.K) (party leaking : Bool) (s : TraceState P) :
    (simSend P hMac irl e ch party leaking).run (simOf e v s) =ᵈ Prod.map id (simOf e v) <$>
        (traceSendAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) party leaking).run
          s := by
  rcases hm : maskState e (s.game.stateAt party) with st' | m
  · obtain rfl := maskState_eq_inl hm
    cases hT : targetSend P hMac e ch (P.kdfOK ch.key e) (s.game.stateAt party) with
    | none => exact sendStep_ghost hMac irl e v ch _ _ party leaking s hm hT
    | some x =>
        cases hst : s.game.stateAt party with
        | keysUnsampled t a =>
            by_cases ht : t = e
            · subst ht
              exact sendStep_keygen hMac irl t v ch sk _ party leaking s hst
            · rw [hst] at hT
              simp [targetSend, ht] at hT
        | headerReceived t a hdr dec =>
            by_cases ht : t = e
            · subst ht
              exact sendStep_encaps1 hMac irl t v ch hv _ es k party leaking s hst
            · rw [hst] at hT
              simp [targetSend, ht] at hT
        | _ =>
            rw [hst] at hT
            simp [targetSend] at hT
  · exact sendStep_masked hMac irl e v ch _ _ party leaking s hm

/-- The ordinary send query agrees. -/
theorem plainStep (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (sk : P.SK) (es : P.inc.St) (k : P.K) (party : Bool) (t : Unit) (s : TraceState P) :
    StepSim e v ((simPlain P hMac irl e ch party t).run (simOf e v s))
      ((tracePlainAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) party t).run s) :=
  StepSim.of_eq (by
    simp only [simPlain, tracePlainAt, StateT.run_map]
    exact exact_mapAnswer _ (sendStep hMac irl e v ch hv sk es k party false s))

/-- The leaking send query agrees. -/
theorem leakStep (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (sk : P.SK) (es : P.inc.St) (k : P.K) (party : Bool) (t : Unit) (s : TraceState P) :
    StepSim e v ((simLeak P hMac irl e ch party t).run (simOf e v s))
      ((traceLeakAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) party t).run s) :=
  StepSim.of_eq (sendStep hMac irl e v ch hv sk es k party true s)

end MLKEMBraid.NoAuth
