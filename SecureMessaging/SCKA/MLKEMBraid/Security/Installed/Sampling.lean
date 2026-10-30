/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Trace
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Stopping
import ToVCVio.OracleComp.QueryTracking.OneUseSampling
import VCVio.ProgramLogic.Relational.Quantitative
import ToVCVio.OracleComp.EvalDist

/-!
# Sampling the key pair and the first-stage encapsulation once

The key pair and the first-stage encapsulation of epoch `e` can be sampled lazily, when a send
needs them, or once before the run and then installed. This module first compares the two kinds
of send, including refused leaking sends and stopping at the exposure of `e`. The comparison of
whole runs then follows from the one-use installation result of ToVCVio, because a query keeps
the records and the first use of a sample records it.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

section Installs

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- The ordinary key-generation send of `e`, lazily. -/
theorem plain_keygen_on (e : ℕ) (party : Bool) (s : TraceState P) {a0 : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a0) :
    (tracePlainAt P hMac irl e none none party ()).run s =ᵈ
        P.kem.keygen >>= fun x => (tracePlainAt P hMac irl e (some x) none party ()).run s := by
  have hL : (tracePlainAt P hMac irl e none none party ()).run s =
      (fun y : (P.PK × P.SK) × irl.KeygenRand =>
        (some (e - 1, none, (keygenStep P hMac e a0 y.1.1 y.1.2).msg),
          keygenState hMac s party false e a0 y.1)) <$> irl.keygenRleak := by
    simp only [tracePlainAt, StateT.run_map, traceSendAt_none,
      traceSend_keygen_run hMac irl false hst, Functor.map_map]
    congr 1
  have hI : ∀ x, (tracePlainAt P hMac irl e (some x) none party ()).run s =
      pure (some (e - 1, none, (keygenStep P hMac e a0 x.1 x.2).msg),
        keygenState hMac s party false e a0 x) := by
    intro x
    simp only [tracePlainAt, StateT.run_map, traceSendAt_keygen_run hMac irl false hst x none]
    simp
  rw [hL, keygen_eq_map irl, bind_map_left]
  simp only [hI, map_eq_bind_pure_comp]
  rfl

/-- The leaking key-generation send of `e`, lazily, when it is not refused. -/
theorem leak_keygen_on (e : ℕ) (party : Bool) (s : TraceState P) {a0 : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a0)
    (hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true) :
    ((fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
        (traceLeakAt P hMac irl e none none party ()).run s) =ᵈ
            P.kem.keygen >>=
                fun x => (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
        (traceLeakAt P hMac irl e (some x) none party ()).run s := by
  have hL : (traceLeakAt P hMac irl e none none party ()).run s =
      (fun y : (P.PK × P.SK) × irl.KeygenRand =>
        (some (e - 1, none, (keygenStep P hMac e a0 y.1.1 y.1.2).msg, SendRand.keygen y.2),
          keygenState hMac s party true e a0 y.1)) <$> irl.keygenRleak := by
    change (traceSendAt P hMac irl e none none party true).run s = _
    rw [traceSendAt_none, traceSend_keygen_run hMac irl true hst]
    congr 1
    funext y
    rw [ite_eq_right hc]
  have hstop : ∀ x, targetStop e (keygenState hMac s party true e a0 x) = true := fun x => by
    simp [targetStop, keygenState]
  have hR : ∀ x, (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e (some x) none party ()).run s =
      pure (none, keygenState hMac s party true e a0 x) := by
    intro x
    change (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceSendAt P hMac irl e (some x) none party true).run s = _
    rw [traceSendAt_keygen_run hMac irl true hst x none, ite_eq_right hc, map_pure]
    simp only [hstop, ↓reduceIte]
  have hLHS : (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e none none party ()).run s =
      (fun y : (P.PK × P.SK) × irl.KeygenRand =>
        (none, keygenState hMac s party true e a0 y.1)) <$> irl.keygenRleak := by
    rw [hL, Functor.map_map]
    simp only [hstop, ↓reduceIte]
  rw [hLHS, keygen_eq_map irl, bind_map_left]
  simp only [hR, map_eq_bind_pure_comp]
  rfl

/-- A refused leaking key-generation send of `e` does not depend on the installed key pair. -/
theorem leak_keygen_refused (e : ℕ) (party : Bool) (s : TraceState P) {a0 : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a0)
    (hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true) (x : P.PK × P.SK) :
    (traceLeakAt P hMac irl e (some x) none party ()).run s =ᵈ
        (traceLeakAt P hMac irl e none none party ()).run s := by
  have h1 : (traceLeakAt P hMac irl e (some x) none party ()).run s = pure (none, s) := by
    change (traceSendAt P hMac irl e (some x) none party true).run s = _
    rw [traceSendAt_keygen_run hMac irl true hst x none, ite_eq_left hc]
  have h2 : (traceLeakAt P hMac irl e none none party ()).run s =
      (fun _ => (none, s)) <$> irl.keygenRleak := by
    change (traceSendAt P hMac irl e none none party true).run s = _
    rw [traceSendAt_none, traceSend_keygen_run hMac irl true hst]
    congr 1
    funext y
    rw [ite_eq_left hc]
  rw [h1, h2, map_eq_bind_pure_comp]
  exact (EvalDistEq.bind_const _ _).symm

/-- The ordinary first-stage encapsulation send of `e`, lazily. -/
theorem plain_encaps1_on (e : ℕ) (kp : Option (P.PK × P.SK)) (party : Bool) (s : TraceState P)
    {a0 : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a0 hdr dec) :
    (tracePlainAt P hMac irl e kp none party ()).run s =ᵈ
        P.inc.encaps1 hdr >>= fun c => (tracePlainAt P hMac irl e kp (some c) party ()).run s := by
  have hL : (tracePlainAt P hMac irl e kp none party ()).run s =
      (fun y : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        (some (e - 1, some e, (encaps1Step P hMac e a0 hdr dec y.1.1 y.1.2.1 y.1.2.2).msg),
          encaps1State hMac s party false e a0 hdr dec y.1)) <$> irl.encaps1Rleak hdr := by
    simp only [tracePlainAt, StateT.run_map, traceSendAt_hdr_lazy hMac irl e kp party false s hst,
      traceSend_encaps1_run hMac irl false hst, Functor.map_map]
    congr 1
  have hI : ∀ c, (tracePlainAt P hMac irl e kp (some c) party ()).run s =
      pure (some (e - 1, some e, (encaps1Step P hMac e a0 hdr dec c.1 c.2.1 c.2.2).msg),
        encaps1State hMac s party false e a0 hdr dec c) := by
    intro c
    simp only [tracePlainAt, StateT.run_map, traceSendAt_encaps1_run hMac irl false hst kp c]
    simp
  rw [hL, encaps1_eq_map irl, bind_map_left]
  simp only [hI, map_eq_bind_pure_comp]
  rfl

/-- The leaking first-stage encapsulation send of `e`, lazily, when it is not refused. -/
theorem leak_encaps1_on (e : ℕ) (kp : Option (P.PK × P.SK)) (party : Bool) (s : TraceState P)
    {a0 : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a0 hdr dec)
    (hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true) :
    ((fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
        (traceLeakAt P hMac irl e kp none party ()).run s) =ᵈ
            P.inc.encaps1 hdr >>= fun c => (fun w => (if targetStop e w.2 then none else some w.1,
        w.2)) <$> (traceLeakAt P hMac irl e kp (some c) party ()).run s := by
  have hL : (traceLeakAt P hMac irl e kp none party ()).run s =
      (fun y : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        (some (e - 1, some e, (encaps1Step P hMac e a0 hdr dec y.1.1 y.1.2.1 y.1.2.2).msg,
          SendRand.encaps1 y.2), encaps1State hMac s party true e a0 hdr dec y.1)) <$>
        irl.encaps1Rleak hdr := by
    change (traceSendAt P hMac irl e kp none party true).run s = _
    rw [traceSendAt_hdr_lazy hMac irl e kp party true s hst,
      traceSend_encaps1_run hMac irl true hst]
    congr 1
    funext y
    rw [ite_eq_right hc]
  have hstop : ∀ c, targetStop e (encaps1State hMac s party true e a0 hdr dec c) = true :=
    fun c => by simp [targetStop, encaps1State]
  have hR : ∀ c, (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e kp (some c) party ()).run s =
      pure (none, encaps1State hMac s party true e a0 hdr dec c) := by
    intro c
    change (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceSendAt P hMac irl e kp (some c) party true).run s = _
    rw [traceSendAt_encaps1_run hMac irl true hst kp c, ite_eq_right hc, map_pure]
    simp only [hstop, ↓reduceIte]
  have hLHS : (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e kp none party ()).run s =
      (fun y : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        (none, encaps1State hMac s party true e a0 hdr dec y.1)) <$> irl.encaps1Rleak hdr := by
    rw [hL, Functor.map_map]
    simp only [hstop, ↓reduceIte]
  rw [hLHS, encaps1_eq_map irl, bind_map_left]
  simp only [hR, map_eq_bind_pure_comp]
  rfl

/-- A refused leaking first-stage encapsulation send of `e` does not depend on the installed
sample. -/
theorem leak_encaps1_refused (e : ℕ) (kp : Option (P.PK × P.SK)) (party : Bool)
    (s : TraceState P) {a0 : Unit} {hdr : P.inc.PKheader}
    {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a0 hdr dec)
    (hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true)
    (c : P.inc.St × P.inc.C₁ × P.K) :
    (traceLeakAt P hMac irl e kp (some c) party ()).run s =ᵈ
        (traceLeakAt P hMac irl e kp none party ()).run s := by
  have h1 : (traceLeakAt P hMac irl e kp (some c) party ()).run s = pure (none, s) := by
    change (traceSendAt P hMac irl e kp (some c) party true).run s = _
    rw [traceSendAt_encaps1_run hMac irl true hst kp c, ite_eq_left hc]
  have h2 : (traceLeakAt P hMac irl e kp none party ()).run s =
      (fun _ => (none, s)) <$> irl.encaps1Rleak hdr := by
    change (traceSendAt P hMac irl e kp none party true).run s = _
    rw [traceSendAt_hdr_lazy hMac irl e kp party true s hst,
      traceSend_encaps1_run hMac irl true hst]
    congr 1
    funext y
    rw [ite_eq_left hc]
  rw [h1, h2, map_eq_bind_pure_comp]
  exact (EvalDistEq.bind_const _ _).symm

end Installs

section Dispatch

variable [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
  [DecidableEq P.Sym] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- The queries other than sends ignore the installed samples. -/
theorem traceImplAt_offSend (e : ℕ) (kp kp' : Option (P.PK × P.SK))
    (ec ec' : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), NonSend q →
      ((stopOnState (traceImplAt P hMac irl e kp ec xo m) (targetStop e) q).run).run s =ᵈ
          ((stopOnState (traceImplAt P hMac irl e kp' ec' xo m) (targetStop e) q).run).run s
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, _ =>
      OracleComp.stopped_congr _ _ s (by
        change (traceUnif P t).run s =ᵈ (traceUnif P t).run s
        rfl)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, _ =>
      OracleComp.stopped_congr _ _ s (by
        change (traceReceive P hMac irl true true n).run s =ᵈ
            (traceReceive P hMac irl true true n).run s
        rfl)
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, _ =>
      OracleComp.stopped_congr _ _ s (by
        change (traceReceive P hMac irl true false n).run s =ᵈ
            (traceReceive P hMac irl true false n).run s
        rfl)
  | .inl (.inl (.inr t)), s, _ =>
      OracleComp.stopped_congr _ _ s (by
        change (traceChallengeAt P m e xo t).run s =ᵈ (traceChallengeAt P m e xo t).run s
        rfl)
  | .inl (.inr t), s, _ =>
      OracleComp.stopped_congr _ _ s (by
        change (traceCorruptA P t).run s =ᵈ (traceCorruptA P t).run s
        rfl)
  | .inr t, s, _ =>
      OracleComp.stopped_congr _ _ s (by
        change (traceCorruptB P t).run s =ᵈ (traceCorruptB P t).run s
        rfl)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))), _, h => False.elim h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))), _, h => False.elim h
  | .inl (.inl (.inl (.inl (.inr _)))), _, h => False.elim h
  | .inl (.inl (.inl (.inr _))), _, h => False.elim h

/-- Off a hit, installing a key pair changes no query. -/
theorem keygen_off (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isKeygenAt e) e q s = false →
      ∀ x, ((stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) q).run).run
          s =ᵈ ((stopOnState (traceImplAt P hMac irl e none none xo m) (targetStop e) q).run).run s
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, x => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      change (tracePlainAt P hMac irl e (some x) none true ()).run s =ᵈ
          (tracePlainAt P hMac irl e none none true ()).run s
      simp only [tracePlainAt, StateT.run_map,
          traceSendAt_kp_off hMac irl e x true false s h, EvalDistEq.refl]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, x => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      change (tracePlainAt P hMac irl e (some x) none false ()).run s =ᵈ
          (tracePlainAt P hMac irl e none none false ()).run s
      simp only [tracePlainAt, StateT.run_map,
          traceSendAt_kp_off hMac irl e x false false s h, EvalDistEq.refl]
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, x => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      by_cases hk : isKeygenAt e (s.game.stateAt true) = true
      · obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_keygen_refused hMac irl e true s hst hc x
      · change (traceSendAt P hMac irl e (some x) none true true).run s =ᵈ
          (traceSendAt P hMac irl e none none true true).run s
        rw [traceSendAt_kp_off hMac irl e x true true s (by simpa using hk)]
  | .inl (.inl (.inl (.inr t))), s, h, x => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      by_cases hk : isKeygenAt e (s.game.stateAt false) = true
      · obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_keygen_refused hMac irl e false s hst hc x
      · change (traceSendAt P hMac irl e (some x) none false true).run s =ᵈ
          (traceSendAt P hMac irl e none none false true).run s
        rw [traceSendAt_kp_off hMac irl e x false true s (by simpa using hk)]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inr t)), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inr t), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inr t, s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial

/-- At a hit, the lazy key generation is the installed one with a sampled key pair. -/
theorem keygen_on (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isKeygenAt e) e q s = true →
      ((stopOnState (traceImplAt P hMac irl e none none xo m) (targetStop e) q).run).run s =ᵈ
          P.kem.keygen >>= fun x =>
          ((stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) q).run).run
            s
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h => by
      have h' : isKeygenAt e (s.game.stateAt true) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      cases t
      exact OracleComp.stopped_bind _ _ _ s (plain_keygen_on hMac irl e true s hst)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h => by
      have h' : isKeygenAt e (s.game.stateAt false) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      cases t
      exact OracleComp.stopped_bind _ _ _ s (plain_keygen_on hMac irl e false s hst)
  | .inl (.inl (.inl (.inl (.inr t)))), s, h => by
      have h' : (isKeygenAt e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      cases t
      simp only [OracleComp.stopOnState_run_eq_map]
      exact leak_keygen_on hMac irl e true s hst hc
  | .inl (.inl (.inl (.inr t))), s, h => by
      have h' : (isKeygenAt e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      cases t
      simp only [OracleComp.stopOnState_run_eq_map]
      exact leak_keygen_on hMac irl e false s hst hc
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, h => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, h => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, h => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, h => by simp [sendHit] at h
  | .inl (.inr _), _, h => by simp [sendHit] at h
  | .inr _, _, h => by simp [sendHit] at h

/-- Off a hit, installing a first-stage sample changes no query. -/
theorem encaps1_off (e : ℕ) (kp : Option (P.PK × P.SK)) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isEncaps1At e) e q s = false →
      ∀ c, ((stopOnState (traceImplAt P hMac irl e kp (some c) xo m) (targetStop e) q).run).run
          s =ᵈ ((stopOnState (traceImplAt P hMac irl e kp none xo m) (targetStop e) q).run).run s
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, c => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      change (tracePlainAt P hMac irl e kp (some c) true ()).run s =ᵈ
          (tracePlainAt P hMac irl e kp none true ()).run s
      simp only [tracePlainAt, StateT.run_map,
          traceSendAt_ec_off hMac irl e kp c true false s h, EvalDistEq.refl]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, c => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      change (tracePlainAt P hMac irl e kp (some c) false ()).run s =ᵈ
          (tracePlainAt P hMac irl e kp none false ()).run s
      simp only [tracePlainAt, StateT.run_map,
          traceSendAt_ec_off hMac irl e kp c false false s h, EvalDistEq.refl]
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, c => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      by_cases hk : isEncaps1At e (s.game.stateAt true) = true
      · obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_encaps1_refused hMac irl e kp true s hst hc c
      · change (traceSendAt P hMac irl e kp (some c) true true).run s =ᵈ
          (traceSendAt P hMac irl e kp none true true).run s
        rw [traceSendAt_ec_off hMac irl e kp c true true s (by simpa using hk)]
  | .inl (.inl (.inl (.inr t))), s, h, c => by
      cases t
      refine OracleComp.stopped_congr _ _ s ?_
      by_cases hk : isEncaps1At e (s.game.stateAt false) = true
      · obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_encaps1_refused hMac irl e kp false s hst hc c
      · change (traceSendAt P hMac irl e kp (some c) false true).run s =ᵈ
          (traceSendAt P hMac irl e kp none false true).run s
        rw [traceSendAt_ec_off hMac irl e kp c false true s (by simpa using hk)]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inr t)), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inr t), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inr t, s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial

/-- At a hit, the lazy first-stage encapsulation is the installed one with a sampled triple. -/
theorem encaps1_on (e : ℕ) (x : P.PK × P.SK) (ec' : Option (P.inc.St × P.inc.C₁ × P.K))
    (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), InstInv hMac e (some x) ec' s →
      sendHit (isEncaps1At e) e q s = true →
      ((stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) q).run).run
          s =ᵈ P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
          ((stopOnState (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e)
            q).run).run s
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, hs, h => by
      have h' : isEncaps1At e (s.game.stateAt true) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      rw [← hs.header hMac hst]
      cases t
      exact OracleComp.stopped_bind _ _ _ s (plain_encaps1_on hMac irl e (some x) true s hst)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, hs, h => by
      have h' : isEncaps1At e (s.game.stateAt false) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      rw [← hs.header hMac hst]
      cases t
      exact OracleComp.stopped_bind _ _ _ s (plain_encaps1_on hMac irl e (some x) false s hst)
  | .inl (.inl (.inl (.inl (.inr t)))), s, hs, h => by
      have h' : (isEncaps1At e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      rw [← hs.header hMac hst]
      cases t
      simp only [OracleComp.stopOnState_run_eq_map]
      exact leak_encaps1_on hMac irl e (some x) true s hst hc
  | .inl (.inl (.inl (.inr t))), s, hs, h => by
      have h' : (isEncaps1At e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      rw [← hs.header hMac hst]
      cases t
      simp only [OracleComp.stopOnState_run_eq_map]
      exact leak_encaps1_on hMac irl e (some x) false s hst hc
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, _, h => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, _, h => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, _, h => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, _, h => by simp [sendHit] at h
  | .inl (.inr _), _, _, h => by simp [sendHit] at h
  | .inr _, _, _, h => by simp [sendHit] at h

/-- **Installing the key pair of `e`.** Sampling the key pair of `e` once before the stopped run
and installing it is the same as sampling it at the key generation of `e`. -/
theorem stoppedRun_installKeygen (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (A : Adversary P irl) (s : TraceState P) (hs : TraceInv hMac true s) :
    Pr{let y ← do
        let x ← P.kem.keygen
        stoppedRun (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) A s}[y = true] =
      Pr{let x ← stoppedRun (traceImplAt P hMac irl e none none xo m) (targetStop e) A s}[x = true]
          :=
  OracleComp.optionRun_install P.kem.keygen
    (fun x => stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e))
    (stopOnState (traceImplAt P hMac irl e none none xo m) (targetStop e))
    (TraceInv hMac true) (fun s => (s.transcript e).keypair ≠ none) (sendHit (isKeygenAt e) e)
    (fun x hx q s hs z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
      exact traceImplAt_traceInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e
        (some x) none xo m (fun y h => by cases h; exact hx) q s hs
        (fun _ _ _ _ _ h => by cases h) w hw)
    (fun x _ q s _ hu z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
      exact (traceImplAt_transcriptStep hMac irl e (some x) none xo m q s w hw).keypair_ne hu)
    (fun q s hs hu => sendHit_false (fun p => isKeygenAt_false hMac hs hu p) q)
    (fun x _ q s _ hh z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
      exact keygen_hit_records hMac irl e x xo m q s hh w hw)
    (fun q s _ hh x _ => keygen_off hMac irl e xo m q s hh x)
    (fun q s _ hh => keygen_on hMac irl e xo m q s hh)
    A s hs

/-- **Installing the first-stage sample of `e`.** With the key pair of `e` installed, sampling the
first-stage encapsulation of `e` once before the stopped run and installing it is the same as
sampling it at the first-stage encapsulation of `e`. -/
theorem stoppedRun_installEncaps1 (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (x : P.PK × P.SK)
    (hx : x ∈ support P.kem.keygen) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (A : Adversary P irl) (s : TraceState P) (hs : InstInv hMac e (some x) none s) :
    Pr{let y ← do
        let c ← P.inc.encaps1 (P.inc.toHeader x.1)
        stoppedRun (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e) A s}[y = true] =
      Pr{let y ← stoppedRun (traceImplAt P hMac irl e (some x) none xo m) (targetStop
          e) A s}[y = true] :=
  OracleComp.optionRun_install (P.inc.encaps1 (P.inc.toHeader x.1))
    (fun c => stopOnState (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e))
    (stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e))
    (InstInv hMac e (some x) none) (fun s => (s.transcript e).encaps1 ≠ none)
    (sendHit (isEncaps1At e) e)
    (fun c hc q s hs z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
      exact traceImplAt_instInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e x
        (some c) none xo m hx (fun c' h => by cases h; exact hc) (Or.inl rfl) q s hs w hw)
    (fun c _ q s _ hu z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
      exact (traceImplAt_transcriptStep hMac irl e (some x) (some c) xo m q s w hw).encaps1_ne hu)
    (fun q s hs hu => sendHit_false (fun p => isEncaps1At_false hMac hs.1 hu p) q)
    (fun c _ q s _ hh z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
      exact encaps1_hit_records hMac irl e (some x) c xo m q s hh w hw)
    (fun q s _ hh c _ => encaps1_off hMac irl e (some x) xo m q s hh c)
    (fun q s hs hh => encaps1_on hMac irl e x none xo m q s hs hh)
    A s hs

/-- **Installing both samples of `e`.** Sampling the key pair and the first-stage sample of `e`
once before the stopped run from the initial state is the same as sampling them at their sends. -/
theorem stoppedRun_installBoth (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (A : Adversary P irl) :
    Pr{let y ← do
        let x ← P.kem.keygen
        let c ← P.inc.encaps1 (P.inc.toHeader x.1)
        stoppedRun (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e) A
          (initTrace P hMac)}[y = true] =
      Pr{let x ← (stoppedRun (traceImplAt P hMac irl e none none xo m) (targetStop e) A
        (initTrace P hMac))}[x = true] :=
  (prEvent_bind_congr_of_support _ _ _ fun x hx =>
    stoppedRun_installEncaps1 hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e x hx xo
      m A (initTrace P hMac)
      ⟨traceInv_init hMac true, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩).trans
    (stoppedRun_installKeygen hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e xo m A
      (initTrace P hMac) (traceInv_init hMac true))

end Dispatch

end MLKEMBraid.NoAuth
