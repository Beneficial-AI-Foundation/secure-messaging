/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Basic
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Stopping
import SecureMessaging.SCKA.MLKEMBraid.Security.Trace
import ToVCVio.OracleComp.SimSemantics.StateT.QueryImplAdd

/-!
# Installed transcript preservation

An installed query records at most one sample, and at the selected epoch records the supplied
sample. The repaired trace invariant and these recording facts give the invariant used by
once-only key-generation and first-stage installation arguments.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

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

section TargetSends

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A non-refused installed key-generation send of `e` records the installed key pair. -/
theorem traceSendAt_keygen_records {s : TraceState P} {party leaking : Bool} {e : ℕ} {a : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a) (x : P.PK × P.SK)
    (hc : ¬ (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSendAt P hMac irl e (some x) none party leaking).run s)) :
    (z.2.transcript e).keypair ≠ none := by
  rw [traceSendAt_keygen_run hMac irl leaking hst x none, ite_eq_right hc,
    mem_support_pure_iff] at hz
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
  rw [traceSendAt_encaps1_run hMac irl leaking hst kp c, ite_eq_right hc,
    mem_support_pure_iff] at hz
  rw [hz]
  simp [encaps1State]

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
      · rw [ite_eq_left hc, mem_support_pure_iff] at hz
        rw [hz]
        exact hs
      · rw [ite_eq_right hc, mem_support_pure_iff] at hz
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
          exact ⟨(x, rand), hrand, by simp only [ite_eq_right hc]⟩
        have hinv := traceSend_traceInv hMac irl party leaking true s hs hlazy
        exact hinv
    · rw [traceSendAt_encaps1_run hMac irl leaking hst kp c] at hz
      by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · rw [ite_eq_left hc, mem_support_pure_iff] at hz
        rw [hz]
        exact hs
      · rw [ite_eq_right hc, mem_support_pure_iff] at hz
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
          exact ⟨(c, rand), hrand, by simp only [ite_eq_right hc]⟩
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
      · rw [ite_eq_left hc, mem_support_pure_iff] at hz
        exact Or.inl (by rw [hz])
      · rw [ite_eq_right hc, mem_support_pure_iff] at hz
        rw [hz]
        exact Or.inr (Or.inl ⟨e, x, rfl, fun _ x0 h => Option.some.inj h⟩)
    · rw [traceSendAt_encaps1_run hMac irl leaking hst kp c] at hz
      by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
      · rw [ite_eq_left hc, mem_support_pure_iff] at hz
        exact Or.inl (by rw [hz])
      · rw [ite_eq_right hc, mem_support_pure_iff] at hz
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

/-- The installed trace invariant: repaired trace consistency, with selected records absent or
identical to the installed samples. -/
def InstInv (hMac : P.Mac = Unit) (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (s : TraceState P) : Prop :=
  TraceInv hMac true s ∧
    (∀ x, kp = some x → (s.transcript e).keypair = none ∨ (s.transcript e).keypair = some x) ∧
    (∀ c, ec = some c → (s.transcript e).encaps1 = none ∨ (s.transcript e).encaps1 = some c)

section InstInvLemmas

variable (hMac : P.Mac = Unit)

/-- Under `InstInv`, a first-stage encapsulation of `e` reads the installed header. -/
theorem InstInv.header {e : ℕ} {x : P.PK × P.SK} {ec : Option (P.inc.St × P.inc.C₁ × P.K)}
    {s : TraceState P} (hs : InstInv hMac e (some x) ec s) {party : Bool} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) : hdr = P.inc.toHeader x.1 := by
  have hl := (hs.1.1 (Or.inl rfl)).1.local party
  rw [hst] at hl
  obtain ⟨-, -, pk, sk, hkp', hhdr, -⟩ := hl
  rcases hs.2.1 x rfl with h0 | h0
  · rw [h0] at hkp'
    cases hkp'
  · rw [h0] at hkp'
    obtain rfl : x = (pk, sk) := Option.some.inj hkp'
    exact hhdr

/-- Under the repaired invariant, a recorded key pair of `e` excludes its key generation. -/
theorem isKeygenAt_false {s : TraceState P} (hs : TraceInv hMac true s) {e : ℕ}
    (hu : (s.transcript e).keypair ≠ none) (p : Bool) :
    isKeygenAt e (s.game.stateAt p) = false := by
  have hl := (hs.1 (Or.inl rfl)).1.local p
  cases hst : s.game.stateAt p with
  | keysUnsampled t a =>
      rw [hst] at hl
      obtain ⟨-, hk, -⟩ := hl
      simp only [isKeygenAt, decide_eq_false_iff_not]
      rintro rfl
      exact hu hk
  | _ => rfl

/-- Under the repaired invariant, a recorded first-stage sample of `e` excludes its first-stage
encapsulation. -/
theorem isEncaps1At_false {s : TraceState P} (hs : TraceInv hMac true s) {e : ℕ}
    (hu : (s.transcript e).encaps1 ≠ none) (p : Bool) :
    isEncaps1At e (s.game.stateAt p) = false := by
  have hl := (hs.1 (Or.inl rfl)).1.local p
  cases hst : s.game.stateAt p with
  | headerReceived t a hdr dec =>
      rw [hst] at hl
      obtain ⟨-, hk, -⟩ := hl
      simp only [isEncaps1At, decide_eq_false_iff_not]
      rintro rfl
      exact hu hk
  | _ => rfl

/-- An installed challenge keeps the trace invariant of the repaired game. -/
theorem traceChallengeAt_traceInv [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) (e : ℕ) (x : Option P.EpochKey) :
    QueryImpl.PreservesInv (traceChallengeAt P mode e x) (TraceInv hMac true) := by
  intro t s hs z hz
  rcases mem_support_traceChallengeAt hz with hz | ⟨hex, hz⟩
  · rw [hz]
    exact hs
  · rw [hz]
    refine ⟨fun _ => ⟨(hs.1 (Or.inl rfl)).1.setFlags _ _, fun h => absurd h (by decide)⟩, ?_⟩
    change s.game.exposed ∩ insert t s.game.challenged = ∅
    rw [Finset.inter_insert_of_notMem hex]
    exact hs.2

end InstInvLemmas

section Dispatch

variable [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
  [DecidableEq P.Sym] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- Every query records at most one sample, the installed one at `e`. -/
theorem traceImplAt_transcriptStep (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ q s z, z ∈ support ((traceImplAt P hMac irl e kp ec xo m q).run s) →
      TranscriptStep e kp ec s z.2 :=
  relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
    (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
      (fun t s z hz => by
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame
          (c := SCKAScheme.oracleUnif (State P Unit) (State P Unit) P.EpochKey (Message P.Sym)
            t) hz
        exact Or.inl rfl)
      (fun t s z hz => by
        obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
        exact traceSendAt_transcriptStep hMac irl e kp ec true false s hw))
      (fun t s z hz => by
        obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
        exact traceSendAt_transcriptStep hMac irl e kp ec false false s hw))
      (fun n s z hz => by
        rw [traceReceive_run] at hz
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
        exact Or.inl rfl))
      (fun n s z hz => by
        rw [traceReceive_run] at hz
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
        exact Or.inl rfl))
      (fun t s z hz => traceSendAt_transcriptStep hMac irl e kp ec true true s hz))
      (fun t s z hz => traceSendAt_transcriptStep hMac irl e kp ec false true s hz))
      (fun t s z hz => by
        rcases mem_support_traceChallengeAt hz with h | ⟨-, h⟩ <;> exact Or.inl (by rw [h])))
      (fun t s z hz => by
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame
          (c := SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
        exact Or.inl rfl))
      (fun t s z hz => by
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame
          (c := SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
        exact Or.inl rfl)

/-- Every query of an installed game keeps the trace invariant of the repaired game. -/
theorem traceImplAt_traceInv (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (hkp : ∀ x, kp = some x → x ∈ support P.kem.keygen) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), TraceInv hMac true s →
      (∀ c party a hdr dec, ec = some c → s.game.stateAt party = .headerReceived e a hdr dec →
        c ∈ support (P.inc.encaps1 hdr)) →
      ∀ z ∈ support ((traceImplAt P hMac irl e kp ec xo m q).run s), TraceInv hMac true z.2
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, hs, _, z, hz =>
      traceUnif_preservesInv hMac true t s hs z hz
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, hs, H, z, hz => by
      obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
      exact traceSendAt_traceInv hMac irl e kp ec true false s hs hkp
        (fun c a hdr dec h1 h2 => H c true a hdr dec h1 h2) hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, hs, H, z, hz => by
      obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
      exact traceSendAt_traceInv hMac irl e kp ec false false s hs hkp
        (fun c a hdr dec h1 h2 => H c false a hdr dec h1 h2) hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, hs, _, z, hz =>
      traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct true true
        n s hs z hz
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, hs, _, z, hz =>
      traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct true false
        n s hs z hz
  | .inl (.inl (.inl (.inl (.inr t)))), s, hs, H, z, hz =>
      traceSendAt_traceInv hMac irl e kp ec true true s hs hkp
        (fun c a hdr dec h1 h2 => H c true a hdr dec h1 h2) hz
  | .inl (.inl (.inl (.inr t))), s, hs, H, z, hz =>
      traceSendAt_traceInv hMac irl e kp ec false true s hs hkp
        (fun c a hdr dec h1 h2 => H c false a hdr dec h1 h2) hz
  | .inl (.inl (.inr t)), s, hs, _, z, hz => traceChallengeAt_traceInv hMac m e xo t s hs z hz
  | .inl (.inr t), s, hs, _, z, hz => traceCorruptA_preservesInv hMac true t s hs z hz
  | .inr t, s, hs, _, z, hz => traceCorruptB_preservesInv hMac true t s hs z hz

/-- Every query of an installed game keeps `InstInv`. -/
theorem traceImplAt_instInv (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (x : P.PK × P.SK)
    (ec ec' : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (hkp : x ∈ support P.kem.keygen)
    (hec : ∀ c, ec = some c → c ∈ support (P.inc.encaps1 (P.inc.toHeader x.1)))
    (hec' : ec' = none ∨ ec' = ec) :
    ∀ q s, InstInv hMac e (some x) ec' s →
      ∀ z ∈ support ((traceImplAt P hMac irl e (some x) ec xo m q).run s),
        InstInv hMac e (some x) ec' z.2 := by
  intro q s hs z hz
  have hstep := traceImplAt_transcriptStep hMac irl e (some x) ec xo m q s z hz
  refine ⟨traceImplAt_traceInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e
    (some x) ec xo m (fun y h => by cases h; exact hkp) q s hs.1 ?_ z hz,
    hstep.keypairAt hs.2.1, ?_⟩
  · intro c party a hdr dec hc hst
    have hrel : InstInv hMac e (some x) ec' s := hs
    rw [hrel.header hMac hst]
    exact hec c hc
  · rcases hec' with rfl | rfl
    · intro c h
      cases h
    · exact hstep.encapsAt hs.2.2

/-- A hit key generation records the installed key pair. -/
theorem keygen_hit_records (e : ℕ) (x : P.PK × P.SK) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isKeygenAt e) e q s = true →
      ∀ w ∈ support ((traceImplAt P hMac irl e (some x) none xo m q).run s),
        (w.2.transcript e).keypair ≠ none
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, w, hw => by
      have h' : isKeygenAt e (s.game.stateAt true) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_keygen_records hMac irl hst x (by simp) hu
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, w, hw => by
      have h' : isKeygenAt e (s.game.stateAt false) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_keygen_records hMac irl hst x (by simp) hu
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, w, hw => by
      have h' : (isKeygenAt e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_keygen_records hMac irl hst x hc hw
  | .inl (.inl (.inl (.inr t))), s, h, w, hw => by
      have h' : (isKeygenAt e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_keygen_records hMac irl hst x hc hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, h, _, _ => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inr _), _, h, _, _ => by simp [sendHit] at h
  | .inr _, _, h, _, _ => by simp [sendHit] at h

/-- A hit first-stage encapsulation records the installed sample. -/
theorem encaps1_hit_records (e : ℕ) (kp : Option (P.PK × P.SK))
    (c : P.inc.St × P.inc.C₁ × P.K) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isEncaps1At e) e q s = true →
      ∀ w ∈ support ((traceImplAt P hMac irl e kp (some c) xo m q).run s),
        (w.2.transcript e).encaps1 ≠ none
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, w, hw => by
      have h' : isEncaps1At e (s.game.stateAt true) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_encaps1_records hMac irl hst kp c (by simp) hu
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, w, hw => by
      have h' : isEncaps1At e (s.game.stateAt false) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_encaps1_records hMac irl hst kp c (by simp) hu
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, w, hw => by
      have h' : (isEncaps1At e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_encaps1_records hMac irl hst kp c hc hw
  | .inl (.inl (.inl (.inr t))), s, h, w, hw => by
      have h' : (isEncaps1At e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_encaps1_records hMac irl hst kp c hc hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, h, _, _ => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inr _), _, h, _, _ => by simp [sendHit] at h
  | .inr _, _, h, _, _ => by simp [sendHit] at h

end Dispatch

end MLKEMBraid.NoAuth
