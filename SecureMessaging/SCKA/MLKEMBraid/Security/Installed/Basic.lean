/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling

/-!
# Installed trace operations and their elementary equations

Installed key-generation and first-stage samples retain the original send outcomes, transcript
updates and refusal/exposure convention. This module contains their executable operations and
joint run equations, without importing trace-invariant or analytical bad-event bounds.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

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

/-- With an installed challenge value, the mode at `e` is irrelevant. -/
theorem traceImplAt_congr (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (x : P.EpochKey) (m m' : ℕ → Mode)
    (h : ∀ t, t ≠ e → m t = m' t) :
    traceImplAt P hMac irl e kp ec (some x) m = traceImplAt P hMac irl e kp ec (some x) m' := by
  unfold traceImplAt
  rw [traceChallengeAt_congr m m' e x h]

end InstalledLemmas

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

end TargetSends

end MLKEMBraid.NoAuth
