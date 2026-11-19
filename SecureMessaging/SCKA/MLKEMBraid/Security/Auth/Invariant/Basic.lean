/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Trace.Sampling
public import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Basic

/-!
# The record-based invariant of the trace games

`RepairInv S tbl modes ik T s` says that the game state `s` agrees with the records `T`, for the
installed game with the scheduled authenticator `S`, the table `tbl` and the modes `modes`. It has
the fields of `TranscriptInv` for the authenticator `recorded S T`, which reads the epoch keys and
authenticator values from the records, and it says how the records were chosen: an installed entry
is the installed value, and a real-mode entry is the value the schedule gives. It says nothing
about decapsulation.

The module also states the authenticator chain through the records, the conversions between
`RepairInv` and `TranscriptInv` for the real game, and the lemmas about the game state that
`TranscriptInv` has in the correctness layer, for `RepairInv`.
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.Auth

open Braid

variable {P : Parameters ProbComp} {Root MacKey : Type}

/-- The game state `s` agrees with the records `T`. The records satisfy the fields of
`TranscriptInv` for the authenticator `recorded S T`, hold the epoch key and the authenticator value
of every epoch that has an encapsulation, and agree with the table `tbl` and the modes `modes`. -/
structure RepairInv [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) (ik : P.EpochKey) (T : ℕ → EpochRecord P (Root × MacKey))
    (s : GameState P (Root × MacKey)) : Prop where
  /-- The correctness flag is true. -/
  correct : s.correct = true
  /-- The control invariant holds. -/
  control : ControlInv s
  /-- The state-pair invariant holds. -/
  statePair : StatePairInv s
  /-- Epoch `0` has no key pair. -/
  keypair_zero : (T 0).keypair = none
  /-- Epoch `0` has no encapsulation. -/
  encaps_zero : (T 0).encaps1 = none
  /-- A recorded key pair belongs to a positive epoch its generator has reached. -/
  keypair : ∀ e pk sk, (T e).keypair = some (pk, sk) →
    0 < e ∧ e ≤ (if e % 2 = 1 then s.stA else s.stB).epoch
  /-- A recorded encapsulation belongs to a positive epoch its encapsulator has completed, and the
  epoch has a recorded key pair. -/
  encaps : ∀ e es ct1 k, (T e).encaps1 = some (es, ct1, k) →
    0 < e ∧ e ≤ (if e % 2 = 1 then s.stB else s.stA).completedEpoch ∧
      ∃ pk sk, (T e).keypair = some (pk, sk)
  /-- A's state agrees with the records. -/
  localA : LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) s.stA
  /-- B's state agrees with the records. -/
  localB : LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) s.stB
  /-- Every recorded message agrees with the records. -/
  messages : ∀ (party : Bool) n msg tsnd,
    (if party then s.msgA else s.msgB) n = some (msg, tsnd) →
      MessagePayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg
  /-- Each party's output keys are the recorded epoch keys of its completed epochs. -/
  keys : ∀ (party : Bool) e,
    (if party then s.keyA else s.keyB) e =
      if 0 < e ∧ e ≤ (if party then s.stA else s.stB).completedEpoch then (T e).key else none
  /-- The initial authenticator value is recorded. -/
  init_pair : (T 0).pair.isSome
  /-- An epoch has a recorded epoch key exactly if it has an encapsulation. -/
  key_some : ∀ e, (T e).key.isSome ↔ (T e).encaps1.isSome
  /-- A positive epoch has a recorded authenticator value exactly if it has an encapsulation. -/
  pair_some : ∀ e, 0 < e → ((T e).pair.isSome ↔ (T e).encaps1.isSome)
  /-- An installed epoch key is the recorded one. -/
  keyInstalled : ∀ e x, (T e).encaps1.isSome → tbl.key e = some x → (T e).key = some x
  /-- In the real mode, without an installed value, the recorded epoch key is derived from the
  shared secret. -/
  keyReal : ∀ e es ct1 k, (T e).encaps1 = some (es, ct1, k) → tbl.key e = none →
    modes.key e = .real → (T e).key = some (P.kdfOK k e)
  /-- An installed authenticator value is the recorded one. -/
  pairInstalled : ∀ e p, 0 < e → (T e).encaps1.isSome → tbl.pair e = some p →
    (T e).pair = some p
  /-- In the real mode, without an installed value, the recorded authenticator value is the
  schedule applied to the previous value and the recorded epoch key. -/
  pairReal : ∀ e x, 0 < e → (T e).encaps1.isSome → (T e).key = some x → tbl.pair e = none →
    modes.pair e = .real → (T e).pair = some (S.F e
      (transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) (e - 1)).1 x)
  /-- An installed initial authenticator value is the recorded one. -/
  initInstalled : ∀ p, tbl.pair 0 = some p → (T 0).pair = some p

/-- The chain through the records at an epoch with a recorded authenticator value is that value. -/
theorem transcriptAuth_recorded [DecidableEq P.Mac] (S : ScheduledAuthenticator P Root MacKey)
    (T : ℕ → EpochRecord P (Root × MacKey)) (ik : P.EpochKey) {t : ℕ} {p : Root × MacKey}
    (hp : (T t).pair = some p) (hrec : t = 0 ∨ (T t).encaps1.isSome) :
    transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) t = p := by
  cases t with
  | zero => simp [transcriptAuth, recorded, hp]
  | succ e =>
      obtain ⟨⟨es, ct1, k⟩, hc⟩ := Option.isSome_iff_exists.mp (hrec.resolve_left (by simp))
      simp [transcriptAuth, EpochRecord.toTranscript, hc, recorded, hp]

/-- The chain through the records does not move at an epoch without an encapsulation. -/
theorem transcriptAuth_recorded_of_none [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) (T : ℕ → EpochRecord P (Root × MacKey))
    (ik : P.EpochKey) {t : ℕ} (h : (T (t + 1)).encaps1 = none) :
    transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) (t + 1) =
      transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) t := by
  simp [transcriptAuth, EpochRecord.toTranscript, h]

/-- Records that agree up to epoch `n` give the same chain at `n`. Both the authenticator and the
transcript depend on the records. -/
theorem transcriptAuth_recorded_congr [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) (ik : P.EpochKey)
    {T T₂ : ℕ → EpochRecord P (Root × MacKey)} (n : ℕ) (h : ∀ i, i ≤ n → T₂ i = T i) :
    transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) n =
      transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) n := by
  induction n with
  | zero => simp [transcriptAuth, recorded, h 0 le_rfl]
  | succ n ih =>
      have hprev := ih fun i hi => h i (Nat.le_succ_of_le hi)
      have hn := h (n + 1) le_rfl
      rw [transcriptAuth, transcriptAuth]
      simp only [Function.comp_apply, EpochRecord.toTranscript, hn, hprev]
      simp only [recorded, hn]

/-- At the real instance the chain through the records is the chain of the real transcript. -/
theorem transcriptAuth_recorded_real [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {ik : P.EpochKey}
    {T : ℕ → EpochRecord P (Root × MacKey)} {s : GameState P (Root × MacKey)}
    (h : RepairInv S (Installed.empty (irl := irl)) Modes.real ik T s)
    (h0 : (T 0).pair = some (S.F 1 S.initRoot ik)) (t : ℕ) :
    transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) t =
      transcriptAuth S.toRatcheted ik (EpochRecord.toTranscript ∘ T) t := by
  induction t with
  | zero => simp [transcriptAuth, recorded, h0, ScheduledAuthenticator.toRatcheted]
  | succ e ih =>
      cases hc : (T (e + 1)).encaps1 with
      | none => simp [transcriptAuth, EpochRecord.toTranscript, hc, ih]
      | some c =>
          obtain ⟨es, ct1, k⟩ := c
          have hkey := h.keyReal (e + 1) es ct1 k hc rfl rfl
          have hpair := h.pairReal (e + 1) _ (Nat.succ_pos e) (by simp [hc]) hkey rfl rfl
          simp only [Nat.add_sub_cancel, ih] at hpair
          rw [transcriptAuth, transcriptAuth]
          simp only [Function.comp_apply, EpochRecord.toTranscript, hc, ih]
          simp only [recorded, hkey, hpair, Option.getD_some, ScheduledAuthenticator.toRatcheted]

/-- The records of a real transcript `T'`: its key pairs and encapsulations, the epoch key derived
from each recorded shared secret, and the authenticator value of each epoch with an encapsulation
(at epoch `0`, the initial value for `ik`). -/
def enrich [DecidableEq P.Mac] (S : ScheduledAuthenticator P Root MacKey) (ik : P.EpochKey)
    (T' : ℕ → EpochTranscript P) : ℕ → EpochRecord P (Root × MacKey) :=
  fun e =>
    { keypair := (T' e).keypair
      encaps1 := (T' e).encaps1
      key := (T' e).encaps1.map (fun (_, _, key) => P.kdfOK key e)
      pair := if e = 0 then some (S.F 1 S.initRoot ik)
        else (T' e).encaps1.map (fun _ => transcriptAuth S.toRatcheted ik T' e) }

/-- Forgetting the keys and authenticator values of `enrich S ik T'` gives `T'`. -/
theorem toTranscript_enrich [DecidableEq P.Mac] (S : ScheduledAuthenticator P Root MacKey)
    (ik : P.EpochKey) (T' : ℕ → EpochTranscript P) :
    EpochRecord.toTranscript ∘ enrich S ik T' = T' := rfl

/-- A transcript-consistent real game state satisfies `RepairInv` for the records of its
transcript, at the empty table and the real modes. -/
theorem RepairInv.of_transcriptInv [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {ik : P.EpochKey}
    {D : ℕ → P.PK → P.SK → P.inc.St → P.inc.C₁ → P.K → Prop} {T' : ℕ → EpochTranscript P}
    {s : GameState P (Root × MacKey)} (hT : TranscriptInv S.toRatcheted D ik T' s) :
    RepairInv S (Installed.empty (irl := irl)) Modes.real ik (enrich S ik T') s := by
  have hchain : ∀ t, transcriptAuth (recorded S (enrich S ik T')) ik T' t =
      transcriptAuth S.toRatcheted ik T' t := by
    intro t
    induction t with
    | zero => simp [transcriptAuth, recorded, enrich, ScheduledAuthenticator.toRatcheted]
    | succ e ih =>
        cases hc : (T' (e + 1)).encaps1 with
        | none => simp [transcriptAuth, hc, ih]
        | some c =>
            obtain ⟨es, ct1, k⟩ := c
            simp [transcriptAuth, hc, recorded, enrich]
  have hlocal : ∀ st : State P (Root × MacKey), LocalPayloadInv S.toRatcheted ik T' st →
      LocalPayloadInv (recorded S (enrich S ik T')) ik (EpochRecord.toTranscript ∘ enrich S ik T')
        st := by
    intro st hst
    change LocalPayloadInv (recorded S (enrich S ik T')) ik T' st
    cases st <;> simp only [LocalPayloadInv, hchain] at hst ⊢ <;> exact hst
  have hmsg : ∀ msg : Message P.Sym, MessagePayloadInv S.toRatcheted ik T' msg →
      MessagePayloadInv (recorded S (enrich S ik T')) ik (EpochRecord.toTranscript ∘ enrich S ik T')
        msg := by
    intro msg hm
    change MessagePayloadInv (recorded S (enrich S ik T')) ik T' msg
    cases htype : msg.type <;> simp only [MessagePayloadInv, htype, hchain] at hm ⊢ <;> exact hm
  refine ⟨hT.correct, hT.control, hT.statePair, hT.keypair_zero, hT.encaps_zero, hT.keypair,
    ?_, hlocal _ hT.localA, hlocal _ hT.localB,
    fun party n msg tsnd hm => hmsg _ (hT.messages party n msg tsnd hm), hT.keys,
    by simp [enrich], fun e => by simp [enrich],
    fun e he => by simp [enrich, Nat.pos_iff_ne_zero.mp he],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro e es ct1 k hc
    obtain ⟨h0, hle, pk, sk, hkp, -⟩ := hT.encaps e es ct1 k hc
    exact ⟨h0, hle, pk, sk, hkp⟩
  · intro e x _ h
    simp [Installed.empty] at h
  · intro e es ct1 k hc _ _
    have hc' : (T' e).encaps1 = some (es, ct1, k) := hc
    simp [enrich, hc']
  · intro e p _ _ h
    simp [Installed.empty] at h
  · intro e x he0 hsome hkey _ _
    obtain ⟨⟨es, ct1, k⟩, hc⟩ := Option.isSome_iff_exists.mp hsome
    have hc' : (T' e).encaps1 = some (es, ct1, k) := hc
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hx : P.kdfOK k (e' + 1) = x := by simpa [enrich, hc'] using hkey
    simp only [Nat.add_sub_cancel]
    rw [toTranscript_enrich, hchain, ← hx]
    simp [enrich, hc', transcriptAuth, ScheduledAuthenticator.toRatcheted]
  · intro p h
    simp [Installed.empty] at h

/-- A real-instance `RepairInv` whose initial record is the schedule's initial value gives the
transcript invariant of `S.toRatcheted` for the transcript of the records. -/
theorem RepairInv.toTranscriptInv [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {ik : P.EpochKey}
    {T : ℕ → EpochRecord P (Root × MacKey)} {s : GameState P (Root × MacKey)}
    (h : RepairInv S (Installed.empty (irl := irl)) Modes.real ik T s)
    (h0 : (T 0).pair = some (S.F 1 S.initRoot ik)) :
    TranscriptInv S.toRatcheted (fun _ _ _ _ _ _ => True) ik (EpochRecord.toTranscript ∘ T) s := by
  have hchain := transcriptAuth_recorded_real h h0
  have hlocal : ∀ st : State P (Root × MacKey),
      LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) st →
      LocalPayloadInv S.toRatcheted ik (EpochRecord.toTranscript ∘ T) st := by
    intro st hst
    cases st <;> simp only [LocalPayloadInv, hchain] at hst ⊢ <;> exact hst
  have hmsg : ∀ msg : Message P.Sym,
      MessagePayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg →
      MessagePayloadInv S.toRatcheted ik (EpochRecord.toTranscript ∘ T) msg := by
    intro msg hm
    cases htype : msg.type <;> simp only [MessagePayloadInv, htype, hchain] at hm ⊢ <;> exact hm
  refine ⟨h.correct, h.control, h.statePair, h.keypair_zero, h.encaps_zero, h.keypair, ?_,
    hlocal _ h.localA, hlocal _ h.localB,
    fun party n msg tsnd hm => hmsg _ (h.messages party n msg tsnd hm), ?_⟩
  · intro e es ct1 k hc
    obtain ⟨h0', hle, pk, sk, hkp⟩ := h.encaps e es ct1 k hc
    exact ⟨h0', hle, pk, sk, hkp, fun _ => trivial⟩
  · intro party e
    rw [h.keys party e]
    by_cases hcond : 0 < e ∧ e ≤ (if party then s.stA else s.stB).completedEpoch
    · rw [ite_eq_left hcond, ite_eq_left hcond]
      cases hc : (T e).encaps1 with
      | none =>
          have hk : (T e).key = none := by
            cases hk : (T e).key with
            | none => rfl
            | some x =>
                have := (h.key_some e).mp (by simp [hk])
                simp [hc] at this
          simp [Function.comp_apply, EpochRecord.toTranscript, hc, hk]
      | some c =>
          obtain ⟨es, ct1, k⟩ := c
          simp [Function.comp_apply, EpochRecord.toTranscript, hc,
            h.keyReal e es ct1 k hc rfl rfl]
    · rw [ite_eq_right hcond, ite_eq_right hcond]

/-- The state of either party agrees with the records. -/
theorem RepairInv.local [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s) (party : Bool) :
    LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) (s.stateAt party) := by
  cases party; exacts [h.localB, h.localA]

/-- The states of a party and its peer satisfy `PairInv` in both directions, have positive epochs,
each have an epoch at most the other's completed epoch plus one, and have opposite roles at equal
epochs. -/
theorem RepairInv.pairBounds [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s) (party : Bool) :
    let st := s.stateAt party
    let peer := s.stateAt (!party)
    PairInv st peer ∧ PairInv peer st ∧ 0 < st.epoch ∧ 0 < peer.epoch ∧
      st.epoch ≤ peer.completedEpoch + 1 ∧ peer.epoch ≤ st.completedEpoch + 1 ∧
      (st.epoch = peer.epoch →
        st.controlPosition.isGenerator = (!peer.controlPosition.isGenerator)) := by
  have hE := h.control.epochKnowledge
  refine ⟨h.statePair.pair party, by simpa using h.statePair.pair (!party),
    hE.keyPrefix.pos party, hE.keyPrefix.pos (!party), hE.epoch_le party,
    by simpa using hE.epoch_le (!party), ?_⟩
  cases party
  · intro heq
    simpa only [GameState.stateAt, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Bool.not_not] using (congrArg Bool.not (roles_opposite h.control heq.symm)).symm
  · exact roles_opposite h.control

/-- A game state with the epochs, completed epochs and keys of a state that satisfies `RepairInv`,
whose party states and recorded messages agree with the records, satisfies `RepairInv` for the same
records. -/
theorem RepairInv.of_party [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s)
    {s' : GameState P (Root × MacKey)}
    (hc : s'.correct = true) (hC : ControlInv s') (hP : StatePairInv s')
    (he : ∀ party, (s'.stateAt party).epoch = (s.stateAt party).epoch)
    (hcomp : ∀ party, (s'.stateAt party).completedEpoch = (s.stateAt party).completedEpoch)
    (hLocal : ∀ party,
      LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) (s'.stateAt party))
    (hMessages : ∀ party n msg tsnd, s'.messagesAt party n = some (msg, tsnd) →
      MessagePayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg)
    (hKeys : ∀ party, s'.keysAt party = s.keysAt party) :
    RepairInv S tbl modes ik T s' := by
  refine ⟨hc, hC, hP, h.keypair_zero, h.encaps_zero, ?_, ?_, hLocal true, hLocal false,
    hMessages, ?_, h.init_pair, h.key_some, h.pair_some, h.keyInstalled, h.keyReal,
    h.pairInstalled, h.pairReal, h.initInstalled⟩
  · intro e pk sk hk
    obtain ⟨hpos, hle⟩ := h.keypair e pk sk hk
    refine ⟨hpos, ?_⟩
    rw [← GameState.stateAt_generator, he, GameState.stateAt_generator]
    exact hle
  · intro e es ct1 k hc'
    obtain ⟨hpos, hle, pk, sk, hkp⟩ := h.encaps e es ct1 k hc'
    refine ⟨hpos, ?_, pk, sk, hkp⟩
    rw [← GameState.stateAt_encapsulator, hcomp, GameState.stateAt_encapsulator]
    exact hle
  · intro party e
    change s'.keysAt party e =
      if 0 < e ∧ e ≤ (s'.stateAt party).completedEpoch then (T e).key else none
    rw [hKeys, hcomp]
    exact h.keys party e

/-- The invariant reads neither the exposed nor the challenged epochs. -/
theorem RepairInv.setFlags [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s) (X Y : Finset ℕ) :
    RepairInv S tbl modes ik T { s with exposed := X, challenged := Y } :=
  have hC := h.control
  have hE := hC.epochKnowledge
  ⟨h.correct,
    ⟨⟨⟨hE.keyPrefix.posA, hE.keyPrefix.posB, hE.keyPrefix.prefixA, hE.keyPrefix.prefixB⟩,
        hE.epochA_le, hE.epochB_le, hE.tcurA_le, hE.tcurB_le, hE.msgA, hE.msgB⟩,
      ⟨hC.recordedReport.msgA, hC.recordedReport.msgB⟩, hC.tcurA_le_sub_one,
      hC.tcurB_le_sub_one, hC.roles⟩,
    h.statePair, h.keypair_zero, h.encaps_zero, h.keypair, h.encaps, h.localA, h.localB,
    h.messages, h.keys, h.init_pair, h.key_some, h.pair_some, h.keyInstalled, h.keyReal,
    h.pairInstalled, h.pairReal, h.initInstalled⟩

/-- A game state with larger epochs and completed epochs, whose party states, messages and keys
agree with the records, satisfies `RepairInv` for the same records. -/
theorem RepairInv.of_le [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s)
    {s' : GameState P (Root × MacKey)}
    (hc : s'.correct = true) (hC : ControlInv s') (hP : StatePairInv s')
    (he : ∀ party, (s.stateAt party).epoch ≤ (s'.stateAt party).epoch)
    (hcomp : ∀ party, (s.stateAt party).completedEpoch ≤ (s'.stateAt party).completedEpoch)
    (hLocal : ∀ party,
      LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) (s'.stateAt party))
    (hMessages : ∀ party n msg tsnd, s'.messagesAt party n = some (msg, tsnd) →
      MessagePayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg)
    (hKeys : ∀ party e, s'.keysAt party e =
      if 0 < e ∧ e ≤ (s'.stateAt party).completedEpoch then (T e).key else none) :
    RepairInv S tbl modes ik T s' := by
  refine ⟨hc, hC, hP, h.keypair_zero, h.encaps_zero, ?_, ?_, hLocal true, hLocal false,
    hMessages, hKeys, h.init_pair, h.key_some, h.pair_some, h.keyInstalled, h.keyReal,
    h.pairInstalled, h.pairReal, h.initInstalled⟩
  · intro e pk sk hk
    obtain ⟨h0, hle⟩ := h.keypair e pk sk hk
    refine ⟨h0, ?_⟩
    rw [← GameState.stateAt_generator] at hle ⊢
    exact hle.trans (he _)
  · intro e es ct1 k hc'
    obtain ⟨h0, hle, pk, sk, hkp⟩ := h.encaps e es ct1 k hc'
    refine ⟨h0, ?_, pk, sk, hkp⟩
    rw [← GameState.stateAt_encapsulator] at hle ⊢
    exact hle.trans (hcomp _)

/-- At equal epochs a generator waiting for `ct₂` is paired with `ct2Sampled`. -/
theorem PairInv.peer_of_ekSentCt1Received {AS : Type} {st peer : State P AS}
    (h : PairInv st peer) (h' : PairInv peer st)
    (hpos : 0 < st.epoch) (hposP : 0 < peer.epoch)
    (hcross : st.epoch ≤ peer.completedEpoch + 1) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    {t : ℕ} {a : AS} {sk : P.SK} {ct1 : P.inc.C₁} {dec : P.decCt2.D}
    (hst : st = .ekSentCt1Received t a sk ct1 dec) :
    ∃ b enc, peer = .ct2Sampled t b enc := by
  subst hst
  cases peer <;>
    simp [PairInv, AllowedStatePair, State.controlPosition, State.epoch,
      State.completedEpoch] at * <;>
    omega

end MLKEMBraid.Auth
