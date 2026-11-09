/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Invariant.Basic
public import SecureMessaging.SCKA.MLKEMBraid.Correctness.SendPayload

/-!
# Sends preserve the record-based invariant

A send that samples nothing keeps the records. A send that generates a key pair or runs the first
stage of encapsulation writes the record of its epoch: the key pair, or the encapsulation, the
epoch key and the authenticator value that the rules of the game have determined. The invariant
`RepairInv` holds after every send of the trace game, for every table and every mode, because it
describes the records and the game state and only constrains the epoch key and the authenticator
value through the table and the real mode.
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid.Auth

variable {P : Parameters ProbComp} {Root MacKey : Type}

/-- An epoch key drawn by the rules is the installed one, or, with no installed value and the real
mode, the key derived from the shared secret. -/
theorem installedRules_key_mem [SampleableType P.K] [SampleableType P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) {t : ℕ} {k : P.K} {x : P.EpochKey}
    (hx : x ∈ support ((installedRules S tbl modes).key t k)) :
    tbl.key t = some x ∨ (tbl.key t = none ∧ (modes.key t = .real → x = P.kdfOK k t)) := by
  simp only [installedRules] at hx
  cases hk : tbl.key t with
  | some y =>
      rw [hk] at hx
      rw [mem_support_pure_iff] at hx
      exact Or.inl (by rw [hx])
  | none =>
      right
      refine ⟨rfl, fun hm => ?_⟩
      rw [hk, hm] at hx
      exact (mem_support_pure_iff _ _).mp hx

/-- An authenticator value drawn by the rules is the installed one, or, with no installed value and
the real mode, the schedule applied to the previous value and the epoch key. -/
theorem installedRules_pair_mem [SampleableType P.K] [SampleableType P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) {t : ℕ} {prev : Root × MacKey} {x : P.EpochKey} {p : Root × MacKey}
    (hp : p ∈ support ((installedRules S tbl modes).pair t prev x)) :
    tbl.pair t = some p ∨ (tbl.pair t = none ∧ (modes.pair t = .real → p = S.F t prev.1 x)) := by
  simp only [installedRules] at hp
  cases hk : tbl.pair t with
  | some y =>
      rw [hk] at hp
      rw [mem_support_pure_iff] at hp
      exact Or.inl (by rw [hp])
  | none =>
      right
      refine ⟨rfl, fun hm => ?_⟩
      rw [hk, hm] at hp
      exact (mem_support_pure_iff _ _).mp hp

/-- A key-generation send, with any key pair, writes the key pair to the record of its epoch and
keeps `RepairInv`, once the successor satisfies the control and pair invariants. -/
theorem sampledSend_keygen_preserves [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s) (party : Bool) {t : ℕ}
    {a : Root × MacKey} (hst : s.stateAt party = .keysUnsampled t a)
    (x : (P.PK × P.SK) × irl.KeygenRand) :
    let r := keygenStep S.toRatcheted t a x.1.1 x.1.2
    let T₂ := Function.update T t { (T t) with keypair := some x.1 }
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') → RepairInv S tbl modes ik T₂ s' := by
  obtain ⟨⟨pk, sk⟩, rand⟩ := x
  dsimp only
  rintro ⟨hC', hP'⟩
  obtain ⟨h1, h2, hpos0, hposP, hcross, hcrossP, -⟩ := h.pairBounds party
  obtain ⟨b, dec, hpeer⟩ := PairInv.peer_of_keysUnsampled h1 h2 hpos0 hposP hcross hcrossP hst
  have hpos : 0 < t := by simpa [hst, State.epoch] using hpos0
  have hLs := h.local party
  have hLp := h.local (!party)
  rw [hst] at hLs
  rw [hpeer] at hLp
  simp only [LocalPayloadInv] at hLs
  obtain ⟨ha, hkp0, hc0⟩ := hLs
  have hkp0' : (T t).keypair = none := hkp0
  have hc0' : (T t).encaps1 = none := hc0
  simp only [LocalPayloadInv, hkp0] at hLp
  obtain ⟨hb, hdec⟩ := hLp
  subst hdec
  set T₂ := Function.update T t { (T t) with keypair := some (pk, sk) } with hT₂def
  have hne : ∀ n, n ≠ t → T₂ n = T n := fun n hn => Function.update_of_ne hn _ _
  have hrec : ∀ n, (T₂ n).encaps1 = (T n).encaps1 ∧ (T₂ n).key = (T n).key ∧
      (T₂ n).pair = (T n).pair := by
    intro n
    by_cases hn : n = t
    · subst hn; simp [T₂]
    · rw [hne n hn]; exact ⟨rfl, rfl, rfl⟩
  have hTke : (T₂ t).keypair = some (pk, sk) := by simp [T₂]
  have hTke' : ((EpochRecord.toTranscript ∘ T₂) t).keypair = some (pk, sk) := hTke
  have hAuth : ∀ n, n < t → transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) n =
      transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) n :=
    fun n hn => transcriptAuth_recorded_congr S ik n (fun i hi => hne i (by omega))
  have haT : a = transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) (t - 1) :=
    ha.trans (hAuth (t - 1) (by omega)).symm
  have hbT : b = transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) (t - 1) :=
    hb.trans (hAuth (t - 1) (by omega)).symm
  have hep : ∀ who, (s.stateAt who).epoch = t := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hcomp : ∀ who, (s.stateAt who).completedEpoch = t - 1 := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hep' : ∀ who,
      ((sendSuccessor s party (keygenStep S.toRatcheted t a pk sk)).stateAt who).epoch =
        (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hcomp' : ∀ who,
      ((sendSuccessor s party (keygenStep S.toRatcheted t a pk sk)).stateAt who).completedEpoch =
        (s.stateAt who).completedEpoch := fun who =>
    completedEpoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hBnd : ∀ who n msg tsnd, s.messagesAt who n = some (msg, tsnd) → msg.epoch ≤ t := by
    intro who n msg tsnd hm
    have := (h.control.epochKnowledge.msgs who n msg tsnd hm).1
    rw [hcomp] at this
    omega
  have hMsgOld : ∀ msg : Message P.Sym, msg.epoch ≤ t →
      MessagePayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg →
      MessagePayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) msg := by
    intro msg hle hm
    have hprev := hAuth (msg.epoch - 1) (by omega)
    have hcur : ∀ c, (T msg.epoch).encaps1 = some c →
        transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) msg.epoch =
          transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg.epoch := by
      intro c hc
      have hlt : msg.epoch < t := lt_of_le_of_ne hle (by
        rintro he
        rw [he, hc0'] at hc
        cases hc)
      exact hAuth _ hlt
    have hkpT : ∀ kp, (T msg.epoch).keypair = some kp → (T₂ msg.epoch).keypair = some kp := by
      intro kp hkpm
      have hmt : msg.epoch ≠ t := by
        rintro he
        rw [he, hkp0'] at hkpm
        cases hkpm
      rw [hne _ hmt]
      exact hkpm
    cases htype : msg.type <;> simp only [MessagePayloadInv, htype] at hm ⊢
    case none => exact hm
    case hdr =>
      obtain ⟨pk', sk', i, hk', hd⟩ := hm
      exact ⟨pk', sk', i, hkpT _ hk', by rw [hprev]; exact hd⟩
    case ek =>
      obtain ⟨pk', sk', i, hk', hd⟩ := hm
      exact ⟨pk', sk', i, hkpT _ hk', hd⟩
    case ekCt1Ack =>
      obtain ⟨pk', sk', i, hk', hd⟩ := hm
      exact ⟨pk', sk', i, hkpT _ hk', hd⟩
    case ct1 =>
      obtain ⟨es, ct1, key, i, hc', hd⟩ := hm
      exact ⟨es, ct1, key, i, (hrec msg.epoch).1.trans hc', hd⟩
    case ct2 =>
      obtain ⟨pk', sk', es, ct1, key, i, hk', hc', hd⟩ := hm
      exact ⟨pk', sk', es, ct1, key, i, hkpT _ hk', (hrec msg.epoch).1.trans hc',
        by rw [hcur _ hc']; exact hd⟩
  have hMsgNew : MessagePayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂)
      (keygenStep S.toRatcheted t a pk sk).msg :=
    ⟨pk, sk, 0, hTke, congrArg (fun y => some (P.ecpHdr.encode
      (P.inc.toHeader pk, S.toRatcheted.macHeader y t (P.inc.toHeader pk)) 0)) haT⟩
  have hTable : ∀ who n msg tsnd,
      (sendSuccessor s party (keygenStep S.toRatcheted t a pk sk)).messagesAt who n =
        some (msg, tsnd) →
      MessagePayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) msg := by
    intro who n msg tsnd hmsg
    rw [messagesAt_sendSuccessor] at hmsg
    split_ifs at hmsg with hwho
    · by_cases hnew : n = s.countAt who + 1
      · subst hnew
        rw [Function.update_self] at hmsg
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmsg)
        exact hMsgNew
      · rw [Function.update_of_ne hnew] at hmsg
        exact hMsgOld msg (hBnd who n msg tsnd hmsg) (h.messages who n msg tsnd hmsg)
    · exact hMsgOld msg (hBnd who n msg tsnd hmsg) (h.messages who n msg tsnd hmsg)
  have hLocal : ∀ who, LocalPayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂)
      ((sendSuccessor s party (keygenStep S.toRatcheted t a pk sk)).stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte]
      exact ⟨haT, pk, hTke, rfl, rfl,
        congrArg (fun y => (P.inc.toHeader pk, S.toRatcheted.macHeader y t (P.inc.toHeader pk)))
          haT⟩
    · simp only [stateAt_sendSuccessor, Bool.not_eq_self, ↓reduceIte]
      rw [hpeer]
      simp only [LocalPayloadInv, hTke']
      exact ⟨hbT, P.decHdr.received_empty P.ecpHdr _⟩
  refine ⟨by simpa only [correct_sendSuccessor] using h.correct, hC', hP', ?_, ?_, ?_, ?_,
    hLocal true, hLocal false, fun who n msg tsnd hmsg => hTable who n msg tsnd hmsg, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hne 0 (by omega)]; exact h.keypair_zero
  · rw [(hrec 0).1]; exact h.encaps_zero
  · intro e' pk' sk' hk
    by_cases he : e' = t
    · subst e'
      rw [hTke] at hk
      cases hk
      refine ⟨hpos, ?_⟩
      rw [← GameState.stateAt_generator, hep', hep]
    · rw [hne e' he] at hk
      obtain ⟨h0, hle⟩ := h.keypair e' pk' sk' hk
      refine ⟨h0, ?_⟩
      rw [← GameState.stateAt_generator, hep', GameState.stateAt_generator]
      exact hle
  · intro e' es ct1 k hc
    rw [(hrec e').1] at hc
    have he : e' ≠ t := by
      rintro rfl
      rw [hc0'] at hc
      cases hc
    obtain ⟨h0, hle, pk', sk', hkp'⟩ := h.encaps e' es ct1 k hc
    refine ⟨h0, ?_, pk', sk', by rw [hne e' he]; exact hkp'⟩
    rw [← GameState.stateAt_encapsulator, hcomp', GameState.stateAt_encapsulator]
    exact hle
  · intro who e'
    change (sendSuccessor s party (keygenStep S.toRatcheted t a pk sk)).keysAt who e' = _
    rw [keysAt_sendSuccessor]
    simp only [keygenStep, ite_self]
    change s.keysAt who e' = if 0 < e' ∧
      e' ≤ ((sendSuccessor s party (keygenStep S.toRatcheted t a pk sk)).stateAt who).completedEpoch
        then _ else _
    rw [hcomp', (hrec e').2.1]
    exact h.keys who e'
  · rw [(hrec 0).2.2]; exact h.init_pair
  · intro e'
    rw [(hrec e').2.1, (hrec e').1]
    exact h.key_some e'
  · intro e' he'
    rw [(hrec e').2.2, (hrec e').1]
    exact h.pair_some e' he'
  · intro e' x' hc hx
    rw [(hrec e').2.1]
    rw [(hrec e').1] at hc
    exact h.keyInstalled e' x' hc hx
  · intro e' es ct1 k hc hx hm
    rw [(hrec e').1] at hc
    rw [(hrec e').2.1]
    exact h.keyReal e' es ct1 k hc hx hm
  · intro e' p' he' hc hx
    rw [(hrec e').1] at hc
    rw [(hrec e').2.2]
    exact h.pairInstalled e' p' he' hc hx
  · intro e' x' he' hc hk hx hm
    rw [(hrec e').1] at hc
    rw [(hrec e').2.1] at hk
    rw [(hrec e').2.2]
    obtain ⟨es, ct1, k, hc'⟩ : ∃ es ct1 k, (T e').encaps1 = some (es, ct1, k) := by
      obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hc
      exact ⟨c.1, c.2.1, c.2.2, hc'⟩
    obtain ⟨-, hle, -⟩ := h.encaps e' es ct1 k hc'
    have hA : s.stA.completedEpoch = t - 1 := hcomp true
    have hB : s.stB.completedEpoch = t - 1 := hcomp false
    have hlt : e' - 1 < t := by
      have : e' ≤ (if e' % 2 = 1 then s.stB else s.stA).completedEpoch := hle
      split_ifs at this <;> omega
    rw [hAuth (e' - 1) hlt]
    exact h.pairReal e' x' he' hc hk hx hm
  · intro p' hp
    rw [(hrec 0).2.2]
    exact h.initInstalled p' hp

/-- A first-stage encapsulation send, with any sample, epoch key and authenticator value that
satisfy the rules of the table and the modes, writes them to the record of its epoch and keeps
`RepairInv`, once the successor satisfies the control and pair invariants. -/
theorem sampledSend_encaps1_preserves [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s) (party : Bool) {t : ℕ}
    {a : Root × MacKey} {hdr : P.inc.PKheader} {dec : P.decEk.D}
    (hst : s.stateAt party = .headerReceived t a hdr dec)
    (x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand) {key : P.EpochKey} {p : Root × MacKey}
    (hkey : tbl.key t = some key ∨
      (tbl.key t = none ∧ (modes.key t = .real → key = P.kdfOK x.1.2.2 t)))
    (hpair : tbl.pair t = some p ∨
      (tbl.pair t = none ∧ (modes.pair t = .real → p = S.F t a.1 key))) :
    let r := encaps1Step t a hdr dec x.1.1 x.1.2.1 key p
    let T₂ := Function.update T t
      { (T t) with encaps1 := some x.1, key := some key, pair := some p }
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') → RepairInv S tbl modes ik T₂ s' := by
  obtain ⟨⟨es, ct1, k⟩, rand⟩ := x
  dsimp only at hkey hpair ⊢
  rintro ⟨hC', hP'⟩
  obtain ⟨h1, h2, hpos0, hposP, hcross, hcrossP, hroles⟩ := h.pairBounds party
  obtain ⟨b, sk', vec, enc, hpeer⟩ :=
    PairInv.peer_of_headerReceived h1 h2 hpos0 hposP hcross hcrossP hroles hst
  have hpos : 0 < t := by simpa [hst, State.epoch] using hpos0
  have hRole := h.control.role party
  have hLs := h.local party
  have hLp := h.local (!party)
  rw [hst] at hRole hLs
  rw [hpeer] at hLp
  simp only [State.controlPosition, State.epoch] at hRole
  have hpar : ¬ t % 2 = if party then 1 else 0 := of_decide_eq_false hRole.symm
  simp only [LocalPayloadInv] at hLs hLp
  obtain ⟨ha, hc0, pk, sk, hkpT, hhdr, hdec⟩ := hLs
  obtain ⟨hb, pk', hkp', hvec, hecp, hpay⟩ := hLp
  obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by
    have hk : (T t).keypair = some (pk, sk) := hkpT
    have hk' : (T t).keypair = some (pk', sk') := hkp'
    simpa using hk.symm.trans hk'
  have hc0' : (T t).encaps1 = none := hc0
  have hkp : (T t).keypair = some (pk, sk) := hkpT
  subst hhdr hdec
  set T₂ := Function.update T t
    { (T t) with encaps1 := some (es, ct1, k), key := some key, pair := some p } with hT₂def
  have hne : ∀ n, n ≠ t → T₂ n = T n := fun n hn => Function.update_of_ne hn _ _
  have hTk : ∀ n, (T₂ n).keypair = (T n).keypair := by
    intro n
    by_cases hn : n = t
    · subst hn; simp [T₂]
    · rw [hne n hn]
  have hTce : (T₂ t).encaps1 = some (es, ct1, k) := by simp [T₂]
  have hTkey : (T₂ t).key = some key := by simp [T₂]
  have hTpair : (T₂ t).pair = some p := by simp [T₂]
  have hTke : (T₂ t).keypair = some (pk, sk) := (hTk t).trans hkp
  have hAuthLt : ∀ n, n < t →
      transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) n =
        transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) n :=
    fun n hn => transcriptAuth_recorded_congr S ik n (fun i hi => hne i (by omega))
  have hAuthE : transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) t = p :=
    transcriptAuth_recorded S T₂ ik hTpair (Or.inr (by simp [hTce]))
  have haT : a = transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) (t - 1) :=
    ha.trans (hAuthLt (t - 1) (by omega)).symm
  have hep : ∀ who, (s.stateAt who).epoch = t := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hcomp : ∀ who, (s.stateAt who).completedEpoch = t - 1 := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hA : s.stA.completedEpoch = t - 1 := hcomp true
  have hB : s.stB.completedEpoch = t - 1 := hcomp false
  have hep' : ∀ who, ((sendSuccessor s party
      (encaps1Step t a (P.inc.toHeader pk) P.decEk.empty es ct1 key p)).stateAt who).epoch =
        (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hcomp' : ∀ who, ((sendSuccessor s party
      (encaps1Step t a (P.inc.toHeader pk) P.decEk.empty es ct1 key p)).stateAt who).completedEpoch
        = if who = party then t else t - 1 := by
    intro who
    simp only [stateAt_sendSuccessor]
    split_ifs
    · rfl
    · exact hcomp who
  have hBnd : ∀ who n msg tsnd, s.messagesAt who n = some (msg, tsnd) → msg.epoch ≤ t := by
    intro who n msg tsnd hm
    have := (h.control.epochKnowledge.msgs who n msg tsnd hm).1
    rw [hcomp] at this
    omega
  have hMsgOld : ∀ msg : Message P.Sym, msg.epoch ≤ t →
      MessagePayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg →
      MessagePayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) msg := by
    intro msg hle hm
    have hprev := hAuthLt (msg.epoch - 1) (by omega)
    have hlt : ∀ c, (T msg.epoch).encaps1 = some c → msg.epoch < t := by
      intro c hc
      exact lt_of_le_of_ne hle (by
        rintro he
        rw [he, hc0'] at hc
        cases hc)
    have hcur : ∀ c, (T msg.epoch).encaps1 = some c →
        transcriptAuth (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) msg.epoch =
          transcriptAuth (recorded S T) ik (EpochRecord.toTranscript ∘ T) msg.epoch :=
      fun c hc => hAuthLt _ (hlt c hc)
    have hcT : ∀ c, (T msg.epoch).encaps1 = some c → (T₂ msg.epoch).encaps1 = some c := by
      intro c hc
      rw [hne _ (ne_of_lt (hlt c hc))]
      exact hc
    cases htype : msg.type <;> simp only [MessagePayloadInv, htype] at hm ⊢
    case none => exact hm
    case hdr =>
      obtain ⟨pk'', sk'', i, hk'', hd⟩ := hm
      exact ⟨pk'', sk'', i, (hTk msg.epoch).trans hk'', by rw [hprev]; exact hd⟩
    case ek =>
      obtain ⟨pk'', sk'', i, hk'', hd⟩ := hm
      exact ⟨pk'', sk'', i, (hTk msg.epoch).trans hk'', hd⟩
    case ekCt1Ack =>
      obtain ⟨pk'', sk'', i, hk'', hd⟩ := hm
      exact ⟨pk'', sk'', i, (hTk msg.epoch).trans hk'', hd⟩
    case ct1 =>
      obtain ⟨es', ct1', key', i, hc', hd⟩ := hm
      exact ⟨es', ct1', key', i, hcT _ hc', hd⟩
    case ct2 =>
      obtain ⟨pk'', sk'', es', ct1', key', i, hk'', hc', hd⟩ := hm
      exact ⟨pk'', sk'', es', ct1', key', i, (hTk msg.epoch).trans hk'', hcT _ hc',
        by rw [hcur _ hc']; exact hd⟩
  have hMsgNew : MessagePayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂)
      (encaps1Step t a (P.inc.toHeader pk) P.decEk.empty es ct1 key p).msg :=
    ⟨es, ct1, k, 0, hTce, rfl⟩
  have hTable : ∀ who n msg tsnd,
      (sendSuccessor s party
        (encaps1Step t a (P.inc.toHeader pk) P.decEk.empty es ct1 key p)).messagesAt who n =
        some (msg, tsnd) →
      MessagePayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂) msg := by
    intro who n msg tsnd hmsg
    rw [messagesAt_sendSuccessor] at hmsg
    split_ifs at hmsg with hwho
    · by_cases hnew : n = s.countAt who + 1
      · subst hnew
        rw [Function.update_self] at hmsg
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmsg)
        exact hMsgNew
      · rw [Function.update_of_ne hnew] at hmsg
        exact hMsgOld msg (hBnd who n msg tsnd hmsg) (h.messages who n msg tsnd hmsg)
    · exact hMsgOld msg (hBnd who n msg tsnd hmsg) (h.messages who n msg tsnd hmsg)
  have hLocal : ∀ who, LocalPayloadInv (recorded S T₂) ik (EpochRecord.toTranscript ∘ T₂)
      ((sendSuccessor s party
        (encaps1Step t a (P.inc.toHeader pk) P.decEk.empty es ct1 key p)).stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte]
      exact ⟨hAuthE.symm, pk, sk, k, hTke, hTce, rfl, ⟨rfl, rfl⟩,
        P.decEk.received_empty P.ecpEk _⟩
    · simp only [stateAt_sendSuccessor, Bool.not_eq_self, ↓reduceIte]
      rw [hpeer]
      refine ⟨hb.trans (hAuthLt (t - 1) (by omega)).symm, pk, hTke, hvec, hecp, ?_⟩
      rw [hAuthLt (t - 1) (by omega)]
      exact hpay
  have howner : decide (t % 2 = 1) = !party := by
    cases party
    · apply decide_eq_true
      simp only [Bool.false_eq_true, ↓reduceIte] at hpar
      omega
    · exact decide_eq_false hpar
  refine ⟨by simpa only [correct_sendSuccessor] using h.correct, hC', hP', ?_, ?_, ?_, ?_,
    hLocal true, hLocal false, fun who n msg tsnd hmsg => hTable who n msg tsnd hmsg, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTk]; exact h.keypair_zero
  · rw [hne 0 (by omega)]; exact h.encaps_zero
  · intro e' pk'' sk'' hk
    rw [hTk] at hk
    obtain ⟨h0, hle⟩ := h.keypair e' pk'' sk'' hk
    refine ⟨h0, ?_⟩
    rw [← GameState.stateAt_generator, hep', GameState.stateAt_generator]
    exact hle
  · intro e' es' ct1' key' hc'
    by_cases he : e' = t
    · subst e'
      rw [hTce] at hc'
      cases hc'
      refine ⟨hpos, ?_, pk, sk, hTke⟩
      rw [← GameState.stateAt_encapsulator, hcomp', howner]
      simp
    · rw [hne e' he] at hc'
      obtain ⟨h0, hle, pk'', sk'', hkp''⟩ := h.encaps e' es' ct1' key' hc'
      refine ⟨h0, ?_, pk'', sk'', by rw [hTk]; exact hkp''⟩
      rw [← GameState.stateAt_encapsulator, hcomp']
      rw [← GameState.stateAt_encapsulator] at hle
      rw [hcomp] at hle
      split_ifs at hle ⊢ <;> omega
  · intro who e'
    change (sendSuccessor s party
      (encaps1Step t a (P.inc.toHeader pk) P.decEk.empty es ct1 key p)).keysAt who e' = _
    rw [keysAt_sendSuccessor]
    change (if who = party then Function.update (s.keysAt who) t (some key)
      else s.keysAt who) e' = if 0 < e' ∧ e' ≤ ((sendSuccessor s party
        (encaps1Step t a (P.inc.toHeader pk) P.decEk.empty es ct1 key p)).stateAt who
          ).completedEpoch then _ else _
    rw [hcomp']
    have hK : s.keysAt who e' =
        if 0 < e' ∧ e' ≤ (s.stateAt who).completedEpoch then (T e').key else none :=
      h.keys who e'
    rw [hcomp] at hK
    by_cases hwho : who = party
    · rw [ite_eq_left hwho, ite_eq_left hwho]
      by_cases he : e' = t
      · subst e'
        rw [Function.update_self, ite_eq_left ⟨hpos, le_rfl⟩, hTkey]
      · rw [Function.update_of_ne he, hK, hne e' he]
        by_cases h1 : 0 < e' ∧ e' ≤ t - 1
        · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    · rw [ite_eq_right hwho, ite_eq_right hwho, hK]
      by_cases he : e' = t
      · subst e'
        simp [show ¬ (0 < t ∧ t ≤ t - 1) by omega]
      · rw [hne e' he]
  · rw [hne 0 (by omega)]; exact h.init_pair
  · intro e'
    by_cases he : e' = t
    · subst e'
      simp [hTkey, hTce]
    · rw [hne e' he]; exact h.key_some e'
  · intro e' he'
    by_cases he : e' = t
    · subst e'
      simp [hTpair, hTce]
    · rw [hne e' he]; exact h.pair_some e' he'
  · intro e' x' hc hx
    by_cases he : e' = t
    · subst e'
      rcases hkey with hk | ⟨hk, -⟩
      · rw [hk] at hx
        cases hx
        exact hTkey
      · rw [hk] at hx
        cases hx
    · rw [hne e' he] at hc ⊢
      exact h.keyInstalled e' x' hc hx
  · intro e' es' ct1' k' hc hx hm
    by_cases he : e' = t
    · subst e'
      rw [hTce] at hc
      cases hc
      rcases hkey with hk | ⟨-, hkr⟩
      · rw [hk] at hx
        cases hx
      · rw [hTkey, hkr hm]
    · rw [hne e' he] at hc ⊢
      exact h.keyReal e' es' ct1' k' hc hx hm
  · intro e' p' he' hc hx
    by_cases he : e' = t
    · subst e'
      rcases hpair with hp | ⟨hp, -⟩
      · rw [hp] at hx
        cases hx
        exact hTpair
      · rw [hp] at hx
        cases hx
    · rw [hne e' he] at hc ⊢
      exact h.pairInstalled e' p' he' hc hx
  · intro e' x' he' hc hk hx hm
    by_cases he : e' = t
    · subst e'
      rw [hTkey] at hk
      cases hk
      rcases hpair with hp | ⟨hp, hpr⟩
      · rw [hp] at hx
        cases hx
      · rw [hTpair, hpr hm, haT]
    · rw [hne e' he] at hc hk ⊢
      obtain ⟨es', ct1', k', hc'⟩ : ∃ es ct1 k, (T e').encaps1 = some (es, ct1, k) := by
        obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hc
        exact ⟨c.1, c.2.1, c.2.2, hc'⟩
      obtain ⟨-, hle, -⟩ := h.encaps e' es' ct1' k' hc'
      have hlt : e' - 1 < t := by
        have : e' ≤ (if e' % 2 = 1 then s.stB else s.stA).completedEpoch := hle
        split_ifs at this <;> omega
      rw [hAuthLt (e' - 1) hlt]
      exact h.pairReal e' x' he' hc hk hx hm
  · intro p' hp
    rw [hne 0 (by omega)]
    exact h.initInstalled p' hp

/-- A send that samples nothing keeps `RepairInv` with the same records, once its successor
satisfies the control and pair invariants. -/
theorem sendSteady_preserves [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s) (party : Bool)
    {r : SendResult P (Root × MacKey)} (hr : r ∈ support (send P S.toRatcheted (s.stateAt party)))
    (hsteady : (s.stateAt party).SendsNoSample) :
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') → RepairInv S tbl modes ik T s' := by
  dsimp only
  have hr' : r ∈ support (send P (recorded S T) (s.stateAt party)) := by
    cases hs : s.stateAt party <;> rw [hs] at hr hsteady <;>
      first | exact False.elim hsteady | exact hr
  obtain ⟨hnone, hep, hcomp, hLocalNew, hMsgNew⟩ :=
    send_steady_step (recorded S T) ((mem_support_send_iff (recorded S T)).mp hr') hsteady
      (h.local party)
  rintro ⟨hC', hP'⟩
  refine h.of_party (by simpa only [correct_sendSuccessor] using h.correct) hC' hP' ?_ ?_ ?_ ?_ ?_
  · exact fun who => epoch_stateAt_sendSuccessor s party who r hep
  · exact fun who => completedEpoch_stateAt_sendSuccessor s party who r hcomp
  · intro who
    simp only [stateAt_sendSuccessor]
    split_ifs with hwho
    · exact hLocalNew
    · exact h.local who
  · intro who n msg tsnd hmsg
    rw [messagesAt_sendSuccessor] at hmsg
    split_ifs at hmsg with hwho
    · by_cases hnew : n = s.countAt who + 1
      · subst hnew
        rw [Function.update_self] at hmsg
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmsg)
        exact hMsgNew
      · rw [Function.update_of_ne hnew] at hmsg
        exact h.messages who n msg tsnd hmsg
    · exact h.messages who n msg tsnd hmsg
  · intro who
    simp [keysAt_sendSuccessor, hnone]

/-- A committed trace send keeps `RepairInv` for its extended records, for every table and every
mode, and keeps decapsulation agreement whenever its bad flag stays false. The control and pair
invariants of an installed successor follow from those of the successor of a real send of the same
state, because they read only epochs, roles, steps and message types. -/
theorem traceSend_preserves [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {tbl : Installed P irl (Root × MacKey)} {modes : Modes} {ik : P.EpochKey}
    (party leaking : Bool) (s : TraceState P (Root × MacKey))
    (h : RepairInv S tbl modes ik s.transcript s.game)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P (Root × MacKey)}
    (hz : z ∈ support ((traceSend S.toRatcheted irl tbl (installedRules S tbl modes) party
      leaking).run s)) :
    RepairInv S tbl modes ik z.2.transcript z.2.game ∧
      (NoAuth.DecapsGood (EpochRecord.toTranscript ∘ s.transcript) → z.2.bad = false →
        NoAuth.DecapsGood (EpochRecord.toTranscript ∘ z.2.transcript)) := by
  rcases mem_support_traceSend S.toRatcheted irl tbl (installedRules S tbl modes) hz with
    hz | ⟨⟨⟨r, rand⟩, T₂, bad'⟩, hw, -, hz⟩
  · rw [hz]
    exact ⟨h, fun hg _ => hg⟩
  rw [hz]
  dsimp only
  -- The control and pair invariants read only the shape of the game state: epochs, completed
  -- epochs, control positions, current game epochs, which keys exist, the allowed state pairs,
  -- and the epoch, type and well-formedness of each message.
  have hxfer : ∀ g g0 : GameState P (Root × MacKey),
      (∀ who, (g.stateAt who).epoch = (g0.stateAt who).epoch) →
      (∀ who, (g.stateAt who).completedEpoch = (g0.stateAt who).completedEpoch) →
      (∀ who, (g.stateAt who).controlPosition = (g0.stateAt who).controlPosition) →
      (∀ who, g.tcurAt who = g0.tcurAt who) →
      (∀ who t, g.keysAt who t = none ↔ g0.keysAt who t = none) →
      (∀ who, (∀ peer, AllowedStatePair (g.stateAt who) peer ↔
          AllowedStatePair (g0.stateAt who) peer) ∧
        (∀ peer, AllowedStatePair peer (g.stateAt who) ↔
          AllowedStatePair peer (g0.stateAt who))) →
      (∀ who n msg tsnd, g.messagesAt who n = some (msg, tsnd) →
        ∃ msg0, g0.messagesAt who n = some (msg0, tsnd) ∧ msg.epoch = msg0.epoch ∧
          msg.type = msg0.type ∧ msg.wellFormed = msg0.wellFormed) →
      ControlInv g0 → StatePairInv g0 → ControlInv g ∧ StatePairInv g := by
    intro g g0 hEp hCe hCp hTc hKy hAl hMs hC0 hP0
    have hpos : ∀ who, 0 < (g.stateAt who).epoch := fun who => by
      rw [hEp who]; exact hC0.epochKnowledge.keyPrefix.pos who
    have hkeys : ∀ who t, g.keysAt who t ≠ none ↔ 0 < t ∧ t ≤ (g.stateAt who).completedEpoch :=
      fun who t => by
        rw [ne_eq, hKy who t, ← ne_eq, hCe who]
        exact hC0.epochKnowledge.keyPrefix.keys who t
    have hel : ∀ who, (g.stateAt who).epoch ≤ (g.stateAt (!who)).completedEpoch + 1 :=
      fun who => by
        rw [hEp who, hCe (!who)]; exact hC0.epochKnowledge.epoch_le who
    have htl : ∀ who, g.tcurAt who ≤ (g.stateAt who).completedEpoch := fun who => by
      rw [hTc who, hCe who]; exact hC0.epochKnowledge.tcur_le who
    have hmsgs : ∀ who n msg tsnd, g.messagesAt who n = some (msg, tsnd) →
        msg.epoch ≤ (g.stateAt who).completedEpoch + 1 ∧
          msg.epoch ≤ (g.stateAt (!who)).completedEpoch + 1 ∧
          (msg.type = .ct2 → msg.epoch ≤ (g.stateAt who).completedEpoch) := by
      intro who n msg tsnd hm
      obtain ⟨msg0, h0, he, ht, -⟩ := hMs who n msg tsnd hm
      have := hC0.epochKnowledge.msgs who n msg0 tsnd h0
      rw [he, ht, hCe who, hCe (!who)]
      exact this
    have hrep : ∀ who n msg tsnd, g.messagesAt who n = some (msg, tsnd) →
        tsnd = msg.epoch - 1 := by
      intro who n msg tsnd hm
      obtain ⟨msg0, h0, he, -⟩ := hMs who n msg tsnd hm
      rw [he]
      exact hC0.recordedReport.report who n msg0 tsnd h0
    have hts : ∀ who, g.tcurAt who ≤ (g.stateAt who).epoch - 1 := fun who => by
      rw [hTc who, hEp who]; exact hC0.tcur_le_sub_one who
    have hroles : ∀ who, PartyControl who g := by
      intro who
      obtain ⟨hr, hl, hm⟩ := hC0.roles who
      refine ⟨?_, ?_, ?_⟩
      · rw [hCp who, hEp who]; exact hr
      · intro hpe
        rw [hEp (!who), hEp who] at hpe
        rw [hCp who]
        exact hl hpe
      · intro n msg tsnd hn
        obtain ⟨msg0, h0, he, ht, hw⟩ := hMs who n msg tsnd hn
        obtain ⟨h1, h2, h3, h4⟩ := hm n msg0 tsnd h0
        refine ⟨by rw [hw]; exact h1, by rw [he, hEp who]; exact h2, fun hx => ?_, ?_⟩
        · rw [ht, hCp who]
          exact h3 (by rw [← he, ← hEp who]; exact hx)
        · unfold MessageOwner at h4 ⊢
          rw [ht, he]
          exact h4
    have hpair : ∀ who, PairInv (g.stateAt who) (g.stateAt (!who)) := by
      intro who
      have h0 := hP0.pair who
      obtain ⟨hA1, -⟩ := hAl who
      obtain ⟨-, hB2⟩ := hAl (!who)
      refine ⟨fun h1 h2 => ?_, fun h3 => ?_⟩
      · have := h0.1 (by rw [← hEp who, ← hEp (!who)]; exact h1) (by rw [← hCp who]; exact h2)
        exact (hB2 _).mpr ((hA1 _).mpr this)
      · have := h0.2 (by rw [← hEp (!who), ← hEp who]; exact h3)
        exact ⟨by rw [hCp who]; exact this.1, by rw [hCp (!who)]; exact this.2⟩
    exact ⟨⟨⟨⟨hpos true, hpos false, fun t => hkeys true t, fun t => hkeys false t⟩, hel true,
        hel false, htl true, htl false, fun n msg tsnd hn => hmsgs true n msg tsnd hn,
        fun n msg tsnd hn => hmsgs false n msg tsnd hn⟩,
      ⟨fun n msg tsnd hn => hrep true n msg tsnd hn,
        fun n msg tsnd hn => hrep false n msg tsnd hn⟩, hts true, hts false, hroles⟩,
      ⟨hpair true, hpair false⟩⟩
  -- The successor of a send with a result `r` has the control and pair invariants of the
  -- successor of a send with a result `r0` of the same shape.
  have hxferR : ∀ r0 r : SendResult P (Root × MacKey),
      r.state.epoch = r0.state.epoch → r.state.completedEpoch = r0.state.completedEpoch →
      r.state.controlPosition = r0.state.controlPosition → r.sendingEpoch = r0.sendingEpoch →
      r.msg.epoch = r0.msg.epoch → r.msg.type = r0.msg.type →
      r.msg.wellFormed = r0.msg.wellFormed →
      (∀ who t, (sendSuccessor s.game party r).keysAt who t = none ↔
        (sendSuccessor s.game party r0).keysAt who t = none) →
      (∀ peer, AllowedStatePair r.state peer ↔ AllowedStatePair r0.state peer) →
      (∀ peer, AllowedStatePair peer r.state ↔ AllowedStatePair peer r0.state) →
      ControlInv (sendSuccessor s.game party r0) → StatePairInv (sendSuccessor s.game party r0) →
      ControlInv (sendSuccessor s.game party r) ∧ StatePairInv (sendSuccessor s.game party r) := by
    intro r0 r hEp hCe hCp hSe hMe hMt hMw hKy hAl1 hAl2
    refine hxfer _ _ ?_ ?_ ?_ ?_ hKy ?_ ?_
    · intro who
      simp only [stateAt_sendSuccessor]
      split_ifs
      · exact hEp
      · rfl
    · intro who
      simp only [stateAt_sendSuccessor]
      split_ifs
      · exact hCe
      · rfl
    · intro who
      simp only [stateAt_sendSuccessor]
      split_ifs
      · exact hCp
      · rfl
    · intro who
      cases party <;> cases who <;> first | rfl | exact hSe
    · intro who
      refine ⟨fun peer => ?_, fun peer => ?_⟩ <;>
        simp only [stateAt_sendSuccessor] <;> split_ifs <;>
        first | exact Iff.rfl | exact hAl1 peer | exact hAl2 peer
    · intro who n msg tsnd hm
      simp only [messagesAt_sendSuccessor] at hm ⊢
      split_ifs at hm ⊢ with hwho
      · by_cases hnew : n = s.game.countAt who + 1
        · subst hnew
          rw [Function.update_self] at hm ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
          exact ⟨r0.msg, by rw [hSe], hMe, hMt, hMw⟩
        · rw [Function.update_of_ne hnew] at hm ⊢
          exact ⟨msg, hm, rfl, rfl, rfl⟩
      · exact ⟨msg, hm, rfl, rfl, rfl⟩
  have hCPgen : ∀ r', r' ∈ support (send P S.toRatcheted (s.game.stateAt party)) →
      ControlInv (sendUpdate s.game party r') ∧ StatePairInv (sendUpdate s.game party r') := by
    intro r' hr'
    cases party
    · exact correctnessImpl_preserves_controlInv_statePairInv S.toRatcheted irl ($ᵗ P.EpochKey)
        (OSendB (Rho := Message P.Sym)) s.game ⟨h.control, h.statePair⟩ _
        ((mem_support_oracleSend_run_iff S.toRatcheted irl ($ᵗ P.EpochKey) s.game false _).2
          ⟨r', hr', rfl⟩)
    · exact correctnessImpl_preserves_controlInv_statePairInv S.toRatcheted irl ($ᵗ P.EpochKey)
        (OSendA (Rho := Message P.Sym)) s.game ⟨h.control, h.statePair⟩ _
        ((mem_support_oracleSend_run_iff S.toRatcheted irl ($ᵗ P.EpochKey) s.game true _).2
          ⟨r', hr', rfl⟩)
  obtain ⟨htcur, hkeys⟩ := h.control.send_prefix party
  cases hst : s.game.stateAt party with
  | keysUnsampled e a =>
      rw [hst] at htcur hkeys
      simp only [State.epoch] at htcur hkeys
      have hc0 : (s.transcript e).encaps1 = none := by
        have hL := h.local party
        rw [hst] at hL
        exact hL.2.2
      have hflagK : ∀ pk sk,
          (sendUpdate s.game party (keygenStep S.toRatcheted e a pk sk)).correct = true := by
        intro pk sk
        rw [sendUpdate_correct]
        simp only [keygenStep, Bool.and_eq_true]
        exact ⟨⟨h.correct, decide_eq_true htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
      obtain ⟨⟨pk0, sk0⟩, hk0⟩ := OracleComp.support_nonempty P.kem.keygen
      have hr0 : keygenStep S.toRatcheted e a pk0 sk0 ∈
          support (send P S.toRatcheted (s.game.stateAt party)) := by
        rw [hst, mem_support_send_iff]
        exact .keygen e a pk0 sk0 hk0
      obtain ⟨hC0, hP0⟩ := hCPgen _ hr0
      rw [sendUpdate_eq_successor_of_correct s.game party _ h.correct (hflagK pk0 sk0)]
        at hC0 hP0
      have hCPK : ∀ pk sk,
          ControlInv (sendSuccessor s.game party (keygenStep S.toRatcheted e a pk sk)) ∧
            StatePairInv (sendSuccessor s.game party (keygenStep S.toRatcheted e a pk sk)) :=
        fun pk sk => hxferR (keygenStep S.toRatcheted e a pk0 sk0)
          (keygenStep S.toRatcheted e a pk sk) rfl rfl rfl rfl rfl rfl rfl
          (fun who t => by simp [keysAt_sendSuccessor, keygenStep])
          (fun peer => by cases peer <;> exact Iff.rfl)
          (fun peer => by cases peer <;> exact Iff.rfl) hC0 hP0
      have hFinal : ∀ x : (P.PK × P.SK) × irl.KeygenRand,
          RepairInv S tbl modes ik
              (Function.update s.transcript e { (s.transcript e) with keypair := some x.1 })
              { sendUpdate s.game party (keygenStep S.toRatcheted e a x.1.1 x.1.2) with
                exposed := if leaking then s.game.exposed ∪
                  (exposureAt P irl (Root × MacKey)).rleak (State.keysUnsampled e a)
                    (SendRand.keygen x.2) else s.game.exposed } ∧
            (NoAuth.DecapsGood (EpochRecord.toTranscript ∘ s.transcript) →
              NoAuth.DecapsGood (EpochRecord.toTranscript ∘
                Function.update s.transcript e { (s.transcript e) with keypair := some x.1 })) := by
        intro x
        refine ⟨?_, fun hg => ?_⟩
        · rw [sendUpdate_eq_successor_of_correct s.game party _ h.correct (hflagK _ _)]
          exact RepairInv.setFlags (sampledSend_keygen_preserves h party hst x (hCPK _ _)) _ _
        · intro e' pk' sk' es ct1 key hk hc
          by_cases he : e' = e
          · subst e'
            simp [Function.comp_apply, EpochRecord.toTranscript, hc0] at hc
          · simp only [Function.comp_apply, EpochRecord.toTranscript,
              Function.update_of_ne he] at hk hc
            exact hg e' pk' sk' es ct1 key hk hc
      cases hkp : tbl.kp e with
      | none =>
          rw [sampledSend_eq_keygen S.toRatcheted irl tbl (installedRules S tbl modes) s party hst
            hkp, support_map] at hw
          obtain ⟨⟨⟨pk, sk⟩, rand₀⟩, hkr, heq⟩ := hw
          simp only [Prod.mk.injEq] at heq
          obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
          obtain ⟨hR, hD⟩ := hFinal ((pk, sk), rand₀)
          exact ⟨hR, fun hg _ => hD hg⟩
      | some x =>
          rw [sampledSend_eq_keygen_installed S.toRatcheted irl tbl (installedRules S tbl modes) s
            party hst hkp, mem_support_pure_iff] at hw
          simp only [Prod.mk.injEq] at hw
          obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hw
          obtain ⟨hR, hD⟩ := hFinal x
          exact ⟨hR, fun hg _ => hD hg⟩
  | headerReceived e a hdr dec =>
      rw [hst] at htcur hkeys
      simp only [State.epoch] at htcur hkeys
      obtain ⟨h1, h2, hpos0, hposP, hcross, hcrossP, hroles⟩ := h.pairBounds party
      obtain ⟨b, sk', vec, enc, hpeer⟩ :=
        PairInv.peer_of_headerReceived h1 h2 hpos0 hposP hcross hcrossP hroles hst
      have hLs := h.local party
      rw [hst] at hLs
      simp only [LocalPayloadInv] at hLs
      obtain ⟨-, -, pk, sk, hkpT, -, -⟩ := hLs
      have hkp : (s.transcript e).keypair = some (pk, sk) := hkpT
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
      have hflagE : ∀ (es : P.inc.St) (ct1 : P.inc.C₁) key p,
          (sendUpdate s.game party (encaps1Step e a hdr dec es ct1 key p)).correct = true := by
        intro es ct1 key p
        rw [sendUpdate_correct]
        simp only [encaps1Step, Bool.and_eq_true]
        exact ⟨⟨⟨⟨h.correct, decide_eq_true htcur⟩, by simp [hnone]⟩, by simp [hnone]⟩,
          SCKAScheme.knownPrefix_update_some (SCKAScheme.knownPrefix_eq_true hkeys) e _⟩
      obtain ⟨⟨es0, ct10, k0⟩, hek0⟩ := OracleComp.support_nonempty (P.inc.encaps1 hdr)
      have hr0 : encaps1Step e a hdr dec es0 ct10 (P.kdfOK k0 e)
          (S.toRatcheted.update a e (P.kdfOK k0 e)) ∈
          support (send P S.toRatcheted (s.game.stateAt party)) := by
        rw [hst, mem_support_send_iff]
        exact .encaps1 e a hdr dec es0 ct10 k0 hek0
      obtain ⟨hC0, hP0⟩ := hCPgen _ hr0
      rw [sendUpdate_eq_successor_of_correct s.game party _ h.correct (hflagE es0 ct10 _ _)]
        at hC0 hP0
      have hCPE : ∀ es ct1 key p,
          ControlInv (sendSuccessor s.game party (encaps1Step e a hdr dec es ct1 key p)) ∧
            StatePairInv (sendSuccessor s.game party (encaps1Step e a hdr dec es ct1 key p)) :=
        fun es ct1 key p => hxferR (encaps1Step e a hdr dec es0 ct10 (P.kdfOK k0 e)
          (S.toRatcheted.update a e (P.kdfOK k0 e))) (encaps1Step e a hdr dec es ct1 key p)
          rfl rfl rfl rfl rfl rfl rfl
          (fun who t => by
            simp only [keysAt_sendSuccessor, encaps1Step]
            split_ifs <;> by_cases ht : t = e <;> simp [ht])
          (fun peer => by cases peer <;> exact Iff.rfl)
          (fun peer => by cases peer <;> exact Iff.rfl) hC0 hP0
      have hFinal : ∀ (x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand) key p,
          (tbl.key e = some key ∨
            (tbl.key e = none ∧ (modes.key e = .real → key = P.kdfOK x.1.2.2 e))) →
          (tbl.pair e = some p ∨
            (tbl.pair e = none ∧ (modes.pair e = .real → p = S.F e a.1 key))) →
          RepairInv S tbl modes ik (Function.update s.transcript e
              { (s.transcript e) with encaps1 := some x.1, key := some key, pair := some p })
            { sendUpdate s.game party (encaps1Step e a hdr dec x.1.1 x.1.2.1 key p) with
              exposed := if leaking then s.game.exposed ∪
                (exposureAt P irl (Root × MacKey)).rleak (State.headerReceived e a hdr dec)
                  (SendRand.encaps1 x.2) else s.game.exposed } ∧
            (NoAuth.DecapsGood (EpochRecord.toTranscript ∘ s.transcript) →
              encaps1Bad s e x.1 = false →
              NoAuth.DecapsGood (EpochRecord.toTranscript ∘ Function.update s.transcript e
                { (s.transcript e) with
                  encaps1 := some x.1, key := some key, pair := some p })) := by
        intro x key p hk hp
        obtain ⟨⟨es, ct1, k⟩, rand₀⟩ := x
        dsimp only at hk hp ⊢
        refine ⟨?_, fun hg hbad => ?_⟩
        · rw [sendUpdate_eq_successor_of_correct s.game party _ h.correct (hflagE _ _ _ _)]
          exact RepairInv.setFlags
            (sampledSend_encaps1_preserves h party hst ((es, ct1, k), rand₀) hk hp
              (hCPE _ _ _ _)) _ _
        · simp only [encaps1Bad, hkp, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            not_not] at hbad
          obtain ⟨-, hdk⟩ := hbad
          intro e' pk' sk' es' ct1' key' hk' hc'
          by_cases he : e' = e
          · subst e'
            simp only [Function.comp_apply, EpochRecord.toTranscript, Function.update_self]
              at hk' hc'
            rw [hkp] at hk'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk')
            obtain ⟨rfl, rfl, rfl⟩ : es = es' ∧ ct1 = ct1' ∧ k = key' := by simpa using hc'
            exact hdk
          · simp only [Function.comp_apply, EpochRecord.toTranscript,
              Function.update_of_ne he] at hk' hc'
            exact hg e' pk' sk' es' ct1' key' hk' hc'
      cases hec : tbl.ec e with
      | none =>
          rw [sampledSend_eq_encaps1 S.toRatcheted irl tbl (installedRules S tbl modes) s party hst
            hec] at hw
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hw
          obtain ⟨x, -, key, hkeyS, pair, hpairS, hEq⟩ := hw
          simp only [Prod.mk.injEq] at hEq
          obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hEq
          exact hFinal x key pair (installedRules_key_mem S tbl modes hkeyS)
            (installedRules_pair_mem S tbl modes hpairS)
      | some x =>
          rw [sampledSend_eq_encaps1_installed S.toRatcheted irl tbl (installedRules S tbl modes) s
            party hst hec] at hw
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hw
          obtain ⟨key, hkeyS, pair, hpairS, hEq⟩ := hw
          simp only [Prod.mk.injEq] at hEq
          obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hEq
          exact hFinal x key pair (installedRules_key_mem S tbl modes hkeyS)
            (installedRules_pair_mem S tbl modes hpairS)
  | _ =>
      have hsteady : (s.game.stateAt party).SendsNoSample := by rw [hst]; trivial
      rw [sampledSend_of_noSample S.toRatcheted irl tbl (installedRules S tbl modes) s party
        (by simp [hst]) (by simp [hst]), support_map] at hw
      obtain ⟨out, hout, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨hrEq, -⟩, hTEq, hBEq⟩ := heq
      rw [hrEq] at hout
      subst T₂
      subst bad'
      have hr : r ∈ support (send P S.toRatcheted (s.game.stateAt party)) := hout
      have hedge := (mem_support_send_iff S.toRatcheted).mp hr
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
      exact ⟨RepairInv.setFlags (sendSteady_preserves h party hr hsteady hCP) _ _,
        fun hg _ => hg⟩

end MLKEMBraid.Auth
