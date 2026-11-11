/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness
public import SecureMessaging.KEM.IncrementalKEM.FromMLKEM.Equivalence
public import SecureMessaging.SCKA.SPQR.Correctness.Relation
public import SecureMessaging.SCKA.SPQR.Instances

/-!
# SPQR correctness

Let:

* `Π := scheme P auth sampleInitKey` be the SPQR SCKA scheme, where `P` holds the incremental
  KEM with explicit coins, the epoch-key derivation and the four erasure-coded streams, `auth` is
  the authenticator, and `sampleInitKey` samples the initial key;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` be its correctness game for an adversary `Adv`;
* `ε := P.det.toKEM.correctnessError ProbCompRuntime.probComp` be the correctness error of the
  underlying KEM.

The game is the one of `Braid.Correctness`. The adversary chooses which party sends and which
recorded message each party receives, so it may omit, delay, reorder, duplicate or replay
messages. The game keeps a correctness flag, which becomes false when a receive refuses a recorded
message or when a check on the reported epochs and the output keys fails.

## Main results

If the four stream decoders of `P` are sound for their erasure codes and `Adv` makes at most `q`
send queries, then

* `correctness_error_le`: `1 - Pr[G(Adv) = true] ≤ q · ε`;
* `v1Scheme_correctness_error_le`: the same bound for `v1Scheme`, whose four SPQR Reed-Solomon
  codes are correct, with `ε` the correctness error of ML-KEM-768.

This is the bound of `Braid.correctness_error_le`, for the SPQR scheme.

## Proof

The proof translates SPQR game states into Braid game states (`GameState.toBraid`) and takes
the invariant `CorrectnessInv` and the potential `failurePotential` of the Braid proof on the
translated state. The SPQR invariant adds
`Ct1AckInv`. Then `SCKAScheme.correctness_error_le_of_potential` gives the bound, once each query
is shown to preserve the invariant and to raise the expected potential by at most `ε` for a send
and not at all otherwise:

* if the correctness flag is already false, it stays false and the potential stays `1`;
* a query that delivers no message in `RecvDivergence` is the Braid query on the translated state
  (`sckaCorrectnessImpl_run_toBraid`), so the Braid lemmas apply;
* otherwise the query delivers a plain vector chunk to a party in `ct1Acknowledged`
  (`DeliveryDivergence.ct1Acknowledged_ek`), and it is the Braid query on the translation in which
  that record is an acknowledging vector chunk (`sckaCorrectnessImpl_run_toBraidAck`).

The relabelling in the last case changes neither the invariant nor the potential. The Braid
invariant sees the type of a recorded
vector chunk only through the step its sender must have reached. The sender is in `ct1Received`,
which is late enough for an acknowledging chunk. The potential does not read recorded messages.

## References

The protocol is Signal's SparsePostQuantumRatchet at release v1.6.0 (commit `06959b47`), which
implements *The ML-KEM Braid Protocol* (https://signal.org/docs/specifications/mlkembraid/),
sections 2.3 to 2.6. The correctness game follows Definition 3.1, Figure 1, and Appendix B.1 of:

- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267
-/

@[expose] public section

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic
open ErasureCodePayload.Streaming

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)

/-! ### Relabelling a recorded vector chunk -/

/-- An entry of an updated message table is the new entry or an entry of the old table. -/
private theorem update_eq_some {f : ℕ → Option (Braid.Message P.Sym × ℕ)} {n k : ℕ}
    {e : Braid.Message P.Sym × ℕ} {m : Braid.Message P.Sym} {t : ℕ}
    (h : Function.update f n (some e) k = some (m, t)) : (m, t) = e ∨ f k = some (m, t) := by
  by_cases hkn : k = n
  · subst hkn
    simp only [Function.update_self, Option.some.injEq] at h
    exact Or.inl h.symm
  · rw [Function.update_of_ne hkn] at h
    exact Or.inr h

/-- Changing the type of a recorded vector chunk to `ek` or `ekCt1Ack` keeps transcript
consistency, provided the sender's state allows the new type. -/
private theorem transcriptConsistent_retype {ik : InitKey}
    {T : ℕ → Braid.EpochTranscript P.toBraid} {s : Braid.GameState P.toBraid AuthState}
    (hT : Braid.TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    {msg : Braid.Message P.Sym} {tsnd : ℕ} (hmsg : s.messagesAt party n = some (msg, tsnd))
    (hty : msg.type = .ek ∨ msg.type = .ekCt1Ack) (ty : Braid.MessageType)
    (hty' : ty = .ek ∨ ty = .ekCt1Ack)
    (hctl : Braid.MessageControl party (s.stateAt party) { msg with type := ty }) :
    Braid.TranscriptConsistent auth ik T
      (if party then
        { s with msgA := Function.update s.msgA n (some ({ msg with type := ty }, tsnd)) }
      else
        { s with msgB := Function.update s.msgB n (some ({ msg with type := ty }, tsnd)) }) := by
  have hpay : Braid.MessagePayloadInv auth ik T { msg with type := ty } := by
    have h := hT.messages party n msg tsnd (by cases party <;> exact hmsg)
    rcases hty with h1 | h1 <;> rcases hty' with rfl | rfl <;>
      simpa only [Braid.MessagePayloadInv, h1] using h
  have hEK := hT.control.epochKnowledge
  have hRR := hT.control.recordedReport
  have hbound := hEK.msgs party n msg tsnd hmsg
  have hrep := hRR.report party n msg tsnd hmsg
  have hct2 : ty ≠ .ct2 := by rcases hty' with rfl | rfl <;> simp
  have hKP : Braid.KeyPrefixInv
      (if party then
        { s with msgA := Function.update s.msgA n (some ({ msg with type := ty }, tsnd)) }
      else
        { s with msgB := Function.update s.msgB n (some ({ msg with type := ty }, tsnd)) }) := by
    cases party <;>
      exact ⟨hEK.keyPrefix.posA, hEK.keyPrefix.posB, hEK.keyPrefix.prefixA,
        hEK.keyPrefix.prefixB⟩
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hKP ⊢
    have hmsgB : ∀ k m t, Function.update s.msgB n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → m.epoch ≤ s.stB.completedEpoch + 1 ∧ m.epoch ≤ s.stA.completedEpoch + 1 ∧
          (m.type = .ct2 → m.epoch ≤ s.stB.completedEpoch) := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact ⟨hbound.1, hbound.2.1, fun h => absurd h hct2⟩
      · exact hEK.msgB k m t hk
    have hrepB : ∀ k m t, Function.update s.msgB n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → t = m.epoch - 1 := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact hrep
      · exact hRR.msgB k m t hk
    have hctlB : ∀ k m t, Function.update s.msgB n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → Braid.MessageControl false s.stB m := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact hctl
      · exact (hT.control.roles false).2.2 k m t hk
    have hpayB : ∀ k m t, Function.update s.msgB n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → Braid.MessagePayloadInv auth ik T m := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact hpay
      · exact hT.messages false k m t hk
    exact { hT with
      control := { hT.control with
        epochKnowledge := { hEK with keyPrefix := hKP, msgB := hmsgB }
        recordedReport := { hRR with msgB := hrepB }
        roles := fun p => by
          cases p
          · exact ⟨(hT.control.roles false).1, (hT.control.roles false).2.1, hctlB⟩
          · exact hT.control.roles true }
      messages := fun p k m t hk => by
        cases p
        · exact hpayB k m t hk
        · exact hT.messages true k m t hk }
  · simp only [↓reduceIte] at hKP ⊢
    have hmsgA : ∀ k m t, Function.update s.msgA n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → m.epoch ≤ s.stA.completedEpoch + 1 ∧ m.epoch ≤ s.stB.completedEpoch + 1 ∧
          (m.type = .ct2 → m.epoch ≤ s.stA.completedEpoch) := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact ⟨hbound.1, hbound.2.1, fun h => absurd h hct2⟩
      · exact hEK.msgA k m t hk
    have hrepA : ∀ k m t, Function.update s.msgA n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → t = m.epoch - 1 := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact hrep
      · exact hRR.msgA k m t hk
    have hctlA : ∀ k m t, Function.update s.msgA n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → Braid.MessageControl true s.stA m := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact hctl
      · exact (hT.control.roles true).2.2 k m t hk
    have hpayA : ∀ k m t, Function.update s.msgA n (some ({ msg with type := ty }, tsnd)) k =
        some (m, t) → Braid.MessagePayloadInv auth ik T m := by
      intro k m t hk
      rcases update_eq_some hk with he | hk
      · cases he
        exact hpay
      · exact hT.messages true k m t hk
    exact { hT with
      control := { hT.control with
        epochKnowledge := { hEK with keyPrefix := hKP, msgA := hmsgA }
        recordedReport := { hRR with msgA := hrepA }
        roles := fun p => by
          cases p
          · exact hT.control.roles false
          · exact ⟨(hT.control.roles true).1, (hT.control.roles true).2.1, hctlA⟩ }
      messages := fun p k m t hk => by
        cases p
        · exact hT.messages false k m t hk
        · exact hpayA k m t hk }

/-- In a consistent state, the sender of a plain vector chunk recorded at the epoch of a receiver in
`ct1Acknowledged` is in `ct1Received` at that epoch, so it allows the chunk to be an acknowledging
vector chunk. -/
private theorem messageControl_ekCt1Ack {ik : InitKey}
    {T : ℕ → Braid.EpochTranscript P.toBraid}
    {s : Braid.GameState P.toBraid AuthState}
    (hT : Braid.TranscriptConsistent auth ik T s)
    (party : Bool) {n e : ℕ} {a : AuthState} {hdr : P.det.PKheader} {es : P.det.St}
    {ct1 : P.det.C₁} {dec : P.decEk.D} {chunk : ℕ × P.Sym} {tsnd : ℕ}
    (hst : s.stateAt party = .ct1Acknowledged e a hdr es ct1 dec)
    (hmsg : s.messagesAt (!party) n = some (⟨e, .ek, some chunk⟩, tsnd)) :
    Braid.MessageControl (!party) (s.stateAt (!party)) ⟨e, .ekCt1Ack, some chunk⟩ := by
  obtain ⟨-, hle, -, hown⟩ := (hT.control.roles (!party)).2.2 n _ tsnd hmsg
  obtain ⟨h, h', -, -, -, hcrossP, hroles⟩ :=
    Braid.TranscriptInv.pairBounds (P := P.toBraid) auth hT party
  rw [hst] at h h' hcrossP hroles
  refine ⟨rfl, hle, fun hep => ?_, by simpa [Braid.MessageOwner] using hown⟩
  simp only at hle hep
  generalize s.stateAt (!party) = peer at h h' hcrossP hroles hle hep
  cases peer <;>
    simp_all [Braid.PairInv, Braid.AllowedStatePair, Braid.State.controlPosition,
      Braid.State.epoch, Braid.State.completedEpoch, Braid.MessageType.sendStep]

variable [DecidableEq P.EpochKey]
  (sampleInitKey : ProbComp InitKey)

omit [DecidableEq P.EpochKey] in
/-- If the translation of a state is consistent with a transcript, so is its relabelling at a plain
vector chunk delivered to a party in `ct1Acknowledged`. -/
private theorem transcriptConsistent_toBraidAck {ik : InitKey}
    {T : ℕ → Braid.EpochTranscript P.toBraid} {s : GameState P AuthState}
    (hT : Braid.TranscriptConsistent auth ik T s.toBraid) (party : Bool) (n : ℕ)
    {core : CtSender.Ct1Sent P AuthState} {dec : P.decEk.D}
    {chunk : ℕ × P.Sym} {tsnd : ℕ}
    (hst : (if party then s.stA else s.stB) = .ct1Acknowledged core dec)
    (hmsg : (if party then s.msgB else s.msgA) n = some (⟨core.ep, .ek chunk⟩, tsnd)) :
    Braid.TranscriptConsistent auth ik T (s.toBraidAck party n) := by
  have hmsg' : s.toBraid.messagesAt (!party) n =
      some (⟨core.ep, .ek, some chunk⟩, tsnd) := by
    cases party <;>
      simpa [Braid.GameState.messagesAt, GameState.toBraid,
        Chunked.Message.toBraid] using congrArg (Option.map fun e => (e.1.toBraid, e.2))
          hmsg
  have hst' :
      s.toBraid.stateAt party = PartyState.toBraid (.ct1Acknowledged core dec) := by
    cases party <;>
      exact congrArg PartyState.toBraid (by simpa using hst)
  have hctl := messageControl_ekCt1Ack auth hT party hst' hmsg'
  have h := transcriptConsistent_retype auth hT (!party) n hmsg' (Or.inl rfl) .ekCt1Ack
    (Or.inr rfl) hctl
  cases party
  · have hraw : s.toBraid.msgA n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := hmsg'
    simpa [GameState.toBraidAck, hraw] using h
  · have hraw : s.toBraid.msgB n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := hmsg'
    simpa [GameState.toBraidAck, hraw] using h

omit [DecidableEq P.EpochKey] in
/-- After a query of the relabelled translation, restoring the plain vector chunk keeps the Braid
invariant. -/
private theorem correctnessInv_restore {ik : InitKey} (party : Bool) (n : ℕ)
    {s : GameState P AuthState} {core : CtSender.Ct1Sent P AuthState} {chunk : ℕ × P.Sym}
    {tsnd : ℕ} (hmsg : (if party then s.msgB else s.msgA) n = some (⟨core.ep, .ek chunk⟩, tsnd))
    {z : Braid.GameState P.toBraid AuthState}
    (hmsgs : z.messagesAt (!party) = (s.toBraidAck party n).messagesAt (!party))
    (hz : Braid.CorrectnessInv auth ik z) :
    Braid.CorrectnessInv auth ik
      (if party then { z with msgB := s.toBraid.msgB }
        else { z with msgA := s.toBraid.msgA }) := by
  rcases hz with hzf | ⟨T, hT⟩
  · exact Or.inl (by cases party <;> exact hzf)
  refine Or.inr ⟨T, ?_⟩
  have hmsgF : s.toBraid.messagesAt (!party) n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := by
    cases party <;>
      simpa [Braid.GameState.messagesAt, GameState.toBraid,
        Chunked.Message.toBraid] using congrArg (Option.map fun e => (e.1.toBraid, e.2))
          hmsg
  have hmsgZ : z.messagesAt (!party) n = some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd) := by
    rw [hmsgs]
    cases party
    · have hraw : s.toBraid.msgA n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := hmsgF
      simp [GameState.toBraidAck, Braid.GameState.messagesAt, hraw]
    · have hraw : s.toBraid.msgB n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := hmsgF
      simp [GameState.toBraidAck, Braid.GameState.messagesAt, hraw]
  obtain ⟨hwf, hle, hstep, hown⟩ := (hT.control.roles (!party)).2.2 n _ tsnd hmsgZ
  have hctl : Braid.MessageControl (!party) (z.stateAt (!party))
      { (⟨core.ep, .ekCt1Ack, some chunk⟩ : Braid.Message P.Sym) with type := .ek } :=
    ⟨rfl, hle, fun h => (hstep h).trans' (by simp [Braid.MessageType.sendStep]),
      by simpa [Braid.MessageOwner] using hown⟩
  have h := transcriptConsistent_retype auth hT (!party) n hmsgZ (Or.inr rfl) .ek (Or.inl rfl) hctl
  -- Restoring the record gives back the message table of the translation.
  have hrestore : ∀ (f : ℕ → Option (Braid.Message P.Sym × ℕ)),
      f n = some (⟨core.ep, .ek, some chunk⟩, tsnd) →
      Function.update (Function.update f n (some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd))) n
        (some (⟨core.ep, .ek, some chunk⟩, tsnd)) = f := by
    intro f hf
    rw [Function.update_idem, ← hf, Function.update_eq_self]
  cases party
  · have hraw : s.toBraid.msgA n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := hmsgF
    have hz' : z.msgA = Function.update s.toBraid.msgA n
        (some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd)) := by
      simpa [GameState.toBraidAck, Braid.GameState.messagesAt, hraw] using hmsgs
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true] at h ⊢
    rw [hz', hrestore _ hraw] at h
    exact h
  · have hraw : s.toBraid.msgB n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := hmsgF
    have hz' : z.msgB = Function.update s.toBraid.msgB n
        (some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd)) := by
      simpa [GameState.toBraidAck, Braid.GameState.messagesAt, hraw] using hmsgs
    simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true] at h ⊢
    rw [hz', hrestore _ hraw] at h
    exact h

/-- A receive query of the Braid game keeps both message tables. -/
private theorem messagesAt_of_mem_support_recv {s : Braid.GameState P.toBraid AuthState}
    (party : Bool) (n : ℕ)
    {z : (SCKAScheme.sckaCorrectnessSpec (Braid.Message P.Sym)).Range
        (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
          else SCKAScheme.sckaCorrectnessSpec.ORecvB n) × Braid.GameState P.toBraid AuthState}
    (hz : z ∈ support ((SCKAScheme.sckaCorrectnessImpl
      (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
      (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
        else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s))
    (who : Bool) : z.2.messagesAt who = s.messagesAt who := by
  cases party
  · rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, keyOpt, -, -, -, -, rfl⟩
    · rfl
    · cases who <;> rfl
    · rcases keyOpt with _ | ⟨tI, key⟩ <;> cases who <;> rfl
  · rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, keyOpt, -, -, -, -, rfl⟩
    · rfl
    · cases who <;> rfl
    · rcases keyOpt with _ | ⟨tI, key⟩ <;> cases who <;> rfl

/-! ### Preservation and drift -/

/-- With sound stream decoders, every query of the SPQR correctness game preserves the Braid
invariant on the translated state together with `Ct1AckInv`. -/
-- ANCHOR: SPQR_correctnessImpl_preserves_correctnessInv
theorem correctnessImpl_preserves_correctnessInv
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (ik : InitKey) :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey))
      (fun s : GameState P AuthState =>
        Braid.CorrectnessInv auth ik s.toBraid ∧ Ct1AckInv s)
-- ANCHOR_END: SPQR_correctnessImpl_preserves_correctnessInv
    := by
  intro t s ⟨hs, hack⟩ z hz
  refine ⟨?_, sckaCorrectnessImpl_preserves_ct1AckInv auth sampleInitKey t s hack z hz⟩
  have hbraid := Braid.correctnessImpl_preserves_correctnessInv (P := P.toBraid) auth
    P.det.toRandLeak sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound ik
  rcases hs with hsf | ⟨T, hT⟩
  · exact Or.inl (SCKAScheme.sckaCorrectnessImpl_preserves_correct_eq_false _ t s hsf z hz)
  by_cases hdiv : DeliveryDivergence s t
  · obtain ⟨party, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩ :=
      DeliveryDivergence.ct1Acknowledged_ek hT.control hT.statePair hack hdiv
    have hmem : GameState.toBraid z.2 ∈ support ((fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey)
          (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
            else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ hz
    rw [sckaCorrectnessImpl_run_toBraidAck auth sampleInitKey s party n core dec chunk
      tsnd hst hmsg, support_map] at hmem
    obtain ⟨z', hz', hzz⟩ := hmem
    have hAck := hbraid _ _
      (Or.inr ⟨T, transcriptConsistent_toBraidAck auth hT party n hst hmsg⟩) z' hz'
    rw [← hzz]
    exact correctnessInv_restore auth party n hmsg
      (messagesAt_of_mem_support_recv auth sampleInitKey party n hz' (!party)) hAck
  · have hmem : GameState.toBraid z.2 ∈ support ((fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ hz
    rw [sckaCorrectnessImpl_run_toBraid auth sampleInitKey s t hdiv, support_map] at hmem
    obtain ⟨z', hz', hzz⟩ := hmem
    rw [← hzz]
    exact hbraid _ _ (Or.inr ⟨T, hT⟩) z' hz'

/-- With sound stream decoders, one query of the SPQR correctness game raises the expected failure
potential of the translated state by at most the KEM correctness error for a send query, and not
at all for other queries. -/
-- ANCHOR: SPQR_wp_failurePotential_query_le
theorem wp_failurePotential_query_le [DecidableEq P.K]
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (ik : InitKey)
    (t : (SCKAScheme.sckaCorrectnessSpec (Chunked.Message P.Sym)).Domain)
    (s : GameState P AuthState)
    (hs : Braid.CorrectnessInv auth ik s.toBraid) (hack : Ct1AckInv s) :
    wp ((SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s)
        (fun z => Braid.failurePotential (GameState.toBraid z.2)) ≤
      Braid.failurePotential s.toBraid +
        if SCKAScheme.isSendQuery (Rho := Chunked.Message P.Sym) t
        then P.det.toKEM.correctnessError ProbCompRuntime.probComp else 0
-- ANCHOR_END: SPQR_wp_failurePotential_query_le
    := by
  have hbraid := Braid.wp_failurePotential_query_le (P := P.toBraid) auth P.det.toRandLeak
    sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound ik
  rcases hs with hsf | ⟨T, hT⟩
  · -- A false flag stays false, and the potential stays `1`.
    have hsf' : s.correct = false := hsf
    have h1 : Braid.failurePotential s.toBraid = 1 := by
      simp [Braid.failurePotential, GameState.toBraid, hsf']
    rw [h1]
    refine le_trans (wp_le_const_of_support _ fun z hz => ?_) le_self_add
    have hzf := SCKAScheme.sckaCorrectnessImpl_preserves_correct_eq_false _ t s hsf z hz
    simp [Braid.failurePotential, GameState.toBraid, hzf]
  by_cases hdiv : DeliveryDivergence s t
  · obtain ⟨party, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩ :=
      DeliveryDivergence.ct1Acknowledged_ek hT.control hT.statePair hack hdiv
    have hAck : Braid.CorrectnessInv auth ik (s.toBraidAck party n) :=
      Or.inr ⟨T, transcriptConsistent_toBraidAck auth hT party n hst hmsg⟩
    calc wp ((SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey)
            (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
              else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s)
          (fun z => Braid.failurePotential (GameState.toBraid z.2))
        = wp ((fun z => GameState.toBraid z.2) <$>
            (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey)
              (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
                else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s)
            Braid.failurePotential := by rw [wp_map]; rfl
      _ = wp ((SCKAScheme.sckaCorrectnessImpl
            (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
            (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
              else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run (s.toBraidAck party n))
            (fun z => Braid.failurePotential z.2) := by
          rw [sckaCorrectnessImpl_run_toBraidAck auth sampleInitKey s party n core dec
            chunk tsnd hst hmsg, wp_map]
          congr 1
          funext z
          cases party <;> rfl
      _ ≤ Braid.failurePotential (s.toBraidAck party n) +
            if SCKAScheme.isSendQuery (Rho := Braid.Message P.Sym)
              (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
                else SCKAScheme.sckaCorrectnessSpec.ORecvB n)
            then P.det.toKEM.correctnessError ProbCompRuntime.probComp else 0 :=
          hbraid _ _ hAck
      _ = _ := by cases party <;> rfl
  · calc wp ((SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s)
          (fun z => Braid.failurePotential (GameState.toBraid z.2))
        = wp ((fun z => GameState.toBraid z.2) <$>
            (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s)
            Braid.failurePotential := by rw [wp_map]; rfl
      _ = wp ((SCKAScheme.sckaCorrectnessImpl
            (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) t).run
            s.toBraid) (fun z => Braid.failurePotential z.2) := by
          rw [sckaCorrectnessImpl_run_toBraid auth sampleInitKey s t hdiv, wp_map]
          rfl
      _ ≤ Braid.failurePotential s.toBraid +
            if SCKAScheme.isSendQuery (Rho := Braid.Message P.Sym) t
            then P.det.toKEM.correctnessError ProbCompRuntime.probComp else 0 :=
          hbraid t _ (Or.inr ⟨T, hT⟩)
      _ = _ := by rcases t with ((((n | u) | u) | n) | n) <;> rfl

end SPQR

/-! ### The correctness bound -/

namespace SPQR

open Chunked

/-- With sound stream decoders, every adversary making at most `q` sends across both parties causes
a false correctness flag with probability at most `q` times the KEM correctness error. -/
-- ANCHOR: SPQR_correctness_error_le
theorem correctness_error_le
    (P : SPQR.Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (sampleInitKey : ProbComp InitKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr)
    (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1)
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Chunked.Message P.Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr{let x ← SCKAScheme.correctnessExp (scheme P auth sampleInitKey) adv}[x = true] ≤
      (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: SPQR_correctness_error_le
    := by
  refine SCKAScheme.correctness_error_le_of_potential (scheme P auth sampleInitKey)
    (fun ik s => Braid.CorrectnessInv auth ik (GameState.toBraid s) ∧ Ct1AckInv s)
    (fun s => Braid.failurePotential (GameState.toBraid s)) _ ?_ ?_
    (correctnessImpl_preserves_correctnessInv auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound)
    (fun ik t s hs => wp_failurePotential_query_le auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound ik t s hs.1 hs.2) adv q hq
  · intro s hs
    simp [Braid.failurePotential, GameState.toBraid, hs]
  · intro ik _ stA hA stB hB
    simp only [scheme, mem_support_pure_iff] at hA hB
    subst hA hB
    refine ⟨⟨Or.inr ⟨_, Braid.transcriptConsistent_initGameState (P := P.toBraid) auth ik⟩,
      ?_⟩, ?_⟩
    · intro party n msg tsnd h
      cases party <;> simp [SCKAScheme.initGameState] at h
    · change Braid.failurePotential
        (SCKAScheme.initGameState (Braid.initA P.toBraid auth ik)
          (Braid.initB P.toBraid auth ik)) = 0
      simp [Braid.failurePotential, Braid.currentEpochFailure,
        Braid.pairFailure, SCKAScheme.initGameState, Braid.initA, Braid.initB,
        Braid.State.controlPosition, Braid.State.epoch]

open ErasureCode.SPQRReedSolomon (Chunk GF16 erasureCode_correct) in
/-- The bound of `correctness_error_le` for `v1Scheme`. The four SPQR Reed-Solomon codes are
correct, and `ε` is the correctness error of ML-KEM-768. -/
-- ANCHOR: SPQR_v1Scheme_correctness_error_le
theorem v1Scheme_correctness_error_le {InitKey AuthState EpochKey Mac : Type}
    [DecidableEq EpochKey]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (serializeHdr : v1Incremental.PKheader × Mac → Fin 3 → Chunk GF16)
    (parseHdr : (Fin 3 → Chunk GF16) → Option (v1Incremental.PKheader × Mac))
    (parseHdr_serializeHdr : ∀ payload, parseHdr (serializeHdr payload) = some payload)
    (serializeEk : v1Incremental.PKvector → Fin 36 → Chunk GF16)
    (parseEk : (Fin 36 → Chunk GF16) → Option v1Incremental.PKvector)
    (parseEk_serializeEk : ∀ payload, parseEk (serializeEk payload) = some payload)
    (serializeCt1 : v1Incremental.C₁ → Fin 30 → Chunk GF16)
    (parseCt1 : (Fin 30 → Chunk GF16) → Option v1Incremental.C₁)
    (parseCt1_serializeCt1 : ∀ payload, parseCt1 (serializeCt1 payload) = some payload)
    (serializeCt2 : v1Incremental.C₂ × Mac → Fin 5 → Chunk GF16)
    (parseCt2 : (Fin 5 → Chunk GF16) → Option (v1Incremental.C₂ × Mac))
    (parseCt2_serializeCt2 : ∀ payload, parseCt2 (serializeCt2 payload) = some payload)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState
      v1Incremental.PKheader (v1Incremental.C₁ × v1Incremental.C₂) Mac)
    (sampleInitKey : ProbComp InitKey)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Chunked.Message (Chunk GF16)))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr{let x ← (SCKAScheme.correctnessExp
        (v1Scheme kdfOK serializeHdr parseHdr parseHdr_serializeHdr serializeEk parseEk
          parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1 serializeCt2 parseCt2
          parseCt2_serializeCt2 auth sampleInitKey) adv)}[x = true] ≤
      (q : ℝ≥0∞) * MLKEM.mlkem768Scheme.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: SPQR_v1Scheme_correctness_error_le
    := by
  let P₀ := v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr serializeEk parseEk
    parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1 serializeCt2 parseCt2
    parseCt2_serializeCt2
  let : DecidableEq P₀.K := by
    change DecidableEq MLKEM.SharedSecret
    infer_instance
  let : DecidableEq P₀.EpochKey := by
    change DecidableEq EpochKey
    infer_instance
  let : DecidableEq P₀.Sym := by
    change DecidableEq (Chunk GF16)
    infer_instance
  have hε : v1Det.toKEM.correctnessError ProbCompRuntime.probComp =
      MLKEM.mlkem768Scheme.correctnessError ProbCompRuntime.probComp :=
    MLKEM.mlkemIncrementalDet_correctnessError _ _ _
  rw [← hε]
  exact correctness_error_le P₀ auth sampleInitKey
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 3 (by norm_num) (by norm_num)))
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 36 (by norm_num) (by norm_num)))
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 30 (by norm_num) (by norm_num)))
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 5 (by norm_num) (by norm_num))) adv q hq

end SPQR
