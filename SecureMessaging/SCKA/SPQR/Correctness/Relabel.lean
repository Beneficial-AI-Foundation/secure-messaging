/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Correctness.Relation

/-!
# Relabelling a recorded vector chunk

Let `s` be an SPQR game state in which `party` is in `ct1Acknowledged` and its peer has recorded a
plain vector chunk `n` of that epoch. `s.toBraidAck party n` is the translation of `s` in which the
record `n` is an acknowledging vector chunk (`SPQR.Correctness.Relation`). The two lemmas of this
module show that the relabelling keeps the transcript invariant `Braid.TranscriptInv D` for every
condition `D`, and so the invariant of the Braid correctness proof:

* `transcriptInv_toBraidAck`: if the translation of `s` satisfies `TranscriptInv D` for a
  transcript, so does `s.toBraidAck party n`;
* `transcriptInv_restore`: after a Braid step from `s.toBraidAck party n` that keeps the recorded
  messages of the peer, restoring the plain vector chunk keeps `TranscriptInv D`;
  `correctnessInv_restore` is the same statement for `Braid.CorrectnessInv`.

The Braid invariant sees the type of a recorded vector chunk only through the step its sender must
have reached. The sender is in `ct1Received`, which is late enough for an acknowledging chunk.
-/

@[expose] public section

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
  {D : ℕ → P.toBraid.PK → P.toBraid.SK → P.toBraid.inc.St → P.toBraid.inc.C₁ → P.toBraid.K → Prop}

/-- If the translation of a state satisfies `TranscriptInv D` for a transcript, so does its
relabelling at a plain vector chunk delivered to a party in `ct1Acknowledged`. -/
theorem transcriptInv_toBraidAck {ik : InitKey}
    {T : ℕ → Braid.EpochTranscript P.toBraid} {s : GameState P AuthState}
    (hT : Braid.TranscriptInv auth D ik T s.toBraid) (party : Bool) (n : ℕ)
    {core : CtSender.Ct1Sent P AuthState} {dec : P.decEk.D}
    {chunk : ℕ × P.Sym} {tsnd : ℕ}
    (hst : s.stateAt party = .ct1Acknowledged core dec)
    (hmsg : s.messagesAt (!party) n = some (⟨core.ep, .ek chunk⟩, tsnd)) :
    Braid.TranscriptInv auth D ik T (s.toBraidAck party n) := by
  have hmsg' : s.toBraid.messagesAt (!party) n =
      some (⟨core.ep, .ek, some chunk⟩, tsnd) := by
    simp [hmsg, Chunked.Message.toBraid]
  have hst' :
      s.toBraid.stateAt party = PartyState.toBraid (.ct1Acknowledged core dec) := by
    simp [hst]
  have hctl := Braid.TranscriptInv.messageControl_ekCt1Ack auth hT party hst' hmsg'
  have h := Braid.TranscriptInv.retype auth hT (!party) n hmsg' (Or.inl rfl) .ekCt1Ack
    (Or.inr rfl) hctl
  simpa [GameState.toBraidAck, hmsg'] using h

/-- After a Braid step from the relabelled translation that keeps the recorded messages of the peer,
restoring the plain vector chunk keeps `TranscriptInv D`. -/
theorem transcriptInv_restore {ik : InitKey} {T : ℕ → Braid.EpochTranscript P.toBraid}
    (party : Bool) (n : ℕ) {s : GameState P AuthState} {core : CtSender.Ct1Sent P AuthState}
    {chunk : ℕ × P.Sym} {tsnd : ℕ}
    (hmsg : s.messagesAt (!party) n = some (⟨core.ep, .ek chunk⟩, tsnd))
    {z : Braid.GameState P.toBraid AuthState}
    (hmsgs : z.messagesAt (!party) = (s.toBraidAck party n).messagesAt (!party))
    (hT : Braid.TranscriptInv auth D ik T z) :
    Braid.TranscriptInv auth D ik T (z.setMessages (!party) (s.toBraid.messagesAt (!party))) := by
  have hmsgF : s.toBraid.messagesAt (!party) n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := by
    simp [hmsg, Chunked.Message.toBraid]
  have hmsgZ : z.messagesAt (!party) n = some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd) := by
    rw [hmsgs]
    simp [GameState.toBraidAck, hmsgF]
  obtain ⟨hwf, hle, hstep, hown⟩ := (hT.control.roles (!party)).2.2 n _ tsnd hmsgZ
  have hctl : Braid.MessageControl (!party) (z.stateAt (!party))
      { (⟨core.ep, .ekCt1Ack, some chunk⟩ : Braid.Message P.Sym) with type := .ek } :=
    ⟨rfl, hle, fun h => (hstep h).trans' (by simp [Braid.MessageType.sendStep]),
      by simpa [Braid.MessageOwner] using hown⟩
  have h := Braid.TranscriptInv.retype auth hT (!party) n hmsgZ (Or.inr rfl) .ek (Or.inl rfl) hctl
  -- Restoring the record gives back the message table of the translation.
  have htable : Function.update (z.messagesAt (!party)) n
      (some (⟨core.ep, .ek, some chunk⟩, tsnd)) = s.toBraid.messagesAt (!party) := by
    rw [hmsgs]
    simp [GameState.toBraidAck, hmsgF]
  rwa [htable] at h

/-- After a query of the relabelled translation, restoring the plain vector chunk keeps the Braid
invariant. -/
theorem correctnessInv_restore {ik : InitKey} (party : Bool) (n : ℕ)
    {s : GameState P AuthState} {core : CtSender.Ct1Sent P AuthState} {chunk : ℕ × P.Sym}
    {tsnd : ℕ} (hmsg : s.messagesAt (!party) n = some (⟨core.ep, .ek chunk⟩, tsnd))
    {z : Braid.GameState P.toBraid AuthState}
    (hmsgs : z.messagesAt (!party) = (s.toBraidAck party n).messagesAt (!party))
    (hz : Braid.CorrectnessInv auth ik z) :
    Braid.CorrectnessInv auth ik
      (if party then { z with msgB := s.toBraid.msgB }
        else { z with msgA := s.toBraid.msgA }) := by
  have hrestore : (if party then { z with msgB := s.toBraid.msgB }
      else { z with msgA := s.toBraid.msgA }) =
      z.setMessages (!party) (s.toBraid.messagesAt (!party)) := by
    cases party <;> rfl
  rw [hrestore]
  rcases hz with hzf | ⟨T, hT⟩
  · exact Or.inl hzf
  · exact Or.inr ⟨T, transcriptInv_restore auth party n hmsg hmsgs hT⟩

end SPQR
