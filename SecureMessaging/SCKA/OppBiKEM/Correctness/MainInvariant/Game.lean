/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Init
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Send
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Recv

/-!
# Opp-BiKEM-CKA — One oracle query preserves the main invariant

Every correctness-game oracle preserves `GameInv`, provided both parties can decapsulate every
ciphertext they have yet to receive (`DecapsReady`, `gameInv_step_of`). The per-oracle steps are
stated separately: sends need nothing beyond the invariant, and receives are stated for any scheme
whose receive is `recvWith recover`, under the proviso that `recover` returns the transcript key
(`gameInv_recvA_step_of`, `gameInv_recvB_step_of`). For the real receive this proviso is where
KEM correctness enters, and the two correctness proofs discharge it differently:
`Quantitative.RecvStep` from `kemFailure s = false`, which leads to the `q · ε` bound, and
`PerfectKEM` at every state, for a perfectly correct KEM.

The file also restates the correctness experiment as the final `correct` bit of the simulated
run from the initial game state (`correctnessExp_eq_map`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The party playing `role`, in state `st`, can decapsulate every ciphertext it has yet to
receive, according to `T`: for every epoch `q` in which the party is the
requester (that is, `q % 2 = role.reqParity`) and ciphertext receipt
is not yet recorded (`q ∉ st.ack.ctRec`), if `T` records a
key pair `(pk, sk)` and an encapsulation `(c, k)` at `q`, then `hDet.decapsDet sk c = some k`. -/
def DecapsReady (role : Role) {kem : KEMScheme ProbComp K PK SK C} (hDet : kem.DeterministicDecaps)
    (T : Transcript kem) (st : State PK SK C Sym) : Prop :=
  ∀ q, q ∉ st.ack.ctRec → q % 2 = role.reqParity →
    ∀ pk sk c k, (T q).keypair = some (pk, sk) → (T q).enc = some (c, k) →
      hDet.decapsDet sk c = some k

/-- A's ordinary send preserves `GameInv`. -/
lemma gameInv_sendA_step [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s),
      GameInv kem ecEk ecCt z.2 := by
  intro z hz
  obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
  rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
  · exact hs
  dsimp only
  obtain ⟨hcorrect, T, hA, hB⟩ := hs
  have hout' : some (key?, ρ, tsnd, stA') ∈ support (send .A kem ecEk ecCt s.stA) := hout
  obtain ⟨hmono, hprefix, hkeys, T', hA', hB'⟩ :=
    partyInv_send_step .A kem ecEk ecCt T s.stA s.stB s.msgA s.msgB s.keyA s.keyB
      s.tcurA s.tcurB hA hB (s.nA + 1) key? ρ tsnd stA' hout'
  rcases key? with _ | ⟨tI, k⟩
  · refine ⟨?_, T', ?_, ?_⟩
    · simp only [SCKAScheme.sendAUpdate, hcorrect, hmono, decide_true, Bool.true_and]
      simpa [SCKAScheme.knownPrefix] using hprefix
    · simpa [SCKAScheme.sendAUpdate] using hA'
    · simpa [SCKAScheme.sendAUpdate, Role.peer] using hB'
  · obtain ⟨hA0, hB0⟩ := hkeys tI k rfl
    refine ⟨?_, T', ?_, ?_⟩
    · simp only [SCKAScheme.sendAUpdate, hcorrect, hmono, decide_true, Bool.true_and, hA0,
        Option.isNone_none]
      rcases hB0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or, beq_self_eq_true,
        Option.isNone_some, Bool.false_or, Bool.true_and] <;>
        simpa [SCKAScheme.knownPrefix] using hprefix
    · simpa [SCKAScheme.sendAUpdate] using hA'
    · simpa [SCKAScheme.sendAUpdate, Role.peer] using hB'

/-- B's ordinary send preserves `GameInv`. -/
lemma gameInv_sendB_step [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s),
      GameInv kem ecEk ecCt z.2 := by
  intro z hz
  obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
  rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
  · exact hs
  dsimp only
  obtain ⟨hcorrect, T, hA, hB⟩ := hs
  have hout' : some (key?, ρ, tsnd, stB') ∈ support (send .B kem ecEk ecCt s.stB) := hout
  obtain ⟨hmono, hprefix, hkeys, T', hB', hA'⟩ :=
    partyInv_send_step .B kem ecEk ecCt T s.stB s.stA s.msgB s.msgA s.keyB s.keyA
      s.tcurB s.tcurA hB hA (s.nB + 1) key? ρ tsnd stB' hout'
  rcases key? with _ | ⟨tI, k⟩
  · refine ⟨?_, T', ?_, ?_⟩
    · simp only [SCKAScheme.sendBUpdate, hcorrect, hmono, decide_true, Bool.true_and]
      simpa [SCKAScheme.knownPrefix] using hprefix
    · simpa [SCKAScheme.sendBUpdate, Role.peer] using hA'
    · simpa [SCKAScheme.sendBUpdate] using hB'
  · obtain ⟨hB0, hA0⟩ := hkeys tI k rfl
    refine ⟨?_, T', ?_, ?_⟩
    · simp only [SCKAScheme.sendBUpdate, hcorrect, hmono, decide_true, Bool.true_and, hB0,
        Option.isNone_none]
      rcases hA0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or, beq_self_eq_true,
        Option.isNone_some, Bool.false_or, Bool.true_and] <;>
        simpa [SCKAScheme.knownPrefix] using hprefix
    · simpa [SCKAScheme.sendBUpdate, Role.peer] using hA'
    · simpa [SCKAScheme.sendBUpdate] using hB'

/-- A's receive through any scheme whose receive is `recvWith .A recover` preserves `GameInv`,
provided `recover` returns the transcript key at the received epoch of the message being
received, for every transcript witnessing the invariant. -/
lemma gameInv_recvA_step_of [DecidableEq K] [DecidableEq Sym] {IK Rand : Type}
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (scka : SCKAScheme ProbComp IK (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) Rand)
    (recover : ℤ → SK → C → Option K)
    (hscka : ∀ st ρ, scka.recvA st ρ = recvWith .A recover ecEk ecCt st ρ)
    (n : ℕ) (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s)
    (hrec : ∀ T : Transcript kem,
      PartyInv .A ecEk ecCt T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA →
      PartyInv .B ecEk ecCt T s.stB s.stA s.msgB s.keyB s.keyA s.tcurB →
      ∀ ρ tsnd, s.msgB n = some (ρ, tsnd) → ρ.tRes ∉ s.stA.ack.ctRec →
      ∀ pk sk c k, (T ρ.tRes).keypair = some (pk, sk) → (T ρ.tRes).enc = some (c, k) →
        recover ρ.tRes sk c = some k) :
    ∀ z ∈ support ((SCKAScheme.oracleRecvA scka n).run s), GameInv kem ecEk ecCt z.2 := by
  intro z hz
  obtain ⟨hcorrect, T, hA, hB⟩ := hs
  rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
    ⟨-, rfl⟩ | ⟨ρ, tsnd, hmsg, hrecv, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stA', hmsg, hrecv, rfl⟩
  · exact ⟨hcorrect, T, hA, hB⟩
  · exfalso
    obtain ⟨⟨key?, trcv, stA', h⟩, -⟩ := partyInv_recvWith_step hA hB hmsg hEk hCt recover
      (hrec T hA hB ρ tsnd hmsg)
    have hrecv' : recvWith .A recover ecEk ecCt s.stA ρ = none := by
      rwa [hscka s.stA ρ] at hrecv
    rw [hrecv'] at h
    cases h
  · have hrecv' : recvWith .A recover ecEk ecCt s.stA ρ = some (key?, trcv, stA') := by
      rwa [hscka s.stA ρ] at hrecv
    obtain ⟨-, hall⟩ := partyInv_recvWith_step hA hB hmsg hEk hCt recover
      (hrec T hA hB ρ tsnd hmsg)
    obtain ⟨htrcv, hprefix, hkeys, hA', hB'⟩ := hall key? trcv stA' hrecv'
    subst htrcv
    rcases key? with _ | ⟨tI, k⟩
    · refine ⟨?_, T, ?_, ?_⟩
      · simp only [SCKAScheme.recvAUpdate, hcorrect, beq_self_eq_true, Bool.true_and]
        simpa [SCKAScheme.knownPrefix] using hprefix
      · simpa [SCKAScheme.recvAUpdate] using hA'
      · simpa [SCKAScheme.recvAUpdate, Role.peer] using hB'
    · obtain ⟨hA0, hB0⟩ := hkeys tI k rfl
      refine ⟨?_, T, ?_, ?_⟩
      · simp only [SCKAScheme.recvAUpdate, hcorrect, beq_self_eq_true, Bool.true_and, hA0,
          Option.isNone_none]
        rcases hB0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or,
          beq_self_eq_true, Option.isNone_some, Bool.false_or, Bool.true_and] <;>
          simpa [SCKAScheme.knownPrefix] using hprefix
      · simpa [SCKAScheme.recvAUpdate] using hA'
      · simpa [SCKAScheme.recvAUpdate, Role.peer] using hB'

/-- B's receive through any scheme whose receive is `recvWith .B recover` preserves `GameInv`,
provided `recover` returns the transcript key at the received epoch of the message being
received, for every transcript witnessing the invariant. -/
lemma gameInv_recvB_step_of [DecidableEq K] [DecidableEq Sym] {IK Rand : Type}
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (scka : SCKAScheme ProbComp IK (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) Rand)
    (recover : ℤ → SK → C → Option K)
    (hscka : ∀ st ρ, scka.recvB st ρ = recvWith .B recover ecEk ecCt st ρ)
    (n : ℕ) (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s)
    (hrec : ∀ T : Transcript kem,
      PartyInv .A ecEk ecCt T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA →
      PartyInv .B ecEk ecCt T s.stB s.stA s.msgB s.keyB s.keyA s.tcurB →
      ∀ ρ tsnd, s.msgA n = some (ρ, tsnd) → ρ.tRes ∉ s.stB.ack.ctRec →
      ∀ pk sk c k, (T ρ.tRes).keypair = some (pk, sk) → (T ρ.tRes).enc = some (c, k) →
        recover ρ.tRes sk c = some k) :
    ∀ z ∈ support ((SCKAScheme.oracleRecvB scka n).run s), GameInv kem ecEk ecCt z.2 := by
  intro z hz
  obtain ⟨hcorrect, T, hA, hB⟩ := hs
  rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
    ⟨-, rfl⟩ | ⟨ρ, tsnd, hmsg, hrecv, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stB', hmsg, hrecv, rfl⟩
  · exact ⟨hcorrect, T, hA, hB⟩
  · exfalso
    obtain ⟨⟨key?, trcv, stB', h⟩, -⟩ := partyInv_recvWith_step hB hA hmsg hEk hCt recover
      (hrec T hA hB ρ tsnd hmsg)
    have hrecv' : recvWith .B recover ecEk ecCt s.stB ρ = none := by
      rwa [hscka s.stB ρ] at hrecv
    rw [hrecv'] at h
    cases h
  · have hrecv' : recvWith .B recover ecEk ecCt s.stB ρ = some (key?, trcv, stB') := by
      rwa [hscka s.stB ρ] at hrecv
    obtain ⟨-, hall⟩ := partyInv_recvWith_step hB hA hmsg hEk hCt recover
      (hrec T hA hB ρ tsnd hmsg)
    obtain ⟨htrcv, hprefix, hkeys, hB', hA'⟩ := hall key? trcv stB' hrecv'
    subst htrcv
    rcases key? with _ | ⟨tI, k⟩
    · refine ⟨?_, T, ?_, ?_⟩
      · simp only [SCKAScheme.recvBUpdate, hcorrect, beq_self_eq_true, Bool.true_and]
        simpa [SCKAScheme.knownPrefix] using hprefix
      · simpa [SCKAScheme.recvBUpdate, Role.peer] using hA'
      · simpa [SCKAScheme.recvBUpdate] using hB'
    · obtain ⟨hB0, hA0⟩ := hkeys tI k rfl
      refine ⟨?_, T, ?_, ?_⟩
      · simp only [SCKAScheme.recvBUpdate, hcorrect, beq_self_eq_true, Bool.true_and, hB0,
          Option.isNone_none]
        rcases hA0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or,
          beq_self_eq_true, Option.isNone_some, Bool.false_or, Bool.true_and] <;>
          simpa [SCKAScheme.knownPrefix] using hprefix
      · simpa [SCKAScheme.recvBUpdate, Role.peer] using hA'
      · simpa [SCKAScheme.recvBUpdate] using hB'

/-- Let `t` be a query and `s` a game state. Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `GameInv s`;
* every transcript `T` for which both parties satisfy `PartyInv` at `s` is `DecapsReady` for
  both parties.

Then every outcome of `t` from `s` satisfies `GameInv`. -/
lemma gameInv_step_of [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s)
    (hdec : ∀ T : Transcript kem,
      PartyInv .A ecEk ecCt T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA →
      PartyInv .B ecEk ecCt T s.stB s.stA s.msgB s.keyB s.keyA s.tcurB →
      DecapsReady .A hDet T s.stA ∧ DecapsReady .B hDet T s.stB) :
    ∀ z ∈ support ((SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak) t).run s),
      GameInv kem ecEk ecCt z.2 := by
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · exact SCKAScheme.oracleUnif_preservesInv (GameInv kem ecEk ecCt) n s hs
  · exact gameInv_sendA_step kem hDet ecEk ecCt leak s hs
  · exact gameInv_sendB_step kem hDet ecEk ecCt leak s hs
  · exact gameInv_recvA_step_of kem ecEk ecCt hEk hCt (scheme kem hDet ecEk ecCt leak) _
      (fun st ρ => recv_eq_recvWith .A kem hDet ecEk ecCt st ρ) n s hs
      (fun T hA hB ρ tsnd hmsg hq =>
        (hdec T hA hB).1 _ hq (recv_tRes_parity (roleR := .A) hB hmsg))
  · exact gameInv_recvB_step_of kem ecEk ecCt hEk hCt (scheme kem hDet ecEk ecCt leak) _
      (fun st ρ => recv_eq_recvWith .B kem hDet ecEk ecCt st ρ) n s hs
      (fun T hA hB ρ tsnd hmsg hq =>
        (hdec T hA hB).2 _ hq (recv_tRes_parity (roleR := .B) hA hmsg))

/-- The initial local state of a party, as `init` returns it. -/
def initialState (role : Role) : State PK SK C Sym :=
  { req := { reqEpoch := if role = .A then 0 else -1
             dk := [], ek := none, receivedChunks := ∅ }
    res := { resEpoch := if role = .A then -1 else 0
             ekPeer := fun _ => none
             ct := none, ich := 0 }
    ack := { ekRec := ∅, ctRec := {-1, 0} } }

/-- The correctness experiment is the final correctness bit of the simulated run from the
initial game state. -/
lemma correctnessExp_eq_map [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv =
      (fun z => z.2.correct) <$>
        (simulateQ (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
          (SCKAScheme.initGameState (initialState .A) (initialState .B)) := by
  simp [SCKAScheme.correctnessExp, scheme, initKeyGen, initA, initB, init, initialState,
    map_eq_bind_pure_comp]

end oppBiKemCKA
