/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness.OracleSupport
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Init
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Send
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Recv

/-!
# Opp-BiKEM correctness from the main invariant

The main invariant is preserved by every correctness-game oracle
(`gameInv_preserved`), hence holds on every reachable state (`simulateQ_gameInv`). Since it
contains `s.correct = true`, the correctness experiment returns `true` with probability one
whenever the KEM is perfectly correct and both erasure codes are correct
(`correctness_of_perfectKEM`).

The oracle case split is the generic one of `SCKA.Correctness.OracleSupport`: each oracle is
handled by one application of `partyInv_send_step` or `partyInv_recv_step`, with the roles
`A`/`B` filled in.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Transcript-level decapsulation correctness follows from the support-level one, because
the transcript records support membership for each sample. -/
theorem transcriptDecaps_of_support {kem : KEMScheme ProbComp K PK SK C}
    (hDet : kem.DeterministicDecaps) (hdec : DecapsCorrectOnSupport kem hDet)
    (T : Transcript kem) (e : ℤ) :
    ∀ pk sk c k, (T e).keypair = some (pk, sk) → (T e).enc = some (c, k) →
      hDet.decapsDet sk c = some k :=
  fun pk sk c k hkp henc =>
    hdec pk sk c k ((T e).keypair_mem pk sk hkp) ((T e).enc_mem pk sk c k hkp henc)

/-- Decapsulation correctness for the epochs a party may decapsulate next, relative to a
transcript consistent with the state: for every unacknowledged requester-parity epoch, the
transcript's secret key recovers the transcript's key from the transcript's ciphertext. -/
def DecapsReady (role : Role) {kem : KEMScheme ProbComp K PK SK C} (hDet : kem.DeterministicDecaps)
    (T : Transcript kem) (st : State PK SK C Sym) : Prop :=
  ∀ q, q ∉ st.ack.ctRec → q % 2 = role.reqParity →
    ∀ pk sk c k, (T q).keypair = some (pk, sk) → (T q).enc = some (c, k) →
      hDet.decapsDet sk c = some k

/-- One step of any correctness-game oracle preserves the main invariant, provided the
transcript consistent with the pre-state is decapsulation-ready for both parties. -/
theorem gameInv_step_of [DecidableEq K] [DecidableEq Sym]
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
  -- Package the state and its hypotheses as an invariant preserved for one step.
  let Inv : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) → Prop :=
    fun s' => GameInv kem ecEk ecCt s' ∧ (s' = s ∨ True)
  suffices h : ∀ z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak) t).run s),
      GameInv kem ecEk ecCt z.2 from h
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · intro z hz
    have hz' : z ∈ support (((QueryImpl.ofLift unifSpec ProbComp) n) >>=
        fun y => pure (y, s)) := hz
    obtain ⟨_, _, hz⟩ := mem_support_bind_peel _ _ hz'
    have hz' := eq_of_mem_support_pure _ hz
    subst z
    exact hs
  · intro z hz
    change z ∈ support ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s) at hz
    rcases SCKAScheme.oracleSendA_run_cases _ s z hz with
      ⟨-, rfl⟩ | ⟨key?, ρ, tsnd, stA', hout, rfl⟩
    · exact hs
    obtain ⟨hcorrect, T, hA, hB⟩ := hs
    have hout' : some (key?, ρ, tsnd, stA') ∈ support (send .A kem ecEk ecCt s.stA) := hout
    obtain ⟨hmono, hprefix, hkeys, T', hA', hB'⟩ :=
      partyInv_send_step .A kem ecEk ecCt T s.stA s.stB s.msgA s.msgB s.keyA s.keyB
        s.tcurA s.tcurB hA hB (s.nA + 1) key? ρ tsnd stA' hout'
    rcases key? with _ | ⟨tI, k⟩
    · refine ⟨?_, T', ?_, ?_⟩
      · simp only [SCKAScheme.applySendA, hcorrect, hmono, decide_true, Bool.true_and]
        simpa using hprefix
      · simpa [SCKAScheme.applySendA] using hA'
      · simpa [SCKAScheme.applySendA, Role.peer] using hB'
    · obtain ⟨hA0, hB0⟩ := hkeys tI k rfl
      refine ⟨?_, T', ?_, ?_⟩
      · simp only [SCKAScheme.applySendA, hcorrect, hmono, decide_true, Bool.true_and, hA0,
          Option.isNone_none]
        rcases hB0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or, beq_self_eq_true,
          Option.isNone_some, Bool.false_or, Bool.true_and] <;> simpa using hprefix
      · simpa [SCKAScheme.applySendA] using hA'
      · simpa [SCKAScheme.applySendA, Role.peer] using hB'
  · intro z hz
    change z ∈ support ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s) at hz
    rcases SCKAScheme.oracleSendB_run_cases _ s z hz with
      ⟨-, rfl⟩ | ⟨key?, ρ, tsnd, stB', hout, rfl⟩
    · exact hs
    obtain ⟨hcorrect, T, hA, hB⟩ := hs
    have hout' : some (key?, ρ, tsnd, stB') ∈ support (send .B kem ecEk ecCt s.stB) := hout
    obtain ⟨hmono, hprefix, hkeys, T', hB', hA'⟩ :=
      partyInv_send_step .B kem ecEk ecCt T s.stB s.stA s.msgB s.msgA s.keyB s.keyA
        s.tcurB s.tcurA hB hA (s.nB + 1) key? ρ tsnd stB' hout'
    rcases key? with _ | ⟨tI, k⟩
    · refine ⟨?_, T', ?_, ?_⟩
      · simp only [SCKAScheme.applySendB, hcorrect, hmono, decide_true, Bool.true_and]
        simpa using hprefix
      · simpa [SCKAScheme.applySendB, Role.peer] using hA'
      · simpa [SCKAScheme.applySendB] using hB'
    · obtain ⟨hB0, hA0⟩ := hkeys tI k rfl
      refine ⟨?_, T', ?_, ?_⟩
      · simp only [SCKAScheme.applySendB, hcorrect, hmono, decide_true, Bool.true_and, hB0,
          Option.isNone_none]
        rcases hA0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or, beq_self_eq_true,
          Option.isNone_some, Bool.false_or, Bool.true_and] <;> simpa using hprefix
      · simpa [SCKAScheme.applySendB, Role.peer] using hA'
      · simpa [SCKAScheme.applySendB] using hB'
  · intro z hz
    change z ∈ support ((SCKAScheme.oracleRecvA (scheme kem hDet ecEk ecCt leak) n).run s) at hz
    obtain ⟨hcorrect, T, hA, hB⟩ := hs
    have hready := (hdec T hA hB).1
    rcases SCKAScheme.oracleRecvA_run_cases _ n s z hz with ⟨-, rfl⟩ | ⟨ρ, tsnd, hmsg, hrecv, rfl⟩ |
      ⟨ρ, tsnd, key?, trcv, stA', hmsg, hrecv, rfl⟩
    · exact ⟨hcorrect, T, hA, hB⟩
    · exfalso
      obtain ⟨⟨key?, trcv, stA', h⟩, -⟩ := partyInv_recv_step hA hB hmsg hEk hCt
        (fun hq => hready _ hq (recv_tRes_parity (roleR := .A) hB hmsg))
      have hrecv' : recv .A kem hDet ecEk ecCt s.stA ρ = none := hrecv
      rw [hrecv'] at h
      cases h
    · have hrecv' : recv .A kem hDet ecEk ecCt s.stA ρ = some (key?, trcv, stA') := hrecv
      obtain ⟨-, hall⟩ := partyInv_recv_step hA hB hmsg hEk hCt
        (fun hq => hready _ hq (recv_tRes_parity (roleR := .A) hB hmsg))
      obtain ⟨htrcv, hprefix, hkeys, hA', hB'⟩ := hall key? trcv stA' hrecv'
      subst htrcv
      rcases key? with _ | ⟨tI, k⟩
      · refine ⟨?_, T, ?_, ?_⟩
        · simp only [SCKAScheme.applyRecvA, hcorrect, beq_self_eq_true, Bool.true_and]
          simpa using hprefix
        · simpa [SCKAScheme.applyRecvA] using hA'
        · simpa [SCKAScheme.applyRecvA, Role.peer] using hB'
      · obtain ⟨hA0, hB0⟩ := hkeys tI k rfl
        refine ⟨?_, T, ?_, ?_⟩
        · simp only [SCKAScheme.applyRecvA, hcorrect, beq_self_eq_true, Bool.true_and, hA0,
            Option.isNone_none]
          rcases hB0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or,
            beq_self_eq_true, Option.isNone_some, Bool.false_or, Bool.true_and] <;>
            simpa using hprefix
        · simpa [SCKAScheme.applyRecvA] using hA'
        · simpa [SCKAScheme.applyRecvA, Role.peer] using hB'
  · intro z hz
    change z ∈ support ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s) at hz
    obtain ⟨hcorrect, T, hA, hB⟩ := hs
    have hready := (hdec T hA hB).2
    rcases SCKAScheme.oracleRecvB_run_cases _ n s z hz with ⟨-, rfl⟩ | ⟨ρ, tsnd, hmsg, hrecv, rfl⟩ |
      ⟨ρ, tsnd, key?, trcv, stB', hmsg, hrecv, rfl⟩
    · exact ⟨hcorrect, T, hA, hB⟩
    · exfalso
      obtain ⟨⟨key?, trcv, stB', h⟩, -⟩ := partyInv_recv_step hB hA hmsg hEk hCt
        (fun hq => hready _ hq (recv_tRes_parity (roleR := .B) hA hmsg))
      have hrecv' : recv .B kem hDet ecEk ecCt s.stB ρ = none := hrecv
      rw [hrecv'] at h
      cases h
    · have hrecv' : recv .B kem hDet ecEk ecCt s.stB ρ = some (key?, trcv, stB') := hrecv
      obtain ⟨-, hall⟩ := partyInv_recv_step hB hA hmsg hEk hCt
        (fun hq => hready _ hq (recv_tRes_parity (roleR := .B) hA hmsg))
      obtain ⟨htrcv, hprefix, hkeys, hB', hA'⟩ := hall key? trcv stB' hrecv'
      subst htrcv
      rcases key? with _ | ⟨tI, k⟩
      · refine ⟨?_, T, ?_, ?_⟩
        · simp only [SCKAScheme.applyRecvB, hcorrect, beq_self_eq_true, Bool.true_and]
          simpa using hprefix
        · simpa [SCKAScheme.applyRecvB, Role.peer] using hA'
        · simpa [SCKAScheme.applyRecvB] using hB'
      · obtain ⟨hB0, hA0⟩ := hkeys tI k rfl
        refine ⟨?_, T, ?_, ?_⟩
        · simp only [SCKAScheme.applyRecvB, hcorrect, beq_self_eq_true, Bool.true_and, hB0,
            Option.isNone_none]
          rcases hA0 with h | h <;> simp only [h, Option.isNone_none, Bool.true_or,
            beq_self_eq_true, Option.isNone_some, Bool.false_or, Bool.true_and] <;>
            simpa using hprefix
        · simpa [SCKAScheme.applyRecvB, Role.peer] using hA'
        · simpa [SCKAScheme.applyRecvB] using hB'

/-- Every correctness-game oracle preserves the main invariant when decapsulation is correct
on every honestly generated tuple. -/
theorem gameInv_preserved [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (hdec : DecapsCorrectOnSupport kem hDet) :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (GameInv kem ecEk ecCt) := by
  intro t s hs z hz
  refine gameInv_step_of kem hDet ecEk ecCt hEk hCt leak t s hs ?_ z hz
  intro T _ _
  exact ⟨fun q _ _ => transcriptDecaps_of_support hDet hdec T q,
    fun q _ _ => transcriptDecaps_of_support hDet hdec T q⟩

/-- The main invariant holds on every reachable correctness-game state. -/
theorem simulateQ_gameInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (hdec : DecapsCorrectOnSupport kem hDet)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym)))
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    GameInv kem ecEk ecCt z.2 :=
  simulateQ_run_preservesInv _ _ (gameInv_preserved kem hDet ecEk ecCt hEk hCt leak hdec) adv _
    (gameInv_init kem ecEk ecCt stA stB hA hB) z hz

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
theorem correctnessExp_eq_map [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv =
      (fun z => z.2.correct) <$>
        (simulateQ (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
          (SCKAScheme.initGameState (initialState .A) (initialState .B)) := by
  simp [SCKAScheme.correctnessExp, scheme, initKeyGen, initA, initB, init, initialState,
    map_eq_bind_pure_comp]

/-- **Correctness of Opp-BiKEM-CKA** for a perfectly correct KEM with deterministic
decapsulation and correct erasure codes: the correctness experiment returns `true` with
probability one, for every adversary. -/
theorem correctness_of_perfectKEM [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] = 1 := by
  have hdec := decapsCorrectOnSupport_of_perfectlyCorrect kem hDet hkem
  have hfalse :
      Pr[= false | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] = 0 := by
    rw [correctnessExp_eq_map, ← probEvent_eq_eq_probOutput, probEvent_map]
    rw [probEvent_eq_zero_iff]
    intro z hz hcontra
    have hinv := simulateQ_gameInv kem hDet ecEk ecCt hEk hCt leak hdec adv
      (initialState .A) (initialState .B) (by simp [initA, init, initialState])
      (by simp [initB, init, initialState]) z hz
    have := hinv.1
    simp only [Function.comp] at hcontra
    rw [this] at hcontra
    cases hcontra
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero] at hfalse
  exact le_antisymm probOutput_le_one ((tsub_eq_zero_iff_le).mp hfalse)

end oppBiKemCKA
