/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Game

/-!
# Opp-BiKEM — honest sends are never rejected

`sendWith` has two error exits, inherited from the paper's convention of returning an error when
a required key is missing: chunking the own public key when none is stored, and encapsulating to
the peer's public key when none was decoded. The correctness game does not observe these exits
(a rejected send leaves the game state unchanged), so the correctness theorems are silent about
them. This file shows that neither exit is reachable from a state satisfying the main invariant,
and hence from any reachable state of the correctness game.

* `send_ne_none`: a party satisfying `PartyInv` never has its send rejected;
* `oracleSendA_run_ne_none`, `oracleSendB_run_ne_none`: the send oracles always answer `some`
  from a state satisfying `GameInv`;
* `sends_never_rejected_of_perfectKEM`: for a perfectly correct KEM, at every reachable state of
  the correctness game. The imperfect-KEM version, valid while the failure flag is down, is
  `sends_never_rejected_of_noFailure` in `Quantitative/Main.lean`.
-/

open OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- From a state satisfying the main invariant, the send is never rejected. -/
theorem send_ne_none {roleS : Role} {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T : Transcript kem} {stS stR : State PK SK C Sym}
    {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyS keyR : ℕ → Option K} {tcurS tcurR : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR) :
    none ∉ support (send roleS kem ecEk ecCt stS) := by
  intro hout
  rw [send, mem_support_bind_iff] at hout
  obtain ⟨out, hmem, hout⟩ := hout
  cases out with
  | some out => simp at hout
  | none =>
    unfold sendWith at hmem
    dsimp only at hmem
    repeat' first
      | split at hmem
      | (rw [mem_support_bind_iff] at hmem; obtain ⟨x, _, hmem⟩ := hmem)
    all_goals simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at hmem
    · -- after an advance: encapsulating to the peer's key for the new epoch, none decoded
      rename_i hgate hack hnot hct ek hpeer hkeys
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hct
      have hpar : (stS.res.resEpoch + 2) % 2 = roleS.resParity := by
        have := hS.res_parity; omega
      obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp (hS.ekRec_res _ hct.2 hpar)
      exact hpeer pk hpk
    · -- chunking the own public key when none is stored
      rename_i hgate hnack ek hnoEk
      have hek : stS.req.ek = none :=
        Option.eq_none_iff_forall_ne_some.mpr fun pk h => hnoEk pk h
      rcases hS.ek_acked hek with hnone | hack
      · have hle : ¬ 0 < stS.res.resEpoch + roleS.offset := fun hpos => by
          have := hS.keypair_current hpos
          rw [hnone] at this
          cases this
        obtain ⟨h1, h0⟩ := hS.init_acks
        have hlow := hS.res_lower
        have hpar := hS.res_parity
        apply hgate
        simp only [hek, Option.isNone_none, Bool.true_and, decide_eq_true_eq]
        cases roleS <;> simp only [Role.offset, Role.resParity] at hle hpar ⊢
        · obtain hres : stS.res.resEpoch = -1 := by omega
          rw [hres]; exact ⟨h1, h0⟩
        · obtain hres : stS.res.resEpoch = 0 := by omega
          rw [hres]; exact ⟨h0, h1⟩
      · exact hnack hack
    · -- encapsulating to the peer's key for the current epoch, none decoded
      rename_i hgate hack hnot hct ek hpeer
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hct
      obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp (hS.ekRec_res _ hct.2 hS.res_parity)
      exact hpeer pk hpk

section Game

variable [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

omit [DecidableEq K] [DecidableEq Sym] in
/-- From a game state satisfying the main invariant, A's send is never rejected. -/
theorem sendA_ne_none
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) : none ∉ support (sendA kem ecEk ecCt s.stA) := by
  obtain ⟨-, T, hA, hB⟩ := hs
  exact send_ne_none hA hB

omit [DecidableEq K] [DecidableEq Sym] in
/-- From a game state satisfying the main invariant, B's send is never rejected. -/
theorem sendB_ne_none
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) : none ∉ support (sendB kem ecEk ecCt s.stB) := by
  obtain ⟨-, T, hA, hB⟩ := hs
  exact send_ne_none hB hA

/-- The `SendA` oracle always answers `some` from a state satisfying the main invariant. -/
theorem oracleSendA_run_ne_none
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s),
      z.1 ≠ none := by
  intro z hz
  rw [SCKAScheme.oracleSendA_run_eq] at hz
  obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
  obtain rfl := eq_of_mem_support_pure _ hz
  rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
  · exact absurd hout (sendA_ne_none kem ecEk ecCt s hs)
  · simp [SCKAScheme.sendAOutcome]

/-- The `SendB` oracle always answers `some` from a state satisfying the main invariant. -/
theorem oracleSendB_run_ne_none
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s),
      z.1 ≠ none := by
  intro z hz
  rw [SCKAScheme.oracleSendB_run_eq] at hz
  obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
  obtain rfl := eq_of_mem_support_pure _ hz
  rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
  · exact absurd hout (sendB_ne_none kem ecEk ecCt s hs)
  · simp [SCKAScheme.sendBOutcome]

/-- For a perfectly correct KEM and correct erasure codes, neither party's send is ever rejected
at any reachable state of the correctness game. -/
theorem sends_never_rejected_of_perfectKEM
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState (initialState .A) (initialState .B)))) :
    none ∉ support (sendA kem ecEk ecCt z.2.stA) ∧
      none ∉ support (sendB kem ecEk ecCt z.2.stB) := by
  have hinv := simulateQ_gameInv kem hDet ecEk ecCt hEk hCt leak
    (decapsCorrectOnSupport_of_perfectlyCorrect kem hDet hkem) adv
    (initialState .A) (initialState .B) (by simp [initA, init, initialState])
    (by simp [initB, init, initialState]) z hz
  exact ⟨sendA_ne_none kem ecEk ecCt _ hinv, sendB_ne_none kem ecEk ecCt _ hinv⟩

end Game

end oppBiKemCKA
