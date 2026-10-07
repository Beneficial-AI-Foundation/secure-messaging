/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Game

/-!
# Opp-BiKEM-CKA — Totality of honest sends

`sendWith` has two error exits, following the paper's convention of returning an error when a
required key is missing: chunking the own public key when none is stored, and encapsulating to
the peer's public key when none was decoded. The correctness game does not observe these exits
(a rejected send leaves the game state unchanged), so the correctness bounds say nothing about
them.

The main result, `send_ne_none`, shows that a party satisfying `PartyInv` takes neither exit.
`sends_never_rejected_of_perfectKEM` lifts this to every reachable state of the correctness
game for a perfectly correct KEM; the version for an imperfect KEM, valid while no KEM failure
has occurred, is `sends_never_rejected_of_noFailure` in `Quantitative.Main`.
-/

open OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- If both parties satisfy `PartyInv` for a common transcript, the sender's `send` never
returns `none`. -/
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
    · -- encapsulating after an advance without a decoded peer key: `ekRec_res` supplies it
      rename_i hgate hack hnot hct ek hpeer hkeys
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hct
      have hpar : (stS.res.resEpoch + 2) % 2 = roleS.resParity := by
        have := hS.res_parity; omega
      obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp (hS.ekRec_res _ hct.2 hpar)
      exact hpeer pk hpk
    · -- chunking without an own public key: `ek_acked` and `keypair_current` exclude it
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
    · -- encapsulating without a decoded peer key: `ekRec_res` supplies it
      rename_i hgate hack hnot hct ek hpeer
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hct
      obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp (hS.ekRec_res _ hct.2 hS.res_parity)
      exact hpeer pk hpk

section Game

variable [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

omit [DecidableEq K] [DecidableEq Sym] in
/-- From a game state satisfying `GameInv`, A's `send` never returns `none`. -/
theorem sendA_ne_none
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) : none ∉ support (sendA kem ecEk ecCt s.stA) := by
  obtain ⟨-, T, hA, hB⟩ := hs
  exact send_ne_none hA hB

omit [DecidableEq K] [DecidableEq Sym] in
/-- From a game state satisfying `GameInv`, B's `send` never returns `none`. -/
theorem sendB_ne_none
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) : none ∉ support (sendB kem ecEk ecCt s.stB) := by
  obtain ⟨-, T, hA, hB⟩ := hs
  exact send_ne_none hB hA

/-- From a game state satisfying `GameInv`, the `SendA` oracle always answers `some`. -/
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

/-- From a game state satisfying `GameInv`, the `SendB` oracle always answers `some`. -/
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

/-- Assume:

* `kem` has deterministic decapsulation and is perfectly correct;
* `ecEk` and `ecCt` are correct erasure codes.

Then, for every adversary, neither party's `send` returns `none` at any reachable state of the
Opp-BiKEM-CKA correctness game. -/
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
