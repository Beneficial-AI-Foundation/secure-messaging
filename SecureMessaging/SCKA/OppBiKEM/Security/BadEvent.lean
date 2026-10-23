/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Tracked

/-!
# Opp-BiKEM — Failure probability under security queries

Let `ε_cor := kem.correctnessError ProbCompRuntime.probComp`.

With deterministic decapsulation and correct erasure codes, the historical KEM-failure flag of a
tracked security run from `(initState, false)` is set with probability at most `q · ε_cor`, for
every adversary making at most `q` ordinary or leaking sends and for either challenge bit. The
expected failure score of the correctness game extends to the security oracles: leaking sends
inherit the ordinary-send bound through the coin-forgetting marginal, and challenges and
corruptions leave the score unchanged.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- A's leaking send raises the expected tracked score by at most `ε_cor` from a state
satisfying `GameInv` without current KEM failure. -/
lemma tracked_sendArleak_score_le
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (b : Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem hDet ecEk ecCt leak b
        SCKAScheme.sckaSecuritySpec.OSendArleak).run (s, false))
      (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet (s, false) + kem.correctnessError ProbCompRuntime.probComp := by
  rw [trackedImpl_run, bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendArleak_expectedPayoff_le
      (scheme kem hDet ecEk ecCt leak) (rleakEpochs .A)
      (sendWith_rleak_forget kem .A ecEk ecCt leak) s (leakEpochs .A s.stA)
      (score := fun state => trackedScore hDet (state, false || kemFailure hDet state))
      (c := trackedScore hDet (s, false) + kem.correctnessError ProbCompRuntime.probComp)
  · intro key msg epoch state coins hout
    exact sendWith_exposure .A leak.keygenRleak leak.encapsRleak ecEk ecCt s.stA
      key msg epoch state coins hout
  · intro state exposed
    rfl
  · simp [hfail]
  · have h := tracked_sendA_score_le kem hDet ecEk ecCt leak s hs hfail
    rw [trackedImpl_run, bind_pure_comp, expectedPayoff_map] at h
    exact h

/-- B's leaking send raises the expected tracked score by at most `ε_cor` from a state
satisfying `GameInv` without current KEM failure. -/
lemma tracked_sendBrleak_score_le
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (b : Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem hDet ecEk ecCt leak b
        SCKAScheme.sckaSecuritySpec.OSendBrleak).run (s, false))
      (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet (s, false) + kem.correctnessError ProbCompRuntime.probComp := by
  rw [trackedImpl_run, bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendBrleak_expectedPayoff_le
      (scheme kem hDet ecEk ecCt leak) (rleakEpochs .B)
      (sendWith_rleak_forget kem .B ecEk ecCt leak) s (leakEpochs .B s.stB)
      (score := fun state => trackedScore hDet (state, false || kemFailure hDet state))
      (c := trackedScore hDet (s, false) + kem.correctnessError ProbCompRuntime.probComp)
  · intro key msg epoch state coins hout
    exact sendWith_exposure .B leak.keygenRleak leak.encapsRleak ecEk ecCt s.stB
      key msg epoch state coins hout
  · intro state exposed
    rfl
  · simp [hfail]
  · have h := tracked_sendB_score_le kem hDet ecEk ecCt leak s hs hfail
    rw [trackedImpl_run, bind_pure_comp, expectedPayoff_map] at h
    exact h

/-- One security query raises the expected tracked score by at most `ε_cor` if it is an
ordinary or leaking send and not at all otherwise, from any state satisfying the tracked
invariant. -/
lemma trackedSecurity_score_step_le
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct)
    (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak)
    (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (p : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool)
    (hp : trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet) p) :
    expectedPayoff ((trackedSecurityImpl kem hDet ecEk ecCt leak b t).run p)
      (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet p +
        if SCKAScheme.sckaSecuritySpec.isSendQuery t then
          kem.correctnessError ProbCompRuntime.probComp
        else 0 := by
  obtain ⟨s, flag⟩ := p
  cases flag with
  | true =>
    exact trackedImpl_expectedPayoff_flag_le _ _ _ 1 (fun s => trackedScore_true hDet s) t s _
  | false =>
    obtain ⟨hs, hfail⟩ := trackedInv_of_flag_false hp rfl
    rcases t with (((((t | u) | u) | t) | u) | u)
    · rw [SCKAScheme.sckaSecuritySpec.isSendQuery_OCorrectness]
      exact tracked_step_score_le kem hDet ecEk ecCt leak hEk hCt t (s, false)
        (Or.inr ⟨hs, hfail⟩)
    · cases u
      simpa only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte] using
        tracked_sendArleak_score_le kem hDet ecEk ecCt leak b s hs hfail
    · cases u
      simpa only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte] using
        tracked_sendBrleak_score_le kem hDet ecEk ecCt leak b s hs hfail
    all_goals
      simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte,
        add_zero]
      rw [trackedImpl_run, bind_pure_comp, expectedPayoff_map]
    · refine (SCKAScheme.oracleChall_expectedPayoff_le b t s
        (fun state => trackedScore hDet (state, false || kemFailure hDet state))
        (fun _ _ => rfl)).trans ?_
      simp [hfail]
    · cases u
      refine (SCKAScheme.oracleCorruptA_expectedPayoff_le vuln s
        (fun state => trackedScore hDet (state, false || kemFailure hDet state))
        (fun _ _ => rfl)).trans ?_
      simp [hfail]
    · cases u
      refine (SCKAScheme.oracleCorruptB_expectedPayoff_le vuln s
        (fun state => trackedScore hDet (state, false || kemFailure hDet state))
        (fun _ _ => rfl)).trans ?_
      simp [hfail]

/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then, for either challenge bit `b`, the historical KEM-failure flag of the tracked security run
of `adv` from the initial state is set with probability at most `q · ε_cor`, where `ε_cor` is the
correctness error of `kem`. -/
theorem security_kemFailure_le
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct)
    (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak)
    (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    Pr[ fun z => z.2.2 = true |
        (simulateQ (trackedSecurityImpl kem hDet ecEk ecCt leak b) adv).run
          (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym), false)] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp :=
  (OracleComp.tracked_bad_le_of_score_step _ (kemFailure hDet) (GameInv kem ecEk ecCt)
    (fun z => trackedScore hDet z)
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
    (kem.correctnessError ProbCompRuntime.probComp)
    (fun p hp => one_le_trackedScore_of_flag hDet p hp)
    (trackedSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak b)
    (trackedSecurity_score_step_le kem hDet ecEk ecCt hEk hCt leak b)
    adv q hq _ (trackedInv_init kem hDet ecEk ecCt)).trans_eq
    (by rw [trackedScore_init kem hDet, zero_add])

end oppBiKemCKA
