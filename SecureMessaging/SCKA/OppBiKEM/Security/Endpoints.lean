/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.BadEvent
import SecureMessaging.SCKA.OppBiKEM.Security.IdealReceive
import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant

/-!
# Opp-BiKEM — Real-to-ideal endpoint

With deterministic decapsulation and correct erasure codes, the fixed-bit real security
experiment and the ideal one differ by at most `q · ε_cor` in the adversary's success
probability, for every adversary making at most `q` ordinary or leaking sends. The two games
agree on every state satisfying `GameInv` without current KEM failure, and the tracked real run
reaches a failure with probability at most `q · ε_cor`.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The ideal security oracles with the same sticky KEM-failure flag as `trackedSecurityImpl`. -/
abbrev trackedIdealImpl [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool)
        ProbComp) :=
  trackedImpl (idealSecurityImpl kem hDet ecEk ecCt leak b) (kemFailure hDet)

/-- The real fixed-bit security experiment is the adversary's guess after the security oracles
run from the initial game state. -/
lemma securityExpFixedBit_eq_run' [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (b : Bool) (adv : SecurityAdversary leak Sym) :
    SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv b
      (exposure .A leak) (exposure .B leak) =
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposure .A leak) (exposure .B leak)
        (scheme kem hDet ecEk ecCt leak)) adv).run'
        (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  simp [SCKAScheme.securityExpFixedBit, scheme, initKeyGen, initA, initB, init, initState,
    initialState, StateT.run'_eq, map_eq_bind_pure_comp]

/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then, for either challenge bit `b`, the real and ideal fixed-bit security experiments differ by
at most `q · ε_cor` in the probability that `adv` outputs `true`, where `ε_cor` is the
correctness error of `kem`. -/
theorem security_ideal_endpoint_le [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    |(Pr[= true | SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv b
        (exposure .A leak) (exposure .B leak)]).toReal -
      (Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak b adv]).toReal| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  have hagree : ∀ t p, trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet) p → ¬ p.2 = true →
      (trackedSecurityImpl kem hDet ecEk ecCt leak b t).run p =
        (trackedIdealImpl kem hDet ecEk ecCt leak b t).run p := by
    intro t p hp hgood
    obtain ⟨hs, hfail⟩ := trackedInv_of_flag_false hp (Bool.eq_false_iff.mpr hgood)
    rw [trackedImpl_run, trackedImpl_run,
      securityImpl_eq_ideal_of_noFailure kem hDet ecEk ecCt hCt leak b t p.1 hs hfail]
  have hbound := abs_probEvent_simulateQ_run_sub_le_bad_of_inv
    (trackedSecurityImpl kem hDet ecEk ecCt leak b) (trackedIdealImpl kem hDet ecEk ecCt leak b)
    (trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)) (fun p => p.2 = true)
    (trackedSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak b)
    (trackedImpl_preserves_flag _ _) hagree adv (fun guess => guess = true)
    (initState, false) (trackedInv_init kem hDet ecEk ecCt)
  have hl : Pr[= true | SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv b
      (exposure .A leak) (exposure .B leak)] =
      Pr[fun z => z.1 = true |
        (simulateQ (trackedSecurityImpl kem hDet ecEk ecCt leak b) adv).run
          (initState, false)] := by
    rw [securityExpFixedBit_eq_run', ← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map,
      ← tracked_run_project (SCKAScheme.sckaSecurityImpl b (exposure .A leak) (exposure .B leak)
        (scheme kem hDet ecEk ecCt leak)) (kemFailure hDet) adv (initState, false), probEvent_map]
    rfl
  have hr : Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak b adv] =
      Pr[fun z => z.1 = true |
        (simulateQ (trackedIdealImpl kem hDet ecEk ecCt leak b) adv).run
          (initState, false)] := by
    rw [idealSecurityExp, ← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map,
      ← tracked_run_project (idealSecurityImpl kem hDet ecEk ecCt leak b) (kemFailure hDet) adv
        (initState, false), probEvent_map]
    rfl
  rw [hl, hr]
  refine hbound.trans ?_
  have hbad := security_kemFailure_le kem hDet ecEk ecCt hEk hCt leak b adv q hq
  have hfinite : (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))
  have hreal := ENNReal.toReal_mono hfinite hbad
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

end oppBiKemCKA
