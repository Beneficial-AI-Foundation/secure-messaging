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

**Setting.** Let `G_b := securityExpFixedBit … b` be the real SCKA security game of Opp-BiKEM
with challenge bit `b`, `I_b := idealSecurityExp … b adv` the ideal game (`IdealReceive`), and
`ε := kem.correctnessError` the KEM correctness error.

**Main result** (`security_ideal_endpoint_le`). With deterministic decapsulation and correct
erasure codes, for every adversary `adv` making at most `q` ordinary or leaking sends and either
bit `b`,

```text
|Pr[G_b = true] − Pr[I_b = true]| ≤ q · ε.
```

The two games agree on every state satisfying `GameInv` without current KEM failure
(`IdealReceive`), and the tracked real run reaches a failure with probability at most `q · ε`
(`BadEvent`); the identical-until-bad bound on invariant states
(`abs_prEvent_simulateQ_run_sub_le_bad_of_inv`) combines the two.
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

Then, for either challenge bit `b`, `|Pr[G_b = true] − Pr[I_b = true]| ≤ q · ε` for the real
game `G_b`, the ideal game `I_b` and the correctness error `ε` of `kem`. -/
theorem security_ideal_endpoint_le [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    |(Pr{let x ← SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv b
           (exposure .A leak) (exposure .B leak)}[x = true]).toReal -
      (Pr{let x ← idealSecurityExp kem hDet ecEk ecCt leak b adv}[x = true]).toReal| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  have hagree : ∀ t p, trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet) p → ¬ p.2 = true →
      (trackedSecurityImpl kem hDet ecEk ecCt leak b t).run p =
        (trackedIdealImpl kem hDet ecEk ecCt leak b t).run p := by
    intro t p hp hgood
    obtain ⟨hs, hfail⟩ := trackedInv_of_flag_false hp (Bool.eq_false_iff.mpr hgood)
    rw [trackedImpl_run, trackedImpl_run,
      securityImpl_eq_ideal_of_noFailure kem hDet ecEk ecCt hCt leak b t p.1 hs hfail]
  have hbound := abs_prEvent_simulateQ_run_sub_le_bad_of_inv
    (trackedSecurityImpl kem hDet ecEk ecCt leak b) (trackedIdealImpl kem hDet ecEk ecCt leak b)
    (trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)) (fun p => p.2 = true)
    (trackedSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak b)
    (trackedImpl_preserves_flag _ _) hagree adv (fun guess => guess = true)
    (initState, false) (trackedInv_init kem hDet ecEk ecCt)
  have hl : Pr{let x ← SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv b
                 (exposure .A leak) (exposure .B leak)}[x = true] =
      Pr{let z ← (simulateQ (trackedSecurityImpl kem hDet ecEk ecCt leak b) adv).run
          (initState, false)}[z.1 = true] := by
    rw [securityExpFixedBit_eq_run', StateT.run'_eq, prEvent_map,
      ← tracked_run_project (SCKAScheme.sckaSecurityImpl b (exposure .A leak) (exposure .B leak)
        (scheme kem hDet ecEk ecCt leak)) (kemFailure hDet) adv (initState, false), prEvent_map]
    rfl
  have hr : Pr{let x ← idealSecurityExp kem hDet ecEk ecCt leak b adv}[x = true] =
      Pr{let z ← (simulateQ (trackedIdealImpl kem hDet ecEk ecCt leak b) adv).run
          (initState, false)}[z.1 = true] := by
    rw [idealSecurityExp, StateT.run'_eq, prEvent_map,
      ← tracked_run_project (idealSecurityImpl kem hDet ecEk ecCt leak b) (kemFailure hDet) adv
        (initState, false), prEvent_map]
    rfl
  rw [hl, hr]
  refine hbound.trans ?_
  have hbad := security_kemFailure_le kem hDet ecEk ecCt hEk hCt leak b adv q hq
  have hfinite : (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))
  have hreal := ENNReal.toReal_mono hfinite hbad
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

end oppBiKemCKA
