/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import SecureMessaging.SCKA.OppUniKEM.Security.FailureBound
import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant

/-!
# Opp-UniKEM correctness-error endpoints

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM with deterministic
decapsulation and correct erasure codes, let `adv : SecurityAdversary leak Sym` make at most
`q` ordinary or leaking sends on every response path (`SecuritySendQueryBound adv q`), and let
`ε` be the KEM correctness error.

For `b : Bool`, let `G_b` be the fixed-bit SCKA experiment, in which eligible challenges return
recorded keys (`b = false`) or independent uniform keys (`b = true`), and let `I_b` be the
auxiliary experiment of `Ideal`, in which A records B's encapsulated key at ciphertext
completion. Let `H_i` be the auxiliary hybrid of `IdealHybrids` randomizing the challenges at
epochs `1, …, i`, and `p_i := Pr[H_i(adv) = true]`.

- `security_correctness_endpoint_le`: for every `b`,
  `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`. Both games are extended by the failure flag of
  `FailureBound`; they agree query by query while the flag is unset, and the flag's final
  probability is at most `q · ε`.
- `security_guess_le_hybrid_gap`: `AdvGuess(Π, adv) ≤ |p_0 - p_q| / 2 + q · ε`. The guessing
  advantage is half the fixed-bit acceptance gap; `H_0 = I_false`, `H_q` has the acceptance
  probability of `I_true`, and the two endpoint bounds close the triangle inequality.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The auxiliary game with constant mode `b`, extended by the persistent failure flag. -/
def trackedIdealImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) ProbComp) :=
  QueryImpl.extendState (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b))
    (failureFlagUpdate kem onoff hDet)

/-- Dropping the failure flag from a tracked auxiliary execution gives the auxiliary execution. -/
theorem trackedIdeal_run_project
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ (trackedIdealImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run p =
      (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b))
        adv).run p.1 :=
  extendState_run_proj_eq _ _ adv p.1 p.2

/-- The fixed-bit security experiment equals the oracle simulation from `initialGame`,
projected to the adversary's output. -/
theorem securityExpFixedBit_eq_run'
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) :
    SCKAScheme.securityExpFixedBit (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
      (exposureA kem onoff leak) (exposureB kem onoff leak) =
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
        (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run' (initialGame kem onoff) := by
  simp [SCKAScheme.securityExpFixedBit, scheme, initKeyGen, initA, initB,
    initialGame, initialA, initialB, StateT.run'_eq, map_eq_bind_pure_comp]

/-- Under the module's assumptions, for every bit `b`, budget `q`, and adversary `adv`
satisfying `SecuritySendQueryBound adv q`, `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`. -/
theorem security_correctness_endpoint_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    |(Pr[= true | SCKAScheme.securityExpFixedBit
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
        (exposureA kem onoff leak) (exposureB kem onoff leak)]).toReal -
      (Pr[= true | idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak
        (fun _ => b) adv]).toReal| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  let left := trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
  let right := trackedIdealImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let s₀ := initialGame (Sym := Sym) kem onoff
  have hagree : ∀ t p, Inv p → ¬p.2 = true → (left t).run p = (right t).run p := by
    intro t p hp hgood
    rcases hp with hbad | ⟨hr, hf⟩
    · exact False.elim (hgood hbad)
    · have hc := currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
        p.1 hr hf
      have heq := securityImpl_eq_ideal_of_current kem onoff hDet ecEk ecCt0 ecCt1 hCt1
        leak b t p.1 hr hc
      simp only [left, right, trackedSecurityImpl, trackedIdealImpl, QueryImpl.extendState_apply]
      rw [heq]
  have hbound := abs_probEvent_simulateQ_run_sub_le_bad_of_inv left right Inv
    (fun p => p.2 = true)
    (trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak b)
    (trackedSecurityImpl_preserves_bad kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    hagree adv (fun guess => guess = true) (s₀, false)
    (tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
  have hl : Pr[= true | SCKAScheme.securityExpFixedBit
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b (exposureA kem onoff leak)
        (exposureB kem onoff leak)] =
      Pr[fun z => z.1 = true | (simulateQ left adv).run (s₀, false)] := by
    rw [securityExpFixedBit_eq_run', ← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map]
    rw [← trackedSecurity_run_project kem onoff hDet ecEk ecCt0 ecCt1 leak b adv (s₀, false),
      probEvent_map]
    rfl
  have hr : Pr[= true | idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b) adv] =
      Pr[fun z => z.1 = true | (simulateQ right adv).run (s₀, false)] := by
    rw [idealSecurityExp, ← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map]
    rw [← trackedIdeal_run_project kem onoff hDet ecEk ecCt0 ecCt1 leak b adv (s₀, false),
      probEvent_map]
    rfl
  rw [hl, hr]
  refine hbound.trans ?_
  have hbad := kem_failure_probability_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak b adv q hq
  have hfinite : (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))
  have hreal := ENNReal.toReal_mono hfinite hbad
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

/-- Under the module's assumptions, for every adversary `adv` and budget `q` satisfying
`SecuritySendQueryBound adv q`,
`AdvGuess ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`. -/
-- ANCHOR: security_guess_le_hybrid_gap
theorem security_guess_le_hybrid_gap
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    |(Pr[= true | idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0]).toReal -
      (Pr[= true | idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv q]).toReal| / 2 +
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two,
    SCKAScheme.sckaDistAdvantage,
    idealEpochHybridExp_zero,
    idealEpochHybridExp_last kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq]
  let G := fun b => (Pr[= true | SCKAScheme.securityExpFixedBit
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
    (exposureA kem onoff leak) (exposureB kem onoff leak)]).toReal
  let I := fun b => (Pr[= true | idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1
    leak (fun _ => b) adv]).toReal
  have h0 : |G false - I false| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal :=
    security_correctness_endpoint_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak false adv q hq
  have h1 : |G true - I true| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal :=
    security_correctness_endpoint_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak true adv q hq
  have htriangle := abs_sub_le (G true) (I true) (G false)
  have htriangle' := abs_sub_le (I true) (I false) (G false)
  rw [abs_sub_comm (I true) (I false), abs_sub_comm (I false) (G false)] at htriangle'
  change |G true - G false| / 2 ≤ |I false - I true| / 2 + _
  linarith
-- ANCHOR_END: security_guess_le_hybrid_gap

end oppUniKemCKA.Security
