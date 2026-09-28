/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealGame
import SecureMessaging.SCKA.OppUniKEM.Security.FailureBound
import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant

/-!
# Correctness-error endpoints of the security hybrids

**Experiments.** For `b : Bool`, let `G_b` be `securityExpFixedBit` and `I_b`
be `idealSecurityExp` with constant mode `b`. In `I_b`, A records B's
encapsulated key instead of decapsulating a completed ciphertext.

**Bound.** Given deterministic decapsulation, correct erasure codes, and
on/off and leakage witnesses, for every `q : ℕ` and adversary `A` with
`SecuritySendQueryBound A q`,
`|Pr[G_b(A) = true] - Pr[I_b(A) = true]| ≤ q · ε`,
where `ε` is the KEM correctness error interpreted in `ℝ`.

**Proof.** Track a persistent KEM-failure flag. `IdealGame` gives query
equality before failure; identical-until-bad bounds the acceptance gap
by the final failure probability; `FailureBound` gives the bound `q · ε`.
Projection lemmas remove the flag from both observable experiments.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For each bit `b`, augment the auxiliary game state `s` with a flag
updated after each query by `bad' = bad || currentKEMFailure(s')`.
The response and every field of `s'` are those of the auxiliary oracle. -/
def trackedIdealImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) ProbComp) :=
  fun t p => do
    let z ← (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b) t).run p.1
    pure (z.1, (z.2, p.2 || currentKEMFailure kem onoff hDet z.2))

/-- Forgetting the auxiliary execution's failure flag recovers its
complete original auxiliary output and state. -/
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
        adv).run p.1 := by
  apply map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst _ adv p
  intro t state
  simp [trackedIdealImpl, StateT.run, monad_norm]

/-- The real security monitor records KEM failure persistently, including
after the associated local material has been erased. -/
theorem trackedSecurityImpl_preserves_bad
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (fun p => p.2 = true) := by
  intro t p hp z hz
  simp only [trackedSecurityImpl, StateT.run, mem_support_bind_iff] at hz
  obtain ⟨y, _, hz⟩ := hz
  obtain rfl := (mem_support_pure_iff _ _).mp hz
  simp [hp]

/-- Opp-UniKEM's fixed-bit experiment is its oracle simulation from the
empty epoch-one state, projected to the adversary's raw output. -/
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

/-- Assume deterministic decapsulation, correct erasure codes, and on/off
and leakage witnesses. For every bit `b`, budget `q`, and adversary `adv`
with `SecuritySendQueryBound adv q`, the real and auxiliary fixed-bit
acceptance probabilities differ by at most `q · ε`, where
`ε = (kem.correctnessError ProbCompRuntime.probComp).toReal`.
The auxiliary receive records B's encapsulated key on ciphertext completion. -/
-- ANCHOR: security_correctness_endpoint_le
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
      simp only [StateT.run] at heq
      simp only [left, right, trackedSecurityImpl, trackedIdealImpl, StateT.run, heq]
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
-- ANCHOR_END: security_correctness_endpoint_le

end oppUniKemCKA.Security
