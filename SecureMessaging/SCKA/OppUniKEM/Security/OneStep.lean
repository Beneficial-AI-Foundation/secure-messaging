/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Score

/-!
# One-query failure-potential bound

**Notation.** Let `Φ = trackedFailureScore`,
`ε = factorCorrectnessError kem onoff`, and `cost(t)` be one for any of
`SendA`, `SendB`, `SendArleak`, `SendBrleak`, and zero for other queries.

**Statement.** For every fixed challenge bit, query `t`, and tracked state
`p` satisfying `trackedInv`,
`E[Φ(p') : (answer, p') ← trackedSecurityImpl(t, p)] ≤ Φ(p) + cost(t) · ε`.

**Proof.** Ordinary queries use the correctness potential lemmas; leaking
sends use `Score`. Challenges and corruptions preserve the potential under
their bookkeeping updates. A set failure flag gives the bound directly.
`FailureBound` composes this estimate over the adversary's send-query budget.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

omit [DecidableEq Sym] in
/-- The send predicate on the security family restricts to the existing
correctness-game send predicate on ordinary send/receive queries. -/
private theorem isSecuritySendQuery_correctness
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain) :
    isSecuritySendQuery (.inl (.inl (.inl (.inl (.inl t))))) = isSendQuery t := by
  rcases t with ((((n | u) | u) | n) | n) <;> rfl

/-- For every fixed bit, query `t`, and tracked state `p` satisfying
`trackedInv`, the expected successor score is at most the current score
plus `factorCorrectnessError kem onoff` for a send, and plus zero otherwise.
The four sends are selected by `isSecuritySendQuery`. -/
theorem trackedSecurity_score_step_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
    (hp : trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p) :
    expectedPayoff ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b t).run p)
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff p +
        if isSecuritySendQuery t then factorCorrectnessError kem onoff else 0 := by
  by_cases hbad : p.2 = true
  · refine (expectedPayoff_le_one _ _ ?_).trans ?_
    · intro z
      exact trackedFailureScore_le_one kem onoff z.2
    · simp [trackedFailureScore, hbad]
  have hfalse : p.2 = false := Bool.eq_false_iff.mpr hbad
  have hgood : reachableInv kem onoff ecEk ecCt0 ecCt1 p.1 ∧
      currentKEMFailure kem onoff hDet p.1 = false := by
    rcases hp with hp | hp
    · exact False.elim (hbad hp)
    · exact hp
  have hpEq : p = (p.1, false) := Prod.ext rfl hfalse
  rw [hpEq]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [isSecuritySendQuery_correctness (Sym := Sym)]
    exact tracked_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak t (p.1, false)
      (Or.inr hgood)
  · cases u
    simpa only [isSecuritySendQuery, ↓reduceIte] using
      tracked_sendArleak_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak b p.1 hgood.1 hgood.2
  · cases u
    simpa only [isSecuritySendQuery, ↓reduceIte] using
      tracked_sendBrleak_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak b p.1 hgood.1 hgood.2
  all_goals
    simp only [isSecuritySendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    apply expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
    intro z hz
    change z ∈ support (do
      let y ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) _).run p.1
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    simp only [mem_support_pure_iff] at hz
    subst z
    let J := fun s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) =>
      currentKEMFailure kem onoff hDet s = false ∧
      currentFailurePotential kem onoff s = currentFailurePotential kem onoff p.1
    have hj : J p.1 := ⟨hgood.2, rfl⟩
    suffices hout : J y.2 by
      exact le_of_eq (by simp [trackedFailureScore, hout.1, hout.2])
  · apply SCKAScheme.oracleChall_preservesInv b J ?_ t p.1 hj y hy
    intro state challenged hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate

end oppUniKemCKA.Security
