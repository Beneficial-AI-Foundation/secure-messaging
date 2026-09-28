/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Core

/-!
# Zero-send security

**Statement.** For every adversary `A` with `SecuritySendQueryBound A 0`,
the real-key and random-key fixed-bit experiments are equal, and A's
guessing advantage is zero. The result holds for every Opp-UniKEM instance
with deterministic decapsulation and on/off and leakage witnesses.

**Proof.** Every permitted query retains the initial local states and empty
message and key tables. Receives and challenges return their unavailable
response. Corruptions and adversary-randomness queries have the same
response/state computation in both branches. Induction on A's computation
gives experiment equality; the definition of advantage gives zero.

This supplies the boundary case `q = 0` of the security bound.
For positive budgets, the reduction selects an epoch from `1, …, q`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

open Reduction.Internal

variable {K PK SK C Sym : Type} [DecidableEq Sym] [DecidableEq K] [SampleableType K]

/-- An execution with zero ordinary or leaking sends has the same output
and state in both fixed-bit security experiments, for every KEM and choice
of erasure codes satisfying the construction interface. -/
theorem security_run_eq_of_zero_sends
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (hq : adv.IsQueryBoundP (fun t => isSecuritySendQuery t = true) 0) :
    (simulateQ (SCKAScheme.sckaSecurityImpl true (exposureA kem onoff leak)
      (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run (initialGame kem onoff) =
    (simulateQ (SCKAScheme.sckaSecurityImpl false (exposureA kem onoff leak)
      (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run (initialGame kem onoff) := by
  revert hq
  induction adv using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t adv ih =>
      intro hq
      rw [isQueryBoundP_query_bind_iff] at hq
      rcases t with (((((((((n | ⟨⟩) | ⟨⟩) | n) | n) | ⟨⟩) | ⟨⟩) | n) | ⟨⟩) | ⟨⟩)
      all_goals simp only [isSecuritySendQuery] at hq
      all_goals
        simp_all only [add_apply_inl, SCKAScheme.sckaSecurityImpl, SCKAScheme.sckaCorrectnessImpl,
          SCKAScheme.oracleUnif, QueryImpl.ofLift_eq_id', initialGame, SCKAScheme.initGameState,
          initialA, initialB, Bool.false_eq_true, not_false_eq_true, lt_self_iff_false, or_false,
          ↓reduceIte, true_and, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, QueryImpl.add_apply_inl, PFunctor.Handler.liftTarget_apply,
          PFunctor.selfMonomial_B, QueryImpl.id'_apply, StateT.run_bind,
          StateT.run_monadLift, monadLift_self, bind_pure_comp, map_eq_bind_pure_comp, bind_assoc,
          Function.comp_apply, pure_bind, add_apply_inr, not_true_eq_false, or_self, zero_tsub,
          false_and, QueryImpl.add_apply_inr, SCKAScheme.oracleRecvA, StateT.run_get,
          StateT.run_pure, SCKAScheme.oracleRecvB, SCKAScheme.oracleChall, Finset.notMem_empty,
          SCKAScheme.oracleCorruptA, vulnA,
          ne_eq, ite_not, Option.isSome_none, Finset.inter_self,
          Finset.union_idempotent, StateT.run_set, SCKAScheme.oracleCorruptB, vulnB]
      all_goals
        first
        | exact ih _ (hq _)
        | apply bind_congr; intro u; exact ih u (hq u)

/-- For every adversary with send budget zero, the Opp-UniKEM guessing
advantage is zero. -/
-- ANCHOR: security_zero_sends
theorem security_zero_sends
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (hq : SecuritySendQueryBound adv 0) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) = 0 := by
  have hrun := security_run_eq_of_zero_sends kem onoff hDet ecEk ecCt0 ecCt1 leak adv hq
  have hexp :
      SCKAScheme.securityExpFixedBit (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
        adv true (exposureA kem onoff leak) (exposureB kem onoff leak) =
      SCKAScheme.securityExpFixedBit (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
        adv false (exposureA kem onoff leak) (exposureB kem onoff leak) := by
    simpa [SCKAScheme.securityExpFixedBit, scheme, initKeyGen, initA, initB,
      initialGame, initialA, initialB] using congrArg (fun x => Prod.fst <$> x) hrun
  rw [SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two]
  simp [SCKAScheme.sckaDistAdvantage, hexp]
-- ANCHOR_END: security_zero_sends

end oppUniKemCKA
