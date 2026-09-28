/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealReceive
import SecureMessaging.SCKA.OppUniKEM.Security.EpochBound

/-!
# Auxiliary security experiment

**Construction.** Fix `mode : ℕ → Bool`. The auxiliary oracle uses
`oracleRecvAIdeal`, which records B's encapsulated key at ciphertext
completion. Eligible challenges at epoch `t` return a uniform key if
`mode t = true`, and the recorded key otherwise. All challenges retain the
honest key tables. `idealSecurityExp` runs an adversary from the initial state.

**Results.** With correct erasure codes, every query preserves `reachableInv`.
For every bit `b`, query `t`, and state `s` satisfying `reachableInv` and
`CurrentKEMCorrect`, the real query computation equals the auxiliary one
with constant mode `b`.

**Proof.** Combine `IdealReceive` with the existing send, leakage, and
bookkeeping lemmas. `Endpoints` bounds the cost of this replacement;
`IdealHybrids` varies the challenge mode by epoch.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Auxiliary oracle family with encapsulated-key receive and a per-epoch
challenge mode: `false` returns the recorded key and `true` samples a
fresh uniform response. Both responses preserve the honest key tables. -/
-- ANCHOR: idealSecurityImpl
def idealSecurityImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  let scka := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak
  SCKAScheme.oracleUnif (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    + SCKAScheme.oracleSendA scka + SCKAScheme.oracleSendB scka
    + oracleRecvAIdeal kem onoff ecEk ecCt0 ecCt1 leak + SCKAScheme.oracleRecvB scka
    + SCKAScheme.oracleSendArleak sendExposureA scka
    + SCKAScheme.oracleSendBrleak sendExposureB scka
    + (fun t => SCKAScheme.oracleChall (mode t) (StA onoff Sym) (StB onoff Sym) K (Message Sym) t)
    + SCKAScheme.oracleCorruptA (vulnA (Sym := Sym) kem onoff) (StB onoff Sym) K (Message Sym)
    + SCKAScheme.oracleCorruptB (vulnB (Sym := Sym) kem onoff) (StA onoff Sym) K (Message Sym)
-- ANCHOR_END: idealSecurityImpl

/-- Run the full adversary from the empty epoch-one state in the auxiliary
game with per-epoch challenge mode `mode`, returning its raw Boolean guess. -/
def idealSecurityExp
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode) adv).run'
    (Reduction.Internal.initialGame kem onoff)

/-- With correct erasure codes, for every challenge mode, query, and
state `s` satisfying `reachableInv`, every supported auxiliary successor
satisfies `reachableInv`. A records B's encapsulated key at completion. -/
theorem idealSecurityImpl_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro t s hs z hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · exact oracleUnif_preserves_reachableInv kem onoff ecEk ecCt0 ecCt1 n s hs z hz
    · exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
        ecEk.ec.nchunk_pos u s hs z hz
    · exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
        ecCt1 ecCt1.ec.nchunk_pos leak u s hs z hz
    · exact oracleRecvAIdeal_preserves_reachableInv kem onoff ecEk ecCt0 hCt0 ecCt1 hCt1
        leak n s hs z hz
    · exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEk ecEk.ec.nchunk_pos
        ecCt0 ecCt1 leak n s hs z hz
  · exact oracleSendArleak_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
  · exact oracleSendBrleak_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
  · apply SCKAScheme.oracleChall_preservesInv (mode t)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) ?_ t s hs z hz
    intro state challenged hstate
    simpa using reachableInv_with_security_bookkeeping hstate state.exposed challenged
  · apply SCKAScheme.oracleCorruptA_preservesInv (vulnA (Sym := Sym) kem onoff)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) ?_ u s hs z hz
    intro state exposed hstate
    simpa using reachableInv_with_security_bookkeeping hstate exposed state.challenged
  · apply SCKAScheme.oracleCorruptB_preservesInv (vulnB (Sym := Sym) kem onoff)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) ?_ u s hs z hz
    intro state exposed hstate
    simpa using reachableInv_with_security_bookkeeping hstate exposed state.challenged

/-- Assume a correct online-component erasure code. For every bit `b`,
query `t`, and state `s` satisfying `reachableInv` and `CurrentKEMCorrect`,
the real query computation equals the auxiliary one with constant mode `b`,
including the response and complete successor state. -/
theorem securityImpl_eq_ideal_of_current
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s) :
    (SCKAScheme.sckaSecurityImpl b (exposureA (Sym := Sym) kem onoff leak)
      (exposureB (Sym := Sym) kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run s =
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b) t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals
      simp only [SCKAScheme.sckaSecurityImpl, SCKAScheme.sckaCorrectnessImpl,
        idealSecurityImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact oracleRecvA_eq_ideal kem onoff hDet ecEk ecCt0 ecCt1 hCt1 leak n s hs hc
  all_goals
    simp only [SCKAScheme.sckaSecurityImpl, idealSecurityImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]

end oppUniKemCKA.Security
