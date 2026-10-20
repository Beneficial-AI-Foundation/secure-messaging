/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Stopping the ideal hybrids at exposure

Let `H_i` be the ideal hybrids of `IdealHybrids`. For `i : ℕ`, the hybrids `H_i` and `H_{i+1}`
*stopped at `i + 1`* run their oracles through `stoppedRun` with stop test `i + 1 ∈ exposed`:
they return `false` at the first query whose successor state exposes epoch `i + 1`.

`idealEpochHybrid_signed_gap_stop_eq`: for every adversary and every initial state with
`Disjoint exposed challenged`, the signed difference `Pr[H_{i+1} = true] - Pr[H_i = true]` of the
executions from that state equals the corresponding difference of the stopped executions.
-/

open OracleSpec OracleComp KEMScheme
open SCKAScheme.sckaCorrectnessSpec SCKAScheme.sckaSecuritySpec

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
variable (hDet : DeterministicDecaps kem)
variable (ecEk : ErasureCodePayload PK Sym)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)

/-- For every challenge mode, every query of the ideal game preserves
`Disjoint exposed challenged`. -/
theorem idealSecurityImpl_preserves_disjoint (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => Disjoint s.exposed s.challenged) :=
  SCKAScheme.securityImplOf_preserves_disjoint _ _ _ _ _
    (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)

/-- For every challenge mode, every query of the ideal game preserves `e ∈ challenged`. -/
theorem idealSecurityImpl_preserves_challenged (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => e ∈ s.challenged) :=
  fun t s hs z hz => SCKAScheme.securityImplOf_challenged_subset _ _ _ _ _
    (fun t s z hz => (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak
      t s z hz).2) (SCKAScheme.challOf_recordsChallenges _) t s z hz hs

/-- For every challenge mode and epoch `e`, every query of the ideal game preserves
`Disjoint exposed challenged ∧ e ∈ challenged`; in particular, `e` remains unexposed. -/
theorem idealSecurityImpl_preserves_committed (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => Disjoint s.exposed s.challenged ∧ e ∈ s.challenged) := by
  intro t s hs z hz
  exact ⟨idealSecurityImpl_preserves_disjoint kem onoff hDet ecEk ecCt0 ecCt1
      leak mode t s hs.1 z hz,
    idealSecurityImpl_preserves_challenged kem onoff hDet ecEk ecCt0 ecCt1
      leak mode e t s hs.2 z hz⟩

/-- For every index `i`, query `t`, and state `s` with `Disjoint s.exposed s.challenged`, either
the oracles of `H_{i+1}` and `H_i` give equal response/state computations for `t` from `s`, or
every possible successor state of either satisfies
`Disjoint exposed challenged ∧ i + 1 ∈ challenged`. -/
theorem idealEpochHybrid_query_eq_or_committed
    (i : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : Disjoint s.exposed s.challenged) :
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1) t).run s =
        (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i t).run s ∨
    ((∀ z ∈ support ((idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1
        leak (i + 1) t).run s),
        Disjoint z.2.exposed z.2.challenged ∧ i + 1 ∈ z.2.challenged) ∧
     (∀ z ∈ support ((idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1
        leak i t).run s), Disjoint z.2.exposed z.2.challenged ∧ i + 1 ∈ z.2.challenged)) := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try exact Or.inl rfl
  by_cases ht : t = i + 1
  · subst t
    by_cases helig : i + 1 ∈ s.exposed ∨ i + 1 ∈ s.challenged
    · left
      exact (SCKAScheme.oracleChall_rejected _ s _ helig).trans
        (SCKAScheme.oracleChall_rejected _ s _ helig).symm
    · by_cases hk : (s.keyA (i + 1)).isSome ∨ (s.keyB (i + 1)).isSome
      · right
        constructor
        all_goals
          intro z hz
          exact ⟨(SCKAScheme.challOf_recordsChallenges
              (fun t => decide (0 < t ∧ t ≤ _))).preserves_disjoint (i + 1) s hs z hz,
            SCKAScheme.oracleChall_adds_challenged _ s _ helig hk z hz⟩
      · simp only [not_or, Option.not_isSome_iff_eq_none] at hk
        left
        exact (SCKAScheme.oracleChall_unavailable _ s _ hk.1 hk.2).trans
          (SCKAScheme.oracleChall_unavailable _ s _ hk.1 hk.2).symm
  · left
    change (SCKAScheme.oracleChall (decide (0 < t ∧ t ≤ i + 1)) _ _ _ _ t).run s =
      (SCKAScheme.oracleChall (decide (0 < t ∧ t ≤ i)) _ _ _ _ t).run s
    rw [SCKAScheme.epochHybrid_challenge_eq_of_ne i t ht]

/-- For every index `i`, adversary `adv`, and initial state `s` with
`Disjoint s.exposed s.challenged`, stopping at the first query whose successor state exposes
`i + 1` preserves the signed difference of the acceptance probabilities of `H_{i+1}` and `H_i`
from `s`. -/
theorem idealEpochHybrid_signed_gap_stop_eq
    (i : ℕ) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : Disjoint s.exposed s.challenged) :
    (Pr[= true | (simulateQ
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1)) adv).run' s]).toReal -
    (Pr[= true | (simulateQ
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i) adv).run' s]).toReal =
    (Pr[= true | stoppedRun
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1))
      (fun u => decide (i + 1 ∈ u.exposed)) adv s]).toReal -
    (Pr[= true | stoppedRun
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i)
      (fun u => decide (i + 1 ∈ u.exposed)) adv s]).toReal := by
  -- A query of the two hybrids is identical or an answered challenge at `i + 1`; afterwards
  -- `i + 1` stays challenged, hence unexposed.
  apply signed_gap_stoppedRun_eq _ _
    (fun s => Disjoint s.exposed s.challenged)
    (fun s => Disjoint s.exposed s.challenged ∧ i + 1 ∈ s.challenged)
    (fun u => decide (i + 1 ∈ u.exposed))
    (idealSecurityImpl_preserves_disjoint kem onoff hDet ecEk ecCt0 ecCt1 leak _)
    (idealSecurityImpl_preserves_committed kem onoff hDet ecEk ecCt0 ecCt1 leak _ (i + 1))
    (idealSecurityImpl_preserves_committed kem onoff hDet ecEk ecCt0 ecCt1 leak _ (i + 1))
    _ (idealEpochHybrid_query_eq_or_committed kem onoff hDet ecEk ecCt0 ecCt1 leak i) _ adv s hs
  · intro u hu
    simp only [decide_eq_false_iff_not]
    exact fun he => Finset.disjoint_left.mp hu.1 he hu.2
  · intro u _ hu cont
    have he : i + 1 ∈ u.exposed := of_decide_eq_true hu
    have h := idealEpochHybrid_run_eq_of_exposed kem onoff hDet ecEk ecCt0 ecCt1 leak i cont u he
    simp only [StateT.run'_eq, h]

end oppUniKemCKA.Security
