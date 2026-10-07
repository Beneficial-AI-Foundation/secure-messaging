/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Stopping the auxiliary hybrids at exposure

**Setting.** Let `H_i` be the auxiliary hybrids of `IdealHybrids`. For `i : ℕ`, the *stopped*
version of a hybrid tests `i + 1 ∈ exposed` after every query and returns `false` as soon as
the test holds (`stoppedRun`).

**Result.** `idealEpochHybrid_signed_gap_stop_eq`: for every adversary and every initial state
with `Disjoint exposed challenged`,
`Pr[H_{i+1} = true] - Pr[H_i = true]` equals the same difference for the stopped hybrids.

The proof instantiates `signed_gap_stoppedRun_eq` with `committed s := Disjoint s.exposed
s.challenged ∧ i + 1 ∈ s.challenged`: a query of the two hybrids is either identical or an
answered challenge at `i + 1`, after which `i + 1` stays challenged and hence unexposed, and
from a state in which `i + 1` is exposed both hybrids have equal executions.
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

/-- Every auxiliary query preserves `Disjoint exposed challenged`, for every challenge mode. -/
theorem idealSecurityImpl_preserves_disjoint (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => Disjoint s.exposed s.challenged) :=
  SCKAScheme.securityImplOf_preserves_disjoint _ _ _ _ _
    (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)

/-- Every auxiliary query preserves membership of `e` in `challenged`, for every mode. -/
theorem idealSecurityImpl_preserves_challenged (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => e ∈ s.challenged) :=
  fun t s hs z hz => SCKAScheme.securityImplOf_challenged_subset _ _ _ _ _
    (fun t s z hz => (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak
      t s z hz).2) (SCKAScheme.challOf_recordsChallenges _) t s z hz hs

/-- For every auxiliary challenge mode and epoch `e`, each query preserves
`Disjoint exposed challenged ∧ e ∈ challenged`. Thus an answered challenge
remains protected by every subsequent exposure guard. -/
theorem idealSecurityImpl_preserves_committed (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => Disjoint s.exposed s.challenged ∧ e ∈ s.challenged) := by
  intro t s hs z hz
  exact ⟨idealSecurityImpl_preserves_disjoint kem onoff hDet ecEk ecCt0 ecCt1
      leak mode t s hs.1 z hz,
    idealSecurityImpl_preserves_challenged kem onoff hDet ecEk ecCt0 ecCt1
      leak mode e t s hs.2 z hz⟩

/-- For every index `i`, query, and state with disjoint exposure and
challenge sets, the adjacent auxiliary queries either have equal computations
or both place epoch `i + 1` in the challenged set while preserving disjointness. -/
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
      · have hA : s.keyA (i + 1) = none := by
          cases h : s.keyA (i + 1) <;> simp_all
        have hB : s.keyB (i + 1) = none := by
          cases h : s.keyB (i + 1) <;> simp_all
        left
        exact (SCKAScheme.oracleChall_unavailable _ s _ hA hB).trans
          (SCKAScheme.oracleChall_unavailable _ s _ hA hB).symm
  · left
    change (SCKAScheme.oracleChall (decide (0 < t ∧ t ≤ i + 1)) _ _ _ _ t).run s =
      (SCKAScheme.oracleChall (decide (0 < t ∧ t ≤ i)) _ _ _ _ t).run s
    rw [SCKAScheme.epochHybrid_challenge_eq_of_ne i t ht]

/-- For every index `i`, Boolean adversary `adv`, and initial state with
`Disjoint exposed challenged`, stopping after each query that exposes epoch
`i + 1` preserves the signed acceptance difference of auxiliary hybrids
`i + 1` and `i`. A stopped execution returns `false`. -/
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
