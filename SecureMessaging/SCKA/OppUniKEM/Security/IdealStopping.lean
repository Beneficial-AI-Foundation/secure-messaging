/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import SecureMessaging.SCKA.Security.Bookkeeping
import ToVCVio.OracleComp.SimSemantics.StateT.StopGap

/-!
# Termination at exposure of the selected epoch

**Experiments.** For each `i : ℕ`, let `H_i` be the auxiliary hybrid that
randomizes challenges in `1, …, i`. Its stopped version tests whether
`i + 1` is exposed after every query and returns `false` when the test holds.

**Statement.** For every adversary and initial state with disjoint exposed
and challenged sets, the signed acceptance difference between `H_{i+1}`
and `H_i` equals the difference between their stopped versions.

**Proof.** Every query preserves disjointness and every answered challenge
remains recorded. A query either agrees in both hybrids or answers the
selected challenge, after which the selected epoch remains challenged and
its exposure test remains false. Once that epoch is exposed, all subsequent
queries have equal computations in the two hybrids. The generic stopped-run
identity cancels these equal continuation contributions.
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

/-- For every challenge mode, correctness-interface query, initial state,
and supported response/state pair, the auxiliary query retains both the
exposed and challenged sets. -/
theorem idealCorrectness_securitySets_eq
    (mode : ℕ → Bool) (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : (securitySpec leak Sym).Range (OCorrectness t) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
      mode (OCorrectness t)).run s)) :
    z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged := by
  rcases t with ((((n | u) | u) | n) | n)
  · exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) (OUnif n) s z hz
  · cases u
    exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) OSendA s z hz
  · cases u
    exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) OSendB s z hz
  · exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme (keyDecapsKEM kem (s.keyB s.stA.t))
        (keyDecapsOnOff kem onoff (s.keyB s.stA.t)) (keyDecapsDet kem (s.keyB s.stA.t))
        ecEk ecCt0 ecCt1 (keyDecapsLeak kem onoff leak (s.keyB s.stA.t))) (ORecvA n) s z hz
  · exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) (ORecvB n) s z hz

/-- For every challenge mode, each auxiliary query preserves disjointness
of exposed and challenged epochs. This follows from the exposure and
challenge guards for arbitrary local states and erasure codes. -/
theorem idealSecurityImpl_preserves_disjoint (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro t s hs z hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · obtain ⟨he, hc⟩ := idealCorrectness_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1
      leak mode t s z hz
    simpa only [he, hc] using hs
  · exact SCKAScheme.oracleSendArleak_preserves_disjoint sendExposureA _ u s hs z hz
  · exact SCKAScheme.oracleSendBrleak_preserves_disjoint sendExposureB _ u s hs z hz
  · exact SCKAScheme.oracleChall_preserves_disjoint (mode t) t s hs z hz
  · exact SCKAScheme.oracleCorruptA_preserves_disjoint (vulnA kem onoff) u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preserves_disjoint (vulnB kem onoff) u s hs z hz

/-- For every challenge mode and epoch `e`, each auxiliary query preserves
membership of `e` in the challenged set. Accepted challenges insert an epoch;
all other queries retain the set. -/
theorem idealSecurityImpl_preserves_challenged (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => e ∈ s.challenged) := by
  intro t s hs z hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · have hc := (idealCorrectness_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1
      leak mode t s z hz).2
    simpa only [hc] using hs
  · have hc := SCKAScheme.oracleSendArleak_challenged_eq sendExposureA _ u s z hz
    simpa only [hc] using hs
  · have hc := SCKAScheme.oracleSendBrleak_challenged_eq sendExposureB _ u s z hz
    simpa only [hc] using hs
  · exact SCKAScheme.oracleChall_preserves_challenged (mode t) e t s hs z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff)
      (fun s => e ∈ s.challenged) (fun _ _ h => h) u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff)
      (fun s => e ∈ s.challenged) (fun _ _ h => h) u s hs z hz

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
        leak (i + 1) t).run s), Disjoint z.2.exposed z.2.challenged ∧ i + 1 ∈ z.2.challenged) ∧
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
          exact ⟨SCKAScheme.oracleChall_preserves_disjoint _ _ s hs z hz,
            SCKAScheme.oracleChall_adds_challenged _ s _ helig hk z hz⟩
      · have hA : s.keyA (i + 1) = none := by
          cases h : s.keyA (i + 1) <;> simp_all
        have hB : s.keyB (i + 1) = none := by
          cases h : s.keyB (i + 1) <;> simp_all
        left
        exact (SCKAScheme.oracleChall_unavailable _ s _ hA hB).trans
          (SCKAScheme.oracleChall_unavailable _ s _ hA hB).symm
  · left
    simp only [idealEpochHybridImpl, idealSecurityImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    rw [SCKAScheme.epochHybrid_challenge_eq_of_ne i t ht]

/-- For every index `i`, Boolean adversary `adv`, and initial state with
`Disjoint exposed challenged`, stopping after each query that exposes epoch
`i + 1` preserves the signed acceptance difference of auxiliary hybrids
`i + 1` and `i`. A stopped execution returns `false`. -/
-- ANCHOR: idealEpochHybrid_signed_gap_stop_eq
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
-- ANCHOR_END: idealEpochHybrid_signed_gap_stop_eq

end oppUniKemCKA.Security
