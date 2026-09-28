/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealGame
import SecureMessaging.SCKA.Security.HybridExposure
import SecureMessaging.SCKA.OppUniKEM.Security.IdealBounds
import SecureMessaging.SCKA.OppUniKEM.Security.ZeroEpoch
import ToVCVio.OracleComp.QueryTracking.StateBudgetSimulation

/-!
# Auxiliary epoch hybrids

**Construction.** For `i : ℕ`, hybrid `H_i` uses the auxiliary receive, where
A records B's encapsulated key. Eligible challenges in `1, …, i` return
uniform keys; other eligible challenges return recorded keys. Every
challenge retains the honest key tables. Hybrid `H_0` equals the auxiliary
real-key experiment. For every adversary with send budget `q`, hybrid
`H_q` equals the auxiliary random-key experiment.

**Statement.** For every `i : ℕ`, state `s` with `i + 1 ∈ s.exposed`, output
type `α`, and adaptive computation `A : OracleComp (securitySpec leak Sym) α`,
the complete output/state computations of `H_i(A)` and `H_{i+1}(A)` from `s`
are equal.

**Proof.** Exposure persists. The modes agree except at epoch `i + 1`, where
the exposure guard rejects both challenges. Query equality lifts to adaptive
execution and identifies the equal continuations used in exposure cancellation.
For `H_q`, the transcript and send-counter invariants restrict every available
challenge to `1, …, q`; state-budget simulation equality lifts the resulting
query equality to the complete experiment.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Auxiliary hybrid `i`: use random challenge responses exactly at
positive epochs at most `i`, retaining honest keys in the transcript. -/
-- ANCHOR: idealEpochHybridImpl
abbrev idealEpochHybridImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (i : ℕ) :=
  idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun t => decide (0 < t ∧ t ≤ i))
-- ANCHOR_END: idealEpochHybridImpl

/-- Boolean output of the adversary in auxiliary hybrid `i`, starting
with both parties in epoch one and empty message and key tables. -/
def idealEpochHybridExp
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (i : ℕ) : ProbComp Bool :=
  idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun t => decide (0 < t ∧ t ≤ i)) adv

/-- Hybrid zero is the auxiliary real-key experiment: the mode predicate
`0 < t ∧ t ≤ 0` is false for every epoch, so challenges return recorded keys. -/
theorem idealEpochHybridExp_zero
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) :
    idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0 =
      idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => false) adv := by
  have hmode : (fun t : ℕ => decide (0 < t ∧ t ≤ 0)) = fun _ => false := by
    funext t
    simp only [decide_eq_false_iff_not]
    omega
  simp only [idealEpochHybridExp, hmode]

/-- Every auxiliary oracle preserves exposure of epoch `e`, independently
of the challenge mode and the delivery, corruption, or send sequence. -/
theorem idealSecurityImpl_preserves_exposed
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => e ∈ s.exposed) := by
  intro t s hs z hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · have hz' : ∃ r, (r, s) = z := by
        simpa [idealSecurityImpl, SCKAScheme.oracleUnif] using hz
      obtain ⟨_, rfl⟩ := hz'
      exact hs
    · exact SCKAScheme.oracleSendA_preserves_exposed _ e u s hs z hz
    · exact SCKAScheme.oracleSendB_preserves_exposed _ e u s hs z hz
    · exact SCKAScheme.oracleRecvA_preserves_exposed
        (scheme (keyDecapsKEM kem (s.keyB s.stA.t))
          (keyDecapsOnOff kem onoff (s.keyB s.stA.t)) (keyDecapsDet kem (s.keyB s.stA.t))
          ecEk ecCt0 ecCt1 (keyDecapsLeak kem onoff leak (s.keyB s.stA.t))) e n s hs z hz
    · exact SCKAScheme.oracleRecvB_preserves_exposed
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) e n s hs z hz
  · exact SCKAScheme.oracleSendArleak_preserves_exposed _ sendExposureA e u s hs z hz
  · exact SCKAScheme.oracleSendBrleak_preserves_exposed _ sendExposureB e u s hs z hz
  · exact SCKAScheme.oracleChall_preservesInv (mode t) (fun s => e ∈ s.exposed)
      (fun _ _ h => h) t s hs z hz
  · exact SCKAScheme.oracleCorruptA_preserves_exposed (vulnA kem onoff) e u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preserves_exposed (vulnB kem onoff) e u s hs z hz

/-- Adjacent auxiliary hybrids give identical query computations from a
state in which their differing epoch `i + 1` is exposed. -/
theorem idealEpochHybrid_query_eq_of_exposed
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (i : ℕ)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : i + 1 ∈ s.exposed) :
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1) t).run s =
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals
    simp only [idealEpochHybridImpl, idealSecurityImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  by_cases ht : t = i + 1
  · subst t
    rw [SCKAScheme.oracleChall_rejected _ s _ (Or.inl hs),
      SCKAScheme.oracleChall_rejected _ s _ (Or.inl hs)]
  · rw [SCKAScheme.epochHybrid_challenge_eq_of_ne i t ht]

/-- Once epoch `i + 1` is exposed, the complete output/state computations
of auxiliary hybrids `i` and `i + 1` are equal for every continuation `adv`.
This equality identifies the exposed paths whose signed contributions cancel. -/
-- ANCHOR: idealEpochHybrid_run_eq_of_exposed
theorem idealEpochHybrid_run_eq_of_exposed
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (i : ℕ)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : i + 1 ∈ s.exposed) :
    (simulateQ (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1)) adv).run s =
      (simulateQ (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i) adv).run s := by
  have h := map_run_simulateQ_eq_of_query_map_eq_inv'
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1))
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i)
    (fun state => i + 1 ∈ state.exposed) id
    (idealSecurityImpl_preserves_exposed kem onoff hDet ecEk ecCt0 ecCt1 leak _ (i + 1))
    (fun t state hstate => by
      simpa using idealEpochHybrid_query_eq_of_exposed kem onoff hDet ecEk ecCt0 ecCt1
        leak i t state hstate)
    adv s hs
  simpa using h
-- ANCHOR_END: idealEpochHybrid_run_eq_of_exposed

/-- For every state `s` satisfying the transcript, epoch-zero, and send-count
invariants, every query has the same response/state distribution in hybrid
`q` and the auxiliary random-key game whenever `s.nA ≤ q`. Available keys
have epochs in `1, …, q`; both games reject unavailable challenges. -/
theorem idealEpochHybrid_query_eq_random
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (q : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : zeroEpochInv kem onoff ecEk ecCt0 ecCt1 s)
    (he : sendEpochInv s) (hc : s.nA ≤ q) :
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak q t).run s =
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true) t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals
    simp only [idealEpochHybridImpl, idealSecurityImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  by_cases hk : (s.keyA t).isSome ∨ (s.keyB t).isSome
  · have htq := (recorded_epoch_le_sends hz.1 he t hk).trans hc
    have hzero : s.keyA 0 = none := by
      obtain ⟨T, hT⟩ := hz.1
      simp [hT.keyA]
    have htpos : 0 < t := by
      by_contra hn
      have ht : t = 0 := by omega
      simp [ht, hzero, hz.2] at hk
    simp only [htpos, htq, and_self, decide_true]
  · have hA : s.keyA t = none := by
      cases h : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by
      cases h : s.keyB t <;> simp_all
    rw [SCKAScheme.oracleChall_unavailable _ s t hA hB,
      SCKAScheme.oracleChall_unavailable _ s t hA hB]

/-- Assume correct erasure codes. For every adversary `adv` with at most
`q` ordinary or leaking sends on each response path, auxiliary hybrid `q`
equals the auxiliary random-key experiment as a Boolean computation.
The proof combines per-query equality on bounded invariant states with
the adversary's send budget. -/
-- ANCHOR: idealEpochHybridExp_last
theorem idealEpochHybridExp_last
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv q =
      idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true) adv := by
  have hi : zeroEpochInv kem onoff ecEk ecCt0 ecCt1
      (Reduction.Internal.initialGame kem onoff) := by
    constructor
    · simpa [Reduction.Internal.initialGame, Reduction.Internal.initialA,
        Reduction.Internal.initialB] using
          reachableInv_init kem onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos
    · rfl
  have h := simulateQ_run_eq_of_query_eq_stateBudget
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak q)
    (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true))
    (fun s => zeroEpochInv kem onoff ecEk ecCt0 ecCt1 s ∧ sendEpochInv s)
    (fun s => s.nA) (fun t => isSecuritySendQuery t = true) q
    (fun t s hs z hz => ⟨
      idealSecurityImpl_preserves_zeroEpochInv kem onoff hDet ecEk hEk ecCt0 hCt0
        ecCt1 hCt1 leak _ t s hs.1 z hz,
      idealSecurityImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1
        leak _ t s hs.2 z hz⟩)
    (idealSecurityImpl_sendCounter_step kem onoff hDet ecEk ecCt0 ecCt1 leak _)
    (fun t s hs hc => idealEpochHybrid_query_eq_random kem onoff hDet ecEk ecCt0 ecCt1
      leak q t s hs.1 hs.2 hc)
    adv q hq (Reduction.Internal.initialGame kem onoff)
    ⟨hi, sendEpochInv_init kem onoff⟩ (by simp [Reduction.Internal.initialGame,
      SCKAScheme.initGameState])
  simpa only [idealEpochHybridExp, idealSecurityExp, StateT.run'_eq] using
    congrArg (fun c => Prod.fst <$> c) h
-- ANCHOR_END: idealEpochHybridExp_last

end oppUniKemCKA.Security
