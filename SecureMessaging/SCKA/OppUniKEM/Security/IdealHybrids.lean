/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealInvariants
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Auxiliary epoch hybrids

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM with deterministic
decapsulation and correct erasure codes, and let `adv : SecurityAdversary leak Sym` be an
adversary. For `i : ℕ`, let
`H_i := idealEpochHybridExp … adv i` be the auxiliary experiment whose eligible challenges
at epochs `1, …, i` return uniform keys; other eligible challenges return recorded keys.
For `b : Bool`, let `I_b := idealSecurityExp (fun _ => b) adv`.

- `idealEpochHybridExp_zero`: `H_0 = I_false` as computations.
- `idealEpochHybrid_run_eq_of_exposed`: from any state where epoch `i + 1` is exposed,
  auxiliary hybrids `i` and `i + 1` have equal output/state computations for every continuation.
- `idealEpochHybridExp_last`: if `SecuritySendQueryBound adv q`, then
  `Pr[H_q = true] = Pr[I_true = true]`.
-/

open OracleSpec OracleComp KEMScheme

namespace SCKAScheme

variable {StA StB I Rho : Type} [SampleableType I]

/-- For every epoch `t ≠ i + 1`, the challenge oracles of epoch hybrids `i` and `i + 1` agree
on `t`. -/
theorem epochHybrid_challenge_eq_of_ne (i t : ℕ) (hne : t ≠ i + 1) :
    oracleChall (decide (0 < t ∧ t ≤ i + 1)) StA StB I Rho t =
      oracleChall (decide (0 < t ∧ t ≤ i)) StA StB I Rho t := by
  have h : (0 < t ∧ t ≤ i + 1) ↔ (0 < t ∧ t ≤ i) := by omega
  simp only [h]

end SCKAScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The auxiliary oracle implementation whose eligible challenges at epochs `1, …, i`
return uniform keys, and whose other eligible challenges return recorded keys. -/
abbrev idealEpochHybridImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (i : ℕ) :=
  idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun t => decide (0 < t ∧ t ≤ i))

/-- The adversary's Boolean output in auxiliary hybrid `i`, starting from the initial state. -/
def idealEpochHybridExp
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (i : ℕ) : ProbComp Bool :=
  idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun t => decide (0 < t ∧ t ≤ i)) adv

/-- Hybrid zero equals the auxiliary real-key experiment as a computation. -/
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

/-- No auxiliary query removes an exposed epoch, for every challenge mode. -/
theorem idealSecurityImpl_exposed_subset
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode t).run s)) :
    s.exposed ⊆ z.2.exposed :=
  SCKAScheme.securityImplOf_exposed_subset _ _ _ _ _
    (fun t s z hz => (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak
      t s z hz).1) (SCKAScheme.challOf_recordsChallenges _) t s z hz

/-- Every auxiliary query preserves exposure of epoch `e`, for every challenge mode. -/
theorem idealSecurityImpl_preserves_exposed
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => e ∈ s.exposed) :=
  fun t s hs z hz => idealSecurityImpl_exposed_subset kem onoff hDet ecEk ecCt0 ecCt1 leak mode
    t s z hz hs

/-- From a state in which epoch `i + 1` is exposed, every query of `H_{i+1}` equals the
corresponding query of `H_i` as a computation. -/
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
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl) ?_ t
  intro t
  by_cases ht : t = i + 1
  · subst t
    exact SCKAScheme.oracleChall_run_eq_of_rejected _ _ s _ (Or.inl (Or.inl hs))
  · simp only [SCKAScheme.challOf]
    rw [SCKAScheme.epochHybrid_challenge_eq_of_ne i t ht]

/-- Once epoch `i + 1` is exposed, auxiliary hybrids `i` and `i + 1` have equal
output/state computations for every continuation `adv`. -/
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

/-- For every state `s` satisfying `reachableInv s`, `sendEpochInv s`, and `s.nA ≤ q`,
each query of auxiliary hybrid `q` equals the corresponding query with constant mode `true`
as a response/state computation. -/
theorem idealEpochHybrid_query_eq_random
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (q : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hr : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (he : sendEpochInv s) (hc : s.nA ≤ q) :
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak q t).run s =
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true) t).run s := by
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl) ?_ t
  intro t
  by_cases hk : (s.keyA t).isSome ∨ (s.keyB t).isSome
  · have htq := (recorded_epoch_le_sends hr he t hk).trans hc
    obtain ⟨T, hT⟩ := hr
    have hzeroA : s.keyA 0 = none := by simp [hT.keyA]
    have htpos : 0 < t := by
      by_contra hn
      have ht : t = 0 := by omega
      simp [ht, hzeroA, hT.keyB_zero] at hk
    simp only [SCKAScheme.challOf, htpos, htq, and_self, decide_true]
  · have hA : s.keyA t = none := by
      cases h : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by
      cases h : s.keyB t <;> simp_all
    exact SCKAScheme.oracleChall_run_eq_of_rejected _ _ s t (Or.inr ⟨hA, hB⟩)

/-- With correct erasure codes, for every adversary `adv` satisfying
`SecuritySendQueryBound adv q`, `Pr[H_q = true] = Pr[I_true = true]`. -/
theorem idealEpochHybridExp_last
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    Pr[= true | idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv q] =
      Pr[= true | idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true) adv] := by
  -- VCVio's query-bounded transport, with the remaining send budget `b` in the invariant.
  have h z := OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_queryBound
    (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true))
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak q)
    (fun s b => (reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧ sendEpochInv s) ∧ s.nA + b ≤ q)
    (fun t b => ¬ (SCKAScheme.sckaSecuritySpec.isSendQuery t = true) ∨ 0 < b)
    (fun t b => if SCKAScheme.sckaSecuritySpec.isSendQuery t = true then b - 1 else b)
    adv q hq
    (fun t s b hs _ => by
      have hb := hs.2
      exact (idealEpochHybrid_query_eq_random kem onoff hDet ecEk ecCt0 ecCt1
        leak q t s hs.1.1 hs.1.2 (by omega)).symm)
    (fun t s b hs hcan z hz => by
      refine ⟨⟨idealSecurityImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0
          ecCt1 hCt1 leak _ t s hs.1.1 z hz,
        idealSecurityImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1
          leak _ t s hs.1.2 z hz⟩, ?_⟩
      have hb := hs.2
      have hc := idealSecurityImpl_sendCounter_step kem onoff hDet ecEk ecCt0 ecCt1 leak _
        t s z hz
      by_cases ht : SCKAScheme.sckaSecuritySpec.isSendQuery t = true
      · have hpos : 0 < b := hcan.resolve_left (not_not_intro ht)
        simp only [ht, ↓reduceIte] at hc ⊢
        omega
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc ⊢
        omega)
    (Reduction.Internal.initialGame kem onoff)
    ⟨⟨reachableInv_initialGame kem onoff ecEk ecCt0 ecCt1, sendEpochInv_init kem onoff⟩, by
      simp [Reduction.Internal.initialGame, SCKAScheme.initGameState]⟩ z
  simp only [idealEpochHybridExp, idealSecurityExp, StateT.run'_eq]
  exact probOutput_map_eq_of_evalDist_eq (evalDist_ext fun z => (h z).symm) Prod.fst true

end oppUniKemCKA.Security
