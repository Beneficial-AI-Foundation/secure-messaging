/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Ideal epoch hybrids

**Setting.** Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM with
deterministic decapsulation and correct erasure codes, and let `adv : SecurityAdversary leak Sym`
be an adversary. Let `idealSecurityImpl … mode` be the oracles of the ideal game of `Endpoints`,
in which A uses B's recorded key in place of decapsulation and `mode : ℕ → Bool` selects the
epochs with uniform challenge keys, and let `I_b := idealSecurityExp (fun _ => b) adv`.

**Definitions.** For `i : ℕ`, the ideal hybrid `H_i := idealEpochHybridExp … adv i` answers
eligible challenges at epochs `1, …, i` with independent uniform keys and other eligible
challenges with recorded keys. The hybrids `H_i` and `H_{i+1}` *stopped at `i + 1`* run their
oracles through `stoppedRun` with stop test `i + 1 ∈ exposed`: they return `false` at the first
query whose successor state exposes epoch `i + 1`.

**Results.** Let `ε` be the KEM correctness error and `AdvGuess(Π, adv) := |Pr[b' = b] - 1/2|`
the guessing advantage, where the game samples a uniform bit `b` and `adv` returns `b'`.

- Accounting: for every `mode`, every query preserves `sendEpochInv` and, with correct erasure
  codes, `reachableInv`; every possible successor `s'` of a query from `s` satisfies
  `s'.nA ≤ s.nA + 1` for the four send queries and `s'.nA ≤ s.nA` otherwise.
- `idealEpochHybridExp_zero`: `H_0 = I_false` as computations.
- `idealEpochHybrid_run_eq_of_exposed`: from every state in which epoch `i + 1` is exposed, the
  oracles of `H_i` and `H_{i+1}` give equal output/state computations for every continuation.
- `idealEpochHybridExp_last`: if `SecuritySendQueryBound adv q`, then
  `Pr[H_q = true] = Pr[I_true = true]`.
- `security_guess_le_hybrid_gap`: if `SecuritySendQueryBound adv q`, then
  `AdvGuess(Π, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`.
- `idealEpochHybrid_signed_gap_stop_eq`: for every adversary and every initial state with
  `Disjoint exposed challenged`, the signed difference `Pr[H_{i+1} = true] - Pr[H_i = true]` of
  the executions from that state equals that of the executions stopped at `i + 1`.
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

/-! ### Send and epoch accounting -/

omit [SampleableType K] in
/-- Every correctness query of the ideal game preserves `sendEpochInv`. -/
theorem idealCorrectnessImpl_preserves_sendEpochInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      sendEpochInv := by
  intro t s hs z hz
  rcases t with ((((n | u) | u) | n) | n)
  · rw [SCKAScheme.mem_support_oracleUnif_run n s z hz]; exact hs
  · exact oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
  · exact oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
  · exact oracleRecvAIdeal_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1
      leak n s hs z hz
  · exact oracleRecvB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs z hz

/-- For every challenge mode, every query of the ideal game preserves `sendEpochInv`. -/
theorem idealSecurityImpl_preserves_sendEpochInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      sendEpochInv :=
  SCKAScheme.securityImplOf_preservesInv_of_book _ _ _ _ _ sendEpochInv (fun _ _ _ h => h)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)
    (idealCorrectnessImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)

/-- For every challenge mode, query `t`, and possible successor `z.2` of `t` from `s`,
`z.2.nA ≤ s.nA + 1` if `t` is one of the four send queries and `z.2.nA ≤ s.nA` otherwise. -/
theorem idealSecurityImpl_sendCounter_step
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
    z.2.nA ≤ s.nA + if SCKAScheme.sckaSecuritySpec.isSendQuery t then 1 else 0 :=
  SCKAScheme.securityImplOf_nA_step _ _ _ _ _
    (idealCorrectnessImpl_nA_step kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _) t s z hz

/-- With correct erasure codes, for every challenge mode, every query of the ideal game
preserves `reachableInv`. -/
theorem idealSecurityImpl_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) :=
  SCKAScheme.securityImplOf_preservesInv_of_book _ _ _ _ _ _
    (fun _ E C h => reachableInv_with_security_bookkeeping h E C)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)
    (idealCorrectnessImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak)
    (oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak ecEk.ec.nchunk_pos)
    (oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak)

/-! ### Hybrids -/

/-- The oracles of `H_i`: the ideal game's oracles with challenge mode `t ↦ 0 < t ∧ t ≤ i`. -/
abbrev idealEpochHybridImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (i : ℕ) :=
  idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun t => decide (0 < t ∧ t ≤ i))

/-- The ideal hybrid `H_i`: run `adv` against `idealEpochHybridImpl … i` from the initial state
and return its output bit. -/
def idealEpochHybridExp
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (i : ℕ) : ProbComp Bool :=
  idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun t => decide (0 < t ∧ t ≤ i)) adv

/-- `H_0 = I_false` as computations. -/
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

/-- For every challenge mode, no query of the ideal game removes an exposed epoch. -/
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

/-- For every challenge mode, every query of the ideal game preserves `e ∈ exposed`. -/
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

/-- From a state in which epoch `i + 1` is exposed, the oracles of `H_{i+1}` and `H_i`
give equal response/state computations for every query. -/
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

/-- From a state in which epoch `i + 1` is exposed, the oracles of `H_{i+1}` and `H_i` give
equal output/state computations for every continuation `adv`. -/
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

/-- For every state `s` satisfying `reachableInv s`, `sendEpochInv s`, and `s.nA ≤ q`, the
oracles of `H_q` and `I_true` give equal response/state computations from `s` for every query. -/
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
    have htpos : 0 < t := Nat.pos_of_ne_zero fun ht => by
      simp [ht, hzeroA, hT.keyB_zero] at hk
    simp only [SCKAScheme.challOf, htpos, htq, and_self, decide_true]
  · simp only [not_or, Option.not_isSome_iff_eq_none] at hk
    exact SCKAScheme.oracleChall_run_eq_of_rejected _ _ s t (Or.inr hk)

/-- With correct erasure codes, if `SecuritySendQueryBound adv q`, then
`Pr[H_q = true] = Pr[I_true = true]`. -/
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

/-- With correct erasure codes, if `SecuritySendQueryBound adv q`, then
`AdvGuess(Π, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`. -/
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
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal
-- ANCHOR_END: security_guess_le_hybrid_gap
    := by
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

end oppUniKemCKA.Security

/-! ### Stopping at exposure -/

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
