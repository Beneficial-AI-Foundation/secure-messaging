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
# Ideal hybrids

Let `scka` be the Opp-UniKEM protocol (`scheme`) over a KEM `kem` with deterministic decapsulation,
an offline/online encapsulation factorization, and correct erasure codes, and let `adv` be an
SCKA security adversary. Define:

- For `i : ℕ`, the ideal hybrid `H_i` runs `adv` from epoch `1` with no KEM material or
  chunks, empty message and key tables, and empty exposure and challenge sets. A uses B's recorded
  key instead of decapsulating; eligible challenges at epochs `1, …, i` return independent uniform
  keys, and all other eligible challenges return recorded keys. The game returns the output bit
  of `adv` (`idealEpochHybridExp … adv i`).
- For a uniform challenge bit `b` in the SCKA security game of `scka` and the output bit `b'` of
  `adv`, its guessing advantage is `AdvGuess_SCKA(scka, adv) := |Pr[b' = b] - 1/2|`. Here
  `b = true` selects uniform challenge keys and `b = false` selects recorded keys.
- For an honest key pair `(pk, sk) ← kem.keygen`, encapsulation `(ct, k) ← kem.encaps pk`,
  and decapsulation result `k' ← kem.decaps sk ct`, the correctness error is
  `ε := 1 - Pr[k' = some k]` (`kem.correctnessError`).

If `adv` makes at most `q : ℕ` ordinary and leaking sends on every oracle-response path
(`SecuritySendQueryBound adv q`), then (`security_guess_le_hybrid_gap`):

`AdvGuess_SCKA(scka, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`.

For an epoch `e > 0`, the *stopped hybrids* `S_e^real` and `S_e^random` run `H_{e-1}` and `H_e`,
which answer a challenge at `e` with the real (recorded) key and with an independent uniform key,
respectively, and return `false` at the first exposure of `e` by a permitted corruption or
leaking send. Stopping preserves the difference in acceptance probability
(`idealEpochHybrid_signed_gap_stop_eq`, stated for `e = i + 1`):

`Pr[S_e^random = true] - Pr[S_e^real = true] = Pr[H_e = true] - Pr[H_{e-1} = true]`.
-/

open OracleSpec OracleComp KEMScheme

namespace SCKAScheme

variable {StA StB I Rho : Type} [SampleableType I]

/-- For every epoch `t ≠ i + 1`, the challenge oracles of hybrids `i` and `i + 1` coincide on
`t`. -/
private theorem epochHybrid_challenge_eq_of_ne (i t : ℕ) (hne : t ≠ i + 1) :
    oracleChall (decide (0 < t ∧ t ≤ i + 1)) StA StB I Rho t =
      oracleChall (decide (0 < t ∧ t ≤ i)) StA StB I Rho t := by
  have h : (0 < t ∧ t ≤ i + 1) ↔ (0 < t ∧ t ≤ i) := by omega
  simp only [h]

end SCKAScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-! ### Send and epoch accounting -/

omit [SampleableType K] in
/-- Ideal correctness queries preserve `sendEpochInv`: A's epoch is at most its send count plus
one, and at most its send count when A holds a secret key. -/
private theorem idealCorrectnessImpl_preserves_sendEpochInv :
    QueryImpl.PreservesInv (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      sendEpochInv := by
  intro t s hs res hres
  rcases t with ((((n | u) | u) | n) | n)
  · rw [SCKAScheme.mem_support_oracleUnif_run n s res hres]; exact hs
  · exact oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs res hres
  · exact oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs res hres
  · exact oracleRecvAIdeal_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1
      leak n s hs res hres
  · exact oracleRecvB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs res hres

/-- Every query of `idealSecurityImpl` preserves `sendEpochInv`. -/
private theorem idealSecurityImpl_preserves_sendEpochInv
    (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      sendEpochInv :=
  SCKAScheme.securityImplOf_preservesInv_of_book _ _ _ _ _ sendEpochInv (fun _ _ _ h => h)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)
    (idealCorrectnessImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak)

/-- Every successor state `res.2` of a query `t` of `idealSecurityImpl` from `s` satisfies
`res.2.nA ≤ s.nA + 1` when `t` is a send query and `res.2.nA ≤ s.nA` otherwise. -/
private theorem idealSecurityImpl_sendCounter_step
    (mode : ℕ → Bool) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (res : (securitySpec leak Sym).Range t ×
      GameState onoff Sym)
    (hres : res ∈ support ((idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode t).run s)) :
    res.2.nA ≤ s.nA + if SCKAScheme.sckaSecuritySpec.isSendQuery t then 1 else 0 :=
  SCKAScheme.securityImplOf_nA_step _ _ _ _ _
    (idealCorrectnessImpl_nA_step kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _) t s res hres

include hEk hCt0 hCt1 in
/-- Assuming correct erasure codes, every ideal security query preserves consistency with a
protocol transcript (`reachableInv`). -/
private theorem idealSecurityImpl_preserves_reachableInv (mode : ℕ → Bool) :
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

/-- Challenge mode of the ideal hybrid `H_i`: a challenge at epoch `t` returns a uniform key
iff `0 < t ∧ t ≤ i`, and the recorded key otherwise. -/
def hybridMode (i t : ℕ) : Bool := decide (0 < t ∧ t ≤ i)

include hDet in
/-- Oracles of the ideal hybrid `H_i`: the ideal security oracles answering eligible
challenges at epochs `1, …, i` with uniform keys and later ones with recorded keys, that is,
`idealSecurityImpl` under the challenge mode `hybridMode i`. -/
abbrev idealEpochHybridImpl (i : ℕ) :=
  idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (hybridMode i)

include hDet in
/-- The ideal hybrid `H_i`: `adv` run from the initial game state against the ideal security
oracles that answer eligible challenges at epochs `1, …, i` with uniform keys and later ones with
recorded keys (`idealEpochHybridImpl … i`). -/
def idealEpochHybridExp
    (adv : SecurityAdversary leak Sym) (i : ℕ) : ProbComp Bool :=
  idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (hybridMode i) adv

/-- Challenge mode of the ideal hybrids adjacent at `e`: `adjacentMode e false` is the mode of
`H_{e-1}` and `adjacentMode e true` that of `H_e`, so a challenge at epoch `t` returns a uniform key
(`U`) iff `0 < t < e`, or `t = e` and `b = true`, and the recorded key (`R`) otherwise:

```text
epoch                  1   …   e-1   e   e+1  …
adjacentMode e false   U   …   U     R   R    …      (H_{e-1}, version real)
adjacentMode e true    U   …   U     U   R    …      (H_e, version random)
```
-/
def adjacentMode (e : ℕ) (b : Bool) : ℕ → Bool := hybridMode (if b then e else e - 1)

/-- `adjacentMode e b t` randomizes `t` iff `0 < t < e`, or `t = e` and `b = true`. -/
theorem adjacentMode_apply (e : ℕ) (b : Bool) (t : ℕ) :
    adjacentMode e b t = decide (0 < t ∧ (t < e ∨ (b = true ∧ t = e))) := by
  cases b <;> simp only [adjacentMode, hybridMode, Bool.false_eq_true, ↓reduceIte, false_and,
    or_false, true_and, decide_eq_decide] <;> omega

/-- The initial hybrid `idealEpochHybridExp … 0` (`H_0`) coincides with the real-key ideal game
`idealSecurityExp … (fun _ => false) adv` (`I_false`) as a probabilistic computation. -/
theorem idealEpochHybridExp_zero
    (adv : SecurityAdversary leak Sym) :
    idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0 =
      idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => false) adv := by
  have hmode : hybridMode 0 = fun _ => false := by
    funext t
    simp only [hybridMode, decide_eq_false_iff_not]
    omega
  simp only [idealEpochHybridExp, hmode]

/-- Every query of `idealSecurityImpl` is monotonic in the `exposed` epoch set. -/
private theorem idealSecurityImpl_exposed_subset
    (mode : ℕ → Bool) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (res : (securitySpec leak Sym).Range t ×
      GameState onoff Sym)
    (hres : res ∈ support ((idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode t).run s)) :
    s.exposed ⊆ res.2.exposed :=
  SCKAScheme.securityImplOf_exposed_subset _ _ _ _ _
    (fun t s res hres => (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak
      t s res hres).1) (SCKAScheme.challOf_recordsChallenges _) t s res hres

/-- Every query of `idealSecurityImpl` preserves membership `e ∈ s.exposed`. -/
private theorem idealSecurityImpl_preserves_exposed
    (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => e ∈ s.exposed) :=
  fun t s hs res hres => idealSecurityImpl_exposed_subset kem onoff hDet ecEk ecCt0 ecCt1 leak mode
    t s res hres hs

/-- In any state `s` satisfying `i + 1 ∈ s.exposed`, `idealEpochHybridImpl … (i + 1)` and
`idealEpochHybridImpl … i` evaluate every query `t` to the same response/state computation. -/
private theorem idealEpochHybrid_query_eq_of_exposed (i : ℕ)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : i + 1 ∈ s.exposed) :
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1) t).run s =
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i t).run s := by
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl) ?_ t
  intro t
  by_cases ht : t = i + 1
  · subst t
    exact SCKAScheme.oracleChall_run_eq_of_rejected _ _ s _ (Or.inl (Or.inl hs))
  · simp only [SCKAScheme.challOf, hybridMode]
    rw [SCKAScheme.epochHybrid_challenge_eq_of_ne i t ht]

/-- From any state `s` satisfying `i + 1 ∈ s.exposed`, simulating any oracle computation `adv`
under `idealEpochHybridImpl … (i + 1)` and `idealEpochHybridImpl … i` yields identical output/state
computations. -/
private theorem idealEpochHybrid_run_eq_of_exposed (i : ℕ)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (s : GameState onoff Sym)
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

/-- In any state `s` satisfying `reachableInv s`, `sendEpochInv s`, and `s.nA ≤ q`, the hybrid
oracles `idealEpochHybridImpl … q` and the random-key ideal oracles
`idealSecurityImpl … (fun _ => true)` evaluate every query `t` to the same response/state
computation. -/
private theorem idealEpochHybrid_query_eq_random
    (q : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
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
    simp only [SCKAScheme.challOf, hybridMode, htpos, htq, and_self, decide_true]
  · simp only [not_or, Option.not_isSome_iff_eq_none] at hk
    exact SCKAScheme.oracleChall_run_eq_of_rejected _ _ s t (Or.inr hk)

include hEk hCt0 hCt1 in
/-- Assuming the erasure codes are correct and `SecuritySendQueryBound adv q`, the final hybrid
`idealEpochHybridExp … q` (`H_q`) has the same acceptance probability as the random-key ideal game
`idealSecurityExp … (fun _ => true) adv` (`I_true`): `Pr[H_q = true] = Pr[I_true = true]`. -/
theorem idealEpochHybridExp_last
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    Pr{let x ← idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv q}[x = true] =
      Pr{let x ← (idealSecurityExp
          kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => true) adv)}[x = true] := by
  -- VCVio's query-bounded transport, with the remaining send budget `b` in the invariant.
  have h := OracleComp.ProgramLogic.Relational.evalDistEq_simulateQ_run_of_impl_eq_queryBound
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
    (fun t s b hs hcan res hres => by
      refine ⟨⟨idealSecurityImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0
          ecCt1 hCt1 leak _ t s hs.1.1 res hres,
        idealSecurityImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1
          leak _ t s hs.1.2 res hres⟩, ?_⟩
      have hb := hs.2
      have hc := idealSecurityImpl_sendCounter_step kem onoff hDet ecEk ecCt0 ecCt1 leak _
        t s res hres
      by_cases ht : SCKAScheme.sckaSecuritySpec.isSendQuery t = true
      · have hpos : 0 < b := hcan.resolve_left (not_not_intro ht)
        simp only [ht, ↓reduceIte] at hc ⊢
        omega
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc ⊢
        omega)
    (Reduction.Internal.initialGame kem onoff)
    ⟨⟨reachableInv_initialGame kem onoff ecEk ecCt0 ecCt1, sendEpochInv_init kem onoff⟩, by
      simp [Reduction.Internal.initialGame, SCKAScheme.initGameState]⟩
  simp only [idealEpochHybridExp, idealSecurityExp, StateT.run'_eq]
  exact (h.symm.map Prod.fst).prEvent_eq _

include hEk hCt0 hCt1 in
/-- Assuming the erasure codes are correct and `SecuritySendQueryBound adv q`, the SCKA guessing
advantage of `adv` is bounded by half the distance between the endpoint ideal hybrids
`H_0 := idealEpochHybridExp … 0` and `H_q := idealEpochHybridExp … q`, plus `q` times the KEM
correctness error `ε`:
`AdvGuess_SCKA(scka, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`. -/
theorem security_guess_le_hybrid_gap
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    |(Pr{let x ← idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0}[x = true]).toReal -
      (Pr{let x ← (idealEpochHybridExp
          kem onoff hDet ecEk ecCt0 ecCt1 leak adv q)}[x = true]).toReal| / 2 +
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two,
    SCKAScheme.sckaDistAdvantage,
    idealEpochHybridExp_zero,
    idealEpochHybridExp_last kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq]
  let G := fun b => (Pr{let x ← (SCKAScheme.securityExpFixedBit
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
    (exposureA kem onoff leak) (exposureB kem onoff leak))}[x = true]).toReal
  let I := fun b => (Pr{let x ← (idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1
    leak (fun _ => b) adv)}[x = true]).toReal
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

end

open SCKAScheme.sckaCorrectnessSpec SCKAScheme.sckaSecuritySpec

/-! ### Stopping at exposure -/

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Every query of `idealSecurityImpl` preserves `Disjoint s.exposed s.challenged`. -/
private theorem idealSecurityImpl_preserves_disjoint (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => Disjoint s.exposed s.challenged) :=
  SCKAScheme.securityImplOf_preserves_disjoint _ _ _ _ _
    (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _)

/-- Every query of `idealSecurityImpl` preserves membership `e ∈ s.challenged`. -/
private theorem idealSecurityImpl_preserves_challenged (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => e ∈ s.challenged) :=
  fun t s hs res hres => SCKAScheme.securityImplOf_challenged_subset _ _ _ _ _
    (fun t s res hres => (idealCorrectnessImpl_securitySets_eq kem onoff hDet ecEk ecCt0 ecCt1 leak
      t s res hres).2) (SCKAScheme.challOf_recordsChallenges _) t s res hres hs

/-- Every query of `idealSecurityImpl` preserves
`Disjoint s.exposed s.challenged ∧ e ∈ s.challenged`, ensuring that a challenged epoch `e` remains
unexposed. -/
private theorem idealSecurityImpl_preserves_committed (mode : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (fun s => Disjoint s.exposed s.challenged ∧ e ∈ s.challenged) := by
  intro t s hs res hres
  exact ⟨idealSecurityImpl_preserves_disjoint kem onoff hDet ecEk ecCt0 ecCt1
      leak mode t s hs.1 res hres,
    idealSecurityImpl_preserves_challenged kem onoff hDet ecEk ecCt0 ecCt1
      leak mode e t s hs.2 res hres⟩

/-- From any state `s` satisfying `Disjoint s.exposed s.challenged`, either
`idealEpochHybridImpl … (i + 1)` and `idealEpochHybridImpl … i` evaluate query `t` to the same
response/state computation, or `t` is an eligible challenge at epoch `i + 1` and every successor
state of either hybrid satisfies `Disjoint exposed challenged ∧ i + 1 ∈ challenged`. -/
private theorem idealEpochHybrid_query_eq_or_committed
    (i : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : Disjoint s.exposed s.challenged) :
    (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1) t).run s =
        (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i t).run s ∨
    ((∀ res ∈ support ((idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1
        leak (i + 1) t).run s),
        Disjoint res.2.exposed res.2.challenged ∧ i + 1 ∈ res.2.challenged) ∧
     (∀ res ∈ support ((idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1
        leak i t).run s), Disjoint res.2.exposed res.2.challenged ∧ i + 1 ∈ res.2.challenged)) := by
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
          intro res hres
          exact ⟨(SCKAScheme.challOf_recordsChallenges
              (hybridMode _)).preserves_disjoint (i + 1) s hs res hres,
            SCKAScheme.oracleChall_adds_challenged _ s _ helig hk res hres⟩
      · simp only [not_or, Option.not_isSome_iff_eq_none] at hk
        left
        exact (SCKAScheme.oracleChall_unavailable _ s _ hk.1 hk.2).trans
          (SCKAScheme.oracleChall_unavailable _ s _ hk.1 hk.2).symm
  · left
    change (SCKAScheme.oracleChall (decide (0 < t ∧ t ≤ i + 1)) _ _ _ _ t).run s =
      (SCKAScheme.oracleChall (decide (0 < t ∧ t ≤ i)) _ _ _ _ t).run s
    rw [SCKAScheme.epochHybrid_challenge_eq_of_ne i t ht]

/-- From any state `s` satisfying `Disjoint s.exposed s.challenged`, stopping at the first exposure
of epoch `i + 1` preserves the difference in acceptance probability between the adjacent ideal
hybrids `idealEpochHybridImpl … (i + 1)` (`H_{i+1}`) and `idealEpochHybridImpl … i` (`H_i`). -/
theorem idealEpochHybrid_signed_gap_stop_eq
    (i : ℕ) (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym)
    (hs : Disjoint s.exposed s.challenged) :
    (Pr{let x ← ((simulateQ
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1)) adv).run'
        s)}[x = true]).toReal -
    (Pr{let x ← ((simulateQ
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i) adv).run'
        s)}[x = true]).toReal =
    (Pr{let x ← (stoppedRun
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (i + 1))
      (fun u => decide (i + 1 ∈ u.exposed)) adv s)}[x = true]).toReal -
    (Pr{let x ← (stoppedRun
      (idealEpochHybridImpl kem onoff hDet ecEk ecCt0 ecCt1 leak i)
      (fun u => decide (i + 1 ∈ u.exposed)) adv s)}[x = true]).toReal := by
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

end

end oppUniKemCKA.Security
