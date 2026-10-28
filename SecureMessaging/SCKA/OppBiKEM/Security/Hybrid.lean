/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Endpoints
import SecureMessaging.SCKA.OppBiKEM.Security.EpochCount
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Opp-BiKEM — Epoch challenge hybrids

**Setting.** Let `I_b := idealSecurityExp … b adv` be the ideal game (`IdealReceive`) and
`ε := kem.correctnessError` the KEM correctness error. The *hybrid* `H_T := hybridExp … T adv`
with threshold `T` is the ideal game answering eligible challenges at epochs below `T` with
independent uniform keys and all others with the recorded key
(`hybridSecurityImpl (hybridRandom T)`); its table values, sends, receives, leaking sends and
corruptions are those of the ideal game. Let `p_T := Pr[H_T = true]`.

```text
epoch    0   1   …   T−1   T   T+1   …
H_T      U   U   …   U     R   R     …        (U: uniform key, R: recorded key)
```

**Main results.** Assume that the erasure codes are correct and that `adv` makes at most `q`
ordinary or leaking sends.

- `H_0 = I_false` (`hybridExp_zero`), and `p_1 = p_0`, because epoch `0` is never keyed
  (`probOutput_hybridExp_one`).
- `p_T = Pr[I_true = true]` for every `T > 2q` (`probOutput_hybridExp_top`): a challengeable
  epoch is keyed, hence at most `2 · advances s ≤ 2q` (`EpochCount`).
- `AdvGuess_SCKA(scka, adv) ≤ q · ε + |Pr[I_true = true] − Pr[I_false = true]| / 2`
  (`sckaGuessAdvantage_le_ideal_term`), and
  `|Pr[I_true = true] − Pr[I_false = true]| ≤ Σ_{t=0}^{2q} |p_{t+1} − p_t|`
  (`idealDist_le_sum_hybrid_hops`).
- For every `δ : ℕ → ℝ` that is non-negative and satisfies `|p_{t+1} − p_t| ≤ δ t` at every
  `1 ≤ t ≤ 2q`, `AdvGuess_SCKA(scka, adv) ≤ q · ε + (1/2) · Σ_{t=0}^{2q} δ t`
  (`sckaGuessAdvantage_le_of_hop_bound`).

`Security` supplies the per-hop bound `δ t` as the IND-CPA advantage of the reduction at target
`t`.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Random challenge answers exactly at the epochs below the threshold `T`. -/
def hybridRandom (T : ℕ) : ℕ → Bool := fun t => decide (t < T)

/-- Threshold `0` selects no epoch. -/
lemma hybridRandom_zero : hybridRandom 0 = fun _ => false := by
  funext t; simp [hybridRandom]

/-- Given a lifted `StateT` computation whose output-state distributions agree with another's
from `s`, the two output distributions agree. -/
lemma probOutput_run'_eq_of_run_eq {σ α : Type} (x y : StateT σ ProbComp α) (s : σ)
    (h : ∀ z, Pr[= z | x.run s] = Pr[= z | y.run s]) (a : α) :
    Pr[= a | x.run' s] = Pr[= a | y.run' s] := by
  rw [StateT.run'_eq, StateT.run'_eq, probOutput_map_eq_tsum, probOutput_map_eq_tsum]
  exact tsum_congr fun z => by rw [h z]

section Hybrid

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-- The ideal security oracles with challenge answers random exactly at the epochs selected by
`random`; all table values stay honest. The constant selection `fun _ => b` gives
`idealSecurityImpl … b`. -/
def hybridSecurityImpl (random : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.securityImplOf (idealCorrectnessImpl kem hDet ecEk ecCt leak)
    (SCKAScheme.oracleChallOn random _ _ _ _) (exposure .A leak) (exposure .B leak)
    (scheme kem hDet ecEk ecCt leak)

/-- A constant selection is the fixed-bit ideal game. -/
lemma hybridSecurityImpl_const (b : Bool) :
    hybridSecurityImpl kem hDet ecEk ecCt leak (fun _ => b) =
      idealSecurityImpl kem hDet ecEk ecCt leak b := rfl

/-- The `T`-th hybrid experiment: the adversary's guess after the hybrid oracles with threshold
`T` run from the initial game state. -/
def hybridExp (T : ℕ) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom T)) adv).run'
    (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))

/-- Every hybrid query is a fixed-bit ideal query: the bit is `random e` for a challenge at
epoch `e` and irrelevant for every other query. -/
lemma hybridSecurityImpl_query_eq_ideal (random : ℕ → Bool)
    (t : (securitySpec leak Sym).Domain) :
    ∃ b : Bool, ∀ s, (hybridSecurityImpl kem hDet ecEk ecCt leak random t).run s =
      (idealSecurityImpl kem hDet ecEk ecCt leak b t).run s := by
  rcases t with (((((t | u) | u) | e) | u) | u)
  · exact ⟨true, fun _ => rfl⟩
  · exact ⟨true, fun _ => rfl⟩
  · exact ⟨true, fun _ => rfl⟩
  · exact ⟨random e, fun _ => rfl⟩
  · exact ⟨true, fun _ => rfl⟩
  · exact ⟨true, fun _ => rfl⟩

/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes.

Then every hybrid query preserves `GameInv`, for every selection `random`. -/
lemma hybridSecurityImpl_preservesInv (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (random : ℕ → Bool) :
    QueryImpl.PreservesInv (hybridSecurityImpl kem hDet ecEk ecCt leak random)
      (GameInv kem ecEk ecCt) := by
  intro t s hs z hz
  obtain ⟨b, hb⟩ := hybridSecurityImpl_query_eq_ideal kem hDet ecEk ecCt leak random t
  rw [hb] at hz
  exact idealSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak b t s hs z hz

/-- Every hybrid query raises `advances` by at most one if it is an ordinary or leaking send
and not at all otherwise, on every state. -/
lemma advances_step_hybrid (random : ℕ → Bool) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((hybridSecurityImpl kem hDet ecEk ecCt leak random t).run s)) :
    advances z.2 ≤ advances s +
      if SCKAScheme.sckaSecuritySpec.isSendQuery t = true then 1 else 0 := by
  obtain ⟨b, hb⟩ := hybridSecurityImpl_query_eq_ideal kem hDet ecEk ecCt leak random t
  rw [hb] at hz
  exact advances_step_ideal kem hDet ecEk ecCt leak b t s z hz

/-- A hybrid and the fixed-bit ideal game have the same query computation from `s` whenever
`random` equals `b` at every epoch eligible in `s`: not exposed, not challenged, and keyed in
one of the game's tables. -/
lemma hybridSecurityImpl_run_eq_ideal (random : ℕ → Bool) (b : Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : ∀ e, ¬(e ∈ s.exposed ∨ e ∈ s.challenged) →
      ((s.keyA e).isSome = true ∨ (s.keyB e).isSome = true) → random e = b)
    (t : (securitySpec leak Sym).Domain) :
    (hybridSecurityImpl kem hDet ecEk ecCt leak random t).run s =
      (idealSecurityImpl kem hDet ecEk ecCt leak b t).run s :=
  SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl)
    (fun e => SCKAScheme.oracleChall_run_eq_of_eligible_imp (random e) b s e (hs e)) t

/-! ## Endpoints -/

/-- The bottom hybrid is the real-key ideal game: `H_0 = I_false` as computations. -/
theorem hybridExp_zero (adv : SecurityAdversary leak Sym) :
    hybridExp kem hDet ecEk ecCt leak 0 adv =
      idealSecurityExp kem hDet ecEk ecCt leak false adv := by
  rw [hybridExp, hybridRandom_zero, hybridSecurityImpl_const]
  rfl

/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes.

Then the first hop is exact, `p_1 = p_0`: epoch `0` is never keyed, so its challenge always
returns `none` for either bit. -/
lemma probOutput_hybridExp_one (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SecurityAdversary leak Sym) :
    Pr[= true | hybridExp kem hDet ecEk ecCt leak 1 adv] =
      Pr[= true | hybridExp kem hDet ecEk ecCt leak 0 adv] := by
  refine probOutput_run'_eq_of_run_eq _ _ _ (fun z => ?_) true
  rw [hybridRandom_zero, hybridSecurityImpl_const]
  refine OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
    _ _ (GameInv kem ecEk ecCt) adv ?_
    (fun t s hs => idealSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak false t s hs)
    _ (gameInv_init kem ecEk ecCt _ _ (by simp [initA, init, initialState])
      (by simp [initB, init, initialState])) z
  intro t s hs
  refine hybridSecurityImpl_run_eq_ideal kem hDet ecEk ecCt leak _ false s ?_ t
  intro e _ hkey
  obtain ⟨-, T, hA, hB⟩ := hs
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · exfalso
    rcases hkey with hk | hk
    · rw [hA.key_zero] at hk; exact Bool.false_ne_true hk
    · rw [hB.key_zero] at hk; exact Bool.false_ne_true hk
  · simp only [hybridRandom, decide_eq_false_iff_not, not_lt]
    exact hpos

/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then every hybrid with threshold `T > 2q` has the output distribution of the random-key ideal
game, `p_T = Pr[I_true = true]`: an eligible epoch is keyed, hence at most
`2 · advances s ≤ 2q`, so its challenge is answered randomly. -/
theorem probOutput_hybridExp_top (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (T : ℕ) (hT : 2 * q < T) :
    Pr[= true | hybridExp kem hDet ecEk ecCt leak T adv] =
      Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak true adv] := by
  refine probOutput_run'_eq_of_run_eq _ _ _ (fun z => ?_) true
  refine OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_queryBound
    _ _ (fun s r => GameInv kem ecEk ecCt s ∧ advances s + r ≤ q) _ _ adv q hq ?_ ?_ _
    ⟨gameInv_init kem ecEk ecCt _ _ (by simp [initA, init, initialState])
      (by simp [initB, init, initialState]), by rw [advances_init]; omega⟩ z
  · intro t s r hs _
    refine hybridSecurityImpl_run_eq_ideal kem hDet ecEk ecCt leak _ true s ?_ t
    intro e _ hkey
    have he := keyed_epoch_le_two_mul_advances kem ecEk ecCt s hs.1 e hkey
    simp only [hybridRandom, decide_eq_true_eq]
    omega
  · intro t s r hs hcan z hz
    refine ⟨idealSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak true t s hs.1 z hz,
      ?_⟩
    have hstep := advances_step_ideal kem hDet ecEk ecCt leak true t s z hz
    by_cases hsend : SCKAScheme.sckaSecuritySpec.isSendQuery t = true
    · simp only [hsend, ↓reduceIte] at hstep ⊢
      rcases hcan with h | h
      · exact absurd hsend h
      · omega
    · simp only [hsend, Bool.false_eq_true, ↓reduceIte, add_zero] at hstep ⊢
      omega

/-! ## Telescoping -/

/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then `AdvGuess_SCKA(scka, adv) ≤ q · ε + |Pr[I_true = true] − Pr[I_false = true]| / 2`, for the
correctness error `ε` of `kem` and the ideal games `I_b`. -/
lemma sckaGuessAdvantage_le_ideal_term (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) *
        |(Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak true adv]).toReal -
         (Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak false adv]).toReal| := by
  rw [SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two, SCKAScheme.sckaDistAdvantage]
  have h1 := security_ideal_endpoint_le kem hDet ecEk ecCt hEk hCt leak true adv q hq
  have h0 := security_ideal_endpoint_le kem hDet ecEk ecCt hEk hCt leak false adv q hq
  rw [abs_sub_comm] at h0
  have h2 := abs_sub_le
    (Pr[= true | SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv true
      (exposure .A leak) (exposure .B leak)]).toReal
    (Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak true adv]).toReal
    (Pr[= true | SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv false
      (exposure .A leak) (exposure .B leak)]).toReal
  have h3 := abs_sub_le
    (Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak true adv]).toReal
    (Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak false adv]).toReal
    (Pr[= true | SCKAScheme.securityExpFixedBit (scheme kem hDet ecEk ecCt leak) adv false
      (exposure .A leak) (exposure .B leak)]).toReal
  linarith

/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then `|Pr[I_true = true] − Pr[I_false = true]| ≤ Σ_{t=0}^{2q} |p_{t+1} − p_t|`, for the ideal
games `I_b` and `p_T := Pr[H_T = true]`. -/
lemma idealDist_le_sum_hybrid_hops (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    |(Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak true adv]).toReal -
     (Pr[= true | idealSecurityExp kem hDet ecEk ecCt leak false adv]).toReal| ≤
      ∑ t ∈ Finset.range (2 * q + 1),
        |(Pr[= true | hybridExp kem hDet ecEk ecCt leak (t + 1) adv]).toReal -
         (Pr[= true | hybridExp kem hDet ecEk ecCt leak t adv]).toReal| := by
  have htel := dist_le_range_sum_dist
    (fun T => (Pr[= true | hybridExp kem hDet ecEk ecCt leak T adv]).toReal) (2 * q + 1)
  simp only [Real.dist_eq] at htel
  rw [hybridExp_zero, probOutput_hybridExp_top kem hDet ecEk ecCt leak hEk hCt adv q hq
    (2 * q + 1) (by omega), abs_sub_comm] at htel
  refine htel.trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_))
  rw [abs_sub_comm]

/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends;
* `δ` is non-negative and bounds every adjacent hybrid distance at positive targets up to
  `2q`.

Then `AdvGuess_SCKA(scka, adv) ≤ q · ε + (1/2) · Σ_{t=0}^{2q} δ t`, for the correctness error
`ε` of `kem`. The hop at target `0` is exact, so `δ 0` only contributes its non-negativity. -/
theorem sckaGuessAdvantage_le_of_hop_bound (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (δ : ℕ → ℝ) (hδ : ∀ t, 0 ≤ δ t)
    (hhop : ∀ t, 0 < t → t ≤ 2 * q →
      |(Pr[= true | hybridExp kem hDet ecEk ecCt leak (t + 1) adv]).toReal -
       (Pr[= true | hybridExp kem hDet ecEk ecCt leak t adv]).toReal| ≤ δ t) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) * ∑ t ∈ Finset.range (2 * q + 1), δ t := by
  refine (sckaGuessAdvantage_le_ideal_term kem hDet ecEk ecCt leak hEk hCt adv q hq).trans ?_
  have htel := idealDist_le_sum_hybrid_hops kem hDet ecEk ecCt leak hEk hCt adv q hq
  have hsum : ∑ t ∈ Finset.range (2 * q + 1),
      |(Pr[= true | hybridExp kem hDet ecEk ecCt leak (t + 1) adv]).toReal -
       (Pr[= true | hybridExp kem hDet ecEk ecCt leak t adv]).toReal| ≤
      ∑ t ∈ Finset.range (2 * q + 1), δ t := by
    refine Finset.sum_le_sum fun t ht => ?_
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rw [zero_add, probOutput_hybridExp_one kem hDet ecEk ecCt leak hEk hCt adv, sub_self,
        abs_zero]
      exact hδ 0
    · exact hhop t hpos (by have := Finset.mem_range.1 ht; omega)
  have := htel.trans hsum
  linarith

end Hybrid

end oppBiKemCKA
