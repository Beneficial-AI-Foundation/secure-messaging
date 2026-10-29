/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Simulation
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# Opp-BiKEM — Security proofs

The proofs of the theorems stated in `Security`, whose module docstring fixes the setting, the
games and the notation used below. Each headline theorem there is proved by the lemma of the
same name in the namespace `Proofs`; this module may change freely, `Security` only when a
delegation changes.

## Proof structure

Paths are relative to `OppBiKEM/Security/`.

**Notation.** Every game runs `adv` from the initial game state. It returns the adversary's
output bit, or `false` if the run stops. The games at a target epoch `t` come in two *versions*
`x ∈ {real, random}`: an eligible challenge at `t` returns the recorded key in `real` and an
independent uniform key in `random`.

- **`I_b`**, the *ideal game*: `G_b` without decapsulation. Each party's receive copies the
  peer's recorded key for the received epoch instead of decapsulating
  (`idealSecurityExp … b adv`, `IdealReceive`).
- **`H_T`**, the *hybrid* with threshold `T`: the ideal game answering eligible challenges at
  epochs below `T` with uniform keys and all others with recorded keys (`hybridExp … T adv`,
  `Hybrid`). Let `p_T := Pr[H_T = true]`; then `H_0 = I_false`, and `p_T = Pr[I_true = true]`
  for every `T > 2q` under the send bound.
- **Exposure**: an epoch `t` is *exposed* once a permitted corruption or leaking send reveals
  its secret key or coins (`Exposure`); the game then rejects challenges at `t`.
- **`S_t^x`**, the *stopped hybrid*: the hybrids on either side of `t`, stopped at the first
  query after which `t` is exposed. `S_t^real := stoppedHybridExp … t t adv` is the stopped
  version of `H_t`, and `S_t^random := stoppedHybridExp … t (t + 1) adv` of `H_{t+1}`.
  Both return `false` on stopping (`Cancellation`).
- **`E_t^x(pk, sk, c, k, r)`**, the *eager hybrid*: `S_t^x` with the target's key pair
  `(pk, sk)`, encapsulation `(c, k)` and uniform challenge key `r` drawn before the run and
  looked up at the queries that would draw them (`stoppedEagerExp … t b pk sk c k r adv`, with
  `b = true` for `random`, `Eager`).
- **`Sim_t(pk, dummy, c, k*)`**, the *simulation*: the run of `adv` that `R_t` performs on the
  challenge `(pk, c, k*)` with the placeholder secret `dummy` in place of the secret key it does
  not have, stopped at the first exposure of `t` (`reductionRun` draws `dummy` from
  `kem.keygen`; `Reduction`, `Simulation`).
- **`R_t^x`**, the *fixed branch*: the IND-CPA experiment of `R_t` with the candidate key fixed
  to the encapsulated key in `real` and to an independent uniform key in `random`
  (`indCPAExpProb kem R_t true` and `… false`).

Below, `(pk, sk) ← KeyGen`, `(c, k) ← Encaps(pk)` and `r ←$ K` are the target's values, and
`k_real := k`, `k_random := r`. Steps 4 to 6 assume `t > 0`. The pointwise equality in step 5
assumes `(pk, sk) ∈ support kem.keygen` and `(c, k) ∈ support (kem.encaps pk)`.

**Proof steps.**

1. *Correctness error* (`Invariant`, `Tracked`, `BadEvent`, `IdealReceive`, `Endpoints`).
   - The real and ideal oracles agree on every state satisfying the game invariant `GameInv`
     without a current decapsulation failure, and a failure occurs within `q` sends with
     probability at most `q · ε` (`security_kemFailure_le`).

   Main result: `|Pr[G_b = true] − Pr[I_b = true]| ≤ q · ε` (`security_ideal_endpoint_le`).

2. *Hybrids and telescoping* (`EpochCount`, `Hybrid`).
   - `H_0 = I_false` (`hybridExp_zero`); `p_1 = p_0`, since epoch `0` is never keyed
     (`prEvent_hybridExp_one`); and `p_T = Pr[I_true = true]` for `T > 2q`, since a keyed
     epoch is at most twice the number of committed epoch advances, which is at most `q`
     (`prEvent_hybridExp_top`, `keyed_epoch_le_two_mul_advances`).

   Main result: for every `δ : ℕ → ℝ` with `0 ≤ δ t` for all `t` and
   `|p_{t+1} − p_t| ≤ δ t` at every `1 ≤ t ≤ 2q`,
   `AdvGuess_SCKA(scka, adv) ≤ q · ε + (1/2) · Σ_{t=0}^{2q} δ t`
   (`sckaGuessAdvantage_le_of_hop_bound`).

3. *Exposure cancellation* (`Cancellation`).
   - `H_t` and `H_{t+1}` differ only at an accepted challenge of `t`. Exposure of `t` prevents
     later challenges of `t`, and an accepted challenge prevents later exposure of `t`. Thus paths
     that expose `t` never reach a differing challenge answer. From exposure onward, the
     hybrids agree, so stopping removes equal contributions to acceptance.

   Main result: `p_{t+1} − p_t = Pr[S_t^random = true] − Pr[S_t^real = true]`
   (`hybridExp_sub_eq_stopped_sub`).

4. *Eager sampling* (`Reduction`, `Injected`, `Eager`).
   - `S_t^x` draws the target's key pair at the owner's generating send, the encapsulation at
     the peer's encapsulating send and, in `random`, the challenge key at the challenge of `t`;
     `E_t^x` holds them from the start. Each sample is consumed by at most one query.
     Drawing it in advance or at that query gives the same acceptance probability, and an
     unused sample integrates out (one-use sampling, `optionRun_sample_once_eq_sampleEachQuery`).
     The continuing states reached with injected values satisfy the injected-state invariant
     `InjInv` (`Injected`), which pins the injected values wherever the state holds them.

   Main result: `Pr[S_t^x = true] = E_{(pk, sk), (c, k), r} Pr[E_t^x(pk, sk, c, k, r) = true]`
   (`prEvent_stoppedHybridExp_eq_eager`).

5. *Simulation* (`Reduction`, `Simulation`).
   - `Sim_t(pk, dummy, c, k*)` runs `adv` against the injected oracles
     (`injectedSecurityImpl`): the owner's key generation at `t` returns `pk` with the
     placeholder `dummy`, the peer's encapsulation at `t` returns `(c, k*)`, receives are ideal,
     challenges below `t` are uniform and the challenge of `t` returns the recorded `k*`, and
     the run stops with output `false` once `t` is exposed. The state map
     `targetStateMap t dummy k_x` relates the continuing states of `E_t^x` and `Sim_t`.
     On an `InjInv` state with `t` unexposed, continuing answers and mapped successors have
     matching joint distributions. Stopped queries have equal probability mass, without
     requiring their successor states to correspond.

   Main result: `Pr[E_t^x(pk, sk, c, k, r) = true] = Pr[Sim_t(pk, dummy, c, k_x) = true]` for
   every placeholder `dummy` (`prEvent_stoppedEagerExp_eq_reductionRun`).

6. *The hop is the reduction's advantage* (this module).
   - Unfolding the IND-CPA experiment of `R_t` and integrating out the placeholder gives
     `Pr[R_t^x = true] = E_{(pk, sk), (c, k), r} Pr[E_t^x(pk, sk, c, k, r) = true]`
     (`prEvent_indCPAExpProb_reduction_eq`), which is `Pr[S_t^x = true]` by step 4; with
     step 3, `|p_{t+1} − p_t| = AdvINDCPA_KEM(kem, R_t)` for `t > 0` (`hybrid_hop_eq_reduction`).
   - Substituting `δ t := AdvINDCPA_KEM(kem, R_t)` for `t > 0` and `δ 0 := 0` into step 2 gives
     `security_positive`.

**Summary.** Writing `Δ_t^S := |Pr[S_t^random = true] − Pr[S_t^real = true]|` and
`Δ_t^R := |Pr[R_t^random = true] − Pr[R_t^real = true]|`, the steps assemble as follows:

```text
AdvGuess_SCKA(scka, adv)
  = |Pr[G_true = true] − Pr[G_false = true]| / 2             (definition)
  ≤ q · ε + |Pr[I_true = true] − Pr[I_false = true]| / 2     (step 1)
  ≤ q · ε + (1/2) · Σ_{t=0}^{2q} |p_{t+1} − p_t|             (step 2)
  = q · ε + (1/2) · Σ_{t=1}^{2q} Δ_t^S                        (step 3, and p_1 = p_0)
  = q · ε + (1/2) · Σ_{t=1}^{2q} Δ_t^R                        (steps 4 to 6)
  = q · ε + (1/2) · Σ_{t=1}^{2q} AdvINDCPA_KEM(kem, R_t)       (definition)
```

Supporting modules: `Defs` (every definition the statements of the theorems depend on),
`Basic` (send budget), `Exposure` (exposure policy), `SCKA.Security` (generic oracle facts),
ToVCVio (sampling, stopping, identical-until-bad).
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)

include hEk hCt in
/-- Step 6: for `t > 0`,
`Pr[R_t^x = true] = E_{(pk, sk), (c, k), r} Pr[E_t^x(pk, sk, c, k, r) = true]` over
`(pk, sk) ← keygen`, `(c, k) ← encaps pk` and `r ←$ K`, where the IND-CPA bit `bb = true` is the
version `real` and the eager bit is `!bb`. -/
lemma prEvent_indCPAExpProb_reduction_eq (adv : SecurityAdversary leak Sym) (t : ℕ)
    (ht : 0 < t) (bb : Bool) :
    Pr{let x ← indCPAExpProb kem (reduction kem hDet ecEk ecCt leak adv t) bb}[x = true] =
      Pr{let w ← kem.keygen >>= fun x => kem.encaps x.1 >>= fun y => ($ᵗ K : ProbComp K) >>=
           fun r => stoppedEagerExp kem hDet ecEk ecCt leak t (!bb) x.1 x.2 y.1 y.2 r
             adv}[w = true] := by
  simp only [indCPAExpProb, indCPAPrefix, reduction_preChallenge, bind_assoc]
  rw [map_bind, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ ?_
  rintro ⟨pk, sk⟩ hx
  change Pr{let x ← (do
              let st ← (pure pk : ProbComp PK)
              let y ← kem.encaps pk
              let r ← ($ᵗ K : ProbComp K)
              pure (⟨st, y.1, y.2, r⟩ :
                INDCPAPrefixState kem (reduction kem hDet ecEk ecCt leak adv t)))
              >>= fun p => reductionRun kem hDet ecEk ecCt leak adv t p.st p.cStar
              (if bb then p.kReal else p.kRand)}[x = true] = _
  simp only [bind_assoc, pure_bind]
  rw [map_bind, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ ?_
  rintro ⟨c, kReal⟩ hy
  rw [map_bind, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ ?_
  intro r _
  dsimp only
  unfold reductionRun
  trans Pr{let x ← kem.keygen >>= fun _ =>
             stoppedEagerExp kem hDet ecEk ecCt leak t (!bb) pk sk c kReal r adv}[x = true]
  · rw [map_bind, map_bind]
    refine prEvent_bind_congr_of_support _ _ _ ?_
    rintro ⟨_, dummy⟩ _
    rw [prEvent_stoppedEagerExp_eq_reductionRun kem hDet ecEk ecCt hEk hCt leak t ht pk sk
      dummy c kReal r (!bb) adv hx hy]
    cases bb <;> rfl
  · exact (evalDistEq_bind_const_probComp _ _).prEvent_eq _

namespace Proofs

include hEk hCt in
/-- The proof of `hybrid_hop_eq_reduction`, stated in `Security`. -/
lemma hybrid_hop_eq_reduction (adv : SecurityAdversary leak Sym) (t : ℕ) (ht : 0 < t) :
    |(Pr{let x ← hybridExp kem hDet ecEk ecCt leak (t + 1) adv}[x = true]).toReal -
        (Pr{let x ← hybridExp kem hDet ecEk ecCt leak t adv}[x = true]).toReal| =
      (kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv t)).toReal := by
  rw [IND_CPA_Advantage_eq_fixed_branch_dist,
    ENNReal.absDiff_toReal (prEvent_ne_top _) (prEvent_ne_top _), ← indCPAExpProb_prEvent_true_eq,
    ← indCPAExpProb_prEvent_true_eq, hybridExp_sub_eq_stopped_sub]
  have h1 := prEvent_stoppedHybridExp_eq_eager kem hDet ecEk ecCt hEk hCt leak adv t ht true
  have h0 := prEvent_stoppedHybridExp_eq_eager kem hDet ecEk ecCt hEk hCt leak adv t ht false
  simp only [Bool.toNat_true, Bool.toNat_false, add_zero] at h1 h0
  rw [h1, h0, prEvent_indCPAExpProb_reduction_eq kem hDet ecEk ecCt hEk hCt leak adv t ht,
    prEvent_indCPAExpProb_reduction_eq kem hDet ecEk ecCt hEk hCt leak adv t ht,
    Bool.not_true, Bool.not_false, abs_sub_comm]

include hEk hCt in
/-- The proof of `security_positive`, stated in `Security`. -/
lemma security_positive (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) * ∑ i ∈ Finset.range (2 * q), (kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv (i + 1))).toReal := by
  set δ' : ℕ → ℝ := fun t => if t = 0 then 0 else
    (kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (reduction kem hDet ecEk ecCt leak adv t)).toReal
    with hδ'
  have hbound := sckaGuessAdvantage_le_of_hop_bound kem hDet ecEk ecCt leak hEk hCt adv q hq δ'
    (fun t => by
      simp only [hδ']
      split_ifs
      · exact le_rfl
      · exact ENNReal.toReal_nonneg)
    (fun t ht _ => by
      simp only [hδ', ite_eq_right (Nat.pos_iff_ne_zero.mp ht)]
      exact le_of_eq (hybrid_hop_eq_reduction kem hDet ecEk ecCt hEk hCt leak adv t ht))
  simpa only [Finset.sum_range_succ', hδ', Nat.succ_ne_zero, ↓reduceIte, add_zero] using hbound

include hEk hCt in
/-- The proof of `security`, stated in `Security`. -/
lemma security (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) * ∑ t ∈ Finset.range (2 * q + 1),
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp
          (reduction kem hDet ecEk ecCt leak adv t)).toReal := by
  refine (security_positive kem hDet ecEk ecCt hEk hCt leak adv q hq).trans ?_
  have h0 : 0 ≤ (kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (reduction kem hDet ecEk ecCt leak adv 0)).toReal := ENNReal.toReal_nonneg
  rw [Finset.sum_range_succ']
  linarith

include hEk hCt in
/-- The proof of `security_uniform`, stated in `Security`. -/
lemma security_uniform (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) (δ : ℝ)
    (hδ : ∀ t, 0 < t → t ≤ 2 * q →
      (kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv t)).toReal ≤ δ) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal + (q : ℝ) * δ := by
  refine (security_positive kem hDet ecEk ecCt hEk hCt leak adv q hq).trans ?_
  have hsum := Finset.sum_le_card_nsmul (Finset.range (2 * q)) _ δ
    (fun i hi => hδ (i + 1) (Nat.succ_pos i) (Nat.succ_le_of_lt (Finset.mem_range.1 hi)))
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at hsum
  linarith

end Proofs

end oppBiKemCKA
