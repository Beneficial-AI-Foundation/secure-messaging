/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Deferral
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.Security

/-!
# Opp-UniKEM SCKA security

**Setting.** Throughout this module, we consider:

- the Opp-UniKEM protocol `scka := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` over a KEM `kem`
  with deterministic decapsulation `hDet`, on/off factorization `onoff`, leakage witness `leak`,
  and correct erasure codes `ecEk`, `ecCt0`, `ecCt1`;
- an SCKA adversary `adv : SecurityAdversary leak Sym` making at most `q` ordinary and leaking
  sends on every oracle-response path (`SecuritySendQueryBound adv q`);
- the IND-CPA adversary `𝓑 := Security.Embedding.securityReduction … adv q` against `kem`
  constructed from `adv`, which draws a *challenge epoch* `e` uniformly from `1, …, q`, embeds the
  KEM challenge in the key generation and encapsulation of epoch `e`, and runs `adv`.

**Security game and adversary advantage functions.**

Let:
- `G_b` be the SCKA security game of `scka` with its challenge bit fixed to `b`:
  uniform keys for `true`, recorded keys for `false` (`securityExpFixedBit`);
- `AdvGuess_SCKA(scka, adv) := |Pr[b' = b] - 1/2| = |Pr[G_true = true] - Pr[G_false = true]| / 2`
  be the advantage of `adv` in guessing the challenge bit;
- `AdvINDCPA_KEM(kem, 𝓑) := |2 Pr[b' = b] - 1| = |Pr[𝓑_real = true] - Pr[𝓑_random = true]|` be
  the advantage of `𝓑` in the IND-CPA game (`IND_CPA_Advantage_eq_fixed_branch_dist`);
- `ε` be the KEM correctness error (`kem.correctnessError`): the probability that an honest
  encapsulation `(ct, k) ← Encaps(pk)` under `(pk, sk) ← KeyGen` does not decapsulate to `k`.

**Theorem** (`security`). For every `q : ℕ`,

`AdvGuess_SCKA(scka, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, 𝓑) + q · ε`.

**Assertion failures.** In [SCKA], failed assertions are additional winning conditions.
Here `security` bounds guessing advantage; `correctness_failure_le_security` in
`OppUniKEM.Correctness` separately bounds assertion failures by `q · ε` for the full interface.

## Proof structure

Paths are relative to `OppUniKEM/Security/`.

**Notation.** Every game runs `adv` and returns its output bit. The games at an epoch `e` come in
two *versions* `x ∈ {real, random}`: a challenge at `e` returns the real key in `real` and an
independent uniform key in `random`.

- **`I_b`**, the *ideal game*: `G_b` without decapsulation failures.
  Party A outputs party B's recorded key instead of decapsulating
  (`idealSecurityExp (fun _ => b) adv`, `Endpoints`).
- **`H_i`**, the *ideal hybrid*: uniform keys at epochs `1, …, i`, real keys after.
  It is the ideal game with these challenge answers (`idealEpochHybridExp adv i`, `IdealHybrids`).
  Let `p_i := Pr[H_i = true]`; then `H_0 = I_false`, and `p_q = Pr[I_true = true]` under the send
  bound.
- **Exposure**: an epoch `e` is *exposed* once a permitted corruption or leaking send reveals its
  secrets (`exposureA`, `exposureB`); the game then rejects challenges at `e`.
- **`S_e^x`**, the *stopped hybrid*: the hybrids on either side of `e`, stopped when `e` is exposed.
  `S_e^real := H_{e-1}` (real key at `e`) and `S_e^random := H_e` (uniform key at `e`), each
  returning `false` at the first exposure of `e` (`IdealHybrids`).
- **`P_e^x`**, the *pinned hybrid*: `S_e^x` with the KEM samples of `e` drawn in advance
  (`stageStopped .pinned`, `Reduction/HybridGame`).
- **`𝓑_e^x`**, the *fixed branch*: the reduction at epoch `e` on a real or random challenge key.
  `𝓑` with its challenge epoch fixed to `e`, run on a fresh KEM challenge whose key is the
  encapsulated key in `real` and an independent uniform key in `random`
  (`fixedBranch adv e true` and `… false`, `Reduction/Simulator`).

For every epoch `e > 0`, steps 2 to 4 connect these games:

```text
Pr[𝓑_e^x = true] = Pr[P_e^x = true] = Pr[S_e^x = true]          (steps 2 and 3)
Pr[S_e^real = true] - Pr[S_e^random = true] = p_{e-1} - p_e      (step 4)
```

**Proof steps.**

1. *Correctness error* (`Endpoints`, `IdealHybrids`).
   - Bound the distance between the real game `G_b` and the ideal game `I_b`:
     `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`, where `q · ε` bounds the probability of a KEM
     failure within `q` sends (`security_correctness_endpoint_le`).

   Main result: `AdvGuess_SCKA(scka, adv) ≤ |p_0 - p_q| / 2 + q · ε`
   (`security_guess_le_hybrid_gap`).

2. *Reduction and simulation* (`Reduction/{Simulator,Relation,Game,Simulation,HybridGame}`).
   - On public key `pk*` and challenge `(ct*, k*)`, the reduction `𝓑` runs `adv` against
     simulated oracles (`simOracle`):
     - key generation at `e` returns `pk*` and encapsulation at `e` returns `ct*`, with *hidden*
       secret key, offline state, shared key, and coins; other epochs sample honestly;
     - a challenge at `t` returns a uniform key if `t < e`, `k*` if `t = e`, and the recorded
       key if `t > e`;
     - a permitted corruption or leaking send that would reveal a hidden value stops the run
       with output `false`.

   Main result: `Pr[𝓑_e^x = true] = Pr[P_e^x = true]` (`fixedBranch_eq_pinnedHybrid`).

3. *Deferred sampling* (`Reduction/Deferral`).
   - `P_e^x` draws the KEM samples of `e` (key generation, offline and online encapsulation) at
     the start, while `S_e^x` draws each one at the protocol call that uses it. Each sample is
     used by at most one query, so drawing it early or at that query gives the same acceptance
     probability (lazy sampling, `stoppedRun_sample_once_eq`).

   Main result: `Pr[P_e^x = true] = Pr[S_e^x = true]` (`pinnedHybrid_eq_ideal`).

4. *Exposure cancellation* (`IdealHybrids`, this module).
   - `H_{e-1}` and `H_e` differ only at a challenge of `e`, which is rejected once `e` is exposed,
     so stopping at that exposure preserves their difference:
     `Pr[S_e^real = true] - Pr[S_e^random = true] = p_{e-1} - p_e`
     (`idealEpochHybrid_signed_gap_stop_eq`).

   Main result, with steps 2 and 3: `Pr[𝓑_e^real = true] - Pr[𝓑_e^random = true] = p_{e-1} - p_e`
   (`fixedBranch_signed_gap_eq`).

5. *Averaging* (this module).
   - For `q > 0`, `𝓑` draws `e` uniformly from `1, …, q`, so

     ```text
     AdvINDCPA_KEM(kem, 𝓑)
       = |Pr[𝓑_real = true] - Pr[𝓑_random = true]|
       = |q⁻¹ · ∑_{e=1}^{q} (Pr[𝓑_e^real = true] - Pr[𝓑_e^random = true])|  (e uniform)
       = |q⁻¹ · ∑_{e=1}^{q} (p_{e-1} - p_e)|                                (step 4)
       = |p_0 - p_q| / q                                                     (telescoping)
     ```

   - Hence `|p_0 - p_q| = q · AdvINDCPA_KEM(kem, 𝓑)` (`hybrid_gap_eq_query_factor`).
   - Substituting into the bound of step 1, `AdvGuess_SCKA(scka, adv) ≤ |p_0 - p_q| / 2 + q · ε`,
     gives `security`:

     ```text
     AdvGuess_SCKA(scka, adv) ≤ |p_0 - p_q| / 2 + q · ε = (q / 2) · AdvINDCPA_KEM(kem, 𝓑) + q · ε
     ```

Supporting modules: `Basic` (interface, send budget), `Invariant` (transcript and epoch
invariants), `SCKA.Security` (generic guards), ToVCVio (sampling and stopping).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-! ## Steps 4 and 5: exposure cancellation and averaging -/

namespace Security.Embedding

variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

include hEk hCt0 hCt1 in
/-- Step 4: for every `i`, `Pr[𝓑_{i+1}^real = true] - Pr[𝓑_{i+1}^random = true] = p_i - p_{i+1}`,
where `𝓑_e^real := fixedBranch adv e true`, `𝓑_e^random := fixedBranch adv e false`, and
`p_i := Pr[idealEpochHybridExp adv i = true]`. -/
theorem fixedBranch_signed_gap_eq (adv : SecurityAdversary leak Sym) (i : ℕ) :
    (Pr{let x ← fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv (i + 1) true}[x = true]).toReal -
      (Pr{let x ← (fixedBranch
          kem onoff ecEk ecCt0 ecCt1 leak adv (i + 1) false)}[x = true]).toReal =
    (Pr{let x ← idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv i}[x = true]).toReal -
      (Pr{let x ← (idealEpochHybridExp
        kem onoff hDet ecEk ecCt0 ecCt1 leak adv (i + 1))}[x = true]).toReal := by
  rw [fixedBranch_eq_ideal kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak (i + 1) (Nat.succ_pos i) true adv,
    fixedBranch_eq_ideal kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak (i + 1) (Nat.succ_pos i) false adv]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
  have hstop := idealEpochHybrid_signed_gap_stop_eq kem onoff hDet ecEk ecCt0 ecCt1
    leak i adv (oppUniKemCKA.Reduction.Internal.initialGame kem onoff)
    (by simp [oppUniKemCKA.Reduction.Internal.initialGame, SCKAScheme.initGameState])
  dsimp only [idealEpochHybridExp, idealSecurityExp, stoppedHybridExp,
    idealEpochHybridImpl] at hstop ⊢
  linarith only [hstop]

include hEk hCt0 hCt1 in
/-- Step 5, averaging over `e`: for `q > 0` and `𝓑 := securityReduction … adv q`,
`Pr[𝓑_real = true] - Pr[𝓑_random = true] = (p_0 - p_q) / q`, where
`p_i := Pr[idealEpochHybridExp adv i = true]`. -/
theorem securityReduction_signed_gap_eq (adv : SecurityAdversary leak Sym)
    (q : ℕ) (hq : q ≠ 0) :
    (Pr{let x ← (kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) true)}[x = true]).toReal -
    (Pr{let x ← (kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) false)}[x = true]).toReal =
    (q : ℝ)⁻¹ *
      ((Pr{let x ← (idealEpochHybridExp
          kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0)}[x = true]).toReal -
       (Pr{let x ← (idealEpochHybridExp
           kem onoff hDet ecEk ecCt0 ecCt1 leak adv q)}[x = true]).toReal) := by
  rw [securityReduction_signed_gap_average kem onoff ecEk ecCt0 ecCt1 leak adv q hq]
  simp_rw [fixedBranch_signed_gap_eq kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (Pr{let x ← idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv i}[x = true]).toReal -
    (Pr{let x ← (idealEpochHybridExp
        kem onoff hDet ecEk ecCt0 ecCt1 leak adv (i + 1))}[x = true]).toReal) q,
    Finset.sum_range_sub']

include hEk hCt0 hCt1 in
/-- Step 5: for every `q` and `𝓑 := securityReduction … adv q`,
`|p_0 - p_q| = q · AdvINDCPA_KEM(kem, 𝓑)`, where `p_i := Pr[idealEpochHybridExp adv i = true]`. -/
theorem hybrid_gap_eq_query_factor (adv : SecurityAdversary leak Sym) (q : ℕ) :
    |(Pr{let x ← (idealEpochHybridExp
        kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0)}[x = true]).toReal -
      (Pr{let x ← (idealEpochHybridExp
          kem onoff hDet ecEk ecCt0 ecCt1 leak adv q)}[x = true]).toReal| =
    (q : ℝ) * (kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q)).toReal := by
  rcases Nat.eq_zero_or_pos q with rfl | hpos
  · simp
  have hq : q ≠ 0 := hpos.ne'
  rw [KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist,
    ENNReal.absDiff_toReal (prEvent_ne_top _) (prEvent_ne_top _),
    securityReduction_signed_gap_eq kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak adv q hq, abs_mul, abs_inv,
    abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q),
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hq), one_mul]

end Security.Embedding

/-! ## The security theorem -/

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Assume correct erasure codes and an adversary making at most `q` ordinary or leaking sends
in total (`SecuritySendQueryBound adv q`). For `𝓑 := securityReduction … adv q`,
`AdvGuess_SCKA(scka, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, 𝓑) + q · ε`. -/
-- ANCHOR: security
theorem security
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    let scka := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak
    let 𝓑 := Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q
    let ε := (kem.correctnessError ProbCompRuntime.probComp).toReal
    SCKAScheme.sckaGuessAdvantage scka adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
      (q / 2 : ℝ) * (kem.IND_CPA_Advantage ProbCompRuntime.probComp 𝓑).toReal + q * ε
-- ANCHOR_END: security
    := by
  dsimp only
  have h := Security.security_guess_le_hybrid_gap kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
  have hgap := Security.Embedding.hybrid_gap_eq_query_factor kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q
  linarith

end

end oppUniKemCKA
