/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Ideal
public import SecureMessaging.SCKA.SPQR.Security.Reduction.Reductions
public import ToVCVio.EvalDist.BoolDist

/-!
# SPQR SCKA security

**Setting.** Throughout this module, we consider:

- the *SPQR protocol* `scka := scheme P auth sampleInitKey` (`SPQR.Construction`) over parameters
  `P` whose four stream decoders are sound for their erasure codes (`StreamDecoder.Sound`), with the
  ratcheted authenticator `auth` and the initial-key sampler `sampleInitKey`;
- the *exposure policy* `V := vuln P AuthState` of both parties (`Security.Basic`);
- an *SCKA adversary* `adv : SecurityAdversary P AuthState` making at most `q` ordinary or leaking
  sends of A and B together, on every response path (`SCKAScheme.SecuritySendQueryBound adv q`);
- the *adversaries* constructed from `adv` (`Reduction.Reductions`), each of which draws a
  *challenge epoch* `e ← epochChoice q`, uniform on `1, …, q` when `q > 0`:
  - the *IND-CPA adversary* `𝓑_KEM := kemReduction … adv q` against the KEM `P.det.toKEM`;
  - the *key-derivation adversary* `𝓑_KDF := kdfReduction … adv q` against `P.kdfOK`;
  - the *key-hiding adversary* `𝓑_Auth := authReduction … adv q` against `auth`.

**Security game and advantage functions.** We consider:

- the *SCKA security game* `G_b` of `scka` under `V` with its challenge bit fixed to `b`: uniform
  keys for `true`, recorded keys for `false` (`securityExpFixedBit`);
- the *SCKA advantage*
  `AdvGuess_SCKA(scka, adv) := |Pr[b' = b] - 1/2| = |Pr[G_true = true] - Pr[G_false = true]| / 2`
  of `adv` in guessing the challenge bit;
- the *IND-CPA advantage*
  `AdvINDCPA_KEM(P.det.toKEM, 𝓑) := |Pr[Exp_real(𝓑) = true] - Pr[Exp_random(𝓑) = true]|` of an
  adversary `𝓑` (`IND_CPA_Advantage_eq_fixed_branch_dist`): `𝓑` receives a public key, an
  encapsulation `c`, and the shared key of `c` in `Exp_real` (`IND_CPA_Experiment … true`) or an
  independent uniform key in `Exp_random` (`… false`);
- the *key-derivation advantage* `AdvKDF(P.kdfOK, 𝓑) := Braid.kdfAdvantage P.kdfOK 𝓑` of an
  adversary `𝓑` in telling `P.kdfOK k t`, for a uniform `k : P.K` and a label `t` of its choice,
  from a uniform epoch key (`Braid.kdfContextExp`);
- the *key-hiding advantage* `AdvAuth(auth, 𝓑) := Braid.authHideAdvantage auth sampleInitKey 𝓑` of
  an adversary `𝓑` in telling the key of a hidden authenticator update from an independent uniform
  key, given the operations of `auth` on the hidden authenticator state of an epoch of its choice
  (`Braid.authHideExp`);
- the *KEM correctness error* `ε := P.det.toKEM.correctnessError`, the probability that an honest
  encapsulation does not decapsulate to its key.

**Theorem** (`security`).

```text
AdvGuess_SCKA(scka, adv) ≤ 2q · AdvINDCPA_KEM(P.det.toKEM, 𝓑_KEM) + 2q · AdvKDF(P.kdfOK, 𝓑_KDF)
  + (q / 2) · AdvAuth(auth, 𝓑_Auth) + q · ε.
```

In [SCKA], failed assertions are additional winning conditions; `correctness_failure_le_security`
(`Security.Ideal`) bounds their probability by `q · ε`.

## Proof structure

Paths are relative to `SPQR/Security/`. Every game draws `ik ← sampleInitKey`, runs `adv` from
`initState auth ik`, and returns the output bit of `adv`, or `false` once stopped.

1. *The advantage is bounded by the hybrid gap* (`Ideal`).
   - The *ideal game* `I_b` is `G_b` in which the generator of an epoch outputs the key recorded
     by the encapsulator instead of decapsulating (`idealExp`).
   - The *ideal hybrid* `H_i` is the ideal game with uniform keys at epochs `1, …, i` and real
     keys after (`hybridMode i`); `p_i := Pr[H_i = true]`.
   - Main result (`security_guess_le_hybrid_gap`): since
     `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`, `H_0 = I_false` and, under the send bound,
     `p_q = Pr[I_true = true]`, `AdvGuess_SCKA(scka, adv) ≤ |p_0 - p_q| / 2 + q · ε`.
2. *The gap at an epoch `e ≥ 1` is a signed sum of game hops*
   (`Reduction/{Deferral,Pinned,Relation,Simulation,HybridGame}`).
   - Stopping `H_{e-1}` and `H_e` at the first exposure of `e`, fixing the KEM samples of `e` or
     `e - 1` in advance, and simulating the resulting games gives the *games of the chain*.
   - `realKey` and `realKeyChal` accept as often as the stopped `H_{e-1}` and `H_e` over `auth`
     with its update of `e - 1` keyed by a uniform `κ` (`hybridAuth`). They answer the challenge
     at `e` with `kdf k := P.kdfOK k e`, for a fresh encapsulation `(c, k)`, and with a uniform key.
   - Between them, each game changes one key, a *hop* in which a reduction embeds its challenge:

     ```text
     game          change from the previous game                reduction
     realKey       challenge key and update key of e: kdf k
     randKey       k replaced by a uniform KEM key r            𝓑_KEM
     randEpochKey  kdf r replaced by a uniform epoch key u      𝓑_KDF
     splitKeys     challenge key replaced by an independent u'  𝓑_Auth
     randKeyChal   update key u replaced by kdf r               𝓑_KDF
     realKeyChal   r replaced by k                              𝓑_KEM
     ```

   - `prevReal x`, `prevRand x` and `prevKdf x` make the `𝓑_KEM` and `𝓑_KDF` hops for the key of
     the update of `e - 1`, from its real key to `κ`, with the challenge at `e` answered by the
     recorded key (`x = real`) or a uniform key (`x = random`).
   - Main result (`idealExp_gap_eq`), a game standing for its acceptance probability:

     ```text
     p_{e-1} - p_e = (realKey - realKeyChal) + (prevReal real - prevKdf real)
                     - (prevReal random - prevKdf random)
     ```

3. *The reductions average the hops* (`Reduction/{AuthMap,Reductions}`).
   - Each reduction draws `e` and one of its hops uniformly and embeds its challenge there: four
     hops for `𝓑_KEM` and for `𝓑_KDF` (those at `e - 1` once per version), one for `𝓑_Auth`.
   - `𝓑_Auth` has only the operations `h` on the authenticator state after the update keyed by
     `κ`; it runs its games over `withHidden auth h e` instead of `hybridAuth`, with the same
     acceptance probability (`prEvent_simRun_withHidden`).
   - Main result (`hybrid_gap_eq_reductions`): averaging step 2 over `e` gives
     `p_0 - p_q = q · (4 Δ_KEM + 4 Δ_KDF + Δ_Auth)` for `q > 0`, where `Δ` is the difference
     between the real-key and random-key experiments of a reduction. Step 1 then gives `security`.

## References

The security game, with its exposure functions and the failed assertions as winning conditions,
follows:

- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267
-/

@[expose] public section

open OracleSpec OracleComp

namespace SPQR

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}

/-! ## The security theorem -/

/-- The arithmetic of the security bound: if `adv ≤ |p| / 2 + q · ε` and
`p = q · (4 (a₁ - b₁) + 4 (a₂ - b₂) + (a₃ - b₃))`, then
`adv ≤ 2q |a₁ - b₁| + 2q |a₂ - b₂| + (q / 2) |a₃ - b₃| + q · ε`. -/
private theorem security_bound_of_gaps (adv q ε p a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) (hq : 0 ≤ q)
    (h : adv ≤ |p| / 2 + q * ε)
    (hp : p = q * (4 * (a₁ - b₁) + 4 * (a₂ - b₂) + (a₃ - b₃))) :
    adv ≤ 2 * q * |a₁ - b₁| + 2 * q * |a₂ - b₂| + q / 2 * |a₃ - b₃| + q * ε := by
  subst hp
  rw [abs_mul, abs_of_nonneg hq] at h
  have habs : |4 * (a₁ - b₁) + 4 * (a₂ - b₂) + (a₃ - b₃)| ≤
      4 * |a₁ - b₁| + 4 * |a₂ - b₂| + |a₃ - b₃| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (a₁ - b₁), neg_abs_le (a₂ - b₂), neg_abs_le (a₃ - b₃)],
      by linarith [le_abs_self (a₁ - b₁), le_abs_self (a₂ - b₂), le_abs_self (a₃ - b₃)]⟩
  nlinarith [mul_le_mul_of_nonneg_left habs hq]

/-- **SPQR SCKA security.** Let `scka := scheme P auth sampleInitKey`, `V := vuln P AuthState` its
exposure policy, and `𝓑_KEM`, `𝓑_KDF`, `𝓑_Auth` the reductions built from `adv` and `q`. Assuming
sound stream decoders, if `adv` makes at most `q` ordinary or leaking sends of A and B together, on
every response path (`SCKAScheme.SecuritySendQueryBound adv q`), then

`AdvGuess_SCKA(scka, adv) ≤ 2q · AdvINDCPA_KEM(P.det.toKEM, 𝓑_KEM) + 2q · AdvKDF(P.kdfOK, 𝓑_KDF)
  + (q / 2) · AdvAuth(auth, 𝓑_Auth) + q · ε`. -/
-- ANCHOR: security
theorem security (P : SPQR.Parameters ProbComp) [DecidableEq P.K] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (adv : SecurityAdversary P AuthState) (q : ℕ)
    (hq : SCKAScheme.SecuritySendQueryBound adv q) :
    let scka := scheme P auth sampleInitKey
    let V := vuln P AuthState
    let 𝓑_KEM := kemReduction auth sampleInitKey adv q
    let 𝓑_KDF := kdfReduction auth sampleInitKey adv q
    let 𝓑_Auth := authReduction auth sampleInitKey adv q
    let ε := (P.det.toKEM.correctnessError ProbCompRuntime.probComp).toReal
    SCKAScheme.sckaGuessAdvantage scka adv V V ≤
      2 * q * (P.det.toKEM.IND_CPA_Advantage ProbCompRuntime.probComp 𝓑_KEM).toReal +
        2 * q * Braid.kdfAdvantage P.kdfOK 𝓑_KDF +
        (q / 2 : ℝ) * Braid.authHideAdvantage auth sampleInitKey 𝓑_Auth + q * ε
-- ANCHOR_END: security
    := by
  dsimp only
  have h := security_guess_le_hybrid_gap auth sampleInitKey hHdrSound hEkSound hCt1Sound
    hCt2Sound adv q hq
  rcases Nat.eq_zero_or_pos q with rfl | hpos
  · simpa using h
  · have hgap := hybrid_gap_eq_reductions auth sampleInitKey adv q hpos.ne'
      (idealExp_gap_eq auth sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound adv)
    rw [KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist,
      ENNReal.absDiff_toReal (prEvent_ne_top _) (prEvent_ne_top _)]
    rw [Braid.kdfAdvantage, Braid.authHideAdvantage, ToVCVio.toReal_boolDist_evalDist,
      ToVCVio.toReal_boolDist_evalDist]
    exact security_bound_of_gaps _ _ _ _ _ _ _ _ _ _ (Nat.cast_nonneg q) h hgap

end SPQR
