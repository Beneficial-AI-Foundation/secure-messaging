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

- the SPQR protocol `scka := scheme P auth sampleInitKey` (`SPQR.Construction`) over parameters `P`
  whose four stream decoders are sound for their erasure codes (`StreamDecoder.Sound`), with the
  ratcheted authenticator `auth` and the initial-key sampler `sampleInitKey`;
- the exposure policy `V := vuln P AuthState` of both parties (`Security.Basic`);
- an SCKA adversary `adv : SecurityAdversary P AuthState` making at most `q` ordinary or leaking
  sends of A and B together, on every response path (`SCKAScheme.SecuritySendQueryBound adv q`);
- the IND-CPA adversary `𝓑_KEM := kemReduction … adv q` against the KEM `P.det.toKEM`, the
  key-derivation adversary `𝓑_KDF := kdfReduction … adv q`, and the key-hiding adversary
  `𝓑_Auth := authReduction … adv q` against `auth` (`Reduction.Reductions`). Each draws a
  *challenge epoch* `e ← epochChoice q`, uniform on `1, …, q` when `q > 0`.

**Security game and advantage functions.** Let:

- `G_b` be the SCKA security game of `scka` under `V` with its challenge bit fixed to `b`:
  uniform keys for `true`, recorded keys for `false` (`securityExpFixedBit`);
- `AdvGuess_SCKA(scka, adv) := |Pr[b' = b] - 1/2| = |Pr[G_true = true] - Pr[G_false = true]| / 2`
  be the advantage of `adv` in guessing the challenge bit;
- `AdvINDCPA_KEM(P.det.toKEM, 𝓑) := |Pr[Exp_real(𝓑) = true] - Pr[Exp_random(𝓑) = true]|` be the
  advantage of an IND-CPA adversary `𝓑` (`IND_CPA_Advantage_eq_fixed_branch_dist`): `𝓑` receives
  a public key, an encapsulation `c`, and the shared key of `c` in `Exp_real`
  (`IND_CPA_Experiment … true`) or an independent uniform key in `Exp_random` (`… false`);
- `AdvKDF(P.kdfOK, 𝓑) := Braid.kdfAdvantage P.kdfOK 𝓑` be the advantage of `𝓑` in telling
  `P.kdfOK k t`, for a uniform `k : P.K` and a label `t` of its choice, from a uniform epoch key
  (`Braid.kdfContextExp`);
- `AdvAuth(auth, 𝓑) := Braid.authHideAdvantage auth sampleInitKey 𝓑` be the advantage of `𝓑` in
  telling the key of a hidden authenticator update from an independent uniform key, given the
  operations of `auth` on the hidden state entering an epoch of its choice (`Braid.authHideExp`);
- `ε := P.det.toKEM.correctnessError` be the probability that an honest encapsulation does not
  decapsulate to its key.

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

**Notation.**

- `I_b`, the *ideal game*: `G_b` in which the generator of an epoch outputs the key recorded by the
  encapsulator instead of decapsulating (`idealExp`, `Ideal`).
- `H_i`, the *ideal hybrid*: the ideal game with uniform keys at epochs `1, …, i` and real keys
  after (`hybridMode i`); `p_i := Pr[H_i = true]`.
- `S_e^x`, the *stopped hybrid* of version `x ∈ {real, random}`: `H_{e-1}` for `real` and `H_e` for
  `random`, returning `false` at the first exposure of `e` (`stoppedHybridExp`, `Ideal`).
- `A_κ := hybridAuth auth e ik κ`: `auth` with its update of `e - 1` replaced by
  `Braid.hiddenState auth e ik κ`, the update keyed by `κ` for `e ≥ 2`, and for `e = 1` an update
  that no reachable state performs (`Reduction/HybridGame`).
- The *games of the chain* (`Reduction/HybridGame`): the simulated games of `e` over `A_κ` for a
  uniform `κ` (`realKey`, `randKey`, `randEpochKey`, `splitKeys`, `randKeyChal`, `realKeyChal`)
  and of `e - 1` over `auth` (`prevReal x`, `prevRand x`, `prevKdf x`, with `false` for `real` and
  `true` for `random`), stopped at the first exposure of `e`. A simulated game holds only the
  public values of a fresh key pair and encapsulation at its *simulated epoch*, `e` or `e - 1`,
  with dummies for the secrets.

**Proof steps.**

1. *Correctness error* (`Ideal`): `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`. Since
   `H_0 = I_false` and, under the send bound, `p_q = Pr[I_true = true]`,
   `AdvGuess_SCKA(scka, adv) ≤ |p_0 - p_q| / 2 + q · ε` (`security_guess_le_hybrid_gap`).
2. *Simulation* (`Reduction/{Pinned,Relation,Simulation}`): a game whose KEM samples at a
   simulated epoch `j` are fixed in advance accepts as often as its simulation, which hides the
   secrets of `j`, when both stop at the first exposure of `j` or `j + 1`
   (`prEvent_stoppedRun_sim_eq_honest`); it is applied at `j = e` and `j = e - 1`, stopping at `e`.
3. *Deferred sampling* (`Reduction/Deferral`): fixing the KEM samples of `e` or `e - 1` in advance
   preserves the acceptance probability of a game stopped at the first exposure of `e`
   (`stoppedRun_material_deferred`).
4. *Hybrid gap* (`Reduction/HybridGame`, this module): `p_{e-1} - p_e` is the difference between
   the stopped hybrids `S_e^real` and `S_e^random` (`hybridImpl_signed_gap_stop_eq`), which steps 2
   and 3 write as a signed sum of games of the chain (`idealExp_gap_eq`).
5. *Authenticator transport* (`Reduction/AuthMap`, `Reduction/Reductions`): given the operations
   `h` on the hidden state entering `e`, `𝓑_Auth` runs the simulated game of `e` over
   `withHidden auth h e`, which runs `h` on a representative kept in place of that state. Its
   real-key and random-key experiments (bits `true` and `false`) accept as often as `randEpochKey`
   and `splitKeys`, respectively, averaged over the challenge epoch, the initial key and the
   dummies (`authReduction_prEvent_toReal`; transport along the authenticator map `hiddenMap`,
   `prEvent_simRun_withHidden`, `prEvent_stoppedRun_authMap`).
6. *Averaging* (`Reduction/Reductions`, this module): the experiments of the reductions average
   games of the chain over the challenge epoch and the reductions' choices; for `q > 0`,
   telescoping gives `p_0 - p_q = q · (4 Δ_KEM + 4 Δ_KDF + Δ_Auth)`, where each `Δ` is the
   difference between a reduction's real-key and random-key experiments
   (`hybrid_gap_eq_reductions`). Step 1 then gives `security`.

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

/-! ## Averaging over the initial key, the dummies and the challenge epoch -/

section Averaging

variable (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)

/-- The acceptance probability of a game at epoch `e`, averaged over the initial key and the
dummies. -/
noncomputable def gameProb (game : ℕ → Dummies P → InitKey → ProbComp Bool) (e : ℕ) : ℝ :=
  (Pr{let x ← (do
    let ik ← sampleInitKey
    let d ← sampleDummies
    game e d ik)}[x = true]).toReal

/-- For `q ≠ 0`, `∑_{i < q} gameProb game (i + 1) = q · contextProb q game`. -/
private theorem sum_gameProb_eq (q : ℕ) (hq : q ≠ 0)
    (game : ℕ → Dummies P → InitKey → ProbComp Bool) :
    ∑ i ∈ Finset.range q, gameProb sampleInitKey game (i + 1) =
      (q : ℝ) * contextProb sampleInitKey q game := by
  have h : contextProb sampleInitKey q game =
      (q : ℝ)⁻¹ * ∑ i : Fin q, gameProb sampleInitKey game (i.val + 1) := by
    simp only [contextProb, sampleContext, bind_assoc, pure_bind]
    exact ToVCVio.toReal_prEvent_epochChoice_bind q hq _ (· = true)
  rw [h, ← Fin.sum_univ_eq_sum_range (fun i => gameProb sampleInitKey game (i + 1)) q,
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hq), one_mul]

/-- If two differences of games agree for every initial key and dummies, so do the differences
of their averages. -/
private theorem gameProb_sub_eq_of_forall (G₁ G₂ G₃ G₄ : ℕ → Dummies P → InitKey → ProbComp Bool)
    (e : ℕ) (h : ∀ ik d, (Pr{let x ← G₁ e d ik}[x = true]).toReal -
      (Pr{let x ← G₂ e d ik}[x = true]).toReal =
      (Pr{let x ← G₃ e d ik}[x = true]).toReal - (Pr{let x ← G₄ e d ik}[x = true]).toReal) :
    gameProb sampleInitKey G₁ e - gameProb sampleInitKey G₂ e =
      gameProb sampleInitKey G₃ e - gameProb sampleInitKey G₄ e := by
  unfold gameProb
  exact toReal_prEvent_bind_sub_eq_of_forall sampleInitKey _ _ _ _ (· = true) fun ik _ =>
    toReal_prEvent_bind_sub_eq_of_forall sampleDummies _ _ _ _ (· = true) fun d _ => h ik d

/-- If two games accept equally often for every initial key and dummies, so do their averages. -/
private theorem gameProb_congr (G₁ G₂ : ℕ → Dummies P → InitKey → ProbComp Bool) (e : ℕ)
    (h : ∀ ik d, Pr{let x ← G₁ e d ik}[x = true] = Pr{let x ← G₂ e d ik}[x = true]) :
    gameProb sampleInitKey G₁ e = gameProb sampleInitKey G₂ e := by
  unfold gameProb
  congr 1
  exact OracleComp.prEvent_bind_congr_of_support' _ _ fun ik _ =>
    OracleComp.prEvent_bind_congr_of_support' _ _ fun d _ => h ik d

variable [DecidableEq P.EpochKey] [SampleableType P.EpochKey]
  (adv : SecurityAdversary P AuthState) (q : ℕ)

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders, for every `i`, with `e := i + 1`,
`p_i := Pr[idealExp (hybridMode i) adv = true]`, and the versions `real` (`false`) and `random`
(`true`) of `prevReal` and `prevKdf`,
```text
p_i - p_{i+1} = (gameProb (prevReal real) e - gameProb (prevKdf real) e)
  + (gameProb realKey e - gameProb realKeyChal e)
  - (gameProb (prevReal random) e - gameProb (prevKdf random) e).
``` -/
theorem idealExp_gap_eq (i : ℕ) :
    (Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode i) adv}[x = true]).toReal -
      (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode (i + 1))
          adv)}[x = true]).toReal =
    (gameProb sampleInitKey (prevReal auth sampleInitKey adv false) (i + 1) -
        gameProb sampleInitKey (prevKdf auth sampleInitKey adv false) (i + 1)) +
      (gameProb sampleInitKey (realKey auth sampleInitKey adv) (i + 1) -
        gameProb sampleInitKey (realKeyChal auth sampleInitKey adv) (i + 1)) -
      (gameProb sampleInitKey (prevReal auth sampleInitKey adv true) (i + 1) -
        gameProb sampleInitKey (prevKdf auth sampleInitKey adv true) (i + 1)) := by
  have hα : (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode i)
        adv)}[x = true]).toReal -
      (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode (i + 1))
        adv)}[x = true]).toReal =
      gameProb sampleInitKey
          (fun e (_ : Dummies P) ik => stoppedHybridExp auth sampleInitKey adv i e ik) (i + 1) -
        gameProb sampleInitKey
          (fun e (_ : Dummies P) ik => stoppedHybridExp auth sampleInitKey adv (i + 1) e ik)
          (i + 1) := by
    unfold idealExp gameProb
    refine toReal_prEvent_bind_sub_eq_of_forall sampleInitKey _ _ _ _ (· = true) fun ik _ => ?_
    rw [(OracleComp.EvalDistEq.bind_const sampleDummies
        (stoppedHybridExp auth sampleInitKey adv i (i + 1) ik)).prEvent_eq,
      (OracleComp.EvalDistEq.bind_const sampleDummies
        (stoppedHybridExp auth sampleInitKey adv (i + 1) (i + 1) ik)).prEvent_eq]
    have hgap : (Pr{let x ← ((simulateQ (idealImpl auth sampleInitKey
          (SCKAScheme.hybridMode (i + 1))) adv).run' (initState auth ik))}[x = true]).toReal -
        (Pr{let x ← ((simulateQ (idealImpl auth sampleInitKey (SCKAScheme.hybridMode i))
          adv).run' (initState auth ik))}[x = true]).toReal =
        (Pr{let x ← (stoppedHybridExp auth sampleInitKey adv (i + 1) (i + 1)
          ik)}[x = true]).toReal -
        (Pr{let x ← stoppedHybridExp auth sampleInitKey adv i (i + 1) ik}[x = true]).toReal :=
      SCKAScheme.hybridImpl_signed_gap_stop_eq (idealSchemeOf auth sampleInitKey)
        (vuln P AuthState) (vuln P AuthState) i adv (initState auth ik)
        (by simp [initState, SCKAScheme.initGameState])
    linarith
  have hβf := gameProb_sub_eq_of_forall sampleInitKey
    (fun e (_ : Dummies P) ik => stoppedHybridExp auth sampleInitKey adv i e ik)
    (fun e (_ : Dummies P) ik => do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv i e ik)
    (prevReal auth sampleInitKey adv false) (prevKdf auth sampleInitKey adv false) (i + 1)
    fun ik d => stoppedHybrid_sub_hybridAuth_eq auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound adv i false d ik
  have hβt := gameProb_sub_eq_of_forall sampleInitKey
    (fun e (_ : Dummies P) ik => stoppedHybridExp auth sampleInitKey adv (i + 1) e ik)
    (fun e (_ : Dummies P) ik => do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv (i + 1) e ik)
    (prevReal auth sampleInitKey adv true) (prevKdf auth sampleInitKey adv true) (i + 1)
    fun ik d => stoppedHybrid_sub_hybridAuth_eq auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound adv i true d ik
  have hγr := gameProb_congr sampleInitKey
    (fun e (_ : Dummies P) ik => do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv i e ik)
    (realKey auth sampleInitKey adv) (i + 1) fun ik d => by
      have h := stoppedHybrid_hybridAuth_real_eq_realKey auth sampleInitKey hHdrSound
        hEkSound hCt1Sound hCt2Sound adv (i + 1) d ik
      rwa [Nat.add_sub_cancel] at h
  have hγc := gameProb_congr sampleInitKey
    (fun e (_ : Dummies P) ik => do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv (i + 1) e ik)
    (realKeyChal auth sampleInitKey adv) (i + 1) fun ik d =>
      stoppedHybrid_hybridAuth_random_eq_realKeyChal auth sampleInitKey hHdrSound hEkSound
        hCt1Sound hCt2Sound adv (i + 1) d ik (Nat.succ_pos i)
  linarith

variable [SampleableType P.K]

/-- Averaging over the challenge epoch: for `q ≠ 0`, if every `p_i - p_{i+1}` is given by
`idealExp_gap_eq`, then `p_0 - p_q = q · (4 Δ_KEM + 4 Δ_KDF + Δ_Auth)`, where
`p_i := Pr[idealExp (hybridMode i) adv = true]` and each `Δ` is the difference of the acceptance
probabilities of the experiment of a reduction with bit `true` and with bit `false`: the IND-CPA
experiment of `kemReduction`, `Braid.kdfContextExp P.kdfOK` of `kdfReduction`, and
`Braid.authHideExp auth sampleInitKey` of `authReduction`. -/
theorem hybrid_gap_eq_reductions (hq : q ≠ 0)
    (hgap : ∀ i, (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode i)
        adv)}[x = true]).toReal -
      (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode (i + 1))
          adv)}[x = true]).toReal =
      (gameProb sampleInitKey (prevReal auth sampleInitKey adv false) (i + 1) -
          gameProb sampleInitKey (prevKdf auth sampleInitKey adv false) (i + 1)) +
        (gameProb sampleInitKey (realKey auth sampleInitKey adv) (i + 1) -
          gameProb sampleInitKey (realKeyChal auth sampleInitKey adv) (i + 1)) -
        (gameProb sampleInitKey (prevReal auth sampleInitKey adv true) (i + 1) -
          gameProb sampleInitKey (prevKdf auth sampleInitKey adv true) (i + 1))) :
    (Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode 0) adv}[x = true]).toReal -
      (Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode q) adv}[x = true]).toReal =
    (q : ℝ) * (
      4 * ((Pr{let x ← (P.det.toKEM.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemReduction auth sampleInitKey adv q) true)}[x = true]).toReal -
        (Pr{let x ← (P.det.toKEM.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemReduction auth sampleInitKey adv q) false)}[x = true]).toReal) +
      4 * ((Pr{let x ← (Braid.kdfContextExp P.kdfOK (kdfReduction auth sampleInitKey adv q)
          true)}[x = true]).toReal -
        (Pr{let x ← (Braid.kdfContextExp P.kdfOK (kdfReduction auth sampleInitKey adv q)
          false)}[x = true]).toReal) +
      ((Pr{let x ← (Braid.authHideExp auth sampleInitKey (authReduction auth sampleInitKey adv q)
          true)}[x = true]).toReal -
        (Pr{let x ← (Braid.authHideExp auth sampleInitKey (authReduction auth sampleInitKey adv q)
          false)}[x = true]).toReal)) := by
  rw [← Finset.sum_range_sub' (fun i =>
    (Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode i) adv}[x = true]).toReal) q]
  simp only [hgap, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_gameProb_eq sampleInitKey q hq]
  rw [kemReduction_prEvent_toReal, kemReduction_prEvent_toReal, kdfReduction_prEvent_toReal,
    kdfReduction_prEvent_toReal, authReduction_prEvent_toReal, authReduction_prEvent_toReal]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, realGame, randGame, unifGame]
  ring

end Averaging

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
