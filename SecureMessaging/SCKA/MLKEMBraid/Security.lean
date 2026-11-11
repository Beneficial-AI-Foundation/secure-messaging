/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Hybrids
public import SecureMessaging.SCKA.MLKEMBraid.Security.Risk
public import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Average
public import SecureMessaging.SCKA.MLKEMBraid.BoundedInstances

/-!
# Security of ML-KEM Braid without internal authentication

This module bounds the guessing advantage in the passive SCKA game for Braid with the
trivial internal authenticator.

**Setting.** Throughout this module, we consider:

- the Braid protocol `scheme P hMac irl` over a KEM `P.kem` with incremental encapsulation and
  randomness leakage `irl`, with the optional internal authenticator switched off
  (`hMac : P.Mac = Unit`, `Braid.NoAuth.auth`), and stream decoders for its four streams (header,
  public-key vector, and the two ciphertext components) that are sound for their erasure codes
  (`StreamDecoder.Sound`);
- the exposure functions `nativeExposure P irl` for both parties: corrupting a party exposes its
  current epoch, except before key generation, while it awaits a header, between receiving a
  header and the first stage of encapsulation, and after the second stage of encapsulation
  (`vuln`); a send that reveals its random coins
  exposes the current epoch when it generates a key pair or performs the first stage of
  encapsulation (`sendExposure`);
- an adversary `A : Adversary P irl` making at most `q` send requests to the two parties in
  total, with or without revealed coins, on every path of oracle answers (`SendQueryBound A q`);
- the IND-CPA adversary `ℬ := kemMixReduction … A q` against `P.kem` and the key-derivation
  adversary `𝒞 := kdfMixReduction … A q`. Each draws a *challenge epoch* `e ← epochChoice q` and
  then runs the reduction for `e` (`kemReduction`, `kdfReduction`). The epoch `e` is uniform on
  `1, …, q` when `q > 0`, and `e = 1` when `q = 0`.

The network is the passive one of the SCKA security game [SCKA, Sec. 3.1, Fig. 1]: the adversary
delivers recorded messages in any order and with any delay, but cannot modify them. `NoAuth` in a
Lean name means only that the internal authenticator is off.

**Security game and advantage functions.**

Let:
- `G_b` be the SCKA security game of `scheme P hMac irl` with its challenge bit fixed to `b`:
  uniform keys for `true`, recorded keys for `false` (`securityExpFixedBit`);
- `AdvGuess(A) := |Pr[b' = b] - 1/2| = |Pr[G_true = true] - Pr[G_false = true]| / 2` be the
  advantage of `A` in guessing the challenge bit (`sckaGuessAdvantage`);
- `AdvINDCPA(ℬ) := |Pr[ℬ_real = true] - Pr[ℬ_random = true]|` be the advantage of `ℬ` in the
  IND-CPA game (indistinguishability under chosen-plaintext attack). `ℬ` receives a public key, an
  encapsulation `c` and a key, which is the shared secret of `c` in `ℬ_real` and an independent
  uniform key in `ℬ_random` (`IND_CPA_Advantage_eq_fixed_branch_dist`);
- `AdvKDF(𝒞) := |Pr[𝒞_derived = true] - Pr[𝒞_uniform = true]|` be the advantage of `𝒞` in the
  key-derivation game `kdfContextExp`. `𝒞` first chooses an epoch label `e`; it then receives
  `kdfOK u e` for a uniform KEM shared secret `u` in `𝒞_derived`, and a uniform epoch key in
  `𝒞_uniform` (`kdfAdvantage`);
- `ε` be the KEM correctness error (`correctnessError`): the probability that an honest
  encapsulation `(c, k) ← Encaps(pk)` under `(pk, sk) ← KeyGen` does not decapsulate to `k`.

**Theorem** (`Braid.NoAuth.security`). For every `q : ℕ`,

`AdvGuess(A) ≤ (q / 2) · (AdvINDCPA(ℬ) + AdvKDF(𝒞)) + q · ε`.

`MLKEMBraid.NoAuth.security` states the same bound for Braid over ML-KEM with finite-payload
Reed–Solomon codes (`Bounded.parameters`). There `ℬ` attacks raw ML-KEM through
`MLKEM.Bounded.liftAdversary`, and `ε` is the correctness error of raw ML-KEM.

**Parameters and scope.**

- The shared-secret and epoch-key types have uniform sampling and decidable equality.
- The bound depends on `kdfOK` through `AdvKDF(𝒞)`, the PRG advantage at a label chosen before
  sampling the shared secret. A useful security bound requires this advantage to be small.
  The Braid specification instantiates `kdfOK` with HKDF; an HKDF-specific bound requires a separate
  analysis.
- The bound uses the real value of `IND_CPA_Advantage : ℝ≥0∞` and applies to every adversary,
  independently of its running time.
- The ML-KEM instance is parameterized by ring operations and hash primitives. Its encapsulation-key
  hash takes `vector seed`; the specification hashes `ek_seed ‖ ek_vector`. Relating these
  representations, establishing SHA-3/SHAKE semantics and supplying a numerical correctness error
  require further results, including `NTTRingLaws` and `CoefficientFailureBound`.
- With the authenticator on, epoch keys also key the public MAC tags through `auth.update`.
  Authenticated security and composition with messaging require separate proofs. The theorem
  concerns the Lean protocol model; C/FFI code, NTT implementations, entropy and sampler failure,
  constant time and physical erasure are outside its scope.

## Proof structure

Paths are relative to `Braid/Security/`.

**Notation.** Every game runs `A` and returns its output bit.

- **`R_b`**, the *repaired game*: `G_b` in which a receiver that completes the second ciphertext
  component of a recorded encapsulation outputs the key derived from the recorded shared secret
  instead of decapsulating (`run … true`, `repairedRecv`, `Games`).
- **`H_i`**, the *hybrid*: the repaired game with uniform keys at epochs `1, …, i` and real keys
  after (`hybrid A i`, `Games`). Let `p_i := Pr[H_i = true]`.
- **`J_e`**, the *raw-key hybrid*: uniform keys at the epochs before `e`, the key `kdfOK u e` for a
  fresh uniform shared secret `u` at `e`, and real keys after `e` (`rawHybrid A e`, `Games`). Let
  `r_e := Pr[J_e = true]`.
- **`ℬ_e`** and **`𝒞_e`**: the reductions for one epoch `e` (`kemReduction A e`,
  `kdfReduction A e`).

**Proof steps.**

1. *Correctness error* (`Trace`, `Risk`, `Hybrids`).
   - `G_b` is the game `fixed A b` (`fixed_eq_native`). It and `R_b` agree unless a
     decapsulation differs from the recorded shared secret, which has probability at most `q · ε`
     (`fixed_repaired_gap_le`, `badEvent_le`).
   - Under the send bound, `R_false` has the distribution of `H_0` and `R_true` that of `H_q`
     (`hybrid_endpoints`).

   Main result: `AdvGuess(A) ≤ |p_0 - p_q| / 2 + q · ε`.

2. *KEM step* (`Installed/Stopping`, `Reduction/KEM`).
   - `H_{e-1}` and `J_e` differ only at a challenge of `e`, which the game refuses once `e` is
     exposed. Stopping both runs with output `false` at the first exposure of `e` keeps the
     difference of their acceptance probabilities (`signedGap_stop`).
   - The stopped `H_{e-1}` and the stopped `J_e` accept with the probabilities of the real-key and
     the random-key IND-CPA experiments of `ℬ_e` (`kem_real_side`, `kem_rand_side`).

   Main result: `Pr[ℬ_e real = true] - Pr[ℬ_e random = true] = p_{e-1} - r_e`
   (`kem_signed_gap_eq`).

3. *Key-derivation step* (`Reduction/KDF`). In the same way, `J_e` and `H_e` differ only at a
   challenge of `e`, which `J_e` answers with `kdfOK u e` and `H_e` with a uniform key. Their
   stopped runs accept with the probabilities of the derived-key and the uniform-key experiments
   of `𝒞_e` (`kdfExp`).

   Main result: `Pr[𝒞_e derived = true] - Pr[𝒞_e uniform = true] = r_e - p_e`
   (`kdf_signed_gap_eq`).

4. *Averaging and telescoping* (`Reduction/Average`).
   - For `q > 0`, `ℬ` and `𝒞` draw `e` uniformly from `1, …, q`, so the difference for `ℬ`
     (real minus random) is the average of the differences of step 2, and the difference for `𝒞`
     (derived minus uniform) is the average of those of step 3 (`kemMixReduction_signed_gap`,
     `kdfMixReduction_signed_gap`).
   - Adding the two, the terms `r_e` cancel and the sum telescopes
     (`hybrid_gap_eq_query_factor`):

     ```text
     p_0 - p_q = ∑_{e=1}^{q} ((p_{e-1} - r_e) + (r_e - p_e))
               = q · ((Pr[ℬ_real] - Pr[ℬ_random]) + (Pr[𝒞_derived] - Pr[𝒞_uniform]))
     ```

   - For `q = 0` both sides are `0`. Hence `|p_0 - p_q| ≤ q · (AdvINDCPA(ℬ) + AdvKDF(𝒞))`, and
     step 1 gives `Braid.NoAuth.security`.

5. *ML-KEM instance* (this module). `MLKEM.Bounded.indCPAAdvantage_lift` and
   `MLKEM.Bounded.correctnessError_eq` move the KEM terms to raw ML-KEM, and
   `Bounded.payloads_correct` and `setDecoder_sound` show that the set-based decoders of the four
   streams are sound (`MLKEMBraid.NoAuth.security`).

Supporting modules: `NoAuth` (authenticator and exposure functions), `KDFGame` (the key-derivation
game), `Games` (games and hybrids), `Reduction/Simulator` (the simulation that `ℬ_e` runs), ToVCVio
(`epochChoice`, stopping).
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

/-- Let `P` be Braid parameters with tag space `Unit`, whose KEM is incremental with randomness
leakage `irl` and whose header, encapsulation-key, `ct₁` and `ct₂` decoders are sound for their
erasure codes. Let `A` be an adversary against Braid without authentication that makes at most `q`
sends, leaking or not (`SendQueryBound A q`). Let `ℬ := kemMixReduction A q`,
`𝒞 := kdfMixReduction A q`, and let `ε` be the correctness error of the KEM. Then, with the
exposure functions `nativeExposure` for both parties,
`AdvGuess(A) ≤ (q / 2) · (AdvINDCPA(ℬ) + AdvKDF(𝒞)) + q · ε`. -/
-- ANCHOR: genericSecurity
theorem Braid.NoAuth.security (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (A : Adversary P irl) (q : ℕ) (hq : SendQueryBound A q) :
    let ℬ := kemMixReduction P hMac irl A q
    let 𝒞 := kdfMixReduction P hMac irl A q
    let ε := (P.kem.correctnessError ProbCompRuntime.probComp).toReal
    SCKAScheme.sckaGuessAdvantage (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl) ≤
      (q / 2 : ℝ) * ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
        kdfAdvantage P.kdfOK 𝒞) + q * ε
-- ANCHOR_END: genericSecurity
    := by
  dsimp only
  have hcE : P.kem.correctnessError ProbCompRuntime.probComp ≠ ⊤ :=
    ENNReal.sub_ne_top ENNReal.one_ne_top
  -- The real game and the repaired game differ by at most `q · ε`, for either bit.
  have hbad : ∀ b : Bool, (𝒟[fixed P hMac irl A b].boolDist
      𝒟[Prod.fst <$> run P hMac irl true (fun _ => if b then .uniform else .real) A]).toReal ≤
        (q : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
    intro b
    refine (fixed_repaired_gap_le P hMac irl hHdrSound hEkSound hCt1Sound hCt2Sound A
      b).trans ?_
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top q) hcE)
      (badEvent_le P hMac irl hHdrSound hEkSound hCt1Sound hCt2Sound A q hq b)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  -- The repaired games are the hybrids with no uniform epoch and with uniform epochs `1, …, q`.
  have hend := hybrid_endpoints P hMac irl hHdrSound hEkSound hCt1Sound hCt2Sound A q hq
  have h0 := hend.1.prEvent_eq (fun x => x = true)
  have hqEnd := hend.2.prEvent_eq (fun x => x = true)
  have h1 := hbad true
  have h2 := hbad false
  rw [ToVCVio.toReal_boolDist_evalDist] at h1 h2
  rw [← hqEnd] at h1
  rw [← h0] at h2
  rw [fixed_eq_native] at h1 h2
  have htri := SCKAScheme.sckaGuessAdvantage_le_of_abs_sub_le (scheme P hMac irl) A
    (nativeExposure P irl) (nativeExposure P irl)
    (fun b => if b then (Pr{let x ← hybrid P hMac irl A q}[x = true]).toReal
      else (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal) _
    fun b => by
      cases b
      · exact h2
      · exact h1
  simp only [↓reduceIte, Bool.false_eq_true] at htri
  -- The hybrid gap is `q` times the sum of the two signed reduction gaps.
  have hK : (P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (kemMixReduction P hMac irl A q)).toReal =
      |(Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemMixReduction P hMac irl A q) true)}[x = true]).toReal -
        (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemMixReduction P hMac irl A q) false)}[x = true]).toReal| := by
    rw [KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist,
      ENNReal.absDiff_toReal (prEvent_ne_top _) (prEvent_ne_top _)]
  have hgap : |(Pr{let x ← hybrid P hMac irl A q}[x = true]).toReal -
      (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal| ≤
      (q : ℝ) * ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (kemMixReduction P hMac irl A q)).toReal +
          kdfAdvantage P.kdfOK (kdfMixReduction P hMac irl A q))
      := by
    rw [abs_sub_comm, hybrid_gap_eq_query_factor P hMac irl hHdrSound hEkSound hCt1Sound
      hCt2Sound A q, abs_mul, abs_of_nonneg (Nat.cast_nonneg q), hK, kdfAdvantage,
      ToVCVio.toReal_boolDist_evalDist]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (Nat.cast_nonneg q)
  linarith

noncomputable section

/-- Let `P` be the Braid parameters over ML-KEM with finite-payload Reed–Solomon codes and the
set-based decoders (`Bounded.parameters`). Let `A` be an adversary against Braid without
authentication that makes at most `q` sends, leaking or not. Let `ℬ` be `kemMixReduction A q`, run
on raw ML-KEM inputs through `MLKEM.Bounded.liftAdversary`, let `𝒞 := kdfMixReduction A q`, and
let `ε` be the correctness error of ML-KEM. Then, with the exposure functions `nativeExposure` for
both parties, `AdvGuess(A) ≤ (q / 2) · (AdvINDCPA(ℬ) + AdvKDF(𝒞)) + q · ε`, where the IND-CPA
game is the one of ML-KEM. -/
-- ANCHOR: security
theorem MLKEMBraid.NoAuth.security
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey : Type} [SampleableType EpochKey] [DecidableEq EpochKey]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey) :
    let P := MLKEMBraid.Bounded.parameters p ring prims kdfOK
    let irl := MLKEM.incrementalRandLeak ring
      (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
      (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
    ∀ (A : Braid.NoAuth.Adversary P irl) (q : ℕ),
      Braid.NoAuth.SendQueryBound A q →
      let ℬ := MLKEM.Bounded.liftAdversary p ring prims
        (Braid.NoAuth.kemMixReduction P rfl irl A q)
      let 𝒞 := Braid.NoAuth.kdfMixReduction P rfl irl A q
      let ε := ((MLKEM.mlkemScheme p ring prims).correctnessError
        ProbCompRuntime.probComp).toReal
      SCKAScheme.sckaGuessAdvantage
        (Braid.NoAuth.scheme P rfl irl) A
        (Braid.NoAuth.nativeExposure P irl)
        (Braid.NoAuth.nativeExposure P irl) ≤
        (q / 2 : ℝ) *
          (((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
            Braid.kdfAdvantage P.kdfOK 𝒞) + q * ε
-- ANCHOR_END: security
    := by
  intro P irl A q hq
  dsimp only
  obtain ⟨hHdr, hEk, hCt1, hCt2⟩ := MLKEMBraid.Bounded.payloads_correct p
  refine le_trans (Braid.NoAuth.security P rfl irl
    (ErasureCodePayload.Streaming.setDecoder_sound _ hHdr)
    (ErasureCodePayload.Streaming.setDecoder_sound _ hEk)
    (ErasureCodePayload.Streaming.setDecoder_sound _ hCt1)
    (ErasureCodePayload.Streaming.setDecoder_sound _ hCt2) A q hq) ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · exact le_of_eq (congrArg ENNReal.toReal (MLKEM.Bounded.indCPAAdvantage_lift p ring prims
        (Braid.NoAuth.kemMixReduction P rfl irl A q))).symm
    · exact le_rfl
  · exact le_of_eq (congrArg (fun x => (q : ℝ) * x.toReal)
      (MLKEM.Bounded.correctnessError_eq p ring prims))

end
