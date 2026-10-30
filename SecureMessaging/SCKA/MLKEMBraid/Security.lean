/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Bounds
import SecureMessaging.SCKA.MLKEMBraid.Security.Hybrids
import SecureMessaging.SCKA.MLKEMBraid.Security.Risk
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction
import SecureMessaging.SCKA.MLKEMBraid.BoundedInstances

/-!
# Security of ML-KEM Braid without internal authentication

ML-KEM Braid is a sparse continuous key agreement (SCKA): two parties exchange messages and, in
each epoch, agree on a fresh epoch key. A key-encapsulation mechanism (KEM) consists of key
generation `KeyGen`, encapsulation `Encaps(pk)`, which returns a ciphertext and a shared secret,
and decapsulation `Decaps(sk, c)`, which recovers the shared secret from the ciphertext.

**Setting.** Throughout this module, we consider:

- the Braid protocol `scheme P hMac irl` over a KEM `P.kem` with incremental encapsulation and
  randomness leakage `irl`, with the optional internal authenticator switched off
  (`hMac : P.Mac = Unit`, `NoAuth.auth`) and correct erasure codes for its four streams (header,
  public-key vector, and the two ciphertext components);
- the exposure functions `nativeExposure P irl` for both parties: corrupting a party exposes its
  current epoch, except before key generation, while it awaits a header, and between receiving a
  header and the first stage of encapsulation (`vuln`); a send that reveals its random coins
  exposes the current epoch when it generates a key pair or performs the first stage of
  encapsulation (`sendExposure`);
- an adversary `A : Adversary P irl` making at most `q` send requests to the two parties in
  total, with or without revealed coins, on every path of oracle answers (`SendQueryBound A q`);
- the IND-CPA adversary `ℬ := kemMixReduction … A q` against `P.kem` and the key-derivation
  adversary `𝒞 := kdfMixReduction … A q`. Each draws a *challenge epoch* `e` uniformly from
  `1, …, q` and then runs the reduction for `e` (`kemReduction`, `kdfReduction`).

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

**Theorem** (`NoAuth.security`). For every `q : ℕ`,

`AdvGuess(A) ≤ (q / 2) · (AdvINDCPA(ℬ) + AdvKDF(𝒞)) + q · ε`.

`MLKEMBraid.security` states the same bound for Braid over ML-KEM with finite-payload
Reed–Solomon codes (`Bounded.parameters`). There `ℬ` attacks raw ML-KEM through
`MLKEM.Bounded.liftAdversary`, and `ε` is the correctness error of raw ML-KEM.

**Assumptions and scope.**

- `kdfOK : SharedSecret → ℕ → EpochKey` is an arbitrary function. The Braid specification
  instantiates it with HKDF: the shared secret as input key material, a zero salt of hash length,
  `info = PROTOCOL_INFO ‖ ":SCKA Key" ‖ ToBytes(epoch)`, and 32 bytes of output. Nothing is proved
  about HKDF. `AdvKDF(𝒞)` is a quantity in the bound, not a hypothesis; in its game the label `e`
  is fixed before `u` is sampled.
- `IND_CPA_Advantage` takes values in `ℝ≥0∞`, and the bound uses its real value.
- The shared-secret and epoch-key types are abstract types with uniform sampling and decidable
  equality; nothing else is assumed about them.
- In the ML-KEM instance, the hash of the encapsulation key is the abstract primitive
  `hEncapsulationKey vector seed` of the supplied `Primitives`, while the specification writes
  `SHA3-256(ek_seed ‖ ek_vector)`. No equality between the two argument orders is asserted, and
  the reduction needs none. The ring and primitive functions are parameters, so the theorem does
  not establish SHA-3 or SHAKE semantics, and a numerical value of `ε` still needs
  `NTTRingLaws` and `CoefficientFailureBound`.
- The bound adds no hardness assumption and no efficiency class of adversaries. It does not cover
  C or FFI code, implemented NTT loops, entropy or sampler failure, constant time, physical
  erasure, authenticated security, or composition with messaging.

## Proof structure

Paths are relative to `MLKEMBraid/Security/`.

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

1. *Correctness error* (`Trace`, `Risk`, `Hybrids`, `Bounds`).
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

   - Hence `|p_0 - p_q| ≤ q · (AdvINDCPA(ℬ) + AdvKDF(𝒞))`, and step 1 gives `NoAuth.security`.

5. *ML-KEM instance* (this module). `MLKEM.Bounded.indCPAAdvantage_lift` and
   `MLKEM.Bounded.correctnessError_eq` move the KEM terms to raw ML-KEM, and
   `Bounded.payloads_correct` supplies correct codes for the four streams (`MLKEMBraid.security`).

Supporting modules: `NoAuth` (authenticator and exposure policy), `Games` (games and hybrids),
`Reduction/Simulator` (the simulation that `ℬ_e` runs), ToVCVio (`epochChoice`, stopping).
-/

open OracleSpec OracleComp ENNReal

/-- Assume correct erasure codes for the four streams and an adversary `A` making at most `q`
send requests in total (`SendQueryBound A q`). For `ℬ := kemMixReduction … A q` and
`𝒞 := kdfMixReduction … A q`, `AdvGuess(A) ≤ (q / 2) · (AdvINDCPA(ℬ) + AdvKDF(𝒞)) + q · ε`,
where `ε` is the KEM correctness error. -/
-- ANCHOR: genericSecurity
theorem MLKEMBraid.NoAuth.security (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (q : ℕ) (hq : SendQueryBound A q) :
    let ℬ := kemMixReduction P hMac irl A q
    let 𝒞 := kdfMixReduction P hMac irl A q
    let ε := (P.kem.correctnessError ProbCompRuntime.probComp).toReal
    SCKAScheme.sckaGuessAdvantage (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl) ≤
      (q / 2 : ℝ) * ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
        kdfAdvantage P 𝒞) + q * ε
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
    refine (fixed_repaired_gap_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A
      b).trans ?_
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top q) hcE)
      (badEvent_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A q hq b)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  -- The repaired games are the hybrids with no uniform epoch and with uniform epochs `1, …, q`.
  have hend := hybrid_endpoints P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A q hq
  have h0 := hend.1.prEvent_eq (fun x => x = true)
  have hqEnd := hend.2.prEvent_eq (fun x => x = true)
  have h1 := hbad true
  have h2 := hbad false
  rw [ToVCVio.toReal_boolDist_evalDist] at h1 h2
  rw [← hqEnd] at h1
  rw [← h0] at h2
  rw [SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two]
  unfold SCKAScheme.sckaDistAdvantage
  rw [← fixed_eq_native P hMac irl A true, ← fixed_eq_native P hMac irl A false]
  have ha := abs_sub_le (Pr{let x ← fixed P hMac irl A true}[x = true]).toReal
    (Pr{let x ← hybrid P hMac irl A q}[x = true]).toReal
    (Pr{let x ← fixed P hMac irl A false}[x = true]).toReal
  have hb := abs_sub_le (Pr{let x ← hybrid P hMac irl A q}[x = true]).toReal
    (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal
    (Pr{let x ← fixed P hMac irl A false}[x = true]).toReal
  rw [abs_sub_comm (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal] at hb
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
        (kemMixReduction P hMac irl A q)).toReal + kdfAdvantage P (kdfMixReduction P hMac irl A q))
      := by
    rw [abs_sub_comm, hybrid_gap_eq_query_factor P hMac irl hHdrCorrect hEkCorrect hCt1Correct
      hCt2Correct A q, abs_mul, abs_of_nonneg (Nat.cast_nonneg q), hK, kdfAdvantage,
      ToVCVio.toReal_boolDist_evalDist]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (Nat.cast_nonneg q)
  linarith

noncomputable section

/-- The bound of `NoAuth.security` for Braid over ML-KEM with finite-payload Reed–Solomon codecs
(`Bounded.parameters`). The IND-CPA adversary `ℬ` runs `kemMixReduction` against raw ML-KEM
through `MLKEM.Bounded.liftAdversary`, and `ε` is the correctness error of raw ML-KEM. -/
-- ANCHOR: security
theorem MLKEMBraid.security
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey : Type} [SampleableType EpochKey] [DecidableEq EpochKey]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey) :
    let P := MLKEMBraid.Bounded.parameters p ring prims kdfOK
    letI : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).K :=
      inferInstanceAs (SampleableType MLKEM.SharedSecret)
    letI : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
      inferInstanceAs (SampleableType EpochKey)
    letI : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
      inferInstanceAs (DecidableEq EpochKey)
    letI : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).Sym :=
      inferInstanceAs (DecidableEq
        (ErasureCode.SPQRReedSolomon.Chunk ErasureCode.SPQRReedSolomon.GF16))
    let irl := MLKEM.incrementalRandLeak ring
      (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
      (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
    ∀ (A : MLKEMBraid.NoAuth.Adversary P irl) (q : ℕ),
      MLKEMBraid.NoAuth.SendQueryBound A q →
      let ℬ := MLKEM.Bounded.liftAdversary p ring prims
        (MLKEMBraid.NoAuth.kemMixReduction P (Eq.refl Unit) irl A q)
      let 𝒞 := MLKEMBraid.NoAuth.kdfMixReduction P (Eq.refl Unit) irl A q
      let ε := ((MLKEM.mlkemScheme p ring prims).correctnessError
        ProbCompRuntime.probComp).toReal
      SCKAScheme.sckaGuessAdvantage
        (MLKEMBraid.NoAuth.scheme P (Eq.refl Unit) irl) A
        (MLKEMBraid.NoAuth.nativeExposure P irl)
        (MLKEMBraid.NoAuth.nativeExposure P irl) ≤
        (q / 2 : ℝ) *
          (((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
            MLKEMBraid.NoAuth.kdfAdvantage P 𝒞) + q * ε
-- ANCHOR_END: security
    := by
  intro P irl A q hq
  dsimp only
  let : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).K :=
    inferInstanceAs (SampleableType MLKEM.SharedSecret)
  let : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
    inferInstanceAs (SampleableType EpochKey)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).K :=
    inferInstanceAs (DecidableEq MLKEM.SharedSecret)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
    inferInstanceAs (DecidableEq EpochKey)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).Sym :=
    inferInstanceAs (DecidableEq
      (ErasureCode.SPQRReedSolomon.Chunk ErasureCode.SPQRReedSolomon.GF16))
  obtain ⟨hHdr, hEk, hCt1, hCt2⟩ := Bounded.payloads_correct p
  refine le_trans (NoAuth.security P (Eq.refl Unit) irl hHdr hEk hCt1 hCt2 A q hq) ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · exact le_of_eq (congrArg ENNReal.toReal (MLKEM.Bounded.indCPAAdvantage_lift p ring prims
        (NoAuth.kemMixReduction P (Eq.refl Unit) irl A q))).symm
    · exact le_rfl
  · exact le_of_eq (congrArg (fun x => (q : ℝ) * x.toReal)
      (MLKEM.Bounded.correctnessError_eq p ring prims))

end
