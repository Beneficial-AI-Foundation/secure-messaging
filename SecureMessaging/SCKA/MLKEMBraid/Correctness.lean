/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Instances
import SecureMessaging.SCKA.MLKEMBraid.Correctness.PotentialDrift

/-!
# ML-KEM Braid correctness

In each epoch of ML-KEM Braid one party samples a key pair of an incremental KEM and the other
encapsulates against it; both parties then derive the key of the epoch. The public key and the
ciphertext travel in erasure-coded chunks. `MLKEMBraid.Basic` traces one epoch.

Let:

* `Π := scheme P auth irl sampleInitKey` be the ML-KEM Braid SCKA scheme;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` be its correctness game for an adversary `Adv`;
* `ε := P.kem.correctnessError ProbCompRuntime.probComp` be the correctness error of the
  underlying KEM.

The adversary chooses which party sends and which recorded message each party receives. It names
a recorded message by its index, so it may omit, delay, reorder, duplicate or replay messages.
The game keeps a correctness flag. The flag becomes false when a receive refuses a recorded
message, or when one of the following checks fails:

* the two parties never output different keys for the same epoch;
* each party outputs at most one key per epoch;
* the receive of a message reports the epoch that its send reported;
* no send reports an epoch below the sender's current epoch;
* every epoch from `1` up to a party's current epoch has a key of that party.

Braid sends never refuse.

## Main results

If the four erasure codes of `P` are correct and `Adv` makes at most `q` send queries
(`SCKAScheme.SendQueryBound Adv q`), then

* `correctness_error_le`: `1 - Pr[G(Adv) = true] ≤ q · ε`;
* `mlkemBraidScheme_correctness_error_le`: the same bound for `mlkemBraidScheme`, where `ε` is
  the correctness error of ML-KEM.

Deterministic decapsulation and deterministic second-stage encapsulation are part of `P`.
The scheme also takes an incremental-KEM randomness-leakage package `irl`.

## References

The protocol is Signal's *The ML-KEM Braid Protocol*
(https://signal.org/docs/specifications/mlkembraid/), sections 1.1 and 2.2 to 2.6. The correctness
game follows Definition 3.1, Figure 1, and Appendix B.1 of:

- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267
-/
open OracleSpec OracleComp ENNReal

universe u

namespace MLKEMBraid

/-- With correct erasure codes, every query preserves `CorrectnessInv auth ik` on supported outcomes
for every initial key `ik`. -/
theorem correctnessImpl_preserves_correctnessInv
    {P : Parameters ProbComp} [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (ik : InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey))
      (CorrectnessInv auth ik) :=
  SCKAScheme.sckaCorrectnessImpl_preservesInv _
    (oracleSend_preserves_correctnessInv auth irl sampleInitKey ik true)
    (oracleSend_preserves_correctnessInv auth irl sampleInitKey ik false)
    (oracleRecv_preserves_correctnessInv auth irl sampleInitKey
      hHdrCorrect hEkCorrect hCt1Correct hCt2Correct ik true)
    (oracleRecv_preserves_correctnessInv auth irl sampleInitKey
      hHdrCorrect hEkCorrect hCt1Correct hCt2Correct ik false)

/-- With correct erasure codes, every adversary making at most `q` sends across both parties causes
a false correctness flag with probability at most `q` times the KEM correctness error. -/
-- ANCHOR: Braid_correctness_error_le
theorem correctness_error_le
    (P : Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message P.Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr[= true |
      SCKAScheme.correctnessExp (scheme P auth irl sampleInitKey) adv] ≤
      (q : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: Braid_correctness_error_le
    := by
  refine SCKAScheme.correctness_error_le_of_potential (scheme P auth irl sampleInitKey)
    (CorrectnessInv auth) failurePotential _ ?_ ?_ ?_ ?_ adv q hq
  · intro s hs
    simp [failurePotential, hs]
  · intro ik _ stA hA stB hB
    simp only [scheme, mem_support_pure_iff] at hA hB
    subst hA hB
    refine ⟨Or.inr ⟨_, transcriptConsistent_initGameState auth ik⟩, ?_⟩
    simp [failurePotential, currentEpochFailure, pairFailure, SCKAScheme.initGameState,
      initA, initB, State.controlPosition, State.epoch]
  · exact correctnessImpl_preserves_correctnessInv auth irl sampleInitKey
      hHdrCorrect hEkCorrect hCt1Correct hCt2Correct
  · exact expectedPayoff_failurePotential_query_le auth irl sampleInitKey
      hHdrCorrect hEkCorrect hCt1Correct hCt2Correct

/-- The bound of `correctness_error_le` for `mlkemBraidScheme`, using the correctness error of
`MLKEM.mlkemScheme p ring prims`. -/
theorem mlkemBraidScheme_correctness_error_le
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {InitKey AuthState EpochKey Mac Sym : Type}
    [DecidableEq EpochKey] [DecidableEq Sym]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (ecpHdr : ErasureCodePayload
      ((MLKEM.mlkemIncremental p ring prims).PKheader × Mac) Sym)
    (ecpEk : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).PKvector Sym)
    (ecpCt1 : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).C₁ Sym)
    (ecpCt2 : ErasureCodePayload
      ((MLKEM.mlkemIncremental p ring prims).C₂ × Mac) Sym)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState
      (MLKEM.mlkemIncremental p ring prims).PKheader
      ((MLKEM.mlkemIncremental p ring prims).C₁ ×
        (MLKEM.mlkemIncremental p ring prims).C₂) Mac)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : ecpHdr.ec.Correct)
    (hEkCorrect : ecpEk.ec.Correct)
    (hCt1Correct : ecpCt1.ec.Correct)
    (hCt2Correct : ecpCt2.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr[= true |
      SCKAScheme.correctnessExp
        (mlkemBraidScheme p ring prims kdfOK
          ecpHdr ecpEk ecpCt1 ecpCt2 auth sampleInitKey) adv] ≤
      (q : ℝ≥0∞) *
        (MLKEM.mlkemScheme p ring prims).correctnessError
          ProbCompRuntime.probComp :=
  by
    let P₀ := mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2
    let : DecidableEq P₀.K := by
      change DecidableEq MLKEM.SharedSecret
      infer_instance
    let : DecidableEq P₀.EpochKey := by
      change DecidableEq EpochKey
      infer_instance
    let : DecidableEq P₀.Sym := by
      change DecidableEq Sym
      infer_instance
    exact correctness_error_le P₀ auth
      (MLKEM.mlkemIncrementalRandLeak p ring prims) sampleInitKey
      hHdrCorrect hEkCorrect hCt1Correct hCt2Correct adv q hq

end MLKEMBraid
