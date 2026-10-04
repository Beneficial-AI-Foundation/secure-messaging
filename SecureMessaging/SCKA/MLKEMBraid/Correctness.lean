/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Instances
import SecureMessaging.SCKA.MLKEMBraid.Correctness.PotentialDrift

/-!
# ML-KEM Braid correctness

Each Braid epoch uses an incremental-KEM key pair and encapsulation to derive both parties'
epoch keys. Public keys and ciphertexts travel in erasure-coded chunks. A generates key pairs
in odd epochs and B in even epochs.

Fix parameters `P : Parameters ProbComp`, a ratcheted authenticator `auth`, an incremental-KEM
randomness-leakage package `irl`, and an initial-key sampler `sampleInitKey : ProbComp InitKey`.
Let `Π := scheme P auth irl sampleInitKey` and let
`ε := P.kem.correctnessError ProbCompRuntime.probComp` be the KEM's correctness error.

The correctness game lets a scheduling adversary
`adv : SCKAScheme.SCKACorrectnessAdversary (Message P.Sym)` choose sends and deliveries by recorded
message index. Its correctness flag checks that the parties agree on epoch keys, output at most one
key per epoch, receive each message with the report of its send, never send with a report below
their current epoch, and have keys for every epoch from `1` to their current epoch. A party's
current epoch (`tcurA`, `tcurB`) is the largest epoch it has reported, which lags its local
protocol epoch. Missing messages leave the state unchanged; refused receives clear the flag. Braid
sends never refuse. The game returns the final flag.

Assume the four erasure codes of `P` are correct. Then every adversary with at most `q` send
queries across both parties (`SCKAScheme.SendQueryBound adv q`) satisfies

```
1 - Pr[SCKAScheme.correctnessExp Π adv = true] ≤ q · ε.
```

`correctness_error_le` gives this bound, and `mlkemBraidScheme_correctness_error_le` specializes
it to ML-KEM. Every query preserves `CorrectnessInv auth ik`.

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
