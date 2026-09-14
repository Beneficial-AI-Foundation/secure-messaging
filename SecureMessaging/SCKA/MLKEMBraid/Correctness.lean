/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Instances
import SecureMessaging.KEM.IncrementalKEM.Correctness.SelectedTrial
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# ML-KEM Braid correctness specification

This module relates the Braid SCKA wrapper to the raw paper transitions and
bounds its correctness error in terms of the underlying KEM.

The protocol source is Signal's *The ML-KEM Braid Protocol*, Revision 1
([specification](https://signal.org/docs/specifications/mlkembraid/)), sections
1.1 and 2.2–2.6. The shared correctness game follows Definition 3.1, Figure 1,
and Appendix B.1 of [SCKA] https://eprint.iacr.org/2025/2267.pdf.

The game permits adaptive sends and delivery of recorded messages by index,
including omission, delay, reordering, duplication, and replay. Epoch zero is
the initial sentinel; emitted epoch keys begin at one.

Correctness error is represented by the missing success mass
`1 - Pr[correctnessExp ... = true]`. Under ProbComp's lawful PMF semantics,
computation failure has zero mass, including failure of the initial-key sampler.
A protocol refusal is an ordinary game result and violates correctness.
-/

open OracleSpec OracleComp ENNReal

universe u

namespace MLKEMBraid

/-- Bound the combined number of SendA and SendB queries in every branch of
the existing correctness adversary. Every send query counts, including chunk
retransmission and empty-message sends. Uniform and receive queries do not
consume this budget. -/
def SendQueryBound {Sym : Type}
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) : Prop :=
  adv.IsQueryBoundP
    (fun t =>
      t = SCKAScheme.sckaCorrectnessSpec.OSendA (Rho := Message Sym) ∨
      t = SCKAScheme.sckaCorrectnessSpec.OSendB (Rho := Message Sym))
    q

/-- The Braid wrapper uses the raw initial states and sends for both parties.
A raw receive error becomes refusal. A successful receive preserves its output
key and successor state and reports the message epoch minus one. For an ignored
off-epoch message, the wrapper reports the message-derived epoch; the raw
receive report may differ. -/
theorem scheme_paper_correspondence
    {m : Type → Type u} [Monad m] [LawfulMonad m]
    (P : Parameters m) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : m InitKey) :
    let scka := scheme P auth irl sampleInitKey
    scka.initKeyGen = sampleInitKey ∧
      (∀ ik,
        scka.initA ik = pure (initA P auth ik) ∧
        scka.initB ik = pure (initB P auth ik)) ∧
      (∀ st,
        scka.sendA st =
          (fun r : SendResult P AuthState =>
            some (r.outputKey, r.msg, r.sendingEpoch, r.state)) <$>
              send P auth st ∧
        scka.sendB st =
          (fun r : SendResult P AuthState =>
            some (r.outputKey, r.msg, r.sendingEpoch, r.state)) <$>
              send P auth st) ∧
      (∀ st msg,
        (scka.recvA st msg, scka.recvB st msg) =
          match receive P auth st msg with
          | .error _ => (none, none)
          | .ok r =>
              (some (r.outputKey, msg.epoch - 1, r.state),
               some (r.outputKey, msg.epoch - 1, r.state))) := by
  dsimp only [scheme]
  constructor
  · rfl
  constructor
  · intro ik
    exact ⟨rfl, rfl⟩
  constructor
  · intro st
    constructor <;> simp only [map_eq_pure_bind]
  · intro st msg
    simp only [recvSCKA]
    split <;> simp_all

/-- Under the four erasure-code correctness laws, the missing success mass of
the SCKA correctness game is at most `q` times the underlying KEM correctness
error. The budget counts both send oracles, while adversarial scheduling may
omit, delay, reorder, duplicate, or replay messages. `Parameters` and the
ratcheted-authenticator interface supply the remaining primitive laws. -/
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
    (q : ℕ) (hq : SendQueryBound adv q) :
    1 - Pr[= true |
      SCKAScheme.correctnessExp (scheme P auth irl sampleInitKey) adv] ≤
      (q : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: Braid_correctness_error_le
    :=
  sorry

/-- Specialize the generic bound to the incremental ML-KEM adapter. The caller
supplies the KDF, four codes, authenticator, and initial sampler. The right-hand
side retains ML-KEM's symbolic correctness error, and the statement is
formulated at the level of the semantic scheme. -/
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
    (q : ℕ) (hq : SendQueryBound adv q) :
    1 - Pr[= true |
      SCKAScheme.correctnessExp
        (mlkemBraidScheme p ring prims kdfOK
          ecpHdr ecpEk ecpCt1 ecpCt2 auth sampleInitKey) adv] ≤
      (q : ℝ≥0∞) *
        (MLKEM.mlkemScheme p ring prims).correctnessError
          ProbCompRuntime.probComp :=
  sorry

end MLKEMBraid
