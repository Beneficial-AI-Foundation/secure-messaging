/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# Correctness error of an incremental KEM per key pair

For a fixed key pair, `decapsFailureProb` is the probability that decapsulation does not return
the key of a fresh staged encapsulation. Its average over key generation is the correctness error
of the KEM.
-/

open OracleComp ENNReal

namespace KEMScheme.IncrementalStructure

variable {K PK SK C : Type} {kem : KEMScheme ProbComp K PK SK C}
  (inc : kem.IncrementalStructure) (hDet : kem.DeterministicDecaps)
  (hEnc2 : inc.DeterministicEncaps2)

/-- The probability that decapsulation with `sk` does not return the key of a fresh staged
encapsulation to the header `hdr` and the vector `vec`. -/
noncomputable def decapsFailureProb [DecidableEq K]
    (hdr : inc.PKheader) (vec : inc.PKvector) (sk : SK) : ℝ≥0∞ :=
  expectedPayoff (inc.encaps1 hdr) fun (encapsState, ct1, key) =>
    if hDet.decapsDet sk (inc.splitC.symm (ct1, hEnc2.encaps2Det encapsState hdr vec)) = some key
    then 0 else 1

/-- The average of `decapsFailureProb` over key generation is the correctness error of `kem`. -/
theorem expectedPayoff_keygen_decapsFailureProb [DecidableEq K] :
    expectedPayoff kem.keygen
        (fun (pk, sk) =>
          inc.decapsFailureProb hDet hEnc2 (inc.toHeader pk) (inc.toVector pk) sk) =
      kem.correctnessError ProbCompRuntime.probComp := by
  rw [kem.correctnessError_eq_probOutput_false_add_probFailure, ← inc.correctExp_eq]
  change _ = Pr[= false | inc.CorrectExp] + Pr[⊥ | inc.CorrectExp]
  unfold CorrectExp
  rw [probOutput_false_add_probFailure_bind]
  unfold decapsFailureProb expectedPayoff
  congr 1
  refine tsum_congr fun kp => ?_
  congr 1
  unfold stagedEncaps
  simp only [hEnc2.encaps2_eq, hDet.decaps_eq, bind_assoc, pure_bind]
  rw [probOutput_false_add_probFailure_bind]
  congr 1
  refine tsum_congr fun c : inc.St × inc.C₁ × K => ?_
  congr 1
  split_ifs <;> simp_all

end KEMScheme.IncrementalStructure
