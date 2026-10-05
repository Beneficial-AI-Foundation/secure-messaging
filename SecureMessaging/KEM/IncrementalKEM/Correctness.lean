/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# Correctness error of an incremental KEM per key pair

For a fixed header, vector, and secret key, `stagedCorrectExp` encapsulates in two stages and
checks whether decapsulation recovers the encapsulated key. `decapsFailureProb` adds the
probability of a false result and the probability that the experiment produces no result.
Its average over key generation is the correctness error of the KEM.

With deterministic decapsulation and second-stage encapsulation, the same quantity is an
expected payoff over the first-stage samples, as shown by `decapsFailureProb_eq_expectedPayoff`.
Here `expectedPayoff` assigns payoff `1` when the first stage produces no result.
-/

open OracleComp ENNReal

namespace KEMScheme.IncrementalStructure

variable {K PK SK C : Type} {kem : KEMScheme ProbComp K PK SK C}
  (inc : kem.IncrementalStructure)

/-- Run both encapsulation stages and return whether decapsulation with `sk` recovers the
encapsulated key. The header, vector, and secret key are fixed inputs to the experiment. -/
def stagedCorrectExp [DecidableEq K]
    (hdr : inc.PKheader) (vec : inc.PKvector) (sk : SK) : ProbComp Bool := do
  let (st, ct1, key) ← inc.encaps1 hdr
  let ct2 ← inc.encaps2 st hdr vec
  let key' ← kem.decaps sk (inc.splitC.symm (ct1, ct2))
  return decide (key' = some key)

/-- The probability of failed key recovery or of no result in `stagedCorrectExp`. -/
noncomputable def decapsFailureProb [DecidableEq K]
    (hdr : inc.PKheader) (vec : inc.PKvector) (sk : SK) : ℝ≥0∞ :=
  Pr[= false | inc.stagedCorrectExp hdr vec sk] + Pr[⊥ | inc.stagedCorrectExp hdr vec sk]

/-- With deterministic decapsulation and second-stage encapsulation, the failure probability
is the expected first-stage indicator of failed key recovery. -/
theorem decapsFailureProb_eq_expectedPayoff [DecidableEq K]
    (hDet : kem.DeterministicDecaps) (hEnc2 : inc.DeterministicEncaps2)
    (hdr : inc.PKheader) (vec : inc.PKvector) (sk : SK) :
    inc.decapsFailureProb hdr vec sk =
      expectedPayoff (inc.encaps1 hdr) fun (encapsState, ct1, key) =>
        if hDet.decapsDet sk
            (inc.splitC.symm (ct1, hEnc2.encaps2Det encapsState hdr vec)) = some key
        then 0 else 1 := by
  unfold decapsFailureProb stagedCorrectExp
  simp only [hEnc2.encaps2_eq, hDet.decaps_eq, pure_bind]
  rw [probOutput_false_add_probFailure_bind]
  congr 1
  refine tsum_congr fun c : inc.St × inc.C₁ × K => ?_
  congr 1
  dsimp only
  split_ifs <;> simp_all

/-- The average of `decapsFailureProb` over key generation is the correctness error of `kem`. -/
theorem expectedPayoff_keygen_decapsFailureProb [DecidableEq K] :
    expectedPayoff kem.keygen
        (fun (pk, sk) => inc.decapsFailureProb (inc.toHeader pk) (inc.toVector pk) sk) =
      kem.correctnessError ProbCompRuntime.probComp := by
  rw [kem.correctnessError_eq_probOutput_false_add_probFailure, ← inc.correctExp_eq]
  change _ = Pr[= false | inc.CorrectExp] + Pr[⊥ | inc.CorrectExp]
  unfold CorrectExp
  rw [probOutput_false_add_probFailure_bind]
  congr 1
  funext ⟨pk, sk⟩
  simp only [decapsFailureProb, stagedCorrectExp, stagedEncaps, bind_assoc, pure_bind]

end KEMScheme.IncrementalStructure
