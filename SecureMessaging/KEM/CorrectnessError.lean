/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.KeyEncapMech
import VCVio.OracleComp.EvalDist.Sum

/-!
# KEM — Correctness Error After Fixing the Key Pair

For a KEM with deterministic decapsulation, this file decomposes the correctness error by the
key-pair sample. Let `φ(pk, sk) := keypairFailure kem hDet pk sk` be the probability, over
encapsulation to `pk`, that deterministic decapsulation with `sk` does not recover the
encapsulated key. The KEM's `correctnessError` is the average of `φ` over generated key pairs
(`correctnessError_eq_avg_keypair`).

A protocol proof uses the two results at different times. When a key pair is drawn, it adds
`φ(pk, sk)` to a failure potential; averaged over key generation this costs at most
`correctnessError` (`correctnessError_eq_avg_keypair`). When it later encapsulates to `pk`,
the proof removes `φ(pk, sk)` from the potential and records a failure if decapsulation with
`sk` disagrees, which happens with probability exactly `φ(pk, sk)`
(`keypairFailure_eq_prEvent`). The removed term covers that probability, so encapsulation adds
nothing to the error bound.
-/

open OracleComp ENNReal

namespace KEMScheme

variable {K PK SK C : Type} [DecidableEq K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)

/-- The correctness experiment after fixing the key pair: encapsulate to `pk` and check that
deterministic decapsulation with `sk` recovers the key. -/
def keypairCorrectExp (pk : PK) (sk : SK) : ProbComp Bool := do
  let (c, k) ← kem.encaps pk
  return decide (hDet.decapsDet sk c = some k)

/-- `φ(pk, sk)`: the correctness error after fixing the key pair. -/
noncomputable def keypairFailure (pk : PK) (sk : SK) : ℝ≥0∞ :=
  Pr{let x ← keypairCorrectExp kem hDet pk sk}[x = false]

/-- `φ(pk, sk)` is at most `1`. -/
theorem keypairFailure_le_one (pk : PK) (sk : SK) :
    keypairFailure kem hDet pk sk ≤ 1 :=
  (prEvent_le_one _)

/-- The KEM's correctness experiment, with decapsulation replaced by its deterministic
function, is key generation followed by `keypairCorrectExp`. -/
theorem correctExp_eq_bind_keypairCorrectExp :
    kem.correctnessExperiment = (do
      let (pk, sk) ← kem.keygen
      keypairCorrectExp kem hDet pk sk) := by
  unfold KEMScheme.correctnessExperiment keypairCorrectExp
  simp only [hDet.decaps_eq, pure_bind]

/-- The KEM's correctness error is the average of `keypairFailure` over generated key pairs. -/
theorem correctnessError_eq_avg_keypair :
    kem.correctnessError ProbCompRuntime.probComp =
      ∑' kp : PK × SK, Pr{let x ← kem.keygen}[x = kp] * keypairFailure kem hDet kp.1 kp.2 := by
  rw [correctnessError_probComp_eq_prEvent_false,
    correctExp_eq_bind_keypairCorrectExp kem hDet, OracleComp.prEvent_bind_eq_tsum]
  rfl

/-- `φ(pk, sk)`, i.e. `keypairFailure kem hDet pk sk`, is the probability that encapsulating to
`pk` yields a pair `(c, k)` with `decapsDet sk c ≠ some k`. -/
theorem keypairFailure_eq_prEvent (pk : PK) (sk : SK) :
    keypairFailure kem hDet pk sk =
      Pr{let ck ← kem.encaps pk}[hDet.decapsDet sk ck.1 ≠ some ck.2] := by
  have hmap : keypairCorrectExp kem hDet pk sk =
      (fun ck : C × K => decide (hDet.decapsDet sk ck.1 = some ck.2)) <$> kem.encaps pk := by
    unfold keypairCorrectExp
    rw [map_eq_bind_pure_comp]
    rfl
  unfold keypairFailure
  rw [hmap, prEvent_map]
  exact prEvent_congr _ _ _ fun ck => by simp only [decide_eq_false_iff_not, ne_eq]

end KEMScheme
