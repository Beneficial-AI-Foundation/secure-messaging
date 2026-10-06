/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# KEM — Correctness Error After Fixing the Key Pair

For a KEM with deterministic decapsulation, this file decomposes the correctness error by the
key-pair sample. `keypairFailure kem hDet pk sk` (`φ(pk, sk)`) is the probability, over
encapsulation to `pk`, that deterministic decapsulation with `sk` does not recover the
encapsulated key, plus encapsulation's missing mass. The KEM's `correctnessError` is the
missing mass of key generation plus the average of `φ` over generated key pairs
(`correctnessError_eq_avg_keypair`).

A protocol proof charges `φ(pk, sk)` when a key pair is drawn and realises it when the
encapsulation to that key pair is drawn (`keypairFailure_eq_probEvent`).

This is the plain-KEM analogue of `SecureMessaging.KEM.OnOffKEM.CorrectnessError`.
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

/-- `φ(pk, sk)`: the correctness error after fixing the key pair, as missing success mass. -/
noncomputable def keypairFailure (pk : PK) (sk : SK) : ℝ≥0∞ :=
  Pr[= false | keypairCorrectExp kem hDet pk sk] + Pr[⊥ | keypairCorrectExp kem hDet pk sk]

/-- `φ(pk, sk)` is at most `1`. -/
theorem keypairFailure_le_one (pk : PK) (sk : SK) :
    keypairFailure kem hDet pk sk ≤ 1 :=
  probOutput_false_add_probFailure_le_one _

/-- The KEM's correctness experiment, with decapsulation replaced by its deterministic
function, is key generation followed by `keypairCorrectExp`. -/
theorem correctExp_eq_bind_keypairCorrectExp :
    kem.CorrectExp = (do
      let (pk, sk) ← kem.keygen
      keypairCorrectExp kem hDet pk sk) := by
  unfold KEMScheme.CorrectExp keypairCorrectExp
  simp only [hDet.decaps_eq, pure_bind]

/-- The KEM's correctness error is the missing mass of key generation plus the average of
`keypairFailure` over generated key pairs. -/
theorem correctnessError_eq_avg_keypair :
    kem.correctnessError ProbCompRuntime.probComp =
      Pr[⊥ | kem.keygen] +
        ∑' kp : PK × SK, Pr[= kp | kem.keygen] * keypairFailure kem hDet kp.1 kp.2 := by
  have h := KEMScheme.correctnessError_eq_probOutput_false_add_probFailure
    kem ProbCompRuntime.probComp
  change kem.correctnessError ProbCompRuntime.probComp =
    Pr[= false | kem.CorrectExp] + Pr[⊥ | kem.CorrectExp] at h
  rw [h, correctExp_eq_bind_keypairCorrectExp kem hDet, probOutput_false_add_probFailure_bind]
  rfl

/-- `φ(pk, sk)` is the probability, over encapsulation, that decapsulation fails to recover the
key, plus encapsulation's missing mass. This is the form the protocol proof charges. -/
theorem keypairFailure_eq_probEvent (pk : PK) (sk : SK) :
    keypairFailure kem hDet pk sk =
      Pr[fun ck : C × K => hDet.decapsDet sk ck.1 ≠ some ck.2 | kem.encaps pk] +
        Pr[⊥ | kem.encaps pk] := by
  have hmap : keypairCorrectExp kem hDet pk sk =
      (fun ck : C × K => decide (hDet.decapsDet sk ck.1 = some ck.2)) <$> kem.encaps pk := by
    unfold keypairCorrectExp
    rw [map_eq_bind_pure_comp]
    rfl
  unfold keypairFailure
  rw [hmap, probFailure_map, ← probEvent_eq_eq_probOutput, probEvent_map]
  congr 1
  apply probEvent_congr'
  · intro ck _
    simp [Function.comp]
  · rfl

end KEMScheme
