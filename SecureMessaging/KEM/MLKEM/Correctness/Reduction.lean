/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.MLKEM.KEM
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Deterministic reduction from ML-KEM failure to K-PKE recovery failure

On a fixed honest outcome `(d,z,m)`, let `(ek,dk)` be ML-KEM key generation,
let `(K,c)` be encapsulation, and let

`m' = KPKE.decrypt(dk.dkPKE,c)`.

The deterministic theorem `decapsInternal_eq_encapsKey_of_decrypt_eq` proves

`m'=m  →  decapsInternal(dk,c)=K`.                        (1)

Indeed, recovery of `m` makes decapsulation derive the same key and coins as
encapsulation; re-encryption reproduces `c`, so implicit rejection is not
taken.  The contrapositive of (1) gives the event inclusion

`{Decaps(dk,c)≠K} ⊆ {KPKE.decrypt(dk.dkPKE,c)≠m}`.         (2)

Both events are measured on the same uniform sample of `(d,z,m)`.  Monotonicity
of probability applied to (2) is
`correctnessError_le_underlyingCorrectnessError`.  No distributional or
random-function assumption enters this reduction; those assumptions arise
only when the K-PKE event on the right of (2) is assigned a numerical bound.
-/

open OracleComp KEMScheme ENNReal

namespace MLKEM

variable {params : Params}
variable (ring : NTTRingOps) (encoding : Encoding params)
  (prims : Primitives params encoding)

/-- On an honest run where K-PKE decryption of the encapsulation ciphertext
recovers the message, ML-KEM decapsulation returns the encapsulated key.

This is the deterministic core of correctness: the recovered message drives the
same `G` derivation as encapsulation, so the re-encryption reproduces the
ciphertext and the implicit-rejection branch is not taken. -/
theorem decapsInternal_eq_encapsKey_of_decrypt_eq
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV]
    (d z : Seed32) (m : Message)
    (hrec : KPKE.decrypt ring encoding prims (keygenInternal ring encoding prims d z).2.dkPKE
              (encapsInternal ring encoding prims
                (keygenInternal ring encoding prims d z).1 m).2 = m) :
    decapsInternal ring encoding prims (keygenInternal ring encoding prims d z).2
        (encapsInternal ring encoding prims
          (keygenInternal ring encoding prims d z).1 m).2
      = (encapsInternal ring encoding prims
          (keygenInternal ring encoding prims d z).1 m).1 := by
  simp only [keygenInternal, encapsInternal, decapsInternal] at hrec ⊢
  rw [hrec]
  simp

/-- The K-PKE recovery experiment: sample the same `(d, z, m)` as the ML-KEM
correctness game and report whether K-PKE decryption of the encapsulation
ciphertext recovers `m`. The seed `z` is sampled to match the KEM experiment's
shape; it does not affect the K-PKE check. -/
def underlyingCorrectExp : ProbComp Bool := do
  let d ← $ᵗ Seed32
  let z ← $ᵗ Seed32
  let m ← $ᵗ Message
  pure (decide (KPKE.decrypt ring encoding prims (keygenInternal ring encoding prims d z).2.dkPKE
                  (encapsInternal ring encoding prims
                    (keygenInternal ring encoding prims d z).1 m).2 = m))

/-- Probability that the K-PKE recovery experiment fails. -/
noncomputable def underlyingCorrectnessError : ℝ≥0∞ :=
  Pr[= false | underlyingCorrectExp ring encoding prims]

/-- The correctness error of VCV-io's ML-KEM `KEMScheme` is at most the
underlying K-PKE decryption-failure probability in the corresponding honest
experiment. -/
theorem correctnessError_le_underlyingCorrectnessError
    [DecidableEq encoding.EncodedTHat] [DecidableEq encoding.EncodedU]
    [DecidableEq encoding.EncodedV] :
    (asKEMScheme ring encoding prims).correctnessError ProbCompRuntime.probComp ≤
      underlyingCorrectnessError ring encoding prims := by
  have hbridge : (asKEMScheme ring encoding prims).correctnessError ProbCompRuntime.probComp
      = Pr[= false | (asKEMScheme ring encoding prims).CorrectExp] := by
    rw [KEMScheme.correctnessError]
    change 1 - Pr[= true | (asKEMScheme ring encoding prims).CorrectExp] =
      Pr[= false | (asKEMScheme ring encoding prims).CorrectExp]
    rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero]
  rw [hbridge, underlyingCorrectnessError, ← probEvent_eq_eq_probOutput,
    ← probEvent_eq_eq_probOutput]
  simp only [KEMScheme.CorrectExp, asKEMScheme, keygen, underlyingCorrectExp, monad_norm]
  refine probEvent_bind_mono fun d _ => probEvent_bind_mono fun z _ =>
    probEvent_bind_mono fun m _ => ?_
  -- Pointwise: if K-PKE recovers the message then decapsulation returns the
  -- encapsulated key, so a ML-KEM failure can occur only on a K-PKE failure.
  simp only [probEvent_pure]
  split_ifs with hS hU hU
  · exact le_rfl
  · rw [Bool.not_eq_false, decide_eq_true_eq] at hU
    rw [decapsInternal_eq_encapsKey_of_decrypt_eq ring encoding prims d z m hU] at hS
    simp at hS
  · exact zero_le
  · exact zero_le

/-- If the K-PKE recovery experiment fails with probability at most `delta`,
then VCV-io's packaged ML-KEM scheme is `delta`-correct. -/
theorem deltaCorrect_of_underlying
    [DecidableEq encoding.EncodedTHat] [DecidableEq encoding.EncodedU]
    [DecidableEq encoding.EncodedV] {delta : ℝ≥0∞}
    (h : underlyingCorrectnessError ring encoding prims ≤ delta) :
    (asKEMScheme ring encoding prims).deltaCorrect ProbCompRuntime.probComp delta :=
  le_trans (correctnessError_le_underlyingCorrectnessError ring encoding prims) h

end MLKEM
