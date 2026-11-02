/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.SymmEncAlg.Deterministic
import ToVCVio.OracleComp.Constructions.LenSampleable

/-!
# Deterministic Symmetric Encryption: Length Regularity and One-Time Secrecy

Length regularity and a computational one-time secrecy game for VCVio's deterministic
symmetric encryption schemes `DetSymmEncAlg M K C`.

VCVio defines the scheme, its correctness `DetSymmEncAlg.PerfectlyCorrect`, and an IND$-CPA
game. That game samples one key for the whole run, and its random ciphertext is uniform on
all of `C`. The one-time secrecy game below samples a fresh key for each encryption query,
and its random ciphertext is uniform among the ciphertexts of length `clen |m|`. The game
uses VCVio's oracle interface `INDDollarOracleSpec` and adversary type `INDDollarAdversary`.

## References

- [Ros26] Rosulek. *The Joy of Cryptography.* Online edition, 2026. Definition 5.3.2:
  computational one-time secrecy. Definition 8.1.1: the set `Σ.C(ℓ)` of ciphertexts of
  messages of length `ℓ`.
- [NRS14] Namprempre, Rogaway, Shrimpton. *Reconsidering Generic Composition.*
  EUROCRYPT 2014. Section 2: the ivE scheme `E : K × {0,1}^η × M → {0,1}*` and length
  regularity. The schemes here have no IV, because each key encrypts one message.

## Differences from Ros26

The game below is the game of Ros26 Definition 5.3.2 when `keygen` is uniform on `K` and all
ciphertexts have one length. It differs in two places.

- Key generation: Ros26 samples the key uniformly from the key space. The game here samples
  it with `keygen`, which can be any distribution.
- Random ciphertexts by length: the game takes a message length `lenM : M → ℕ` and a
  ciphertext length `clen : ℕ → ℕ`. The random branch returns a uniform ciphertext of length
  `clen |m|`. The length and the uniform sample of each length come from the class
  `LenSampleable C`. This is the sample from `Σ.C(|M|)` of Ros26 Definition 8.1.1, with
  `Σ.C(ℓ) = {c ∈ C : |c| = clen ℓ}`. With one length (`LenSampleable.const C`), it is the
  sampling of Ros26 Definition 5.3.2.
-/

open OracleSpec OracleComp

namespace DetSymmEncAlg

variable {M K C : Type}

/-- Let `lenM : M → ℕ` be a length function on messages and `clen : ℕ → ℕ` a ciphertext length,
and write `|m| = lenM m` and `|c| = LenSampleable.len c`. The scheme `se` is length-regular for
`lenM` and `clen` if `|Enc(K, m)| = clen |m|` for all keys `K` and messages `m`. Then the
ciphertext length depends only on the message length [NRS14, Section 2]. -/
-- ANCHOR: DetSymmEncAlgLengthRegular
def LengthRegular [LenSampleable C] (lenM : M → ℕ) (clen : ℕ → ℕ)
    (se : DetSymmEncAlg M K C) : Prop :=
  ∀ (k : K) (m : M), LenSampleable.len (se.encrypt k m) = clen (lenM m)
-- ANCHOR_END: DetSymmEncAlgLengthRegular

section OTS

/-! ## One-Time Secrecy Game

The adversary has two oracles: uniform randomness, and an encryption oracle. Each encryption
query `m` samples a fresh key `K ← keygen`. With `b = false`, the oracle returns `Enc(K, m)`.
With `b = true`, it returns a ciphertext uniform among those of length `clen |m|`. The game
has no state.
-/

/-! ### Oracle implementations -/

/-- Uniform-randomness oracle for the one-time secrecy game. -/
def oracleUnif : QueryImpl unifSpec ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)

/-- Encryption oracle for the one-time secrecy game. Each call samples a fresh key `k`. With
`b = false`, it returns `se.encrypt k m`. With `b = true`, it returns a uniform ciphertext of
length `clen (lenM m)`. -/
-- ANCHOR: detSEOracleEncrypt
def oracleEncrypt [LenSampleable C] (se : DetSymmEncAlg M K C) (lenM : M → ℕ)
    (clen : ℕ → ℕ) (b : Bool) : QueryImpl (M →ₒ C) ProbComp :=
  fun m => do
    let k ← se.keygen
    if b then LenSampleable.unifOfLen (clen (lenM m))
    else pure (se.encrypt k m)
-- ANCHOR_END: detSEOracleEncrypt

/-- Oracles of the one-time secrecy game: `oracleUnif` for uniform randomness and
`oracleEncrypt se lenM clen b` for encryption. -/
def otsImpl [LenSampleable C] (se : DetSymmEncAlg M K C) (lenM : M → ℕ) (clen : ℕ → ℕ)
    (b : Bool) : QueryImpl (INDDollarOracleSpec M C) ProbComp :=
  oracleUnif + oracleEncrypt se lenM clen b

/-! ### Security experiment -/

/-- One-time secrecy experiment with a fixed challenge bit `b`. The branch `b = false` is
`L_ots-real` of Ros26, and `b = true` is `L_ots-rand`. -/
-- ANCHOR: detSESecurityExpFixedBit
def securityExpFixedBit [LenSampleable C] (se : DetSymmEncAlg M K C) (lenM : M → ℕ)
    (clen : ℕ → ℕ) (adversary : INDDollarAdversary M C) (b : Bool) : ProbComp Bool :=
  simulateQ (otsImpl se lenM clen b) adversary
-- ANCHOR_END: detSESecurityExpFixedBit

/-- One-time secrecy distinguishing advantage:
`|Pr[A^{L_ots-rand} = 1] - Pr[A^{L_ots-real} = 1]|`. -/
-- ANCHOR: detSEDistAdvantage
noncomputable def distAdvantage [LenSampleable C] (se : DetSymmEncAlg M K C) (lenM : M → ℕ)
    (clen : ℕ → ℕ) (adversary : INDDollarAdversary M C) : ℝ :=
  |(Pr{let x ← securityExpFixedBit se lenM clen adversary true}[x = true]).toReal -
   (Pr{let x ← securityExpFixedBit se lenM clen adversary false}[x = true]).toReal|
-- ANCHOR_END: detSEDistAdvantage

end OTS

end DetSymmEncAlg
