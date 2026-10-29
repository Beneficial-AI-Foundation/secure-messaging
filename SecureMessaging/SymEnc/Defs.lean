/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import ToVCVio.OracleComp.Constructions.LenSampleable

/-!
# Deterministic Symmetric Encryption (Local Placeholder)

Formalization of a deterministic symmetric encryption primitive with computational one-time
secrecy, following:

- [Ros26] Rosulek. *The Joy of Cryptography.* Online edition, 2026.
  — Definition 5.3.2: computational one-time secrecy (OTS). Each encryption query uses a
  fresh key, and the adversary may make any number of queries.

- [NRS14] Namprempre, Rogaway, Shrimpton.
  *Reconsidering Generic Composition.*
  EUROCRYPT 2014.
  — Section 2: "ivE scheme" `E : K × {0,1}^η × M → {0,1}*`.
  We omit the IV parameter because each key encrypts one message (IV absorbed into key).

VCVio's `SymmEncAlg` has monadic, possibly randomized `encrypt`/`decrypt`
operations and information-theoretic perfect-secrecy notions. The EtM proof
instead uses a deterministic cipher with a computational one-time secrecy
assumption; `DetSEAlg` and its game below provide that interface.

## Generalizations of Ros26

The game below is Ros26's game when `keygen` is uniform on `K` and all ciphertexts have one
length.

- **Key generation**: Ros26 samples the key uniformly from the key space. We use the
  scheme's `keygen`, which can be any distribution; `keygen = $ᵗ K` gives Ros26's game. EtM
  builds its key generation from `keygen`.
- **Random ciphertexts by length**: Ros26 samples the random ciphertext from the whole
  ciphertext space. As in NRS14, the random branch here returns a uniform ciphertext of the
  same length as the real one (`|C|` random bits). The length and the uniform sample of each
  length come from the class `LenSampleable C`. With one length (`LenSampleable.const C`),
  this is Ros26's sampling. With several lengths, Ros26's game is undefined (infinite `C`) or
  lost by every padded cipher (finite `C`). The game leaks the ciphertext length, so it
  implies message privacy only for schemes that satisfy `LengthRegular`.
-/

open OracleSpec OracleComp ENNReal

/-- A deterministic symmetric encryption scheme with key space `K`, message
space `M`, and ciphertext space `C`.

NRS14 Section 2: ivE scheme `E : K × {0,1}^η × M → {0,1}*`.
Deviation: no IV parameter (each key encrypts one message). -/
-- ANCHOR: DetSEAlg
structure DetSEAlg (K M C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : ProbComp K
  /-- Deterministic encryption: `Enc(K, M) = C`. -/
  encrypt : K → M → C
  /-- Deterministic decryption: `Dec(K, C) = some M` or `none`. -/
  decrypt : K → C → Option M
-- ANCHOR_END: DetSEAlg

namespace DetSEAlg

variable {K M C : Type}

/-- A `DetSEAlg` is correct if decryption always recovers the plaintext. -/
-- ANCHOR: DetSEAlgCorrect
def Correct (se : DetSEAlg K M C) : Prop :=
  ∀ (k : K) (m : M), se.decrypt k (se.encrypt k m) = some m
-- ANCHOR_END: DetSEAlgCorrect

/-- Let `lenM : M → ℕ` be a message length. The ciphertext length of `se` depends only on the
message length: `|m| = |m'|` implies `|Enc(K, m)| = |Enc(K', m')|` for all keys `K, K'`.
NRS14 Section 2 requires this of every scheme. -/
-- ANCHOR: DetSEAlgLengthRegular
def LengthRegular [LenSampleable C] (lenM : M → ℕ) (se : DetSEAlg K M C) : Prop :=
  ∀ (k k' : K) (m m' : M), lenM m = lenM m' →
    LenSampleable.len (se.encrypt k m) = LenSampleable.len (se.encrypt k' m')
-- ANCHOR_END: DetSEAlgLengthRegular

section OTS

/-! ## One-Time Secrecy Game

Ros26 Definition 5.3.2 (computational one-time secrecy), with the random ciphertext sampled by
length.

The adversary `A` has access to:
- Uniform randomness (`unifSpec`).
- An encryption oracle `encrypt(m)` that samples a fresh key `K ← keygen` on every call;
  if `b = false`, it returns `Enc(K, m)`;
  if `b = true`, it returns a ciphertext uniform among those of length `|Enc(K, m)|`.

The game has no state. For schemes that satisfy `LengthRegular`, it is strictly stronger than
left-or-right one-time secrecy on messages of equal length. Without `LengthRegular`, the
ciphertext length can reveal the message.
-/

/-! ### Oracle spec -/

/-- Oracle spec (signatures only) for the one-time secrecy game: uniform randomness plus an
encryption oracle `M →ₒ C`. -/
abbrev otsSpec (M C : Type) := unifSpec + (M →ₒ C)

/-! ### Adversary -/

/-- One-time secrecy adversary: a computation with access to uniform randomness and the
encryption oracle, outputting a guess bit. -/
abbrev OTSAdversary (M C : Type) :=
  OracleComp (otsSpec M C) Bool

/-! ### Oracle implementations -/

/-- Uniform-randomness oracle for the one-time secrecy game. -/
def oracleUnif : QueryImpl unifSpec ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)

/-- Encryption oracle for the one-time secrecy game. Each call samples a fresh key `k`; if
`b = false`, it returns `se.encrypt k m`; if `b = true`, it returns a uniform ciphertext of the
same length as `se.encrypt k m`. -/
-- ANCHOR: detSEOracleEncrypt
def oracleEncrypt [LenSampleable C] (se : DetSEAlg K M C) (b : Bool) :
    QueryImpl (M →ₒ C) ProbComp :=
  fun m => do
    let k ← se.keygen
    if b then LenSampleable.unifSameLen (se.encrypt k m)
    else pure (se.encrypt k m)
-- ANCHOR_END: detSEOracleEncrypt

/-- Complete oracle set for the one-time secrecy game. -/
def otsImpl [LenSampleable C] (se : DetSEAlg K M C) (b : Bool) :
    QueryImpl (otsSpec M C) ProbComp :=
  oracleUnif + oracleEncrypt se b

/-! ### Security experiment -/

/-- One-time secrecy experiment with a fixed challenge bit `b`. The branch `b = false` is
`L_ots-real` of Ros26, and `b = true` is `L_ots-rand`. -/
-- ANCHOR: detSESecurityExpFixedBit
def securityExpFixedBit [LenSampleable C] (se : DetSEAlg K M C)
    (adversary : OTSAdversary M C) (b : Bool) : ProbComp Bool :=
  simulateQ (otsImpl se b) adversary
-- ANCHOR_END: detSESecurityExpFixedBit

/-- One-time secrecy distinguishing advantage:
`|Pr[A^{L_ots-rand} = 1] - Pr[A^{L_ots-real} = 1]|`. -/
-- ANCHOR: detSEDistAdvantage
noncomputable def distAdvantage [LenSampleable C] (se : DetSEAlg K M C)
    (adversary : OTSAdversary M C) : ℝ :=
  |(Pr{let x ← securityExpFixedBit se adversary true}[x = true]).toReal -
   (Pr{let x ← securityExpFixedBit se adversary false}[x = true]).toReal|
-- ANCHOR_END: detSEDistAdvantage

end OTS

end DetSEAlg
