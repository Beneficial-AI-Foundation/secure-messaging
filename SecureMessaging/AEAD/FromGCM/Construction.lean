/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM
import SecureMessaging.AEAD.Defs
import ToVCVio.CryptoFoundations.PRP

/-!
# One-time-key GCM as an `AEADScheme` (ACD19)

Packages the 96-bit-IV GCM algorithms (`Algorithms`) as the one-time-key `AEADScheme`
`gcmOneTimeAEAD`, targeting the ACD19 AEAD interface (`SecureMessaging.AEAD.Defs`).

## References

- [ACD19] Alwen, Coretti, Dodis. *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol.* EUROCRYPT 2019.
  https://eprint.iacr.org/2018/1037.pdf
- [RFC9180] Barnes, Bhargavan, Lipp, Wood. *Hybrid Public Key Encryption*, RFC 9180,
  2022. HPKE, libsignal's only production plain-GCM caller.
  https://www.rfc-editor.org/rfc/rfc9180
-/

namespace GCM

open OracleSpec OracleComp

/-- One-time-key GCM as an `AEADScheme` (ACD19 interface): `gcmEncrypt`/`gcmDecrypt` under the
block cipher of `prp`, at a public 96-bit IV `iv` fixed at construction time. A fixed IV is
sound because `keygen` draws a fresh key per encryption, so no `(key, IV)` pair is reused
(NIST SP 800-38D §8); the security theorem (`FromGCM/Security.lean`) is quantified over `iv`.

The message length is fixed to `L` so that the ciphertext type `BitVec L × BitVec 128` is a
`SampleableType`, as the IND-CCA game needs. `_hL` records `ValidMsgLength L` at construction
but is unused in the body, hence `nolint`. -/
@[nolint unusedArguments]
-- ANCHOR: gcmOneTimeAEAD
def gcmOneTimeAEAD {K : Type} (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.toBlockCipher k iv ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.toBlockCipher k iv ad.1.2 c
-- ANCHOR_END: gcmOneTimeAEAD

end GCM
