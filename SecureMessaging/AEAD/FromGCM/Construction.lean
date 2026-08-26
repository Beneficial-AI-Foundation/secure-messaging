/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM
import SecureMessaging.AEAD.Defs
import SecureMessaging.PRP.Defs

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

/-- One-time-key GCM as an `AEADScheme` (ACD19 interface). The IV is fixed to `0`; this
is sound because `keygen` draws a fresh key per encryption, so the `(key, IV)` pair is
never reused (GCM's uniqueness requirement, NIST §8). For a multi-invocation interface
call `gcmEncrypt`/`gcmDecrypt` directly.

`prp` supplies the block cipher and key generation; the mode itself uses only
`prp.toBlockCipher` (the PRP→PRF switch lives in the security reduction). The AEAD key
is the block-cipher key `K`, with no IV bundled in, and the ciphertext is `(C, T)`. The
message is fixed to `BitVec L` so the ciphertext `BitVec L × BitVec 128` is a
`SampleableType`, as the IND-CCA game needs; `SupportedAAD` and `_hL : ValidMsgLength L`
keep the domain within NIST's supported lengths.

`_hL` records the length requirement at construction but is unused in the body
(correctness supplies its own), hence `nolint`. -/
@[nolint unusedArguments]
-- ANCHOR: gcmOneTimeAEAD
def gcmOneTimeAEAD {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 c
-- ANCHOR_END: gcmOneTimeAEAD

end GCM
