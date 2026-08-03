/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM.Specification
import SecureMessaging.AEAD.Defs
import SecureMessaging.PRP.Defs

/-!
# One-time-key GCM as an `AEADScheme` (ACD19)

Packages the 96-bit-IV GCM algorithms (`Specification`) as the one-time-key `AEADScheme`
`gcmOneTimeAEAD`, targeting the ACD19 AEAD interface (`SecureMessaging.AEAD.Defs`).

## References

- [ACD19] Alwen, Coretti, Dodis. *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol.* EUROCRYPT 2019.
  https://eprint.iacr.org/2018/1037.pdf
- [RFC9180] Barnes, Bhargavan, Lipp, Wood. *Hybrid Public Key Encryption*, RFC 9180,
  2022 — HPKE, libsignal's only production plain-GCM caller.
  https://www.rfc-editor.org/rfc/rfc9180
-/

open OracleSpec OracleComp

/-- **One-time-key GCM as an `AEADScheme`** (ACD19 interface). Fixes the IV to `0`,
sound because `keygen` draws a fresh key per encryption, so the `(key, IV)` pair is
never reused (GCM's uniqueness requirement, NIST §8); it is not a multi-invocation
interface (for that, call `gcmEncrypt`/`gcmDecrypt` directly).

`prp : PRPScheme K (BitVec 128)` supplies the block cipher plus key generation; the
mode uses only `prp.toBlockCipher`, and the PRP→PRF switch belongs to the security
reduction, not the mode. The AEAD key is the block-cipher key `K` (no IV bundled in)
and the ciphertext is `(C, T)`. The domain is NIST-supported by construction — AAD is
`SupportedAAD`, the message length carries `_hL : ValidMsgLength L` — with the message
fixed to `BitVec L` so the ciphertext `BitVec L × BitVec 128` is `SampleableType` for
the IND-CCA game.

`_hL` documents/requires length-support at construction but is unused in the body
(correctness supplies its own hypothesis), hence `nolint`. -/
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

/-- `gcmOneTimeAEAD` satisfies the unconditional ACD19 `AEADScheme.Correct` (given the
message length is supported, `hL`): every domain AAD is supported so the length guard
passes, the recomputed tag matches by construction, and `gctr_involution` recovers the
plaintext. -/
-- ANCHOR: gcmOneTimeAEAD_correct
theorem gcmOneTimeAEAD_correct {K : Type} (prp : PRPScheme K (BitVec 128)) {L : ℕ}
    (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp L hL).Correct
-- ANCHOR_END: gcmOneTimeAEAD_correct
    := by
  rintro k ⟨⟨av, ad⟩, hav⟩ m
  have hv : ValidMsgLength L ∧ ValidAADLength av := ⟨hL, hav⟩
  simp only [gcmOneTimeAEAD, gcmEncrypt, gcmDecrypt]
  rw [if_pos hv]
  simp only [if_true, gctr_involution]
