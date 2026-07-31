/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM.Construction
import SecureMessaging.AEAD.GCM.Tests.TestVectors

/-!
# GCM authenticated encryption known-answer tests (not part of the spec)

Test Case 3 (four full blocks, empty AAD) covers the block-aligned path; Test
Case 4 (60-byte plaintext, 20-byte AAD) covers the **partial final block**,
**partial AAD block**, and the **true bit-length** field. Both share the Test
Case 3 key/IV, so the block cipher `tc3BlockCipher` (see
`SecureMessaging.AEAD.GCM.Tests.TestVectors`) already covers every counter block and
the hash subkey both vectors query. `native_decide` is used because kernel `decide`
cannot reduce the wide `BitVec` literals (their `2^n` modulus exceeds the
exponentiation threshold); the resulting `Lean.ofReduceBool` axiom is confined to
these anonymous `example`s and does not enter `gcmOneTimeAEAD`/`gcmOneTimeAEAD_correct`.

## References

- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  the original GCM proposal; source of the "Test Case 3/4" validation vectors
  (App. B), which are not part of SP 800-38D. https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false

/-- Test Case 3 plaintext (four blocks, 512 bits). -/
private def tc3Plain : BitVec 512 :=
  0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255

/-- Test Case 3 ciphertext (512 bits) and full tag. -/
private def tc3Ct : BitVec 512 :=
  0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985
private def tc3Tag : BitVec 128 := 0x4d5c2af327cd64a62cf35abd2ba6fab4

/-- `gcmEncrypt` reproduces the Test Case 3 ciphertext and tag (empty AAD). -/
example :
    gcmEncrypt tc3BlockCipher () 0xcafebabefacedbaddecaf888 (0 : BitVec 0) tc3Plain
      = (tc3Ct, tc3Tag) := by native_decide

/-- `gcmDecrypt` inverts `gcmEncrypt` on Test Case 3. -/
example :
    gcmDecrypt tc3BlockCipher () 0xcafebabefacedbaddecaf888 (0 : BitVec 0) (tc3Ct, tc3Tag)
      = some tc3Plain := by native_decide

/-- `gcmDecrypt` rejects a tampered tag. -/
example :
    gcmDecrypt tc3BlockCipher () 0xcafebabefacedbaddecaf888 (0 : BitVec 0) (tc3Ct, 0)
      = none := by native_decide

/-- Test Case 4 AAD (20 bytes = 160 bits): a full block plus a partial block. -/
private def tc4Aad : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2

/-- Test Case 4 plaintext (60 bytes = 480 bits): three full blocks plus a
12-byte partial final block. -/
private def tc4Plain : BitVec 480 :=
  0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39

/-- Test Case 4 ciphertext (480 bits) and full tag. -/
private def tc4Ct : BitVec 480 :=
  0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091
private def tc4Tag : BitVec 128 := 0x5bc94fbc3221a5db94fae95ae7121a47

/-- `gcmEncrypt` reproduces Test Case 4: exercises the partial final block (GCTR
keystream truncation), the partial AAD block (`0^v`/`0^u` padding), and the true
`len(A) ‖ len(C)` field, all against the authoritative vector. -/
example :
    gcmEncrypt tc3BlockCipher () 0xcafebabefacedbaddecaf888 tc4Aad tc4Plain
      = (tc4Ct, tc4Tag) := by native_decide

/-- `gcmDecrypt` inverts `gcmEncrypt` on Test Case 4 (partial blocks, non-empty AAD). -/
example :
    gcmDecrypt tc3BlockCipher () 0xcafebabefacedbaddecaf888 tc4Aad (tc4Ct, tc4Tag)
      = some tc4Plain := by native_decide

/-- AAD is authenticated: decrypting Test Case 4 under a different AAD is rejected
(GHASH, hence the tag, binds the AAD). -/
example :
    gcmDecrypt tc3BlockCipher () 0xcafebabefacedbaddecaf888
      (0xfeedfacedeadbeeffeedfacedeadbeef00000000 : BitVec 160) (tc4Ct, tc4Tag)
      = none := by native_decide
