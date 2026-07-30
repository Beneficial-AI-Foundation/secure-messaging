/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec

/-!
# Shared GCM known-answer test scaffolding (not part of the spec)

The GCM building blocks (`gctr`, `gcmEncrypt`/`gcmDecrypt`) are validated against
the McGrew–Viega *Test Case 3* vector without pulling in a concrete AES: the
cipher is replaced by the lookup table `tc3Cipher`, which returns the published
`E_K(CBᵢ)` outputs for exactly the counter blocks GCM queries under that vector.

This lives in its own module so the `Gcm` and `Construction` test suites share a
single source of truth for the table (avoiding drift between the two files).

## References

- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  source of the "Test Case 3" validation vector (App. B), which is not part of
  SP 800-38D. https://csrc.nist.gov/csrc/media/projects/block-cipher-techniques/documents/bcm/proposed-modes/gcm/gcm-revised-spec.pdf
-/

/-- Test scaffolding: the GCM Test Case 3 keyed cipher `E_K`, tabulated over
exactly the inputs GCM queries under that vector — `0` for the hash subkey
`H = E_K(0)`, the pre-counter block `J₀` for the tag mask, and the `inc₃₂`
counter chain from `J₀` (i.e. the `E_K(CBᵢ)` keystream). Lets `gctr` and
`gcmEncrypt`/`gcmDecrypt` be checked against the vector without a concrete AES.
Not part of the spec.

Presented as a key-indexed block-cipher family `CIPH : K → BitVec 128 → BitVec 128`
over `K = Unit` — the table already fixes McGrew–Viega's single key, so there is
one key, written `()` — to match the `ciph`/`k` shape that `gctr`,
`gcmEncrypt`, and `gcmDecrypt` take. `tc3Cipher () = E_K` is the tabulated map. -/
@[nolint unusedArguments]
def tc3Cipher (_k : Unit) (cb : BitVec 128) : BitVec 128 :=
  if cb = 0xcafebabefacedbaddecaf88800000001 then 0x3247184b3c4f69a44dbcd22887bbb418
  else if cb = 0xcafebabefacedbaddecaf88800000002 then 0x9bb22ce7d9f372c1ee2b28722b25f206
  else if cb = 0xcafebabefacedbaddecaf88800000003 then 0x650d887c3936533a1b8d4e1ea39d2b5c
  else if cb = 0xcafebabefacedbaddecaf88800000004 then 0x3de91827c10e9a4f5240647ee5221f20
  else if cb = 0xcafebabefacedbaddecaf88800000005 then 0xaac9e6ccc0074ac0873b9ba85d908bd0
  else if cb = 0 then 0xb83b533708bf535d0aa6e52980d53b78
  else 0
