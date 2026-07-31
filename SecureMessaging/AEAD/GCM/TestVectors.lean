/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec
import Mathlib.Logic.Equiv.Basic
import SecureMessaging.PRP.Defs

/-!
# Shared GCM known-answer test scaffolding (not part of the spec)

The GCM building blocks are validated against the McGrew–Viega *Test Case 3* vector
without pulling in a concrete AES. Two views of the same cipher share one source of
truth here (avoiding drift between the `Gcm` and `Construction` test suites):

- `tc3Cipher` — the forward map `E_K` as a plain function `K → BitVec 128 → BitVec 128`,
  a lookup table returning the published `E_K(CBᵢ)` outputs for exactly the blocks GCM
  queries. Used by `gctr`, which takes the raw forward function.
- `tc3BlockCipher` — the same map packaged as a `BlockCipher` (a genuine keyed
  permutation), the type `gcmEncrypt`/`gcmDecrypt` require.

## References

- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  source of the "Test Case 3" validation vector (App. B), which is not part of
  SP 800-38D. https://csrc.nist.gov/csrc/media/projects/block-cipher-techniques/documents/bcm/proposed-modes/gcm/gcm-revised-spec.pdf
-/

/-- Test scaffolding: the GCM Test Case 3 keyed cipher `E_K`, tabulated over
exactly the inputs GCM queries under that vector — `0` for the hash subkey
`H = E_K(0)`, the pre-counter block `J₀` for the tag mask, and the `inc₃₂`
counter chain from `J₀` (i.e. the `E_K(CBᵢ)` keystream). Lets `gctr` be checked
against the vector without a concrete AES. Not part of the spec.

Presented as a key-indexed forward-cipher family `K → BitVec 128 → BitVec 128` over
`K = Unit` — the table already fixes McGrew–Viega's single key, so there is one key,
written `()` — to match the `ciph`/`k` shape `gctr` takes. `tc3Cipher () = E_K` is
the tabulated map. -/
@[nolint unusedArguments]
def tc3Cipher (_k : Unit) (cb : BitVec 128) : BitVec 128 :=
  if cb = 0xcafebabefacedbaddecaf88800000001 then 0x3247184b3c4f69a44dbcd22887bbb418
  else if cb = 0xcafebabefacedbaddecaf88800000002 then 0x9bb22ce7d9f372c1ee2b28722b25f206
  else if cb = 0xcafebabefacedbaddecaf88800000003 then 0x650d887c3936533a1b8d4e1ea39d2b5c
  else if cb = 0xcafebabefacedbaddecaf88800000004 then 0x3de91827c10e9a4f5240647ee5221f20
  else if cb = 0xcafebabefacedbaddecaf88800000005 then 0xaac9e6ccc0074ac0873b9ba85d908bd0
  else if cb = 0 then 0xb83b533708bf535d0aa6e52980d53b78
  else 0

/-- The Test Case 3 cipher as a genuine permutation: the involution that swaps each
block GCM queries under the vector (`0`, the pre-counter block `J₀`, and the `inc₃₂`
counter chain) with its published `E_K` output, and fixes every other block. The six
queried inputs and their six outputs are pairwise distinct, so these are disjoint
transpositions — a bona-fide `Equiv.Perm`, hence its own inverse. It agrees with
`tc3Cipher` on every block GCM queries, so the vectors are unchanged, while being a
genuine permutation as NIST requires. GCM never queries the outputs, so the swap
direction on them is irrelevant. -/
private def tc3Equiv : Equiv.Perm (BitVec 128) :=
  (Equiv.swap 0xcafebabefacedbaddecaf88800000001 0x3247184b3c4f69a44dbcd22887bbb418).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000002 0x9bb22ce7d9f372c1ee2b28722b25f206).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000003 0x650d887c3936533a1b8d4e1ea39d2b5c).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000004 0x3de91827c10e9a4f5240647ee5221f20).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000005 0xaac9e6ccc0074ac0873b9ba85d908bd0).trans <|
  (Equiv.swap 0 0xb83b533708bf535d0aa6e52980d53b78)

/-- Test Case 3 cipher packaged as a `BlockCipher` over `K = Unit`, for the
`gcmEncrypt`/`gcmDecrypt` vectors. `perm` and `invPerm` are both `tc3Equiv` (an
involution), so `correct` is immediate. -/
def tc3BlockCipher : BlockCipher Unit (BitVec 128) where
  perm _ x := tc3Equiv x
  invPerm _ x := tc3Equiv.symm x
  correct _ x := ⟨tc3Equiv.symm_apply_apply x, tc3Equiv.apply_symm_apply x⟩
