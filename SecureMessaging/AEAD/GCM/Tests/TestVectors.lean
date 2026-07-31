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

Validation fixtures for the McGrew–Viega *Test Case 3* vector, letting the GCM mode
be tested independently of a concrete AES formalization (avoiding drift between the
`Gcm` and `Construction` test suites by sharing one source of truth here):

- `tc3Cipher` — the forward map `E_K` as a plain function `K → BitVec 128 → BitVec 128`,
  a lookup table returning the published `E_K(CBᵢ)` outputs for exactly the six blocks
  the vector queries — `0`, the pre-counter block `J₀`, and the counter chain
  `inc₃₂(J₀) … inc₃₂⁴(J₀)`; every other input maps to `0`. Used by `gctr`, which takes
  the raw forward function.
- `tc3BlockCipher` — an artificial invertible cipher agreeing with `tc3Cipher` on
  those same six blocks, packaged as a `BlockCipher` (a genuine keyed permutation),
  the type `gcmEncrypt`/`gcmDecrypt` require. The permutation is necessary because
  `tc3Cipher`'s lookup table is not invertible (every untabulated input collapses to
  `0`), while `BlockCipher` demands `perm`/`invPerm` be mutual inverses.

`tc3Cipher` and `tc3BlockCipher.perm` agree on every block queried by these test
vectors. **Neither definition is an implementation of AES**; they are validation
fixtures used to test the GCM mode independently of a concrete AES formalization.

## References

- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  source of the "Test Case 3" validation vector (App. B), which is not part of
  SP 800-38D. https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
-/

/-- Test scaffolding: the GCM Test Case 3 keyed cipher `E_K`, tabulated over
exactly the six inputs GCM queries under that vector — `0` for the hash subkey
`H = E_K(0)`, the pre-counter block `J₀` for the tag mask, and the `inc₃₂` counter
chain `inc₃₂(J₀) … inc₃₂⁴(J₀)` for the keystream. Every other input returns `0`,
which is *not* a real `E_K` output — those inputs are never queried by `gctr` under
this vector, so the placeholder value is unobservable. Lets `gctr` be checked
against the vector without a concrete AES. Not part of the spec; not an AES
implementation.

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

/-- An artificial permutation, **not** a model of AES: the composition of six disjoint
transpositions, each swapping one of the vector's six queried blocks (`0`, `J₀`, and
`inc₃₂(J₀) … inc₃₂⁴(J₀)`) with its published `E_K` output, and fixing every other
block. Since the twelve values involved (six inputs, six outputs) are pairwise
distinct, the transpositions are disjoint, so the composition is a bona-fide
`Equiv.Perm` and, as a product of disjoint involutions, is its own inverse.

This permutation — not `tc3Cipher` — is what `tc3BlockCipher` needs, because
`gcmEncrypt`/`gcmDecrypt` require an invertible `BlockCipher`, whereas `tc3Cipher`'s
raw lookup table is not invertible (every untabulated input collapses to `0`).
`tc3Equiv` and `tc3Cipher` therefore **disagree** off the query set (fixed vs. `0`);
they agree only on the six blocks the vector queries, which is all `gctr`,
`gcmEncrypt`, and `gcmDecrypt` ever touch under this vector, so the swap direction on
the six outputs is irrelevant — GCM never queries them. -/
private def tc3Equiv : Equiv.Perm (BitVec 128) :=
  (Equiv.swap 0xcafebabefacedbaddecaf88800000001 0x3247184b3c4f69a44dbcd22887bbb418).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000002 0x9bb22ce7d9f372c1ee2b28722b25f206).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000003 0x650d887c3936533a1b8d4e1ea39d2b5c).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000004 0x3de91827c10e9a4f5240647ee5221f20).trans <|
  (Equiv.swap 0xcafebabefacedbaddecaf88800000005 0xaac9e6ccc0074ac0873b9ba85d908bd0).trans <|
  (Equiv.swap 0 0xb83b533708bf535d0aa6e52980d53b78)

/-- Test Case 3 cipher packaged as a `BlockCipher` over `K = Unit`, for the
`gcmEncrypt`/`gcmDecrypt` vectors: `perm` is `tc3Equiv`, `invPerm` is
`tc3Equiv.symm`, and `correct` follows directly from the `Equiv` inverse laws
(`symm_apply_apply`/`apply_symm_apply`) — no involution argument needed, since an
`Equiv.Perm`'s `symm` is always a two-sided inverse. -/
def tc3BlockCipher : BlockCipher Unit (BitVec 128) where
  perm _ x := tc3Equiv x
  invPerm _ x := tc3Equiv.symm x
  correct _ x := ⟨tc3Equiv.symm_apply_apply x, tc3Equiv.apply_symm_apply x⟩
