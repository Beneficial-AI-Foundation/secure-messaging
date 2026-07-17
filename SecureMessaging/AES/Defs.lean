/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Mathlib.Data.BitVec
import SecureMessaging.PRP.Defs

/-!
# AES as a block-cipher interface

`AES` is the interface an AES implementation plugs into: a keyed, invertible
permutation on 128-bit blocks.

The naming deserves care. AES (FIPS 197) is a *concrete* algorithm — a specific
round function over `GF(2^8)`, key schedule, and block/key sizes. "PRP"
(pseudorandom permutation) is the *abstract* security property AES is *assumed* to
satisfy; there is no proof, only the failure of cryptanalysis. So "PRP" names the
bar and "AES" names a specific candidate that clears it. Here we model only the
interface: `AES` is a `PRPScheme` on `BitVec 128`, and the FIPS-197 rounds stay
abstract (an assumed-PRP instance to be supplied later).

Consumers (e.g. `SecureMessaging.AEAD.AESGCM`) use the forward direction `perm`
only; confidentiality/integrity of a mode is derived from AES's PRP security via
the PRP/PRF switching lemma, not assumed of AES itself. (The lemma's PRF-side
object is `PRPScheme.toPRFScheme`, the forgetful `PRP → PRF` view; the switching
lemma itself is future work.)

## References

- [FIPS197] NIST. *Advanced Encryption Standard (AES)*, FIPS 197, 2001.
  https://csrc.nist.gov/pubs/fips/197/final
-/

/-- An AES block cipher: a PRP on 128-bit blocks. The key space `K` is an
arbitrary type parameter; intended instantiations are `BitVec 128`, `BitVec 192`,
and `BitVec 256` for AES-128/192/256.

The `PRPScheme` fields give the interface: encryption is the forward permutation
`perm`, decryption is `invPerm`. The security-relevant properties are *not*
bundled by this alias but assumed separately: correctness is invertibility
(`PRPScheme.Correct`) and pseudorandomness is PRP security. -/
abbrev AES (K : Type) := PRPScheme K (BitVec 128)

namespace AES

variable {K : Type}

/-- Forward AES block encryption (definitionally `PRPScheme.perm`). -/
abbrev encrypt (a : AES K) : K → BitVec 128 → BitVec 128 := a.perm

/-- AES block decryption (definitionally `PRPScheme.invPerm`). -/
abbrev decrypt (a : AES K) : K → BitVec 128 → BitVec 128 := a.invPerm

end AES
