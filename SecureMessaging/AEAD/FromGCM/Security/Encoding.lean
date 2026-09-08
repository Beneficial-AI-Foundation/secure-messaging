/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM

/-!
# GCM — GHASH encoding domain and injectivity

The block-sequence encoding `A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ len(A) ‖ len(C)` that GCM feeds to
GHASH, and its injectivity on valid (AAD, ciphertext) pairs (Phase 1 criterion 4).

This file provides the foundations: the named encoding map `gcmEncode` over the domain
`SupportedAAD × BitVec L` (matching `gcmEncrypt`'s ghash argument verbatim), the block
budget `maxBlocks` with the length bound `gcmEncode_length_le` (the degree bound the
GHASH root count uses), and the injectivity helpers the distinctness theorem assembles:
`padBlocks_injective` at fixed bit-width and `ofNat64_inj` below `2 ^ 64`.

GHASH itself (`ghash`, `gfmul`) is treated as opaque here: nothing in this file unfolds
it.
-/

namespace GCM

/-! ## The GHASH encoding map -/

/-- The block sequence GCM feeds to GHASH: `A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ [len(A)]₆₄ ‖ [len(C)]₆₄`
(NIST SP 800-38D §7.1 steps 4–5), as a map over the AEAD domain
`SupportedAAD × BitVec L`. Matches `gcmEncrypt`'s ghash argument verbatim
(`gcmEncrypt_ghash_eq_gcmEncode`). -/
def gcmEncode {L : ℕ} (ad : SupportedAAD) (c : BitVec L) : List (BitVec 128) :=
  padBlocks ad.1.2 ++ padBlocks c ++ [BitVec.ofNat 64 ad.1.1 ++ BitVec.ofNat 64 L]

/-- `gcmEncrypt` hashes exactly `gcmEncode ad c` where `c` is the GCTR ciphertext:
the connection between the spec (`GCM.lean`) and the named encoding map. Stated as a
full unfolding of `gcmEncrypt` at a `SupportedAAD` argument so games can rewrite the
encryption call into `gcmEncode` form. -/
theorem gcmEncrypt_ghash_eq_gcmEncode {K : Type} (ciph : CIPH K) (k : K) (iv : BitVec 96)
    {L : ℕ} (ad : SupportedAAD) (m : BitVec L) :
    gcmEncrypt ciph k iv ad.1.2 m =
      (gctr ciph.perm k (inc32 (iv ++ (0 : BitVec 31) ++ (1 : BitVec 1))) m,
        gctr ciph.perm k (iv ++ (0 : BitVec 31) ++ (1 : BitVec 1))
          (ghash (ciph.perm k 0)
            (gcmEncode ad
              (gctr ciph.perm k (inc32 (iv ++ (0 : BitVec 31) ++ (1 : BitVec 1))) m)))) :=
  rfl

/-! ## Block budget -/

/-- The largest AAD bit-length `ValidAADLength` admits: the largest multiple of 8 that
is `≤ 2 ^ 64 - 1` (NIST SP 800-38D §5.2.1.1). -/
def lenA_max : ℕ := 2 ^ 64 - 8

/-- Upper bound on `(gcmEncode ad c).length` for `c : BitVec L`: maximal AAD blocks,
plus ciphertext blocks, plus the length block (`gcmEncode_length_le`). This is the
degree bound for the GHASH polynomial. -/
def maxBlocks (L : ℕ) : ℕ := (lenA_max + 127) / 128 + (L + 127) / 128 + 1

/-- The maximal AAD occupies `2 ^ 57` blocks. -/
theorem lenA_max_blocks : (lenA_max + 127) / 128 = 2 ^ 57 := by
  simp [lenA_max]

/-- `padBlocks` produces `⌈n/128⌉` blocks. -/
@[simp] theorem length_padBlocks {n : ℕ} (x : BitVec n) :
    (padBlocks x).length = (n + 127) / 128 := by
  simp [padBlocks]

/-- A valid AAD length is at most `lenA_max`: a multiple of 8 that is `≤ 2 ^ 64 - 1`
is `≤ 2 ^ 64 - 8`. -/
theorem le_lenA_max (ad : SupportedAAD) : ad.1.1 ≤ lenA_max := by
  have hle : ad.1.1 ≤ 2 ^ 64 - 1 := ad.2.1
  have hdvd : 8 ∣ ad.1.1 := ad.2.2
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  change ad.1.1 ≤ 2 ^ 64 - 8
  omega

/-- The encoding never exceeds `maxBlocks L` blocks: the degree bound the GHASH root
count uses (Phase 1 criterion 4). -/
theorem gcmEncode_length_le {L : ℕ} (ad : SupportedAAD) (c : BitVec L) :
    (gcmEncode ad c).length ≤ maxBlocks L := by
  have h : (ad.1.1 + 127) / 128 ≤ (lenA_max + 127) / 128 :=
    Nat.div_le_div_right (by have := le_lenA_max ad; omega)
  simp only [gcmEncode, maxBlocks, List.length_append, length_padBlocks,
    List.length_cons, List.length_nil]
  omega

/-! ## Injectivity helpers -/

/-- `BitVec.ofNat 64` is injective below `2 ^ 64`: distinct valid lengths give distinct
64-bit length fields. -/
theorem ofNat64_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have h' : a % 2 ^ 64 = b % 2 ^ 64 := by
    simpa using BitVec.toNat_inj.mpr h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- Bit `i` of `x` sits at position `i % 128` of block `i / 128`: the bridge between
`padBlocks` blocks and the bits of `x`. Holds for all `i` (out-of-range reads are
`false` on both sides). -/
theorem getMsbD_paddedBlock {n : ℕ} (x : BitVec n) (i : ℕ) :
    (paddedBlock x (i / 128)).getMsbD (i % 128) = x.getMsbD i := by
  have hm : i % 128 < 128 := Nat.mod_lt _ (by omega)
  simp only [paddedBlock, BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm,
    Option.map_some, Option.getD_some]
  rw [Nat.div_add_mod]

/-- At a fixed bit-width, `padBlocks` is injective: the blocks determine the
bit-string (zero-padding adds no ambiguity once the width is fixed). -/
theorem padBlocks_injective {n : ℕ} : Function.Injective (padBlocks (n := n)) := by
  intro x y h
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have hlen : i / 128 < (n + 127) / 128 := by omega
  have hblock : paddedBlock x (i / 128) = paddedBlock y (i / 128) := by
    have h' := congrArg (fun l => l[i / 128]?) h
    simpa [padBlocks, List.getElem?_range hlen] using h'
  rw [← getMsbD_paddedBlock x i, ← getMsbD_paddedBlock y i, hblock]

/-- Distinct AAD lengths below `2 ^ 64` give distinct length blocks
`[len(A)]₆₄ ‖ [len(C)]₆₄`, whatever the (equal) ciphertext length `L`: the unequal-lenA
case of the encoding distinctness theorem. -/
theorem lenBlock_ne_of_ne {L : ℕ} {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hab : a ≠ b) :
    BitVec.ofNat 64 a ++ BitVec.ofNat 64 L ≠ BitVec.ofNat 64 b ++ BitVec.ofNat 64 L := by
  intro h
  refine hab (ofNat64_inj ha hb ?_)
  have h' := congrArg (BitVec.extractLsb' 64 64) h
  simp only [BitVec.extractLsb'_append_eq_left] at h'
  exact h'

end GCM
