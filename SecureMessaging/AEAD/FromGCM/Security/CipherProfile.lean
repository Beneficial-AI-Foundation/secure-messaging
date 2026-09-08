/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Construction

/-!
# GCM — cipher-call profile

The exact cipher-call profile of one-time GCM (Phase 1 criterion 1): at the all-zero
96-bit IV, `gcmEncrypt`/`gcmDecrypt` consume exactly three separated cipher outputs —
the hash key `H = CIPH_K(0¹²⁸)`, the tag mask `CIPH_K(J₀)` with `J₀ = 1`, and the GCTR
keystream blocks `CIPH_K` over `counterChain 2 ⌈lenP/128⌉`.

Foundations: the single-block keystream identity, the `J₀ = 1` and `inc₃₂(1) = 2`
numeral identities, and the single-block `gctr` mask identity.
-/

namespace GCM

/-! ## Foundation lemmas -/

/-- The GCTR keystream of a single block, untruncated, is the block itself
(`MSB₁₂₈(b) = b`). -/
theorem keystream_singleton (b : BitVec 128) : keystream [b] 128 = b := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  simp [keystream, hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]

/-- At the all-zero 96-bit IV, the pre-counter block `J₀ = IV ‖ 0³¹ ‖ 1`
(NIST SP 800-38D §7.1 step 2) is the numeral `1`. -/
theorem j0_zero_iv : ((0 : BitVec 96) ++ (0 : BitVec 31) ++ (1 : BitVec 1)) = (1 : BitVec 128) := by
  decide

/-- `inc₃₂(1) = 2`: the first GCTR counter block after `J₀ = 1` (NIST SP 800-38D §6.2). -/
theorem inc32_one : inc32 (1 : BitVec 128) = 2 := by
  decide

/-- A single-step counter chain is just the initial counter block. -/
theorem counterChain_one (icb : BitVec 128) : counterChain icb 1 = [icb] := rfl

/-- `gctr` on a single 128-bit block XORs in one cipher output: the tag-mask identity
`GCTR_K(ICB, S) = S ⊕ CIPH_K(ICB)` (NIST SP 800-38D §7.1 step 6, `MSB₁₂₈` trivial). -/
theorem gctr_single_block {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) (s : BitVec 128) :
    gctr ciph k icb s = s ^^^ ciph k icb := by
  simp only [gctr, Nat.reduceAdd, Nat.reduceDiv, counterChain_one, List.map_cons,
    List.map_nil, keystream_singleton]

/-! ## Encryption profile -/

/-- GCM encryption parameterized by its three separated cipher outputs: hash key `h`,
tag mask `mask`, and keystream blocks `ksBlocks`. Phases 2–3 substitute sampled values
for exactly these three parameters. -/
def gcmEncryptSpec (h mask : BitVec 128) (ksBlocks : List (BitVec 128))
    {lenA lenP : ℕ} (ad : BitVec lenA) (m : BitVec lenP) :
    BitVec lenP × BitVec 128 :=
  let c := m ^^^ keystream ksBlocks lenP
  (c, ghash h (padBlocks ad ++ padBlocks c ++
        [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP]) ^^^ mask)

/-- The cipher-call profile of GCM encryption at the all-zero IV: `gcmEncrypt` consumes
exactly `H = CIPH_K(0)` (the ghash key), `CIPH_K(1)` (the tag mask, `J₀ = 1`), and the
keystream blocks `CIPH_K` over `counterChain 2 ⌈lenP/128⌉` (message ICB `inc₃₂(J₀) = 2`). -/
-- ANCHOR: gcmEncrypt_profile
theorem gcmEncrypt_profile {K : Type} (ciph : CIPH K) (k : K) {lenA lenP : ℕ}
    (ad : BitVec lenA) (m : BitVec lenP) :
    gcmEncrypt ciph k 0 ad m =
      gcmEncryptSpec (ciph.perm k 0) (ciph.perm k 1)
        ((counterChain 2 ((lenP + 127) / 128)).map (ciph.perm k)) ad m := by
-- ANCHOR_END: gcmEncrypt_profile
  simp only [gcmEncrypt, gcmEncryptSpec]
  rw [j0_zero_iv, gctr_single_block, inc32_one]
  simp only [gctr]

end GCM
