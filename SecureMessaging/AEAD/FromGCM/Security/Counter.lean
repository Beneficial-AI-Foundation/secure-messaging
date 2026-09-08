/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM

/-!
# GCM — inc32 and counter-block distinctness

Arithmetic of `GCM.inc32` and pairwise distinctness of the counter blocks
`counterChain` produces from `J₀` (Phase 1 criterion 2), the input-freshness fact
behind idealizing the cipher calls.
-/

namespace GCM

/-! ## `inc32` without wraparound -/

/-- `inc₃₂` at the `toNat` level: while the low 32-bit counter field is below its
maximum `2³² - 1`, incrementing it produces no carry into the fixed high 96 bits,
so `inc₃₂` is plain successor on `toNat`. -/
theorem toNat_inc32 (x : BitVec 128) (h : x.toNat % 2 ^ 32 < 2 ^ 32 - 1) :
    (inc32 x).toNat = x.toNat + 1 := by
  have hx := x.isLt
  rw [inc32, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt (x.extractLsb' 0 32 + 1))]
  simp only [BitVec.toNat_add, BitVec.extractLsb'_toNat, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- Criterion 2, non-wrap characterization of `inc₃₂` (NIST SP 800-38D §6.2): as
long as the low 32-bit counter field is below its maximum, `inc₃₂ x = x + 1` in
`BitVec 128`. -/
theorem inc32_eq_add_one (x : BitVec 128) (h : x.toNat % 2 ^ 32 < 2 ^ 32 - 1) :
    inc32 x = x + 1 := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [toNat_inc32 x h]
  simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  omega

end GCM
