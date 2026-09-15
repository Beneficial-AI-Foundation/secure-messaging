/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Construction

/-!
# GCM — `inc₃₂` and counter-block distinctness

Arithmetic of `GCM.inc32` in numeral (`toNat`) form, and pairwise distinctness of the `n + 2`
block-cipher inputs of one GCM call: the GHASH-key input `0¹²⁸`, `J₀`, and the counter chain
from `inc₃₂(J₀)`. The IV occupies the high 96 bits of every input other than `0¹²⁸`, and the
low 32-bit counter field runs over `1, …, n + 1` without wrapping under `ValidMsgLength`, so
the inputs never collide. This is what lets the security proof replace the cipher outputs by
independent uniform values.
-/

namespace GCM

/-! ## `inc32` without wraparound -/

/-- While the counter field is below its maximum `2³² - 1`, `inc₃₂` carries nothing into the
high 96 bits, so it is plain successor on `toNat`. -/
theorem toNat_inc32 (x : BitVec 128) (h : x.toNat % 2 ^ 32 < 2 ^ 32 - 1) :
    (inc32 x).toNat = x.toNat + 1 := by
  have hx := x.isLt
  rw [inc32, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt (x.extractLsb' 0 32 + 1))]
  simp only [BitVec.toNat_add, BitVec.extractLsb'_toNat, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem inc32_eq_add_one (x : BitVec 128) (h : x.toNat % 2 ^ 32 < 2 ^ 32 - 1) :
    inc32 x = x + 1 := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [toNat_inc32 x h]
  simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## `counterChain` in numeral form -/

private lemma succ_mod_two_pow_32 (c : ℕ) (h : c % 2 ^ 32 < 2 ^ 32 - 1) :
    (c + 1) % 2 ^ 32 = c % 2 ^ 32 + 1 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show (1 : ℕ) < 2 ^ 32 by norm_num),
    Nat.mod_eq_of_lt (by omega)]

/-- Only the counter field `c % 2³²` is constrained; the high 96 bits (the IV) are
arbitrary. -/
theorem inc32_ofNat (c : ℕ) (h : c % 2 ^ 32 < 2 ^ 32 - 1) :
    inc32 (BitVec.ofNat 128 c) = BitVec.ofNat 128 (c + 1) := by
  have hlow : (BitVec.ofNat 128 c).toNat % 2 ^ 32 < 2 ^ 32 - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by norm_num : (2 : ℕ) ^ 32 ∣ 2 ^ 128)]
    exact h
  rw [inc32_eq_add_one _ hlow]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  omega

/-- The counter chain from a numeral is a run of consecutive numerals, provided the run stays
inside the 32-bit counter field so that no `inc₃₂` wraps. -/
theorem counterChain_ofNat (c m : ℕ) (h : c % 2 ^ 32 + m ≤ 2 ^ 32) :
    counterChain (BitVec.ofNat 128 c) m =
      (List.range m).map (fun i => BitVec.ofNat 128 (c + i)) := by
  induction m generalizing c with
  | zero => simp [counterChain]
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [counterChain]
    · have hlt : c % 2 ^ 32 < 2 ^ 32 - 1 := by omega
      rw [counterChain, inc32_ofNat c hlt,
        ih (c + 1) (by rw [succ_mod_two_pow_32 c hlt]; omega), List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.add_zero, List.cons.injEq, true_and]
      exact List.map_congr_left fun i _ => by rw [Function.comp_apply]; congr 1; omega

/-! ## The IV in numeral form -/

theorem ivBase_add_lt (iv : BitVec 96) {n : ℕ} (h : n < 2 ^ 32) :
    iv.toNat * 2 ^ 32 + n < 2 ^ 128 := by
  have := iv.isLt
  omega

theorem j0_eq_ofNat (iv : BitVec 96) :
    j0 iv = BitVec.ofNat 128 (iv.toNat * 2 ^ 32 + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ivBase_add_lt iv (by norm_num)), j0,
    BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (show (1 : BitVec 1).toNat < 2 ^ 1 by decide)]
  simp only [show (0 : BitVec 31).toNat = 0 from rfl, show (1 : BitVec 1).toNat = 1 from rfl,
    Nat.or_zero, Nat.shiftLeft_eq]
  omega

/-- `J₀` never equals the GHASH-key input `0¹²⁸`, whatever the IV: its counter field is `1`. -/
theorem j0_ne_zero (iv : BitVec 96) : j0 iv ≠ 0 := by
  rw [j0_eq_ofNat]
  intro h
  have hlt := ivBase_add_lt iv (show (1 : ℕ) < 2 ^ 32 by norm_num)
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, show (0 : BitVec 128).toNat = 0 from rfl] at h'
  omega

/-! ## Pairwise distinctness of the cipher inputs -/

/-- `ValidMsgLength` keeps the block count `n = ⌈L/128⌉` and its successor inside the counter
field: `2³⁹ - 256 = 128 · (2³² - 2)`, so `n ≤ 2³² - 2`. -/
theorem blockCount_add_one_le {L : ℕ} (hL : ValidMsgLength L) :
    (L + 127) / 128 + 1 ≤ 2 ^ 32 - 1 := by
  have h := hL.1
  omega

/-- The `n + 2` cipher inputs of one GCM call (GHASH key, tag mask, `n` keystream blocks) in
numeral form: `0¹²⁸` and the run `iv.toNat · 2³² + 1, …, iv.toNat · 2³² + n + 1`. -/
theorem cipherInputs_eq (iv : BitVec 96) (n : ℕ) (h : n + 1 ≤ 2 ^ 32 - 1) :
    (0 : BitVec 128) :: j0 iv :: counterChain (inc32 (j0 iv)) n =
      (0 : BitVec 128) :: (List.range (n + 1)).map
        (fun i => BitVec.ofNat 128 (iv.toNat * 2 ^ 32 + 1 + i)) := by
  have hbase : iv.toNat * 2 ^ 32 % 2 ^ 32 = 0 := Nat.mul_mod_left _ _
  rw [j0_eq_ofNat, inc32_ofNat _ (by omega),
    counterChain_ofNat _ n (by omega), List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero, List.cons.injEq, true_and]
  refine List.map_congr_left fun i _ => ?_
  have hi : iv.toNat * 2 ^ 32 + 1 + 1 + i = iv.toNat * 2 ^ 32 + 1 + Nat.succ i := by omega
  rw [Function.comp_apply, hi]

/-- No chain numeral is `0¹²⁸` (its counter field is `≥ 1`), and the run is injective below
the field maximum. -/
theorem cipherInputs_nodup (iv : BitVec 96) (n : ℕ) (h : n + 1 ≤ 2 ^ 32 - 1) :
    ((0 : BitVec 128) :: (List.range (n + 1)).map
      (fun i => BitVec.ofNat 128 (iv.toNat * 2 ^ 32 + 1 + i))).Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · -- The GHASH-key input `0¹²⁸` is off the chain: every chain numeral is in `[1, 2¹²⁸)`.
    rw [List.mem_map]
    rintro ⟨i, hi, hzero⟩
    rw [List.mem_range] at hi
    have hlt := ivBase_add_lt iv (show 1 + i < 2 ^ 32 by omega)
    have := congrArg BitVec.toNat hzero
    simp only [BitVec.toNat_ofNat, show (0 : BitVec 128).toNat = 0 from rfl] at this
    omega
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro i hi j hj hij
    rw [List.mem_range] at hi hj
    have hi' := ivBase_add_lt iv (show 1 + i < 2 ^ 32 by omega)
    have hj' := ivBase_add_lt iv (show 1 + j < 2 ^ 32 by omega)
    have h128 : (iv.toNat * 2 ^ 32 + 1 + i) % 2 ^ 128 =
        (iv.toNat * 2 ^ 32 + 1 + j) % 2 ^ 128 := by
      simpa only [BitVec.toNat_ofNat] using congrArg BitVec.toNat hij
    omega

/-- The cipher inputs of one GCM call are pairwise distinct, for every IV, from
`ValidMsgLength L` alone. -/
theorem cipherInputs_pairwise_ne {L : ℕ} (iv : BitVec 96) (hL : ValidMsgLength L) :
    ((0 : BitVec 128) :: j0 iv ::
      counterChain (inc32 (j0 iv)) ((L + 127) / 128)).Pairwise (· ≠ ·) := by
  rw [cipherInputs_eq iv _ (blockCount_add_one_le hL)]
  exact cipherInputs_nodup iv _ (blockCount_add_one_le hL)

theorem counterChain_length (icb : BitVec 128) (m : ℕ) :
    (counterChain icb m).length = m := by
  induction m generalizing icb with
  | zero => rfl
  | succ n ih => simp [counterChain, ih]

end GCM
