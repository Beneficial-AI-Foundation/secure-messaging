/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM

/-!
# GCM — inc32 and counter-block distinctness

Arithmetic of `GCM.inc32` and pairwise distinctness of the counter blocks
`counterChain` produces from `J₀`, the input-freshness fact behind idealizing the
cipher calls.
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

/-- `inc₃₂` on a numeral below the 32-bit field maximum is the numeral successor. -/
theorem inc32_ofNat (c : ℕ) (h : c < 2 ^ 32 - 1) :
    inc32 (BitVec.ofNat 128 c) = BitVec.ofNat 128 (c + 1) := by
  rw [inc32_eq_add_one]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
    omega
  · simp only [BitVec.toNat_ofNat]
    omega

/-- Numeral characterization of the counter chain: starting from the
numeral ICB `c`, the chain is `[c, c + 1, …, c + m - 1]` as `BitVec 128` numerals,
provided the whole run stays inside the 32-bit counter field (`c + m ≤ 2 ^ 32`, so
no `inc₃₂` call wraps: every increment input is at most `c + m - 2 ≤ 2 ^ 32 - 2`). -/
theorem counterChain_ofNat (c m : ℕ) (h : c + m ≤ 2 ^ 32) :
    counterChain (BitVec.ofNat 128 c) m =
      (List.range m).map (fun i => BitVec.ofNat 128 (c + i)) := by
  induction m generalizing c with
  | zero => simp [counterChain]
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [counterChain]
    · rw [counterChain, inc32_ofNat c (by omega), ih (c + 1) (by omega),
        List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.add_zero, List.cons.injEq, true_and]
      exact List.map_congr_left fun i _ => by rw [Function.comp_apply]; congr 1; omega

/-- The chain the GCM keystream uses (`ICB = inc₃₂(J₀) = 2` at the zero IV): the
message counter blocks are the numerals `[2, 3, …, n + 1]` whenever `n + 1` fits
below the 32-bit field maximum. -/
theorem counterChain_two (n : ℕ) (h : n + 1 ≤ 2 ^ 32 - 1) :
    counterChain (2 : BitVec 128) n =
      (List.range n).map (fun i => BitVec.ofNat 128 (2 + i)) := by
  have h2 : (2 : BitVec 128) = BitVec.ofNat 128 2 := rfl
  rw [h2, counterChain_ofNat 2 n (by omega)]

/-! ## Pairwise distinctness of the cipher inputs -/

/-- `ValidMsgLength` keeps the block count `n = ⌈L/128⌉` and its successor inside the counter
field: `2³⁹ - 256 = 128 · (2³² - 2)`, so `n ≤ 2³² - 2`. -/
theorem blockCount_add_one_le {L : ℕ} (hL : ValidMsgLength L) :
    (L + 127) / 128 + 1 ≤ 2 ^ 32 - 1 := by
  have h := hL.1
  omega

/-- The full cipher-input list of one GCM call at the zero IV in numeral form:
`H = CIPH_K(0)`, tag mask `CIPH_K(1)` and keystream blocks `CIPH_K(2), …, CIPH_K(n + 1)`,
i.e. `{0, 1, …, n + 1}` as `BitVec 128` numerals. -/
theorem cipherInputs_eq (n : ℕ) (h : n + 1 ≤ 2 ^ 32 - 1) :
    0 :: 1 :: counterChain (2 : BitVec 128) n =
      (List.range (n + 2)).map (fun i => BitVec.ofNat 128 i) := by
  rw [counterChain_two n h, List.range_succ_eq_map, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.cons.injEq]
  refine ⟨rfl, rfl, ?_⟩
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply]
    congr 1
    omega

/-- The `n + 2` cipher inputs `{0, 1, …, n + 1}` of one GCM call (`n = ⌈L / 128⌉`) are
pairwise distinct in `BitVec 128`; the counter bound comes from `ValidMsgLength`, of which
only the `L ≤ 2 ^ 39 - 256` conjunct is used. Answering these queries with independent
uniforms on the ideal side of the PRF hop is valid because they never collide. -/
theorem cipherInputs_nodup {L : ℕ} (hL : ValidMsgLength L) :
    ((List.range ((L + 127) / 128 + 2)).map (fun i => BitVec.ofNat 128 i)).Nodup := by
  have hn := blockCount_add_one_le hL
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij
  rw [List.mem_range] at hi hj
  have h128 : i % 2 ^ 128 = j % 2 ^ 128 := by
    simpa only [BitVec.toNat_ofNat] using congrArg BitVec.toNat hij
  omega

/-- Distinctness in the shape downstream consumers take the list: the concrete
cipher-input list `0 :: 1 :: counterChain 2 n` is `Pairwise (· ≠ ·)`, from
`ValidMsgLength L` alone. -/
theorem cipherInputs_pairwise_ne {L : ℕ} (hL : ValidMsgLength L) :
    (0 :: 1 :: counterChain (2 : BitVec 128) ((L + 127) / 128)).Pairwise (· ≠ ·) := by
  rw [cipherInputs_eq _ (blockCount_add_one_le hL)]
  exact cipherInputs_nodup hL

theorem counterChain_length (icb : BitVec 128) (m : ℕ) :
    (counterChain icb m).length = m := by
  induction m generalizing icb with
  | zero => rfl
  | succ n ih => simp [counterChain, ih]

end GCM
