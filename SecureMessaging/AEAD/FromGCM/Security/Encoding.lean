/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM

/-!
# GCM — GHASH encoding domain and injectivity

The block sequence `A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ [len(A)]₆₄ ‖ [len(C)]₆₄` that GCM feeds to its keyed
hash GHASH (`gcmEncode`), the bound `maxBlocks` on its length, and its injectivity on
`SupportedAAD × BitVec L`. The positional form `gcmEncode_tail_distinct` is what the GHASH
almost-XOR-universality bound (`GhashAXU.lean`) consumes.
-/

namespace GCM

/-! ## The GHASH encoding map -/

/-- The block sequence GCM feeds to GHASH, `A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ [len(A)]₆₄ ‖ [len(C)]₆₄`
(NIST SP 800-38D §7.1 steps 4–5), as a map on the AEAD domain. Definitionally equal to
`gcmEncrypt`'s GHASH argument. -/
def gcmEncode {L : ℕ} (ad : SupportedAAD) (c : BitVec L) : List (BitVec 128) :=
  padBlocks ad.1.2 ++ padBlocks c ++ [BitVec.ofNat 64 ad.1.1 ++ BitVec.ofNat 64 L]

/-! ## Block budget -/

/-- The largest AAD bit-length `ValidAADLength` admits (NIST SP 800-38D §5.2.1.1). -/
def lenAMax : ℕ := 2 ^ 64 - 8

/-- Upper bound on the block count of `gcmEncode ad c` for `c : BitVec L`, proved in
`gcmEncode_length_le`. It bounds the degree of the GHASH difference polynomial in
`GhashAXU.lean` and is the numerator of the AXU bound `maxBlocks L / 2¹²⁸`. -/
def maxBlocks (L : ℕ) : ℕ := (lenAMax + 127) / 128 + (L + 127) / 128 + 1

theorem lenAMax_blocks : (lenAMax + 127) / 128 = 2 ^ 57 := by
  simp [lenAMax]

@[simp] theorem length_padBlocks {n : ℕ} (x : BitVec n) :
    (padBlocks x).length = (n + 127) / 128 := by
  simp [padBlocks]

theorem le_lenAMax (ad : SupportedAAD) : ad.1.1 ≤ lenAMax := by
  have hle : ad.1.1 ≤ 2 ^ 64 - 1 := ad.2.1
  have hdvd : 8 ∣ ad.1.1 := ad.2.2
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  change ad.1.1 ≤ 2 ^ 64 - 8
  omega

theorem gcmEncode_length_le {L : ℕ} (ad : SupportedAAD) (c : BitVec L) :
    (gcmEncode ad c).length ≤ maxBlocks L := by
  have h : (ad.1.1 + 127) / 128 ≤ (lenAMax + 127) / 128 :=
    Nat.div_le_div_right (by have := le_lenAMax ad; omega)
  simp only [gcmEncode, maxBlocks, List.length_append, length_padBlocks,
    List.length_cons, List.length_nil]
  omega

/-! ## Injectivity helpers -/

theorem ofNat64_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have h' : a % 2 ^ 64 = b % 2 ^ 64 := by
    simpa using BitVec.toNat_inj.mpr h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- Bit `i` of `x` is bit `i % 128` of block `i / 128`, for all `i`: out-of-range reads are
`false` on both sides. -/
theorem getMsbD_paddedBlock {n : ℕ} (x : BitVec n) (i : ℕ) :
    (paddedBlock x (i / 128)).getMsbD (i % 128) = x.getMsbD i := by
  have hm : i % 128 < 128 := Nat.mod_lt _ (by omega)
  simp only [paddedBlock, BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm,
    Option.map_some, Option.getD_some]
  rw [Nat.div_add_mod]

theorem padBlocks_injective {n : ℕ} : Function.Injective (padBlocks (n := n)) := by
  intro x y h
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have hlen : i / 128 < (n + 127) / 128 := by omega
  have hblock : paddedBlock x (i / 128) = paddedBlock y (i / 128) := by
    have h' := congrArg (fun l => l[i / 128]?) h
    simpa [padBlocks, List.getElem?_range hlen] using h'
  rw [← getMsbD_paddedBlock x i, ← getMsbD_paddedBlock y i, hblock]

theorem lenBlock_ne_of_ne {L : ℕ} {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hab : a ≠ b) :
    BitVec.ofNat 64 a ++ BitVec.ofNat 64 L ≠ BitVec.ofNat 64 b ++ BitVec.ofNat 64 L :=
  fun h => hab (ofNat64_inj ha hb ((BitVec.append_left_inj _).mp h))

/-! ## Tail-aligned distinctness: the unequal-lenA case -/

theorem gcmEncode_reverse_getD_zero {L : ℕ} (ad : SupportedAAD) (c : BitVec L) :
    (gcmEncode ad c).reverse.getD 0 0 = BitVec.ofNat 64 ad.1.1 ++ BitVec.ofNat 64 L := by
  simp [gcmEncode]

theorem gcmEncode_getLast_ne_of_lenA_ne {L : ℕ} {ad ad' : SupportedAAD}
    (h : ad.1.1 ≠ ad'.1.1) (c c' : BitVec L) :
    (gcmEncode ad c).reverse.getD 0 0 ≠ (gcmEncode ad' c').reverse.getD 0 0 := by
  rw [gcmEncode_reverse_getD_zero, gcmEncode_reverse_getD_zero]
  exact lenBlock_ne_of_ne (by have := ad.2.1; omega) (by have := ad'.2.1; omega) h

/-! ## Equal-lenA case and the assembled theorems -/

theorem gcmEncode_length_eq_of_lenA_eq {L : ℕ} {ad ad' : SupportedAAD}
    (h : ad.1.1 = ad'.1.1) (c c' : BitVec L) :
    (gcmEncode ad c).length = (gcmEncode ad' c').length := by
  simp [gcmEncode, h]

theorem gcmEncode_ne_of_lenA_eq {L : ℕ} {ad ad' : SupportedAAD} {c c' : BitVec L}
    (hlen : ad.1.1 = ad'.1.1) (hne : (ad, c) ≠ (ad', c')) :
    gcmEncode ad c ≠ gcmEncode ad' c' := by
  obtain ⟨⟨a, x⟩, hx⟩ := ad
  obtain ⟨⟨a', x'⟩, hx'⟩ := ad'
  dsimp only at hlen
  subst hlen
  intro h
  simp only [gcmEncode] at h
  obtain ⟨h₁, -⟩ := List.append_inj h (by simp)
  obtain ⟨hA, hC⟩ := List.append_inj h₁ (by simp)
  obtain rfl := padBlocks_injective hA
  obtain rfl := padBlocks_injective hC
  exact hne rfl

theorem exists_getD_ne_of_ne {α : Type _} (d : α) {l₁ l₂ : List α}
    (hlen : l₁.length = l₂.length) (hne : l₁ ≠ l₂) :
    ∃ i, l₁.getD i d ≠ l₂.getD i d := by
  by_contra hc
  push Not at hc
  refine hne (List.ext_getElem hlen fun i h₁ h₂ => ?_)
  have h := hc i
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some, Option.getD_some] at h

/-- Distinct domain points give encodings that differ at some position of the *reversed* block
list. This is the shape `card_filter_le` in `GhashAXU.lean` consumes: since
`ghash h [X₁, …, Xₘ] = X₁·hᵐ ⊕ ⋯ ⊕ Xₘ·h`, reversed index `i` is the coefficient of `h^(i+1)`,
and a differing position is a differing coefficient of the difference polynomial. A front
index would not do: for encodings of different lengths, the blocks at one front index multiply
different powers of `h`. -/
theorem gcmEncode_tail_distinct {L : ℕ} {p q : SupportedAAD × BitVec L}
    (h : p ≠ q) :
    ∃ i, ((gcmEncode p.1 p.2).reverse).getD i 0 ≠ ((gcmEncode q.1 q.2).reverse).getD i 0 := by
  by_cases hlen : p.1.1.1 = q.1.1.1
  · have hne : gcmEncode p.1 p.2 ≠ gcmEncode q.1 q.2 := gcmEncode_ne_of_lenA_eq hlen h
    have hlens : ((gcmEncode p.1 p.2).reverse).length = ((gcmEncode q.1 q.2).reverse).length := by
      simpa using gcmEncode_length_eq_of_lenA_eq hlen p.2 q.2
    exact exists_getD_ne_of_ne 0 hlens fun hr => hne (List.reverse_injective hr)
  · exact ⟨0, gcmEncode_getLast_ne_of_lenA_ne hlen p.2 q.2⟩

/-- The padded encoding with trailing length block is unambiguous. The AXU proof uses the
positional form `gcmEncode_tail_distinct` rather than this. -/
theorem gcmEncode_injective {L : ℕ} :
    Function.Injective (fun p : SupportedAAD × BitVec L => gcmEncode p.1 p.2) := by
  intro p q h
  by_contra hne
  obtain ⟨i, hi⟩ := gcmEncode_tail_distinct hne
  exact hi (by simp only at h; rw [h])

end GCM
