/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec
import SecureMessaging.PRP.Defs

/-!
# GCM authenticated encryption (NIST SP 800-38D §6–§7)

The NIST GCM mode of operation, in two parts:

- **Mathematical components (§6)** — the cipher-agnostic building blocks:
  `gfmul` (GF(2^128) multiplication `X • Y`, §6.3 Algorithm 1), `ghash` (the keyed
  hash `GHASH_H`, §6.4 Algorithm 2), `padBlocks` (reblocking for GHASH, §5.2/§7.1),
  and `inc₃₂` / `gctr` (counter increment §6.2 and CTR mode §6.5 Algorithm 3);
- **GCM specification (§7)** — the assembly of those components with a block cipher
  into GCM encryption (`gcmEncrypt`, §7.1 Algorithm 4) and decryption (`gcmDecrypt`,
  §7.2 Algorithm 5).

`gcmOneTimeAEAD` (`AEAD.FromGCM.Construction`) packages these as an `AEADScheme`.

## Scope

The IV is 96 bits only (`J₀ = IV ‖ 0³¹ ‖ 1`, NIST §5.2.1.1's recommended length, the
one HPKE/RFC 9180 fixes); the GHASH-derived `J₀` path for other IV lengths is out of
scope. Message and AAD lengths stay generic, with `ValidMsgLength`/`ValidAADLength`
capturing NIST's §5.2.1.1 supported range.

## Bit ordering

NIST indexes a block `S = S₀ … S₁₂₇` most-significant-first, so `Sᵢ = S.getMsbD i`,
`LSB₁(S) = S.getLsbD 0`, `S ≫ 1 = S >>> 1`, and `R = 0xE1 <<< 120`.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007. https://csrc.nist.gov/pubs/sp/800/38/d/final
-/

namespace GCM

/-! ## Mathematical components (NIST SP 800-38D §6) -/

/-! ### GF(2^128) multiplication (NIST SP 800-38D §6.3) -/

/-- The GCM reduction constant `R = 0xE1 <<< 120` (NIST SP 800-38D §6.3), XORed in
by `gfmul` after each right shift. -/
def gcmReductionConst : BitVec 128 := (0xE1 : BitVec 128) <<< 120

/-- GF(2^128) block multiplication `X • Y` (NIST SP 800-38D §6.3, Algorithm 1).
`Z₀ = 0`, `V₀ = Y`; for `i = 0 … 127`: `Zᵢ₊₁ = Zᵢ ⊕ Vᵢ` if `Xᵢ` else `Zᵢ`,
`Vᵢ₊₁ = (Vᵢ ≫ 1) ⊕ R` if `LSB₁(Vᵢ)` else `Vᵢ ≫ 1`; returns `Z₁₂₈`. The `⊕ R`
reduces mod `x^128 + x^7 + x^2 + x + 1`. -/
def gfmul (x y : BitVec 128) : BitVec 128 :=
  (List.range 128 |>.foldl
    (fun (p : BitVec 128 × BitVec 128) (i : ℕ) =>
      let z := if x.getMsbD i then p.1 ^^^ p.2 else p.1
      let v := if p.2.getLsbD 0 then (p.2 >>> 1) ^^^ gcmReductionConst else p.2 >>> 1
      (z, v))
    ((0 : BitVec 128), y)).1

/-! ### GHASH (NIST SP 800-38D §6.4) -/

/-- `GHASH_H(X₁ ‖ … ‖ Xₘ)` (NIST SP 800-38D §6.4, Algorithm 2): fold
`Y ↦ (Y ⊕ Xᵢ) • H` from `Y = 0` over whole blocks (the caller zero-pads any final
partial block via `padBlocks`). -/
def ghash (h : BitVec 128) (blocks : List (BitVec 128)) : BitVec 128 :=
  blocks.foldl (fun y x => gfmul (y ^^^ x) h) 0

/-! ### Bit-string blocking for GHASH (NIST SP 800-38D §5.2, §7.1)

An `n`-bit string is modelled as `BitVec n`, bits indexed most-significant-first via
`getMsbD` (reads past the end return `false`), which supplies NIST's zero-padding of
a final partial block for free.
-/

/-- The `i`-th 128-bit block of `x` (0-indexed, most-significant block first), bits
past `len(x)` read as `0`, giving NIST's right zero-padding of the final partial block. -/
def paddedBlock {n : ℕ} (x : BitVec n) (i : ℕ) : BitVec 128 :=
  (BitVec.ofBoolListBE ((List.range 128).map fun t => x.getMsbD (128 * i + t))).cast (by simp)

/-- `x` split into `⌈len(x)/128⌉` blocks, final partial block zero-padded
(NIST SP 800-38D §7.1 steps 4–5, `A ‖ 0^v` and `C ‖ 0^u`). -/
def padBlocks {n : ℕ} (x : BitVec n) : List (BitVec 128) :=
  (List.range ((n + 127) / 128)).map (paddedBlock x)

/-! ### `inc₃₂` and GCTR (NIST SP 800-38D §6.2, §6.5) -/

/-- `inc₃₂` (NIST SP 800-38D §6.2): low 32-bit counter field `+1 mod 2^32`, high 96
bits fixed. -/
def inc32 (x : BitVec 128) : BitVec 128 :=
  x.extractLsb' 32 96 ++ (x.extractLsb' 0 32 + 1)

/-- The GCTR keystream truncated to `p` bits: `MSB_p(blocks[0] ‖ blocks[1] ‖ …)`,
bit `j` is bit `j % 128` of `blocks[j / 128]` (NIST SP 800-38D §6.5). -/
private def keystream (blocks : List (BitVec 128)) (p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE
    ((List.range p).map fun j => (blocks.getD (j / 128) 0).getMsbD (j % 128))).cast (by simp)

/-- The counter chain `[ICB, inc₃₂(ICB), …, inc₃₂ⁿ⁻¹(ICB)]` (`n` blocks), built
incrementally, one `inc₃₂` step per block (NIST SP 800-38D §6.5, `CBᵢ₊₁ = inc₃₂(CBᵢ)`). -/
def counterChain (icb : BitVec 128) : ℕ → List (BitVec 128)
  | 0 => []
  | n + 1 => icb :: counterChain (inc32 icb) n

/-- GCTR (NIST SP 800-38D §6.5, Algorithm 3, `GCTR_K`):
`Y = X ⊕ MSB_{len(X)}(CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …)`, counter chain
`CBᵢ = inc₃₂ⁱ⁻¹(ICB)` (`counterChain`, one cipher call per block). GCM supplies
`ICB = inc₃₂(J₀)`. The keystream is independent of `X`, so `gctr` is an involution
(`gctr_involution`). -/
def gctr {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K) (icb : BitVec 128)
    {p : ℕ} (x : BitVec p) : BitVec p :=
  x ^^^ keystream ((counterChain icb ((p + 127) / 128)).map (ciph k)) p

/-- `gctr ciph k icb` is an involution (`(x ⊕ ks) ⊕ ks = x`). -/
theorem gctr_involution {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) {p : ℕ} (x : BitVec p) :
    gctr ciph k icb (gctr ciph k icb x) = x := by
  simp only [gctr, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-! ## GCM specification (NIST SP 800-38D §7) -/

/-! ### Supported input lengths (NIST SP 800-38D §5.2.1.1) -/

/-- Supported plaintext/ciphertext bit-length (NIST SP 800-38D §5.2.1.1):
`≤ 2^39 - 256` and a multiple of 8 (byte-aligned). -/
-- ANCHOR: ValidMsgLength
@[reducible] def ValidMsgLength (lenC : ℕ) : Prop := lenC ≤ 2 ^ 39 - 256 ∧ 8 ∣ lenC
-- ANCHOR_END: ValidMsgLength

/-- Supported AAD bit-length (NIST SP 800-38D §5.2.1.1): `≤ 2^64 - 1` and a multiple
of 8 (byte-aligned). -/
-- ANCHOR: ValidAADLength
@[reducible] def ValidAADLength (lenA : ℕ) : Prop := lenA ≤ 2 ^ 64 - 1 ∧ 8 ∣ lenA
-- ANCHOR_END: ValidAADLength

/-- Variable-length byte-string AAD of supported length (`ValidAADLength`);
`gcmOneTimeAEAD`'s associated-data type. -/
-- ANCHOR: SupportedAAD
abbrev SupportedAAD := { x : (a : ℕ) × BitVec a // ValidAADLength x.1 }
-- ANCHOR_END: SupportedAAD

/-! ### The GCM algorithms (NIST SP 800-38D §7) -/

/-- `CIPH K` (NIST SP 800-38D §5.1): the 128-bit block cipher GCM is built over. Only
the forward direction `ciph.perm k = CIPH_K` is used. -/
abbrev CIPH (K : Type) := BlockCipher K (BitVec 128)

/-- GCM authenticated encryption `GCM-AE_K(IV, P, A)` (NIST SP 800-38D §7.1,
Algorithm 4): AAD `ad : BitVec lenA`, plaintext `m : BitVec lenP`, ciphertext
`BitVec lenP` (GCTR preserves length), 96-bit `iv`, forward cipher `ciph.perm k = CIPH_K`.
Length-generic like NIST Algorithm 4 (no length check; the `[len(A)]₆₄ ‖ [len(C)]₆₄`
block wraps mod 2⁶⁴ outside `ValidMsgLength`/`ValidAADLength`).
- (1) `H = E_K(0)`; (2) `J₀ = IV ‖ 0³¹ ‖ 1`; (3) `C = GCTR_K(inc₃₂(J₀), P)`;
- (4–5) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)` (padding via `padBlocks`);
- (6) `T = GCTR_K(J₀, S)` (one block, so `MSB₁₂₈` is the identity); (7) output `(C, T)`. -/
def gcmEncrypt {K : Type} (ciph : CIPH K) (k : K)
    (iv : BitVec 96) {lenA lenP : ℕ} (ad : BitVec lenA) (m : BitVec lenP) :
    BitVec lenP × BitVec 128 :=
  let h := ciph.perm k 0
  let j₀ := iv ++ (0 : BitVec 31) ++ (1 : BitVec 1)
  let c := gctr ciph.perm k (inc32 j₀) m
  -- trailing GHASH block `[len(A)]₆₄ ‖ [len(C)]₆₄` (NIST SP 800-38D §7.1 step 5)
  let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP])
  -- (6) `T = GCTR_K(J₀, S)` (NIST SP 800-38D §7.1 step 6); one block, so no truncation
  let t := gctr ciph.perm k j₀ s
  (c, t)

/-- GCM authenticated decryption `GCM-AD_K(IV, C, A, T)` (NIST SP 800-38D §7.2,
Algorithm 5); `none` is NIST's `FAIL`, `some P` the recovered plaintext.
- (1) FAIL if lengths are unsupported (`ValidMsgLength lenP ∧ ValidAADLength lenA`;
  the IV/tag widths are fixed by the `BitVec 96`/`BitVec 128` types);
- (2) `H = E_K(0)`; (3) `J₀ = IV ‖ 0³¹ ‖ 1`; (4) `P = GCTR_K(inc₃₂(J₀), C)`;
- (5–6) `S` as in `gcmEncrypt`; (7) `T' = GCTR_K(J₀, S)`;
- (8) return `P` if `T = T'`, else FAIL. -/
def gcmDecrypt {K : Type} (ciph : CIPH K) (k : K)
    (iv : BitVec 96) {lenA lenP : ℕ} (ad : BitVec lenA) (ct : BitVec lenP × BitVec 128) :
    Option (BitVec lenP) :=
  -- (1) FAIL immediately on unsupported input lengths, before any GHASH work
  if ValidMsgLength lenP ∧ ValidAADLength lenA then
    let (c, t) := ct
    let h := ciph.perm k 0                          -- (2)
    let j₀ := iv ++ (0 : BitVec 31) ++ (1 : BitVec 1) -- (3)
    let p := gctr ciph.perm k (inc32 j₀) c          -- (4)
    -- (5–6) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)`
    let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP])
    -- (7–8) recompute `T'` and return `P` on a match, else FAIL
    if t = gctr ciph.perm k j₀ s then some p else none
  else none

end GCM
