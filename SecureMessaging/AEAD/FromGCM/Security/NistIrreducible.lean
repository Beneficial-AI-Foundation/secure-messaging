/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.GhashAXU
import SecureMessaging.AEAD.FromGCM.Security.GhashPolynomial
import ToVCVio.CryptoFoundations.AdjoinRootReflect
import ToVCVio.CryptoFoundations.RabinIrreducibility


open OracleComp OracleSpec ENNReal ToVCVio Polynomial ToVCVio.AdjoinRootReflect

namespace GCM

/-! ### The `BitVec 128` encoding constants -/

/-- `1` in GCM's bit order, where the most-significant bit is the coefficient of `x⁰`. -/
def one128 : BitVec 128 := (1 : BitVec 128) <<< 127

/-- `x` in GCM's bit order. -/
def alpha : BitVec 128 := (1 : BitVec 128) <<< 126

/-- An offline-computed inverse of `α^(2⁶⁴) + α` in `𝔽₂[x]/(nistPoly)`. The literal is not
trusted: `kernel_rabin2` checks it, so a wrong value fails to compile rather than proving
something false. -/
def gammaInv : BitVec 128 := 0x180da934bf53158251c13dbb149f5279

/-- `sqIter n x = x^(2ⁿ)`, by `n`-fold `gfmul`-squaring. -/
def sqIter : ℕ → BitVec 128 → BitVec 128
  | 0,     x => x
  | n + 1, x => sqIter n (gfmul x x)

/-! ### The kernel certificate -/

/-- Rabin's first condition, `α^(2¹²⁸) = α`, computed on `BitVec 128`. `nistPoly_irreducible`
transports it to `root nistPoly ^ (2 ^ 128) = root nistPoly` via `reflectN_sqIter` and
`reflectN_alpha`. -/
theorem kernel_rabin1 : sqIter 128 alpha = alpha := by decide +kernel

/-- Rabin condition 2: `α^(2⁶⁴) + α` is a unit, witnessed by `gammaInv`. The weaker
`sqIter 64 alpha ≠ alpha` would not do: in a ring not yet known to be a domain, being nonzero
does not give coprimality. -/
theorem kernel_rabin2 : gfmul ((sqIter 64 alpha) ^^^ alpha) gammaInv = one128 := by
  decide +kernel

/-! ### The `BitVec 128` ↔ `AdjoinRoot nistPoly` bridge -/

theorem reflectN_one : reflectN one128 = 1 := by
  have h : ∀ i : Fin 128, boolToZMod2 (one128.getMsbD i) = if i = 0 then 1 else 0 := by decide
  rw [reflectN_apply]; simp [h, Finset.sum_ite_eq']

theorem reflectN_alpha : reflectN alpha = AdjoinRoot.root nistPoly := by
  have h : ∀ i : Fin 128, boolToZMod2 (alpha.getMsbD i) = if i = 1 then 1 else 0 := by decide
  rw [reflectN_apply]; simp [h, Finset.sum_ite_eq']

theorem reflectN_sqIter (n : ℕ) (x : BitVec 128) :
    reflectN (sqIter n x) = reflectN x ^ (2 ^ n) := by
  induction n generalizing x with
  | zero => simp [sqIter]
  | succ n ih =>
      have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [sqIter, ih, reflect_gfmul, h2, pow_mul, pow_two]

/-! ### Assembly -/

/-- The NIST GCM pentanomial `x¹²⁸ + x⁷ + x² + x + 1` is irreducible over `𝔽₂`.

This is an arithmetic fact about a fixed polynomial, not one of the cryptographic assumptions the
project admits unproved (the PRF/PRP security of a block cipher is such an assumption; this is
not). It therefore may not enter the development as an `axiom`, as a `sorry`, or through
`native_decide`, and it does not: see the axiom report below.

Mathlib at this toolchain has no irreducibility decision procedure that reaches degree `128` over
`GF(2)`, and no polynomial factorisation algorithm at all (`grep -rn "Rabin" Mathlib/` returns
nothing), so the test is built here.

The route is Rabin's irreducibility test at `q = 2`, `n = 128 = 2⁷`. Since `2` is the only prime
dividing `128`, the test has exactly two conditions: the `128`-fold Frobenius fixes the root
(`kernel_rabin1`), and `α^(2⁶⁴) − α` is a unit in the quotient (`kernel_rabin2`, as a Bézout
witness). Both are checked by `decide +kernel`, which asks the Lean kernel to reduce the decidable
proposition and adds no axiom; `native_decide` would instead mint a generated
`_native.<tacticName>.ax` auxiliary axiom, which would be visible in the axiom report. The
certificates report exactly `[propext, Quot.sound]`, and this theorem reports exactly
`[propext, Classical.choice, Quot.sound]`.

The soundness layer is `ToVCVio.irreducible_of_rabin_root`, cryptography-free and generic over any
finite field. Its forward half is Mathlib's own
`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`
(`Mathlib/FieldTheory/Finite/Extension.lean:161`); only the converse had to be supplied.

The transport from `BitVec 128` arithmetic into `AdjoinRoot nistPoly` is `reflectN`, via
`reflectN_alpha`, `reflectN_sqIter` and `reflect_gfmul`. The characteristic-2 collapse of the
subtraction is `adjoinRoot_neg_eq_self` (`Security/GhashAXU.lean`). -/
theorem nistPoly_irreducible : Irreducible nistPoly := by
  have hcard : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  have hpos : 0 < nistPoly.natDegree := by rw [nistPoly_natDegree]; omega
  refine ToVCVio.irreducible_of_rabin_root nistPoly_monic hpos ?_ (fun p hp hpn => ?_)
  · rw [hcard, nistPoly_natDegree, ← reflectN_alpha, ← reflectN_sqIter, kernel_rabin1]
  · rw [nistPoly_natDegree] at hpn
    have hp2 : p = 2 := by
      have h27 : (128 : ℕ) = 2 ^ 7 := by norm_num
      rw [h27] at hpn
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpn)
    subst hp2
    have hdiv : (128 : ℕ) / 2 = 64 := by norm_num
    rw [hcard, nistPoly_natDegree, hdiv]
    have hb : reflectN ((sqIter 64 alpha) ^^^ alpha)
        = AdjoinRoot.root nistPoly ^ (2 ^ 64 : ℕ) - AdjoinRoot.root nistPoly := by
      rw [reflectN_xor, reflectN_sqIter, reflectN_alpha, sub_eq_add_neg, adjoinRoot_neg_eq_self]
    exact ⟨⟨_, reflectN gammaInv,
      by rw [← hb, ← reflect_gfmul, kernel_rabin2, reflectN_one],
      by rw [mul_comm, ← hb, ← reflect_gfmul, kernel_rabin2, reflectN_one]⟩, rfl⟩

/-! ### Unconditional GHASH almost-XOR-universality -/

theorem ghash_isAXU_unconditional (L : ℕ) :
    GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ)) :=
  ghash_isAXU L nistPoly_irreducible

end GCM
