/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.GhashAXU
import SecureMessaging.AEAD.FromGCM.Security.Polynomial
import ToVCVio.CryptoFoundations.AdjoinRootReflect
import ToVCVio.CryptoFoundations.RabinIrreducibility

/-!
# Irreducibility of GCM's field polynomial

`nistPoly = x¹²⁸ + x⁷ + x² + x + 1` is irreducible over `𝔽₂` (`nistPoly_irreducible`), so the
GHASH AXU bound holds with no hypotheses (`ghash_isAXU_unconditional`).

The proof is Rabin's test (`ToVCVio.irreducible_of_rabin_root`). At `q = 2`, `n = 128 = 2⁷` it
has two conditions, `2` being the only prime dividing `128`: `α^(2¹²⁸) = α` and
`α^(2⁶⁴) − α` is a unit, where `α` is the class of `x`. Both are computed with GCM's own
`gfmul` on `BitVec 128` and checked by `decide +kernel`, which reduces in the kernel and adds no
axiom (unlike `native_decide`); the results are then transported into `AdjoinRoot nistPoly`
through `reflectN`.
-/

open OracleComp OracleSpec ENNReal ToVCVio Polynomial ToVCVio.AdjoinRootReflect

namespace GCM

/-! ### The `BitVec 128` encoding constants -/

/-- `1` in GCM's bit order (most-significant bit is the coefficient of `x⁰`). -/
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

/-- Rabin condition 1: `α^(2¹²⁸) = α`. -/
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

/-- GCM's field polynomial is irreducible over `𝔽₂`: Rabin's test with the two kernel-checked
conditions transported through `reflectN`. Axioms: `propext`, `Classical.choice`, `Quot.sound`
only. -/
theorem nistPoly_irreducible : Irreducible nistPoly := by
  have hcard : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hpos : 0 < nistPoly.natDegree := by rw [nistPoly_natDegree]; omega
  refine ToVCVio.irreducible_of_rabin_root hpos ?_ (fun p hp hpn => ?_)
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

/-- `ghash_isAXU` with its irreducibility hypothesis discharged. -/
theorem ghash_isAXU_unconditional (L : ℕ) :
    GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ)) :=
  ghash_isAXU L nistPoly_irreducible

end GCM
