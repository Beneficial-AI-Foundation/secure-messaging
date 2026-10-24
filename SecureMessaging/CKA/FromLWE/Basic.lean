/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

/-!
# Basic types for continuous key agreement from LWE

The four matrix shapes follow the LWE construction in [ACD19, Section 4.1.2].
References are listed in `Construction.lean`.
Party names follow the repository interface: A sends first
(the party labels are swapped relative to the paper).
-/

@[expose] public section

namespace lweCKA

/-- Numerical parameters for the LWE construction. -/
structure Params where
  /-- Dimension of the square public base matrix (`n × n`). -/
  n : ℕ
  /-- Dimension of the square shared matrices (`nbar × nbar`). -/
  nbar : ℕ
  /-- The exponent `D` in the modulus `q = 2 ^ D`. -/
  logQ : ℕ
  /-- Number of shared-key bits extracted per shared-matrix entry (the paper's `B`). -/
  keyBits : ℕ

/-- Parameter constraints for the LWE construction. -/
structure Params.WellFormed (p : Params) : Prop where
  /-- The public base matrix is nonempty. -/
  n_pos : 0 < p.n
  /-- The shared-key matrices are nonempty. -/
  nbar_pos : 0 < p.nbar
  /-- Each matrix entry contributes at least one key bit. -/
  keyBits_pos : 0 < p.keyBits
  /-- Bound on key bits per entry from [BCDMNNRS16, Section 3.2]: `B < log₂(q) - 1`. -/
  keyBits_lt : p.keyBits + 1 < p.logQ

/-- The power-of-two LWE modulus. -/
def Params.q (p : Params) : ℕ :=
  2 ^ p.logQ

/-- The number of low bits discarded by extraction. -/
def Params.discardBits (p : Params) : ℕ :=
  p.logQ - p.keyBits

/-- Spacing between consecutive rounding levels in key extraction. -/
def Params.blockWidth (p : Params) : ℕ :=
  2 ^ p.discardBits

/-- Half the extraction-block width for well-formed parameters, used as the rounding offset
and as the interval width for alternating hint bits. -/
def Params.halfWidth (p : Params) : ℕ :=
  2 ^ (p.discardBits - 1)

/-- A scalar modulo the LWE modulus. -/
abbrev Scalar (p : Params) := ZMod p.q

/-- An extracted key scalar modulo `2 ^ keyBits`. -/
abbrev KeyScalar (p : Params) := ZMod (2 ^ p.keyBits)

/-- A one-bit reconciliation hint. -/
abbrev HintScalar := ZMod 2

/-- The paper's square public base matrix. -/
abbrev BaseMatrix (p : Params) :=
  Matrix (Fin p.n) (Fin p.n) (Scalar p)

/-- An `n × nbar` matrix. -/
abbrev RightMatrix (p : Params) :=
  Matrix (Fin p.n) (Fin p.nbar) (Scalar p)

/-- An `nbar × n` matrix. -/
abbrev LeftMatrix (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.n) (Scalar p)

/-- An `nbar × nbar` matrix over the scalar ring. -/
abbrev SharedMatrix (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.nbar) (Scalar p)

/-- An `nbar × nbar` matrix of extracted key scalars. -/
abbrev Key (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.nbar) (KeyScalar p)

/-- An `nbar × nbar` matrix of reconciliation hints. -/
abbrev HintMatrix (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.nbar) HintScalar

/-- Initial material shared between parties A and B. -/
structure InitKey (p : Params) where
  /-- Uniform public base matrix. -/
  baseMatrix : BaseMatrix p
  /-- Initial secret matrix sampled from `χ`. -/
  secret : RightMatrix p
  /-- Initial error matrix sampled from `χ`. -/
  error : RightMatrix p

/-- Fresh matrices sampled for a single send by party A. -/
structure SendACoins (p : Params) where
  /-- Fresh `nbar × n` secret matrix. -/
  secret : LeftMatrix p
  /-- Fresh error for the public matrix. -/
  error : LeftMatrix p
  /-- Fresh extra error for the shared matrix. -/
  extra : SharedMatrix p

/-- Fresh matrices sampled for a single send by party B. -/
structure SendBCoins (p : Params) where
  /-- Fresh `n × nbar` secret matrix. -/
  secret : RightMatrix p
  /-- Fresh error for the public matrix. -/
  error : RightMatrix p
  /-- Fresh extra error for the shared matrix. -/
  extra : SharedMatrix p

/-- The actual matrix values sampled by a randomness-leaking send. -/
inductive Rand (p : Params) where
  | fromA : SendACoins p → Rand p
  | fromB : SendBCoins p → Rand p

/-- Phase-tagged local state for the two parties. -/
inductive State (p : Params) where
  /-- A retains the public base and an `n × nbar` public matrix, ready to send. -/
  | aSend : BaseMatrix p → RightMatrix p → State p
  /-- A retains the public base and its `nbar × n` secret matrix, ready to receive from B. -/
  | aRecv : BaseMatrix p → LeftMatrix p → State p
  /-- B retains the public base and an `nbar × n` public matrix, ready to send. -/
  | bSend : BaseMatrix p → LeftMatrix p → State p
  /-- B retains the public base and its `n × nbar` secret matrix, ready to receive from A. -/
  | bRecv : BaseMatrix p → RightMatrix p → State p

/-- A public matrix together with its reconciliation hint. -/
inductive Message (p : Params) where
  | fromA : LeftMatrix p → HintMatrix p → Message p
  | fromB : RightMatrix p → HintMatrix p → Message p

/-- The modulus `q = 2 ^ logQ` is nonzero for every parameter choice.
Register this fact for automatic use by operations requiring a nonzero modulus. -/
instance instNeZeroModulus (p : Params) : NeZero p.q :=
  ⟨by simp [Params.q]⟩

end lweCKA
