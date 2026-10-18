/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

/-!
# Basic types for continuous key agreement from LWE

The four matrix shapes follow the LWE construction in [ACD19, Section 4.1.2].
References are listed in `Construction.lean`.
Party names follow the repository interface. A sends first.
The paper swaps these labels.
A scalar is one number modulo the given modulus.
Extraction converts a scalar to shared-key bits.
A reconciliation hint helps the receiver recover those bits.
The sampler `χ` supplies the secret and error values.
-/

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
  n_pos : 0 < p.n
  nbar_pos : 0 < p.nbar
  keyBits_pos : 0 < p.keyBits
  keyBits_lt : p.keyBits + 1 < p.logQ

/-- The power-of-two LWE modulus. -/
def Params.q (p : Params) : ℕ :=
  2 ^ p.logQ

/-- The number of low bits discarded by extraction. -/
def Params.discardBits (p : Params) : ℕ :=
  p.logQ - p.keyBits

/-- The distance between successive rounding points when extracting key bits. -/
def Params.blockWidth (p : Params) : ℕ :=
  2 ^ p.discardBits

/-- For well-formed parameters, this value is half of `blockWidth`.
It gives the rounding offset and the width of each interval with a constant hint bit. -/
def Params.halfWidth (p : Params) : ℕ :=
  2 ^ (p.discardBits - 1)

/-- A scalar modulo the LWE modulus. -/
abbrev Scalar (p : Params) := ZMod p.q

/-- An extracted key scalar modulo `2 ^ keyBits`. -/
abbrev KeyScalar (p : Params) := ZMod (2 ^ p.keyBits)

/-- A one-bit reconciliation hint. -/
abbrev HintScalar := ZMod 2

/-- The paper's square public base matrix. -/
abbrev Base (p : Params) :=
  Matrix (Fin p.n) (Fin p.n) (Scalar p)

/-- An `n × nbar` matrix. -/
abbrev Right (p : Params) :=
  Matrix (Fin p.n) (Fin p.nbar) (Scalar p)

/-- An `nbar × n` matrix. -/
abbrev Left (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.n) (Scalar p)

/-- An `nbar × nbar` matrix over the scalar ring. -/
abbrev Shared (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.nbar) (Scalar p)

/-- An `nbar × nbar` matrix of extracted key scalars. -/
abbrev Key (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.nbar) (KeyScalar p)

/-- An `nbar × nbar` matrix of reconciliation hints. -/
abbrev Hint (p : Params) :=
  Matrix (Fin p.nbar) (Fin p.nbar) HintScalar

/-- Initial material shared between parties A and B. -/
structure InitKey (p : Params) where
  /-- Uniform public base matrix. -/
  base : Base p
  /-- Initial secret matrix sampled from `χ`. -/
  secret : Right p
  /-- Initial error matrix sampled from `χ`. -/
  error : Right p

/-- Fresh matrices sampled for a single send by party A. -/
structure SendACoins (p : Params) where
  /-- Fresh `nbar × n` secret matrix. -/
  secret : Left p
  /-- Fresh error for the public matrix. -/
  error : Left p
  /-- Fresh extra error for the shared matrix. -/
  extra : Shared p

/-- Fresh matrices sampled for a single send by party B. -/
structure SendBCoins (p : Params) where
  /-- Fresh `n × nbar` secret matrix. -/
  secret : Right p
  /-- Fresh error for the public matrix. -/
  error : Right p
  /-- Fresh extra error for the shared matrix. -/
  extra : Shared p

/-- The sampled matrices that a send returns as leaked randomness. -/
inductive Rand (p : Params) where
  | fromA : SendACoins p → Rand p
  | fromB : SendBCoins p → Rand p

/-- The local state of each party, with a tag that identifies whether it can send or receive. -/
inductive State (p : Params) where
  /-- A retains the public base and an `n × nbar` public matrix, ready to send. -/
  | aSend : Base p → Right p → State p
  /-- A retains the public base and its `nbar × n` secret matrix, ready to receive from B. -/
  | aRecv : Base p → Left p → State p
  /-- B retains the public base and an `nbar × n` public matrix, ready to send. -/
  | bSend : Base p → Left p → State p
  /-- B retains the public base and its `n × nbar` secret matrix, ready to receive from A. -/
  | bRecv : Base p → Right p → State p

/-- A public matrix together with its reconciliation hint. -/
inductive Message (p : Params) where
  | fromA : Left p → Hint p → Message p
  | fromB : Right p → Hint p → Message p

/-- The modulus `q = 2 ^ logQ` is nonzero for every parameter choice.
Lean uses this fact automatically when an operation requires a nonzero modulus. -/
instance instNeZeroModulus (p : Params) : NeZero p.q :=
  ⟨by simp [Params.q]⟩

end lweCKA
