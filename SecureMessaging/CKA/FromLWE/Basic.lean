/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

/-!
# Basic types for continuous key agreement from LWE

The four matrix shapes follow the direct LWE construction in Alwen, Coretti, and Dodis,
*The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol*,
Section 4.1.2. All party names in this namespace are the paper's names: B sends first.
-/

namespace lweCKA

/-- Numerical parameters for the direct LWE construction. -/
structure Params where
  /-- The large square matrix dimension. -/
  n : ℕ
  /-- The smaller shared-secret matrix dimension. -/
  nbar : ℕ
  /-- The exponent `D` in the modulus `q = 2 ^ D`. -/
  logQ : ℕ
  /-- The number `B` of extracted key bits per shared-matrix entry. -/
  keyBits : ℕ

/-- Admissibility conditions for the source interpretation of the construction. -/
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

/-- The width of one extraction block. -/
def Params.blockWidth (p : Params) : ℕ :=
  2 ^ p.discardBits

/-- Half an extraction block, used for rounding and hints. -/
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

/-- Initial material shared between paper parties A and B. -/
structure InitKey (p : Params) where
  /-- Uniform public base matrix. -/
  base : Base p
  /-- Initial secret matrix sampled from `χ`. -/
  secret : Right p
  /-- Initial error matrix sampled from `χ`. -/
  error : Right p

/-- Fresh matrices sampled for one send by paper party B. -/
structure SendBCoins (p : Params) where
  /-- Fresh left-oriented secret matrix. -/
  secret : Left p
  /-- Fresh error for the public matrix. -/
  error : Left p
  /-- Fresh extra error for the shared matrix. -/
  extra : Shared p

/-- Fresh matrices sampled for one send by paper party A. -/
structure SendACoins (p : Params) where
  /-- Fresh right-oriented secret matrix. -/
  secret : Right p
  /-- Fresh error for the public matrix. -/
  error : Right p
  /-- Fresh extra error for the shared matrix. -/
  extra : Shared p

/-- The actual matrix values sampled by a randomness-leaking send. -/
inductive Rand (p : Params) where
  | fromB : SendBCoins p → Rand p
  | fromA : SendACoins p → Rand p

/-- Phase-tagged local state for the two paper parties. -/
inductive State (p : Params) where
  /-- B retains the base and current right-oriented public matrix, ready to send. -/
  | bSend : Base p → Right p → State p
  /-- B retains the base and its left-oriented secret, ready to receive from A. -/
  | bRecv : Base p → Left p → State p
  /-- A retains the base and current left-oriented public matrix, ready to send. -/
  | aSend : Base p → Left p → State p
  /-- A retains the base and its right-oriented secret, ready to receive from B. -/
  | aRecv : Base p → Right p → State p

/-- A directional public matrix together with its reconciliation hint. -/
inductive Message (p : Params) where
  | fromB : Left p → Hint p → Message p
  | fromA : Right p → Hint p → Message p

/-- A power of two is nonzero, so every construction modulus is a valid `ZMod` modulus. -/
instance instNeZeroModulus (p : Params) : NeZero p.q :=
  ⟨by simp [Params.q]⟩

end lweCKA
