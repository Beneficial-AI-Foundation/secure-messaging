/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Mathlib.Data.Nat.Notation

/-!
# FrodoKEM Parameters

The cryptographic parameters of FrodoKEM, following Tables 1 and 2 of
[FrodoKEM](https://frodokem.org/).

This file is under construction. It currently fixes the constants that are
shared by every parameter set, the record `Params` of the quantities that vary
between them, and the names of the parameter sets and variants. Still missing:
the derived lengths (`q`, the `ℓ`-family, `lenSeedSE`, `lenSalt`), the
parameter-dependent types, and the table of values itself.
-/

namespace FrodoKEM

/-- A byte, modeled as an unsigned 8-bit integer. -/
abbrev Byte := UInt8

/-- Fixed-length byte strings used throughout the FrodoKEM specification. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- Seeds used for pseudorandom matrix generation, of `lenSeedA` bits. -/
abbrev SeedA := Bytes 16

/-- The named FrodoKEM parameter sets (Table 1). -/
inductive ParameterSet where
  | FrodoKEM640
  | FrodoKEM976
  | FrodoKEM1344
deriving Repr, DecidableEq

/-- The two FrodoKEM variants: the salted `FrodoKEM` and the ephemeral
`eFrodoKEM`, which differ in the lengths of Table 2. -/
inductive Variant where
  | FrodoKEM
  | eFrodoKEM
deriving Repr, DecidableEq

/-- Bit length of the seeds used for pseudorandom matrix generation. -/
def lenSeedA : ℕ := 128

/-- Bit length of the seeds used for pseudorandom generation of `seedA`. -/
def lenZ : ℕ := 128

/-- Precision parameter of the error-distribution table `Tχ`, whose entries satisfy
`Tχ 0 = 2 ^ (lenChi - 1) * χ 0 - 1` (Section 3.1). -/
def lenChi : ℕ := 16

/-- Integer matrix dimension. Together with `mbar` it fixes the shape of encoded
messages: bit strings of length `B * mbar * nbar` are encoded as `mbar`-by-`nbar`
matrices. -/
def nbar : ℕ := 8

/-- Integer matrix dimension; see `nbar`. -/
def mbar : ℕ := 8

/-- The quantities that vary between the FrodoKEM parameter sets (Table 1). -/
structure Params where
  /-- Integer matrix dimension, satisfying `n ≡ 0 (mod 8)`. -/
  n : ℕ
  /-- Exponent of the power-of-two modulus `q = 2 ^ D`, satisfying `D ≤ 16`. -/
  D : ℕ
  /-- The number of bits encoded in each matrix entry, satisfying `B ≤ D`. -/
  B : ℕ
deriving Repr, DecidableEq

end FrodoKEM
