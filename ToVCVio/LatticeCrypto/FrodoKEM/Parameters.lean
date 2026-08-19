/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic

/-!
# FrodoKEM Parameters

The cryptographic parameters of FrodoKEM, following Tables 1 and 2 of
[FrodoKEM](https://frodokem.org/).

The development stays generic over the parameters while exposing the six named
parameter sets. Only `n`, `D`, `B` and the variant are stored; every other
published quantity is derived from them — the modulus `q = 2 ^ D`, the length
`ℓ = B * mbar * nbar` shared by `μ`, `s`, `k`, `pkh` and `ss`, and the
variant-dependent lengths `lenSeedSE` and `lenSalt` of Table 2.

Lengths are published in bits but the corresponding types are byte vectors, so
each length comes in both units and the docstrings name which is which.

The tables themselves are checked in `ToVCVio.LatticeCrypto.FrodoKEM.Smoke`.
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
  | eFrodoKEM640
  | eFrodoKEM976
  | eFrodoKEM1344
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
  /-- The frodoKEM variants: salted, ephemeral -/
  variant : Variant
deriving Repr, DecidableEq

namespace Params

/-- Power of 2 modulus with D ≤ 16 -/
def q (p : Params) : ℕ := 2 ^ (p.D)

/-- The length of bit strings to be encoded in an mbar-by-nbar matrix -/
def ellBits (p : Params) : ℕ := p.B * mbar * nbar

/-- `ellBits` expressed in bytes. -/
def ellBytes (p : Params) : ℕ := p.B * 8

/-- `ellBits` is eight times `ellBytes`. -/
theorem ellBits_eq_eight_ellBytes (p : Params) :
    p.ellBits = 8 * p.ellBytes := by
      simp [ellBits, ellBytes, mbar, nbar]
      omega

/-- The bit length of seeds used for pseudorandom bit generation for error
sampling -/
def lenSeedSE (p : Params) : ℕ := match p.variant with
  | .FrodoKEM => 2 * p.ellBits
  | .eFrodoKEM => p.ellBits

/-- The bit length of salt -/
def lenSalt (p : Params) : ℕ := match p.variant with
  | .FrodoKEM => 2 * p.ellBits
  | .eFrodoKEM => 0

/-- The length of seeds expressed in bytes -/
def lenSeedSEBytes (p : Params) : ℕ := match p.variant with
  | .FrodoKEM => 2 * p.ellBytes
  | .eFrodoKEM => p.ellBytes

/-- The length of salt expressed in bytes -/
def lenSaltBytes (p : Params) : ℕ := match p.variant with
  | .FrodoKEM => 2 * p.ellBytes
  | .eFrodoKEM => 0

/-- The conditions of Section 3 that a FrodoKEM parameter record must satisfy.
They are recorded here rather than as fields of `Params` so that the record
stays plain data, and are discharged for the named parameter sets in
`ToVCVio.LatticeCrypto.FrodoKEM.Smoke`. -/
structure WellFormed (p : Params) : Prop where
  /-- The lattice dimension is a multiple of eight. -/
  n_mod_eight : p.n % 8 = 0
  /-- The modulus exponent is at most sixteen. -/
  D_le : p.D ≤ 16
  /-- At most `D` bits are encoded in each matrix entry, so that `2 ^ B ≤ q`. -/
  B_le_D : p.B ≤ p.D

end Params

/-- Seeds used for pseudorandom bit generation for error sampling, of
`lenSeedSE` bits, represented as `lenSeedSEBytes` bytes. -/
abbrev SeedSE (p : Params) := Bytes p.lenSeedSEBytes

/-- Matrices over `ZMod q`. FrodoKEM has no polynomial ring: all of its
arithmetic happens in plain matrices over the integers mod `q`. -/
abbrev FrodoMatrix (p : Params) (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) (ZMod p.q)

/-- The message space `M = {0,1}^lenMu` with `lenMu = ℓ`, represented as
`ellBytes` bytes. -/
abbrev Message (p : Params) := Bytes p.ellBytes

/-- Shared secrets `ss`, of `lenSS = ℓ` bits, represented as `ellBytes` bytes. -/
abbrev SharedSecret (p : Params) := Bytes p.ellBytes

/-- The hash `G₁(pk)` of the public key, of `lenPkh = ℓ` bits, represented as
`ellBytes` bytes. -/
abbrev PublicKeyHash (p : Params) := Bytes p.ellBytes

/-- Salts, of `lenSalt` bits, represented as `lenSaltBytes` bytes; empty for
the ephemeral variant. -/
abbrev Salt (p : Params) := Bytes p.lenSaltBytes

namespace ParameterSet

/-- Table 1 cryptographic parameters for FrodoKEM-640, FrodoKEM-976, FrodoKEM-1344 and
  the ephemeral versions. The rest of the parameters in Table 1 are not included because
  they can be computed from n, D, B -/
def params : ParameterSet → Params
  | .FrodoKEM640 => {n := 640, D := 15, B := 2, variant := .FrodoKEM}
  | .FrodoKEM976 => {n := 976, D := 16, B := 3, variant := .FrodoKEM}
  | .FrodoKEM1344 => {n := 1344, D := 16, B := 4, variant := .FrodoKEM}
  | .eFrodoKEM640 => {n := 640, D := 15, B := 2, variant := .eFrodoKEM}
  | .eFrodoKEM976 => {n := 976, D := 16, B := 3, variant := .eFrodoKEM}
  | .eFrodoKEM1344 => {n := 1344, D := 16, B := 4, variant := .eFrodoKEM}

end ParameterSet

end FrodoKEM

