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

The cryptographic parameters of FrodoKEM, following Tables 1 and 2 of the
specification, published at [frodokem.org](https://frodokem.org/) and as
[Glabush, Longa, Naehrig, Peikert, Stebila and Virdia,
*FrodoKEM: A CCA-Secure Learning With Errors Key Encapsulation Mechanism*,
Communications in Cryptology 2:3](https://cic.iacr.org/p/2/3/25).

The published tables are recorded verbatim in `ParameterSet.params`. The relations
between the entries are stated as theorems. The quantities are:

* `n`, the lattice dimension, which is also the size of the public matrix `A`;
* `D`, the exponent of the modulus, and `q = 2 ^ D`, the modulus itself;
* `B`, the number of bits encoded in each matrix entry by `Frodo.Encode`;
* `ℓ = B * mbar * nbar`, the length of bit strings encoded as `mbar`-by-`nbar`
  matrices, and also the bit length of the message `μ`, the shared secret `ss`,
  the intermediate secret `k`, the public-key hash `pkh`, and the vector `s`
  from which `ss` is derived when decapsulation fails;
* `lenSeedSE`, the bit length of the seeds used for error sampling, and
  `lenSalt`, the bit length of the salt, which is zero for the ephemeral
  variant.

The constants `mbar = nbar = 8`, `lenSeedA = lenZ = 128` and `lenChi = 16` are
shared by every parameter set; the remaining entries are:

| parameter set   |  D |     q |    n | B |   ℓ | lenSeedSE | lenSalt |
| --------------- | --:| -----:| ----:| -:| ---:| ---------:| -------:|
| FrodoKEM-640    | 15 | 32768 |  640 | 2 | 128 |       256 |     256 |
| FrodoKEM-976    | 16 | 65536 |  976 | 3 | 192 |       384 |     384 |
| FrodoKEM-1344   | 16 | 65536 | 1344 | 4 | 256 |       512 |     512 |
| eFrodoKEM-640   | 15 | 32768 |  640 | 2 | 128 |       128 |       0 |
| eFrodoKEM-976   | 16 | 65536 |  976 | 3 | 192 |       192 |       0 |
| eFrodoKEM-1344  | 16 | 65536 | 1344 | 4 | 256 |       256 |       0 |

Lengths are published in bits but the corresponding types are byte vectors, so
each length comes in both units and the docstrings name which is which.

A `Params` is plain data, so nothing constrains its fields. `Params.WellFormed`
collects the conditions of Section 3 that the encoding and packing proofs
depend on, and `params_wellFormed` discharges them for every published set.
`ValidParams` pairs a record with that proof, for the definitions that need it
to typecheck rather than only to be proved correct.
-/

namespace FrodoKEM

/-- A byte, modeled as an unsigned 8-bit integer. -/
abbrev Byte := UInt8

/-- Fixed-length byte strings used throughout the FrodoKEM specification. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- Bit length of the seeds used for pseudorandom matrix generation. -/
def lenSeedA : ℕ := 128

/-- Seeds used for pseudorandom matrix generation, of `lenSeedA` bits. -/
abbrev SeedA := Bytes (lenSeedA / 8)

/-- The named FrodoKEM parameter sets of Tables 1 and 2, salted and ephemeral. -/
inductive ParameterSet where
  | FrodoKEM640
  | FrodoKEM976
  | FrodoKEM1344
  | eFrodoKEM640
  | eFrodoKEM976
  | eFrodoKEM1344
deriving Repr, DecidableEq

set_option linter.dupNamespace false in
/-- The two FrodoKEM variants: the salted `FrodoKEM` and the ephemeral
`eFrodoKEM`, which differ in the lengths of Table 2. -/
inductive Variant where
  | FrodoKEM
  | eFrodoKEM
deriving Repr, DecidableEq

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

/-- One field per column of Tables 1 and 2. The fields are independent data;
the relations between them are theorems about the six named parameter sets
rather than part of this record. -/
structure Params where
  /-- Exponent of the modulus; `Params.WellFormed.D_le` bounds it by sixteen. -/
  D : ℕ
  /-- The modulus; `Params.WellFormed.q_eq` identifies it with `2 ^ D`. -/
  q : ℕ
  /-- Integer matrix dimension; `Params.WellFormed.n_mod_eight` makes it a
  multiple of eight. -/
  n : ℕ
  /-- The number of bits encoded in each matrix entry;
  `Params.WellFormed.B_le_D` bounds it by `D`. -/
  B : ℕ
  /-- The length of bit strings encoded as `mbar`-by-`nbar` matrices;
  `Params.WellFormed.ell_eq` identifies it with `B * mbar * nbar`. -/
  ell : ℕ
  /-- The bit length of seeds used for pseudorandom bit generation for error
  sampling -/
  lenSeedSE : ℕ
  /-- The bit length of salt -/
  lenSalt : ℕ
  /-- The FrodoKEM variant: salted or ephemeral. -/
  variant : Variant
deriving Repr, DecidableEq

-- False positive: the precedence argument of `reprPrec` cannot be used by a
-- derived structure printer, whose `{ ... }` output never needs parentheses.
attribute [nolint unusedArguments] instReprParams.repr

namespace Params

/-- `ell` expressed in bytes. -/
def ellBytes (p : Params) : ℕ := p.ell / 8

/-- `lenSeedSE` expressed in bytes. -/
def lenSeedSEBytes (p : Params) : ℕ := p.lenSeedSE / 8

/-- `lenSalt` expressed in bytes. -/
def lenSaltBytes (p : Params) : ℕ := p.lenSalt / 8

/-- The conditions of Section 3 that a parameter record must satisfy. -/
structure WellFormed (p : Params) : Prop where
  /-- The lattice dimension is a multiple of eight. -/
  n_mod_eight : p.n % 8 = 0
  /-- The modulus exponent is at most sixteen. -/
  D_le : p.D ≤ 16
  /-- At most `D` bits are encoded in each matrix entry, so that `2 ^ B ≤ q`. -/
  B_le_D : p.B ≤ p.D
  /-- The modulus satisfies `q = 2 ^ D`. -/
  q_eq : p.q = 2 ^ p.D
  /-- A message fills the matrix: `ℓ = B * mbar * nbar`. -/
  ell_eq : p.ell = p.B * mbar * nbar

end Params

/-- A parameter record with its well-formedness proof. Definitions that need a
`Params.WellFormed` field in order to typecheck, `encodeMessage` and
`decodeMessage` for the length of a message, take one of these, so that a
caller passes one argument rather than a record and a proof about it. The
scalar maps, `Encode` and `Decode` need no hypothesis and stay on `Params`. -/
structure ValidParams extends Params where
  /-- The record satisfies the conditions of Section 3. -/
  wf : toParams.WellFormed

/-- Seeds used for error sampling, of `lenSeedSE` bits, represented as
`lenSeedSEBytes` bytes. -/
abbrev SeedSE (p : Params) := Bytes p.lenSeedSEBytes

/-- Matrices over `ZMod q`. FrodoKEM has no polynomial ring; all of its
arithmetic is plain matrix arithmetic. -/
abbrev FrodoMatrix (p : Params) (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) (ZMod p.q)

/-- The message space `M = {0,1}^lenMu` with `lenMu = ℓ`, represented as
`ellBytes` bytes. -/
abbrev Message (p : Params) := Bytes p.ellBytes

/-- Shared secrets `ss`, of `lenSS = ℓ` bits, represented as `ellBytes`
bytes. -/
abbrev SharedSecret (p : Params) := Bytes p.ellBytes

/-- The hash `G₁(pk)` of the public key, of `lenPkh = ℓ` bits, represented as
`ellBytes` bytes. -/
abbrev PublicKeyHash (p : Params) := Bytes p.ellBytes

/-- Salts, of `lenSalt` bits, represented as `lenSaltBytes` bytes; empty for
the ephemeral variant. -/
abbrev Salt (p : Params) := Bytes p.lenSaltBytes

namespace ParameterSet

/-- The published rows of Tables 1 and 2, recorded verbatim for comparison
against the specification. The relations between entries are the theorems
below. -/
def params : ParameterSet → Params
  | .FrodoKEM640 =>
      {D := 15, q := 32768, n := 640, B := 2, ell := 128,
       lenSeedSE := 256, lenSalt := 256, variant := .FrodoKEM}
  | .FrodoKEM976 =>
      {D := 16, q := 65536, n := 976, B := 3, ell := 192,
       lenSeedSE := 384, lenSalt := 384, variant := .FrodoKEM}
  | .FrodoKEM1344 =>
      {D := 16, q := 65536, n := 1344, B := 4, ell := 256,
       lenSeedSE := 512, lenSalt := 512, variant := .FrodoKEM}
  | .eFrodoKEM640 =>
      {D := 15, q := 32768, n := 640, B := 2, ell := 128,
       lenSeedSE := 128, lenSalt := 0, variant := .eFrodoKEM}
  | .eFrodoKEM976 =>
      {D := 16, q := 65536, n := 976, B := 3, ell := 192,
       lenSeedSE := 192, lenSalt := 0, variant := .eFrodoKEM}
  | .eFrodoKEM1344 =>
      {D := 16, q := 65536, n := 1344, B := 4, ell := 256,
       lenSeedSE := 256, lenSalt := 0, variant := .eFrodoKEM}
/-! ### The relations between the published entries

Each theorem below states one relation that the specification asserts between
the columns of Tables 1 and 2. They hold of the six published rows, not of an
arbitrary `Params`, whose fields are independent. -/

/-- The modulus `q = 2 ^ D`. -/
theorem q_eq_two_pow (p : ParameterSet) :
    p.params.q = 2 ^ p.params.D := by
  cases p <;> rfl

/-- `ℓ = B * mbar * nbar`: a message fills an `mbar`-by-`nbar` matrix with `B`
bits per entry. -/
theorem ell_eq_mul (p : ParameterSet) :
    p.params.ell = p.params.B * mbar * nbar := by
  cases p <;> rfl

/-- `lenSeedSE` is twice `ℓ` for the salted variant and `ℓ` for the ephemeral
one (Table 2). -/
theorem lenSeedSE_eq (p : ParameterSet) :
    p.params.lenSeedSE = match p.params.variant with
      | .FrodoKEM => 2 * p.params.ell
      | .eFrodoKEM => p.params.ell := by
  cases p <;> rfl

/-- `lenSalt` is twice `ℓ` for the salted variant, and the ephemeral variant
carries no salt (Table 2). -/
theorem lenSalt_eq (p : ParameterSet) :
    p.params.lenSalt = match p.params.variant with
      | .FrodoKEM => 2 * p.params.ell
      | .eFrodoKEM => 0 := by
  cases p <;> rfl

/-! Each published bit length is eight times its byte count, so the divisions
defining `ellBytes`, `lenSeedSEBytes` and `lenSaltBytes` are exact. -/

/-- `ell` is eight times `ellBytes`. -/
theorem ell_eq_eight_mul_ellBytes (p : ParameterSet) :
    p.params.ell = 8 * p.params.ellBytes := by
  cases p <;> rfl

/-- `lenSeedSE` is eight times `lenSeedSEBytes`. -/
theorem lenSeedSE_eq_eight_mul_lenSeedSEBytes (p : ParameterSet) :
    p.params.lenSeedSE = 8 * p.params.lenSeedSEBytes := by
  cases p <;> rfl

/-- `lenSalt` is eight times `lenSaltBytes`. -/
theorem lenSalt_eq_eight_mul_lenSaltBytes (p : ParameterSet) :
    p.params.lenSalt = 8 * p.params.lenSaltBytes := by
  cases p <;> rfl

/-- Every named parameter set satisfies the conditions of Section 3. -/
theorem params_wellFormed (p : ParameterSet) : p.params.WellFormed := by
  cases p <;> constructor <;> decide

end ParameterSet

end FrodoKEM

