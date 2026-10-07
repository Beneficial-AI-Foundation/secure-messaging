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
`[CiC25]`, which Section 9.1 of `[LBES26]` tabulates as well.

References are listed in `Construction.lean`.

The parameter overview and table are in `Construction.lean`. The published values
are recorded in `ParameterSet.params`, with relations between them stated as theorems.

Lengths are published in bits; the byte-vector types use these lengths divided
by eight. This division is exact for the named parameter sets, but rounds down
for arbitrary `Params`.

A `Params` is plain data, so nothing constrains its fields. `Params.WellFormed`
collects the conditions `[LBES26]` places on them, and `params_wellFormed`
discharges them for every published set. Section 3 of `[CiC25]` introduces the
same parameters but leaves their positivity and the bound `n < q` unstated, so
`[LBES26]` is the one transcribed here.

`Params.WellFormed.ell_eq` requires `ℓ = B * mbar * nbar`, so that the message
fills the matrix produced by `Frodo.Encode`. `[CiC25]` states this identity in
Section 3 and Table 1; `[LBES26]` states the encoder's input length in Section 6.3
but does not tie it to `lensec`, which is what this condition does.
-/

namespace FrodoKEM

/-- A byte, modeled as an unsigned 8-bit integer. -/
abbrev Byte := UInt8

/-- Fixed-length byte strings used throughout the FrodoKEM specification. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- Bit length of the seeds used for pseudorandom matrix generation. -/
def lenSeedA : ℕ := 128

/-- Seeds used for pseudorandom matrix generation, of `lenSeedA` bits,
represented as `lenSeedA / 8` bytes. -/
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
`Tχ 0 = 2 ^ (lenChi - 1) * χ 0 - 1` (Section 3.1 of `[CiC25]`). -/
def lenChi : ℕ := 16

/-- Integer matrix dimension. Together with `mbar` it fixes the shape of encoded
messages: bit strings of length `B * mbar * nbar` are encoded as `mbar`-by-`nbar`
matrices. -/
def nbar : ℕ := 8

/-- Integer matrix dimension; see `nbar`. -/
def mbar : ℕ := 8

/-- Conditions on the constants that do not vary per parameter set. Section 5
of `[LBES26]` states them for the matrix dimensions and `lenSeedA`, and
Section 3.1 of `[CiC25]` calls `lenChi` a positive integer. Table 1 of `[CiC25]`
fixes `lenZ = 128`. -/
theorem constants_wellFormed :
    0 < mbar ∧ mbar % 8 = 0 ∧ 0 < nbar ∧ nbar % 8 = 0 ∧
      0 < lenSeedA ∧ 0 < lenZ ∧ 0 < lenChi := by decide

/-- Parameters from Tables 1 and 2 of `[CiC25]`. The table shown in
`Construction.lean` is defined in `ParameterSet.params`.
`ParameterSet.params_wellFormed` proves that each parameter set satisfies
`Params.WellFormed`. -/
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
  /-- The security parameter, Section 5's `lensec`: the bit length of the
  message, the shared secret and the public-key hash.
  `Params.WellFormed.ell_values` restricts it to `128`, `192` and `256`, and
  `Params.WellFormed.ell_eq` asks that a message of that length fill the
  matrix. -/
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

/-- Conditions from Section 5 of `[LBES26]`, together with `ell_eq`, which
ensures that the message contains exactly `B` bits per entry of the encoding
matrix described in Section 6.3. The positive salt-length requirement is omitted
because the ephemeral parameter sets use `lenSalt = 0`. -/
structure WellFormed (p : Params) : Prop where
  /-- The lattice dimension is positive. -/
  n_pos : 0 < p.n
  /-- The lattice dimension is a multiple of eight. -/
  n_mod_eight : p.n % 8 = 0
  /-- The lattice dimension is below the modulus. -/
  n_lt_q : p.n < p.q
  /-- The modulus exponent is positive. -/
  D_pos : 0 < p.D
  /-- The modulus exponent is at most sixteen. -/
  D_le : p.D ≤ 16
  /-- At least one bit is encoded in each matrix entry. -/
  B_pos : 0 < p.B
  /-- At most `D` bits are encoded in each matrix entry, so that `2 ^ B ≤ q`. -/
  B_le_D : p.B ≤ p.D
  /-- The modulus satisfies `q = 2 ^ D`. -/
  q_eq : p.q = 2 ^ p.D
  /-- A message fills the matrix: `ℓ = B * mbar * nbar`. -/
  ell_eq : p.ell = p.B * mbar * nbar
  /-- The security parameter is one of the three Section 5 allows. -/
  ell_values : p.ell = 128 ∨ p.ell = 192 ∨ p.ell = 256
  /-- The bit length of the error sampling seed is positive. -/
  lenSeedSE_pos : 0 < p.lenSeedSE

end Params

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

/-- Salt represented as `lenSaltBytes` bytes; empty for the ephemeral parameter sets. -/
abbrev Salt (p : Params) := Bytes p.lenSaltBytes

namespace ParameterSet

/-- Values from Tables 1 and 2 of `[CiC25]` for each supported parameter set.
Relations between these values are proved below. -/
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
/-! ### Relations between parameters

The theorems below prove relations between the values in `ParameterSet.params`
for each of the six supported parameter sets. -/

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

/-- Every named parameter set satisfies `Params.WellFormed`. -/
theorem params_wellFormed (p : ParameterSet) : p.params.WellFormed := by
  cases p <;> constructor <;> decide

end ParameterSet

end FrodoKEM
