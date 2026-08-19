/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Parameters

/-!
# FrodoKEM Parameter Smoke Checks

Compile-only regression guard for the FrodoKEM parameter tables. Each check
below restates one entry of Tables 1 and 2 of the specification and is closed by
`rfl`, so a transcription error in `FrodoKEM.ParameterSet.params`, or a wrong
formula for a derived quantity, becomes a build failure.

The derived quantities are the interesting ones: `q`, `ellBits`, `lenSeedSE`
and `lenSalt` are all computed from `n`, `D`, `B` and the variant rather than
stored, so these checks are what ties those formulas back to the published
tables.

No runtime assertions — this file is purely a typecheck-time regression guard.
-/

namespace FrodoKEM
namespace Smoke

open ParameterSet

/-! ## Table 1: `n`, `D` and `B` -/

example : (FrodoKEM640).params.n = 640 := rfl
example : (FrodoKEM976).params.n = 976 := rfl
example : (FrodoKEM1344).params.n = 1344 := rfl

example : (FrodoKEM640).params.D = 15 := rfl
example : (FrodoKEM976).params.D = 16 := rfl
example : (FrodoKEM1344).params.D = 16 := rfl

example : (FrodoKEM640).params.B = 2 := rfl
example : (FrodoKEM976).params.B = 3 := rfl
example : (FrodoKEM1344).params.B = 4 := rfl

/-! ## Table 1: the modulus `q = 2 ^ D` -/

example : (FrodoKEM640).params.q = 32768 := rfl
example : (FrodoKEM976).params.q = 65536 := rfl
example : (FrodoKEM1344).params.q = 65536 := rfl

/-! ## Table 1: `ℓ = B * mbar * nbar`, the shared length of `μ`, `s`, `k`, `pkh` and `ss` -/

example : (FrodoKEM640).params.ellBits = 128 := rfl
example : (FrodoKEM976).params.ellBits = 192 := rfl
example : (FrodoKEM1344).params.ellBits = 256 := rfl

/-! ## Table 2: `lenSeedSE` and `lenSalt`

The salted and ephemeral variants share `n`, `D` and `B`, and differ only here.
-/

example : (FrodoKEM640).params.lenSeedSE = 256 := rfl
example : (FrodoKEM976).params.lenSeedSE = 384 := rfl
example : (FrodoKEM1344).params.lenSeedSE = 512 := rfl

example : (eFrodoKEM640).params.lenSeedSE = 128 := rfl
example : (eFrodoKEM976).params.lenSeedSE = 192 := rfl
example : (eFrodoKEM1344).params.lenSeedSE = 256 := rfl

example : (FrodoKEM640).params.lenSalt = 256 := rfl
example : (FrodoKEM976).params.lenSalt = 384 := rfl
example : (FrodoKEM1344).params.lenSalt = 512 := rfl

example : (eFrodoKEM640).params.lenSalt = 0 := rfl
example : (eFrodoKEM976).params.lenSalt = 0 := rfl
example : (eFrodoKEM1344).params.lenSalt = 0 := rfl

/-! ## The ephemeral sets agree with the salted ones on Table 1 -/

example : (eFrodoKEM640).params.n = (FrodoKEM640).params.n := rfl
example : (eFrodoKEM976).params.D = (FrodoKEM976).params.D := rfl
example : (eFrodoKEM1344).params.B = (FrodoKEM1344).params.B := rfl

end Smoke
end FrodoKEM
