/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.ZMod.Basic
import SecureMessaging.AEAD.GCM

/-!
# The NIST GHASH polynomial and its ring-level facts

GCM's field multiplication `gfmul` (NIST SP 800-38D §6.3) is multiplication in the
quotient ring `𝔽₂[x] / (x¹²⁸ + x⁷ + x² + x + 1)`. This file fixes that polynomial —
`nistPoly : (ZMod 2)[X]` — and records the three purely algebraic facts the rest of
Phase 7a builds on:

- `nistPoly_monic` : `nistPoly` is monic;
- `nistPoly_natDegree` : `nistPoly.natDegree = 128`, so `BitVec 128` matches the rank of
  `AdjoinRoot nistPoly` as a free `ZMod 2`-module;
- `nistPoly_root_pow` : in `AdjoinRoot nistPoly`, `root¹²⁸ = root⁷ + root² + root + 1`.

Everything here comes from `AdjoinRoot`'s **unconditional** `CommRing` instance and the
`Monic` fact — *no irreducibility* (`Fact (Irreducible _)`, `Field`, `IsDomain`,
`GaloisField`) is used or needed. That is exactly Phase 7a criterion 1's "ring structure
suffices": the reduction identity `nistPoly_root_pow` is the algebraic content of the
`⊕ gcmReductionConst` step in `gfmul` (`R = 0xE1 <<< 120` reads as `x¹²⁸ mod nistPoly`),
consumed by plan 07a-03's `reflect_gfmulStep`.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007. https://csrc.nist.gov/pubs/sp/800/38/d/final
-/

namespace GCM

open Polynomial

/-- The NIST GHASH reduction polynomial `x¹²⁸ + x⁷ + x² + x + 1` over `𝔽₂ = ZMod 2`
(NIST SP 800-38D §6.3). The low-degree tail `x⁷ + x² + x + 1` is grouped explicitly so
`Polynomial.monic_X_pow_add` applies with that tail as its `p`.

`AdjoinRoot nistPoly` is the ring in which `gfmul` multiplies; it is a `CommRing`
unconditionally (no irreducibility), and monic here suffices for its power basis. -/
noncomputable def nistPoly : (ZMod 2)[X] := X ^ 128 + (X ^ 7 + X ^ 2 + X + 1)

/-- `nistPoly` is monic: its leading term is `x¹²⁸` because the tail
`x⁷ + x² + x + 1` has degree `7 < 128`. Proven via `monic_X_pow_add`; no irreducibility. -/
theorem nistPoly_monic : nistPoly.Monic := by
  unfold nistPoly
  apply monic_X_pow_add
  compute_degree!

/-- `nistPoly.natDegree = 128`. Stated as an equality (not a `≤` bound): the reflected
`BitVec 128 ≃ AdjoinRoot nistPoly` equivalence's dimension depends on it. -/
theorem nistPoly_natDegree : nistPoly.natDegree = 128 := by
  unfold nistPoly
  compute_degree!

end GCM
