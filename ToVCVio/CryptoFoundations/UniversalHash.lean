/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType

/-!
# Almost-XOR-universal hash families

Generic almost-XOR-universal (AXU) predicate for keyed hash families, stated via
`probOutput` over `ProbComp`, together with the generic forgery-probability floor
it yields (Phase 1 criteria 5–6, generic bricks).
-/
