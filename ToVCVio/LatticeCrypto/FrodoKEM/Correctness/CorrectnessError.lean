/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness

/-!
# FrodoKEM through the generic KEM interface

`FrodoKEM.KEM.asKEMScheme ops` packages the FrodoKEM algorithms as a VCVio `KEMScheme`. This
file supplies the deterministic-decapsulation witness that generic protocols require and
identifies the generic correctness error of the packaged scheme with FrodoKEM's honest
failure probability:

* `KEM.honestFailureProb_eq_correctnessError` — for fixed operations;
* `ROM.honestFailureProb_eq_tsum_correctnessError` — in the finite random-oracle model, the
  table-averaged honest failure probability is the average, over the sampled table, of the
  generic correctness error for that table.

The numerical bounds of `RandomOracle.Numerical` hold on average over the table, not for
each fixed table.
-/

open OracleComp
open scoped ENNReal

namespace FrodoKEM.KEM

/-- FrodoKEM decapsulation as a pure function. `asKEMScheme` wraps `some (decaps ops sk c)`
in `ProbComp`; implicit rejection makes `decaps` total. -/
def deterministicDecaps {ps : ParameterSet} (ops : Operations ps) :
    KEMScheme.DeterministicDecaps (asKEMScheme ops) where
  decapsDet := fun sk c => some (decaps ops sk c)
  decaps_eq := fun _sk _c => rfl

/-- The honest failure probability of FrodoKEM with operations `ops` is the generic
correctness error of the packaged scheme. -/
theorem honestFailureProb_eq_correctnessError {ps : ParameterSet} (ops : Operations ps) :
    honestFailureProb ops = (asKEMScheme ops).correctnessError ProbCompRuntime.probComp := by
  rw [KEMScheme.correctnessError_probComp_eq_prEvent_false]
  simp only [honestFailureProb, KEMScheme.correctnessExperiment, asKEMScheme, monad_norm,
    Option.some.injEq, Function.comp_def, decide_eq_false_iff_not]

end FrodoKEM.KEM

namespace FrodoKEM.ROM

/-- The table-averaged honest failure probability is the average, over the sampled finite
random-oracle table, of the generic correctness error of FrodoKEM with that table. -/
theorem honestFailureProb_eq_tsum_correctnessError (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen =
      ∑' H : Table ps,
        Pr{let x ← ToVCVio.FiniteXOF.sampleTable (inputLengths ps) (outputBits ps)}[x = H] *
          (KEM.asKEMScheme (operations ps gen H)).correctnessError ProbCompRuntime.probComp := by
  rw [honestFailureProb, OracleComp.prEvent_bind_eq_tsum_prEvent]
  refine tsum_congr fun H => ?_
  -- Each summand's event is the fixed-table honest failure event.
  rw [← KEM.honestFailureProb_eq_correctnessError]
  rfl

end FrodoKEM.ROM
