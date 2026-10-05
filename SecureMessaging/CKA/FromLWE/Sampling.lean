/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Basic
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Sampling for continuous key agreement from LWE

The supplied scalar computation `χ` represents the paper's noise distribution. Nested
`ProbComp.sampleIID` calls draw matrix entries independently, in row order and then column order.
Every invocation draws fresh values. Initialization samples the uniform base, secret, and error in
that order; each directional send samples its secret, error, and extra error in that order.

The leaking interface returns the actual sampled matrices used by the deterministic transition; it
does not model a byte-level sampler transcript. `ProbComp` supplies the existing total uniform-query
language, so no separate probability abstraction or losslessness assumption is introduced here.
-/

namespace lweCKA

/-- Independently sample every entry of a matrix from `χ`. -/
def sampleMatrix {p : Params}
    (χ : ProbComp (Scalar p)) (rows cols : ℕ) :
    ProbComp (Matrix (Fin rows) (Fin cols) (Scalar p)) :=
  ProbComp.sampleIID rows (ProbComp.sampleIID cols χ)

/-- Sample the public base uniformly, followed by the initial secret and error from `χ`. -/
def initKeyGen (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (InitKey p) := do
  let base ← ($ᵗ (Base p) : ProbComp (Base p))
  let secret ← sampleMatrix χ p.n p.nbar
  let error ← sampleMatrix χ p.n p.nbar
  return { base := base, secret := secret, error := error }

/-- Sample fresh secret, error, and extra error matrices for paper party B. -/
def sampleSendBCoins (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (SendBCoins p) := do
  let secret ← sampleMatrix χ p.nbar p.n
  let error ← sampleMatrix χ p.nbar p.n
  let extra ← sampleMatrix χ p.nbar p.nbar
  return { secret := secret, error := error, extra := extra }

/-- Sample fresh secret, error, and extra error matrices for paper party A. -/
def sampleSendACoins (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (SendACoins p) := do
  let secret ← sampleMatrix χ p.n p.nbar
  let error ← sampleMatrix χ p.n p.nbar
  let extra ← sampleMatrix χ p.nbar p.nbar
  return { secret := secret, error := error, extra := extra }

end lweCKA
