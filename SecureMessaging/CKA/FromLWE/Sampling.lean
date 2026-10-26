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

The supplied computation `χ` samples one scalar from the noise distribution in the paper.
Nested `ProbComp.sampleIID` calls sample matrix entries independently from this distribution.
They visit rows in increasing order, then columns in increasing order within each row.
Each call samples fresh values. Initialization samples the uniform base matrix, secret, and error
in that order.
Each send samples its secret, error, and extra error in that order.

`sendArleak` and `sendBrleak` return the sampled secret, error, and extra-error matrices as
leaked randomness.
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
  let baseMatrix ← ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
  let secret ← sampleMatrix χ p.n p.nbar
  let error ← sampleMatrix χ p.n p.nbar
  return { baseMatrix := baseMatrix, secret := secret, error := error }

/-- Sample fresh secret, error, and extra error matrices for party A. -/
def sampleSendACoins (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (SendACoins p) := do
  let secret ← sampleMatrix χ p.nbar p.n
  let error ← sampleMatrix χ p.nbar p.n
  let extra ← sampleMatrix χ p.nbar p.nbar
  return { secret := secret, error := error, extra := extra }

/-- Sample fresh secret, error, and extra error matrices for party B. -/
def sampleSendBCoins (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (SendBCoins p) := do
  let secret ← sampleMatrix χ p.n p.nbar
  let error ← sampleMatrix χ p.n p.nbar
  let extra ← sampleMatrix χ p.nbar p.nbar
  return { secret := secret, error := error, extra := extra }

end lweCKA
