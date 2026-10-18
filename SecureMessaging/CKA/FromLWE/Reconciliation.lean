/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Basic

/-!
# Frodo reconciliation for continuous key agreement from LWE

Extraction, hints, and recovery follow the original Frodo key-exchange paper
[BCDMNNRS16, Section 3.2, pp. 8–9 of the full version dated February 23, 2017].
References are listed in `Construction.lean`. The later FrodoKEM encoding and decoding
operations are formalized separately in `ToVCVio.LatticeCrypto.FrodoKEM.Encoding`.

Parameters satisfy `Params.WellFormed`. A residue is a value modulo `q`.
Its canonical representative is the integer in `[0, q - 1]`, written `v.val` in Lean.

Extraction rounds to the nearest multiple of `blockWidth`. It rounds midpoint ties upward.
It returns the index of that multiple modulo `2 ^ keyBits`. Hints alternate between 0 and 1 on
successive
intervals of `halfWidth` representatives, starting with 0.

Recovery finds the closest residue with the received hint, measuring distance around the circle
modulo `q`, then extracts its shared-key bits. The search breaks equal-distance ties by choosing
the smaller representative. The paper does not state this rule for ties.
Under its parameter constraints (`Params.WellFormed`), the closest residue with the received hint
is unique.
-/

namespace lweCKA

/-- Extract shared-key bits from a residue by rounding, with midpoint ties rounded upward. -/
def extractScalar (p : Params) (v : Scalar p) : KeyScalar p :=
  ((v.val + p.halfWidth) / p.blockWidth : ℕ)

/-- Return a hint bit that alternates between 0 and 1 on successive intervals of
`halfWidth` canonical representatives, starting with 0. -/
def hintScalar (p : Params) (v : Scalar p) : HintScalar :=
  (v.val / p.halfWidth : ℕ)

/-- The shortest distance around the circle of residues modulo `q`. -/
def modularDistance (p : Params) (u v : Scalar p) : ℕ :=
  min (u - v).val (v - u).val

/-- Search for the closest residue with the requested hint using circular distance modulo `q`.
Resolve equal distances by choosing the smaller representative in the interval `[0, q - 1]`. -/
def nearestWithHint
    (p : Params) (w : Scalar p) (b : HintScalar) : Scalar p :=
  (List.range p.q).foldl
    (fun best k =>
      let v : Scalar p := k
      if hintScalar p v = b ∧
          (modularDistance p w v < modularDistance p w best ∨
            (modularDistance p w v = modularDistance p w best ∧
              v.val < best.val)) then
        v
      else
        best)
    ((b.val * p.halfWidth : ℕ) : Scalar p)

/-- Recover shared-key bits from one residue using the received hint. -/
def reconcileScalar
    (p : Params) (w : Scalar p) (b : HintScalar) : KeyScalar p :=
  extractScalar p (nearestWithHint p w b)

/-- Extract shared-key bits from each entry of a shared matrix. -/
def extract (p : Params) (v : Shared p) : Key p :=
  fun i j => extractScalar p (v i j)

/-- Generate a hint bit for each entry of a shared matrix. -/
def makeHint (p : Params) (v : Shared p) : Hint p :=
  fun i j => hintScalar p (v i j)

/-- Recover shared-key bits from each matrix entry using its received hint. -/
def reconcile (p : Params) (w : Shared p) (b : Hint p) : Key p :=
  fun i j => reconcileScalar p (w i j) (b i j)

end lweCKA
