/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Basic

/-!
# Frodo reconciliation for continuous key agreement from LWE

These definitions follow Section 3.2 of Bos et al., *Frodo: Take off the ring!*. Extraction
rounds half upward and then reduces modulo `2 ^ keyBits`. Hints split the canonical residue
representatives into alternating half-block classes.

Recovery searches all residues in the received hint class using circular distance modulo `q`,
including across zero. Equal-distance candidates use the smaller canonical representative; this
extra rule is a deterministic convention of this specification rather than a rule attributed to
the paper. The initial candidate `b.val * halfWidth` is in the requested class for well-formed
parameters. The low-level functions remain total for raw parameters, but behavior outside that
supported domain is not claimed to conform to the source construction.
-/

namespace lweCKA

/-- Round a residue half upward to an extracted key scalar. -/
def extractScalar (p : Params) (v : Scalar p) : KeyScalar p :=
  ((v.val + p.halfWidth) / p.blockWidth : ℕ)

/-- Return the alternating half-block class of a residue. -/
def hintScalar (p : Params) (v : Scalar p) : HintScalar :=
  (v.val / p.halfWidth : ℕ)

/-- Circular distance between two residues modulo `q`. -/
def modularDistance (p : Params) (u v : Scalar p) : ℕ :=
  min (u - v).val (v - u).val

/-- Choose the closest residue with the requested hint, breaking ties by canonical value. -/
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

/-- Recover an extracted key scalar using the received hint. -/
def reconcileScalar
    (p : Params) (w : Scalar p) (b : HintScalar) : KeyScalar p :=
  extractScalar p (nearestWithHint p w b)

/-- Apply scalar extraction entrywise to a shared matrix. -/
def extract (p : Params) (v : Shared p) : Key p :=
  fun i j => extractScalar p (v i j)

/-- Apply scalar hint generation entrywise to a shared matrix. -/
def makeHint (p : Params) (v : Shared p) : Hint p :=
  fun i j => hintScalar p (v i j)

/-- Apply scalar reconciliation entrywise to a shared matrix and hint. -/
def reconcile (p : Params) (w : Shared p) (b : Hint p) : Key p :=
  fun i j => reconcileScalar p (w i j) (b i j)

end lweCKA
