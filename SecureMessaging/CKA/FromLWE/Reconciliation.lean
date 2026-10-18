/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Basic

/-!
# Frodo reconciliation for continuous key agreement from LWE

Reconciliation lets a receiver recover the sender's key from a nearby value and a public hint.
The sender and receiver hold residues `v, w ∈ ℤ_q` that differ by LWE noise.
Independent rounding can give different keys when a rounding boundary lies between them.
The sender publishes a hint bit `h(v)` to help the receiver recover `Ext(v)` from `w`.

Reconciliation here follows [BCDMNNRS16, Section 3.2, pp. 8–9].
The separate FrodoKEM encoding and decoding operations follow [CiC25, Section 3.3 and Appendix B].
Those operations are formalized in `ToVCVio.LatticeCrypto.FrodoKEM.Encoding`.

## Definitions

Assume `p.WellFormed`. Write `D = p.logQ`, `B = p.keyBits`, and `q = 2^D`, with `0 < B < D - 1`.
Let `Δ = 2^(D - B) = p.blockWidth` and `H = Δ/2 = p.halfWidth`.
Write `[x] = x.val ∈ {0, …, q - 1}` for the canonical representative of `x ∈ ℤ_q`.
All residue arithmetic and intervals below are modulo `q`.

* Extraction: `Ext(v) = ⌊([v] + H) / Δ⌋ mod 2^B` (`extractScalar`).
  This rounds to the nearest multiple of `Δ`, with midpoint ties rounded upward.
* Hint: `h(v) = ⌊[v] / H⌋ mod 2` (`hintScalar`).
  The hint alternates between 0 and 1 on intervals of width `H`.
* Distance: `d(u, v) = min([u - v], [v - u])` (`modularDistance`).
  This measures the shorter distance around the circle of residues.
* Recovery: `Rec(w, b) = Ext(u*)` (`reconcileScalar`), where
  `u* = argmin_{u ∈ ℤ_q, h(u) = b} d(w, u)` (`nearestWithHint`).
  Recovery selects the closest residue with the received hint, then extracts its key bits.

The search resolves equal distances by choosing the smaller canonical representative.
For well-formed parameters, `H` is even and the closest residue with the requested hint is unique.
Agreement means `Rec(w, h(v)) = Ext(v)`.
It requires a bound on the noise between `v` and `w` and does not hold for arbitrary residues.

## How the hint works

Key `j` is extracted from the interval `[(2j - 1)H, (2j + 1)H)`, centered at `jΔ = 2jH`.
The hint is 1 on the lower half and 0 on the upper half of this interval.
It changes at each rounding level and each rounding boundary.
For well-formed parameters, recovery has the following shift description:

```text
Rec(w, 0) = Ext(w - H/2)
Rec(w, 1) = Ext(w + H/2)
```

The shifts are modulo `q`. The definitions below implement recovery by searching for the nearest
residue with the requested hint. The shift identities are explanatory and are not proved here.

For example, take `D = 4` and `B = 1`, so `q = 16`, `Δ = 8`, and `H = 4`.
The following rows show every residue. The circle wraps from 15 back to 0.

```text
x           0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
h(x)        0  0  0  0  1  1  1  1  0  0  0  0  1  1  1  1
Ext(x)      0  0  0  0  1  1  1  1  1  1  1  1  0  0  0  0
Rec(x,0)    0  0  0  0  0  0  1  1  1  1  1  1  1  1  0  0
Rec(x,1)    0  0  1  1  1  1  1  1  1  1  0  0  0  0  0  0
```

For sender value `v = 3` and receiver value `w = 4`, independent extraction gives different keys.
The sender extracts `Ext(3) = 0` and sends `h(3) = 0`.
The receiver recovers `Rec(4, 0) = 0`, which matches the sender's key.
The matrix operations apply these scalar functions to each entry.

## References

* [BCDMNNRS16], Bos, Costello, Ducas, Mironov, Naehrig, Nikolaenko, Raghunathan and Stebila,
  *Frodo: Take off the ring! Practical, Quantum-Secure Key Exchange from LWE*, CCS 2016.
  Section and page references use the full version dated February 23, 2017:
  <https://www.douglas.stebila.ca/files/research/papers/CCS-BCDMNNRS16-full.pdf>.
* [CiC25], Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR Communications in
  Cryptology 2:3, 2025, <https://cic.iacr.org/p/2/3/25>.
-/

namespace lweCKA

-- ANCHOR: scalarReconciliation
/-- Extract shared-key bits from a residue by rounding, with midpoint ties rounded upward. -/
def extractScalar (p : Params) (v : Scalar p) : KeyScalar p :=
  ((v.val + p.halfWidth) / p.blockWidth : ℕ)

/-- Return a hint bit that alternates between 0 and 1 on successive intervals of
`halfWidth` canonical representatives, starting with 0. -/
def hintScalar (p : Params) (v : Scalar p) : HintScalar :=
  (v.val / p.halfWidth : ℕ)

/-- Circular distance between two residues modulo `q`. -/
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
-- ANCHOR_END: scalarReconciliation

-- ANCHOR: matrixReconciliation
/-- Extract shared-key bits from each entry of a shared matrix. -/
def extract (p : Params) (v : SharedMatrix p) : Key p :=
  fun i j => extractScalar p (v i j)

/-- Generate a hint bit for each entry of a shared matrix. -/
def makeHint (p : Params) (v : SharedMatrix p) : HintMatrix p :=
  fun i j => hintScalar p (v i j)

/-- Recover shared-key bits entrywise using the shared matrix and received hints. -/
def reconcile (p : Params) (w : SharedMatrix p) (b : HintMatrix p) : Key p :=
  fun i j => reconcileScalar p (w i j) (b i j)
-- ANCHOR_END: matrixReconciliation

end lweCKA
