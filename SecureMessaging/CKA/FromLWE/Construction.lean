/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.Defs
import SecureMessaging.CKA.FromLWE.Reconciliation
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Continuous Key Agreement from Learning With Errors (LWE)

This file defines the LWE-based CKA construction from [ACD19, Section 4.1.2].
Its reconciliation operations follow [BCDMNNRS16, Section 3.2].
The party labels follow the repository interface: A sends first.
In [ACD19, Section 4.1.2], B sends first, so this implementation swaps the labels.

For parameters `n` and `nbar`, the matrices in the sketch below have these dimensions.

| Matrices                           | Dimensions    | Entries    |
| ---------------------------------- | ------------- | ---------- |
| `baseMatrix`                       | `n × n`       | Modulo `q` |
| `S₀`, `E₀`, `P₀`; `S₂`, `E₂`, `P₂` | `n × nbar`    | Modulo `q` |
| `S₁`, `E₁`, `P₁`                   | `nbar × n`    | Modulo `q` |
| `Ẽ₁`, `V₁`; `Ẽ₂`, `V₂`             | `nbar × nbar` | Modulo `q` |
| `h₁`, `h₂`                         | `nbar × nbar` | One bit    |

The initial shared material `ik = (baseMatrix, S₀, E₀)` contains a uniformly sampled matrix
`baseMatrix ∈ ℤ_q^(n × n)` and independently sampled matrices `S₀, E₀` from `χ^(n × nbar)`.
Here, `χ^(r × c)` samples each entry of an `r × c` matrix independently from `χ`.
Party A initially stores `(baseMatrix, P₀ := baseMatrix * S₀ + E₀) = initA ik`.
Party B initially stores `(baseMatrix, S₀) = initB ik`.
These party labels are swapped relative to [ACD19, Section 4.1.2].

The first two sends are shown below. Both parties retain `baseMatrix` throughout.
All freshly sampled secret and error matrices have independent `χ`-distributed entries.

```text
A (first sender)                              B (first receiver)
State: (baseMatrix, P₀)                       State: (baseMatrix, S₀)

Sample S₁, E₁, Ẽ₁
P₁ = S₁ * baseMatrix + E₁
V₁ = S₁ * P₀ + Ẽ₁
// compute reconciliation information
h₁ = makeHint p V₁
Output: extract p V₁  // compute the shared key
                      ───── (P₁, h₁) ─────▶   Output: reconcile p (P₁ * S₀) h₁
State: (baseMatrix, S₁), ready to receive     State: (baseMatrix, P₁), ready to send

                                              Sample S₂, E₂, Ẽ₂
                                              P₂ = baseMatrix * S₂ + E₂
                                              V₂ = P₁ * S₂ + Ẽ₂
                                              // compute reconciliation information
                                              h₂ = makeHint p V₂
                                              Output: extract p V₂  // compute the shared key
                      ◀───── (P₂, h₂) ─────
Output: reconcile p (S₁ * P₂) h₂
State: (baseMatrix, P₂), ready to send        State: (baseMatrix, S₂), ready to receive
```

## References

* [ACD19], Alwen, Coretti and Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019,
  <https://eprint.iacr.org/2018/1037>.
* [BCDMNNRS16], Bos, Costello, Ducas, Mironov, Naehrig, Nikolaenko, Raghunathan and Stebila,
  *Frodo: Take off the ring! Practical, Quantum-Secure Key Exchange from LWE*, CCS 2016,
  <https://eprint.iacr.org/2016/659>. Section and page references use the full version dated
  February 23, 2017: <https://www.douglas.stebila.ca/files/research/papers/CCS-BCDMNNRS16-full.pdf>.
-/

namespace lweCKA

-- ANCHOR: sampleMatrix
/-- Independently sample every entry of a matrix from `χ`. -/
def sampleMatrix {p : Params}
    (χ : ProbComp (Scalar p)) (rows cols : ℕ) :
    ProbComp (Matrix (Fin rows) (Fin cols) (Scalar p)) :=
  ProbComp.sampleIID rows (ProbComp.sampleIID cols χ)
-- ANCHOR_END: sampleMatrix

-- ANCHOR: initKeyGen
/-- Sample the public base uniformly, followed by the initial secret and error from `χ`. -/
def initKeyGen (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (InitKey p) := do
  let baseMatrix ← ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
  let secret ← sampleMatrix χ p.n p.nbar
  let error ← sampleMatrix χ p.n p.nbar
  return { baseMatrix := baseMatrix, secret := secret, error := error }
-- ANCHOR_END: initKeyGen

-- ANCHOR: initialStates
/-- Initialize party A in its first sending phase. -/
def initA {p : Params} (ik : InitKey p) : State p :=
  .aSend ik.baseMatrix (ik.baseMatrix * ik.secret + ik.error)

/-- Initialize party B in its first receiving phase. -/
def initB {p : Params} (ik : InitKey p) : State p :=
  .bRecv ik.baseMatrix ik.secret
-- ANCHOR_END: initialStates

-- ANCHOR: sendArleak
/-- Party A sends a message and leaks the sampled secret and error matrices. -/
def sendArleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .aSend baseMatrix pub => do
      let secret ← sampleMatrix χ p.nbar p.n
      let error ← sampleMatrix χ p.nbar p.n
      let extra ← sampleMatrix χ p.nbar p.nbar
      let nextPub := secret * baseMatrix + error
      let value := secret * pub + extra
      let hint := makeHint p value
      let key := extract p value
      let msg : Message p := .fromA nextPub hint
      let nextState : State p := .aRecv baseMatrix secret
      let coins : SendACoins p := { secret := secret, error := error, extra := extra }
      return some (key, msg, nextState, .fromA coins)
  | _ => pure none
-- ANCHOR_END: sendArleak

-- ANCHOR: recvB
/-- Party B receives A's message. -/
def recvB {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .bRecv baseMatrix secret, .fromA pub hint =>
      let key := reconcile p (pub * secret) hint
      let nextState : State p := .bSend baseMatrix pub
      some (key, nextState)
  | _, _ => none
-- ANCHOR_END: recvB

-- ANCHOR: sendBrleak
/-- Party B sends a message and leaks the sampled secret and error matrices. -/
def sendBrleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .bSend baseMatrix pub => do
      let secret ← sampleMatrix χ p.n p.nbar
      let error ← sampleMatrix χ p.n p.nbar
      let extra ← sampleMatrix χ p.nbar p.nbar
      let nextPub := baseMatrix * secret + error
      let value := pub * secret + extra
      let hint := makeHint p value
      let key := extract p value
      let msg : Message p := .fromB nextPub hint
      let nextState : State p := .bRecv baseMatrix secret
      let coins : SendBCoins p := { secret := secret, error := error, extra := extra }
      return some (key, msg, nextState, .fromB coins)
  | _ => pure none
-- ANCHOR_END: sendBrleak

-- ANCHOR: recvA
/-- Party A receives B's message. -/
def recvA {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .aRecv baseMatrix secret, .fromB pub hint =>
      let key := reconcile p (secret * pub) hint
      let nextState : State p := .aSend baseMatrix pub
      some (key, nextState)
  | _, _ => none
-- ANCHOR_END: recvA

-- ANCHOR: eraseCoins
/-- Remove sampled randomness from the output of the send operation with leaked randomness. -/
def eraseCoins {p : Params}
    (out : Option (Key p × Message p × State p × Rand p)) :
    Option (Key p × Message p × State p) :=
  out.map fun (key, msg, next, _) => (key, msg, next)
-- ANCHOR_END: eraseCoins

/-- The LWE construction with A acting as the first sender throughout. -/
-- ANCHOR: scheme
def scheme (p : Params) (_h : p.WellFormed) (χ : ProbComp (Scalar p)) :
    CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p) where
  initKeyGen := initKeyGen p χ
  initA := fun ik => pure (initA ik)
  initB := fun ik => pure (initB ik)
  sendA := fun st => eraseCoins <$> sendArleak χ st
  sendArleak := sendArleak χ
  recvB := recvB
  sendB := fun st => eraseCoins <$> sendBrleak χ st
  sendBrleak := sendBrleak χ
  recvA := recvA
-- ANCHOR_END: scheme

end lweCKA
