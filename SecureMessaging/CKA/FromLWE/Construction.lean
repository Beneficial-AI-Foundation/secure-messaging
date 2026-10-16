/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.Defs
import SecureMessaging.CKA.FromLWE.Reconciliation
import SecureMessaging.CKA.FromLWE.Sampling

/-!
# Continuous Key Agreement from Learning With Errors (LWE)

This file defines the LWE-based CKA construction from [ACD19, Section 4.1.2]. Its reconciliation
operations use the original Frodo key-exchange mechanism [BCDMNNRS16, Section 3.2].
The separate `ToVCVio.LatticeCrypto.FrodoKEM` modules formalize the later FrodoKEM mechanism;
the reconciliation definitions used here come from the 2016 key-exchange paper.
The names of the two parties follow the repository interface: A sends first which is the inverse
convention on the roles of A,B in the paper where B sends first.

For parameters `n` and `nbar`, the matrices in the sketch below have these dimensions.

| Matrices | Dimensions |
| --- | --- |
| `base` | `n × n` |
| `S₀`, `E₀`, `P₀`; `S₂`, `E₂`, `P₂` | `n × nbar` |
| `S₁`, `E₁`, `P₁` | `nbar × n` |
| `Ẽ₁`, `V₁`; `Ẽ₂`, `V₂` | `nbar × nbar` |

The hints `h₁` and `h₂` also have dimensions `nbar × nbar`, with one hint bit per entry.

Initialization samples a uniform `base` and independent `χ`-distributed matrices `S₀` and `E₀`,
and sets `P₀ = base * S₀ + E₀`. The first two sends are shown below; `base` is retained throughout.
All freshly sampled secret and error matrices have independent `χ`-distributed entries.

```text
A (first sender)                               B (first receiver)
State: (base, P₀)                              State: (base, S₀)

Sample S₁, E₁, Ẽ₁
P₁ = S₁ * base + E₁
V₁ = S₁ * P₀ + Ẽ₁
h₁ = makeHint p V₁
Output: extract p V₁
                      ───── (P₁, h₁) ─────▶   Output: reconcile p (P₁ * S₀) h₁
State: (base, S₁), ready to receive            State: (base, P₁), ready to send

                                              Sample S₂, E₂, Ẽ₂
                                              P₂ = base * S₂ + E₂
                                              V₂ = P₁ * S₂ + Ẽ₂
                                              h₂ = makeHint p V₂
                                              Output: extract p V₂
                      ◀───── (P₂, h₂) ─────
Output: reconcile p (S₁ * P₂) h₂
State: (base, P₂), ready to send               State: (base, S₂), ready to receive
```

State replacement records the information retained by the abstract transition. It does not prove
physical memory erasure.

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

/-- Initialize party A in its first sending phase. -/
def initA {p : Params} (ik : InitKey p) : State p :=
  .aSend ik.base (ik.base * ik.secret + ik.error)

/-- Initialize party B in its first receiving phase. -/
def initB {p : Params} (ik : InitKey p) : State p :=
  .bRecv ik.base ik.secret

/-- Party A receives B's message. -/
def recvA {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .aRecv base secret, .fromB pub hint =>
      some (reconcile p (secret * pub) hint, .aSend base pub)
  | _, _ => none

/-- Party B receives A's message. -/
def recvB {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .bRecv base secret, .fromA pub hint =>
      some (reconcile p (pub * secret) hint, .bSend base pub)
  | _, _ => none

/-- A send that also returns, i.e. leaks, the actual sampled matrices. -/
def sendArleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .aSend base pub => do
      let r ← sampleSendACoins p χ
      let nextPub := r.secret * base + r.error
      let value := r.secret * pub + r.extra
      return some (extract p value, .fromA nextPub (makeHint p value),
        .aRecv base r.secret, .fromA r)
  | _ => pure none

/-- B send that also returns, i.e. leaks, the actual sampled matrices. -/
def sendBrleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .bSend base pub => do
      let r ← sampleSendBCoins p χ
      let nextPub := base * r.secret + r.error
      let value := pub * r.secret + r.extra
      return some (extract p value, .fromB nextPub (makeHint p value),
        .bRecv base r.secret, .fromB r)
  | _ => pure none

/-- Remove sampled randomness from the output of the send operation with leaked randomness. -/
def eraseCoins {p : Params}
    (out : Option (Key p × Message p × State p × Rand p)) :
    Option (Key p × Message p × State p) :=
  out.map fun (key, msg, next, _) => (key, msg, next)

/-- The LWE construction with A acting as the first sender throughout. -/
-- ANCHOR: scheme
def scheme (p : Params) (_h : p.WellFormed) (χ : ProbComp (Scalar p)) :
    CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p) where
  initKeyGen := initKeyGen p χ
  initA := fun ik => pure (initA ik)
  initB := fun ik => pure (initB ik)
  sendA := fun st => eraseCoins <$> sendArleak χ st
  sendArleak := sendArleak χ
  recvA := recvA
  sendB := fun st => eraseCoins <$> sendBrleak χ st
  sendBrleak := sendBrleak χ
  recvB := recvB
-- ANCHOR_END: scheme

end lweCKA
