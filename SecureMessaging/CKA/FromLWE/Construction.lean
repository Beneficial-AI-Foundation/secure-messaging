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

This file defines the direct LWE-based CKA construction from Section 4.1.2 of Alwen, Coretti, and
Dodis, *The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol*.
Party names in this namespace follow the paper, where B sends first.

For parameters `n` and `nbar`, `Base` is `n × n`, `Right` is `n × nbar`, `Left` is
`nbar × n`, and `Shared` is `nbar × nbar`. Initialization samples a uniform base and independent
`χ`-distributed matrices `S₀` and `E₀`. Paper A retains `(base, S₀)`, while paper B retains
`(base, P₀)` for `P₀ = base * S₀ + E₀`.

Paper B first samples `S₁`, `E₁`, and extra error `Ẽ₁`, sends
`P₁ = S₁ * base + E₁` with a hint for `V₁ = S₁ * P₀ + Ẽ₁`, and retains `S₁` while waiting to
receive. Paper A recovers from `P₁ * S₀`, retains `P₁`, and becomes ready to send. It then samples
`S₂`, `E₂`, and `Ẽ₂`, sends `P₂ = base * S₂ + E₂` with a hint for
`V₂ = P₁ * S₂ + Ẽ₂`, and retains `S₂`. Paper B recovers from `S₁ * P₂`, retains `P₂`, and
returns to its sending phase.

State replacement records the information retained by the abstract transition. It does not prove
physical memory erasure. Only `scheme` adapts the paper's B-first roles to the repository interface:
repository A is paper B, and repository B is paper A.
-/

namespace lweCKA

/-- Initialize paper party B in its first sending phase. -/
def initB {p : Params} (ik : InitKey p) : State p :=
  .bSend ik.base (ik.base * ik.secret + ik.error)

/-- Initialize paper party A in its first receiving phase. -/
def initA {p : Params} (ik : InitKey p) : State p :=
  .aRecv ik.base ik.secret

/-- Deterministic paper-B send using explicit sampled matrices. -/
def sendBCore {p : Params} (st : State p) (r : SendBCoins p) :
    Option (Key p × Message p × State p) :=
  match st with
  | .bSend base pub =>
      let nextPub := r.secret * base + r.error
      let value := r.secret * pub + r.extra
      some (extract p value, .fromB nextPub (makeHint p value),
        .bRecv base r.secret)
  | _ => none

/-- Deterministic paper-A send using explicit sampled matrices. -/
def sendACore {p : Params} (st : State p) (r : SendACoins p) :
    Option (Key p × Message p × State p) :=
  match st with
  | .aSend base pub =>
      let nextPub := base * r.secret + r.error
      let value := pub * r.secret + r.extra
      some (extract p value, .fromA nextPub (makeHint p value),
        .aRecv base r.secret)
  | _ => none

/-- Paper party B receives A's directional message. -/
def recvB {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .bRecv base secret, .fromA pub hint =>
      some (reconcile p (secret * pub) hint, .bSend base pub)
  | _, _ => none

/-- Paper party A receives B's directional message. -/
def recvA {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .aRecv base secret, .fromB pub hint =>
      some (reconcile p (pub * secret) hint, .aSend base pub)
  | _, _ => none

/-- Paper-B send that also returns the actual sampled matrices. -/
def sendBrleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .bSend _ _ => do
      let r ← sampleSendBCoins p χ
      return (sendBCore st r).map fun (key, msg, next) =>
        (key, msg, next, .fromB r)
  | _ => pure none

/-- Paper-A send that also returns the actual sampled matrices. -/
def sendArleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .aSend _ _ => do
      let r ← sampleSendACoins p χ
      return (sendACore st r).map fun (key, msg, next) =>
        (key, msg, next, .fromA r)
  | _ => pure none

/-- Remove leaked send coins from a transition result. -/
def eraseCoins {p : Params}
    (out : Option (Key p × Message p × State p × Rand p)) :
    Option (Key p × Message p × State p) :=
  out.map fun (key, msg, next, _) => (key, msg, next)

/-- Paper-B send obtained by projecting the leaking send. -/
def sendB {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p)) :=
  eraseCoins <$> sendBrleak χ st

/-- Paper-A send obtained by projecting the leaking send. -/
def sendA {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p)) :=
  eraseCoins <$> sendArleak χ st

/-- The direct LWE construction adapted from paper B-first roles to repository A-first roles. -/
-- ANCHOR: scheme
def scheme (p : Params) (_h : p.WellFormed) (χ : ProbComp (Scalar p)) :
    CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p) where
  initKeyGen := initKeyGen p χ
  initA := fun ik => pure (lweCKA.initB ik)
  initB := fun ik => pure (lweCKA.initA ik)
  sendA := lweCKA.sendB χ
  sendArleak := lweCKA.sendBrleak χ
  recvA := lweCKA.recvB
  sendB := lweCKA.sendA χ
  sendBrleak := lweCKA.sendArleak χ
  recvB := lweCKA.recvA
-- ANCHOR_END: scheme

end lweCKA
