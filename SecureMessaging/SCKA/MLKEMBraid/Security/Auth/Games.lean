/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Scheduled
public import ToVCVio.EvalDist.BoolDist

/-!
# Games of authenticated ML-KEM Braid

The SCKA security interface of the scheme with a scheduled authenticator, its adversaries and the
bound on their send queries (`Spec`, `Adversary`, `SendQueryBound`).

The two key-derivation experiments for the schedule `F`. Both are real-or-random on the whole
output `(root, MAC key)`, and in both the distinguisher chooses the label and the known argument
before the hidden one is sampled:

- `inputExp`: the root is known and the update input is hidden;
- `rootExp`: the update input is known and the root is hidden.

In the ideal branch the root and the MAC key are sampled independently.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MLKEMBraid.Auth

/-- The full SCKA security interface of the scheme with a scheduled authenticator. -/
abbrev Spec (P : Parameters ProbComp) (Root MacKey : Type)
    (irl : P.kem.IncrementalRandLeak P.inc) :=
  SCKAScheme.sckaSecuritySpec (State P (Root × MacKey)) (State P (Root × MacKey))
    P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)

/-- An adaptive Boolean-output adversary for the full security interface of `scheme P S irl`. -/
abbrev Adversary (P : Parameters ProbComp) {Root MacKey : Type}
    (_S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc) :=
  OracleComp (Spec P Root MacKey irl) Bool

/-- On every path of oracle answers, `A` makes at most `q` send queries in total, counting all
four send queries: the ordinary and the leaking sends of both parties. -/
def SendQueryBound {P : Parameters ProbComp} {Root MacKey : Type}
    {S : ScheduledAuthenticator P Root MacKey} {irl : P.kem.IncrementalRandLeak P.inc}
    (A : Adversary P S irl) (q : ℕ) : Prop :=
  A.IsQueryBoundP (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q

variable {P : Parameters ProbComp} {Root MacKey : Type}

/-- A distinguisher for the secret-input experiment. It chooses the label and the root. -/
structure InputAdversary (P : Parameters ProbComp) (Root MacKey : Type) where
  /-- The information kept between choosing and guessing. -/
  State : Type
  /-- Choose the label, the root and the kept information. -/
  choose : ProbComp (ℕ × Root × State)
  /-- Guess from the kept information and the pair received. -/
  guess : State → Root × MacKey → ProbComp Bool

/-- The secret-input experiment. With `real = true` the distinguisher `D` receives `F e r u` for
its label `e`, its root `r` and a uniform update input `u`; with `real = false` it receives a
uniform root and an independent uniform MAC key. -/
def inputExp [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (D : InputAdversary P Root MacKey)
    (real : Bool) : ProbComp Bool := do
  let (e, r, st) ← D.choose
  if real then
    let u ← $ᵗ P.EpochKey
    D.guess st (S.F e r u)
  else
    let r' ← $ᵗ Root
    let m' ← $ᵗ MacKey
    D.guess st (r', m')

/-- The advantage of `D` in the secret-input experiment: the distance between its output
distributions in the real and in the ideal branch. -/
noncomputable def inputAdvantage [SampleableType P.EpochKey] [SampleableType Root]
    [SampleableType MacKey] (S : ScheduledAuthenticator P Root MacKey)
    (D : InputAdversary P Root MacKey) : ℝ :=
  (𝒟[inputExp S D true].boolDist 𝒟[inputExp S D false]).toReal

/-- A distinguisher for the secret-root experiment. It chooses the label and the update input. -/
structure RootAdversary (P : Parameters ProbComp) (Root MacKey : Type) where
  /-- The information kept between choosing and guessing. -/
  State : Type
  /-- Choose the label, the update input and the kept information. -/
  choose : ProbComp (ℕ × P.EpochKey × State)
  /-- Guess from the kept information and the pair received. -/
  guess : State → Root × MacKey → ProbComp Bool

/-- The secret-root experiment. With `real = true` the distinguisher `E` receives `F e r x` for
its label `e`, its update input `x` and a uniform root `r`; with `real = false` it receives a
uniform root and an independent uniform MAC key. -/
def rootExp [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (E : RootAdversary P Root MacKey)
    (real : Bool) : ProbComp Bool := do
  let (e, x, st) ← E.choose
  if real then
    let r ← $ᵗ Root
    E.guess st (S.F e r x)
  else
    let r' ← $ᵗ Root
    let m' ← $ᵗ MacKey
    E.guess st (r', m')

/-- The advantage of `E` in the secret-root experiment: the distance between its output
distributions in the real and in the ideal branch. -/
noncomputable def rootAdvantage [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (E : RootAdversary P Root MacKey) : ℝ :=
  (𝒟[rootExp S E true].boolDist 𝒟[rootExp S E false]).toReal

end MLKEMBraid.Auth
