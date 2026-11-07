/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Basic
public import VCVio.CryptoFoundations.PRG

/-!
# The key-derivation game

The epoch key of epoch `e` is `kdfOK u e`, where `u` is a KEM shared secret. For a fixed label
`e`, we regard the map `u ↦ kdfOK u e` as a PRG from shared secrets to epoch keys. `kdfExp` is its
PRG game. In `kdfContextExp` the distinguisher first chooses the label. The security bound of
Braid without authentication contains the advantage `kdfAdvantage` of this game as a term and
assumes no bound on it.
-/

@[expose] public section

open OracleSpec OracleComp

namespace MLKEMBraid.NoAuth

/-- The key-derivation game at the label `e`: the PRG game of `kdfOK (·, e)`. With
`derived = true` the distinguisher `D` receives `kdfOK u e` for a uniform shared secret `u`
(`prgRealExperiment`), and with `derived = false` a uniform epoch key (`prgIdealExperiment`). -/
-- ANCHOR: kdfGame
def kdfExp (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    (e : ℕ) (D : P.EpochKey → ProbComp Bool) (derived : Bool) : ProbComp Bool :=
  if derived then PRGScheme.prgRealExperiment ⟨(P.kdfOK · e)⟩ D
  else PRGScheme.prgIdealExperiment D

/-- A key-derivation distinguisher that first chooses the epoch label. -/
structure KDFContextAdversary (P : Parameters ProbComp) where
  /-- The information kept between choosing the label and guessing. -/
  State : Type
  /-- Choose the epoch label and the kept information. -/
  context : ProbComp (ℕ × State)
  /-- Guess from the kept information and the epoch key received. -/
  guess : State → P.EpochKey → ProbComp Bool

/-- The key-derivation game with a chosen label. The distinguisher `C` first chooses the label
`e`, and then `kdfExp` runs the game at `e`. -/
def kdfContextExp (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    (C : KDFContextAdversary P) (derived : Bool) : ProbComp Bool := do
  let (e, st) ← C.context
  kdfExp P e (C.guess st) derived

/-- The advantage of `C` in the key-derivation game: the distance between its output
distributions for derived and for uniform keys. -/
noncomputable def kdfAdvantage (P : Parameters ProbComp) [SampleableType P.K]
    [SampleableType P.EpochKey] (C : KDFContextAdversary P) : ℝ :=
  (𝒟[kdfContextExp P C true].boolDist 𝒟[kdfContextExp P C false]).toReal
-- ANCHOR_END: kdfGame

end MLKEMBraid.NoAuth
