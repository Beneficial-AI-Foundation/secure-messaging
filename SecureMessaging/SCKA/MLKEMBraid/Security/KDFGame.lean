/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.CryptoFoundations.PRG

/-!
# Key derivation with an adversarially chosen label

For each label `e`, the map `u ↦ kdfOK u e` is viewed as a PRG.
The distinguisher chooses the label before the shared secret is sampled.
-/

@[expose] public section

open OracleSpec OracleComp

namespace Braid

/-- The PRG experiment for `kdfOK (·, e)`, with a derived key or a uniform epoch key. -/
-- ANCHOR: kdfExp
def kdfExp {K EpochKey : Type} (kdfOK : K → ℕ → EpochKey)
    [SampleableType K] [SampleableType EpochKey]
    (e : ℕ) (D : EpochKey → ProbComp Bool) (derived : Bool) : ProbComp Bool :=
  if derived then PRGScheme.prgRealExperiment ⟨(kdfOK · e)⟩ D
  else PRGScheme.prgIdealExperiment D
-- ANCHOR_END: kdfExp

/-- A distinguisher that chooses a label and retains state before receiving an epoch key. -/
-- ANCHOR: KDFContextAdversary
structure KDFContextAdversary (EpochKey : Type) where
  /-- The information kept between choosing the label and guessing. -/
  State : Type
  /-- Choose the label and the kept information. -/
  context : ProbComp (ℕ × State)
  /-- Guess from the kept information and the epoch key received. -/
  guess : State → EpochKey → ProbComp Bool
-- ANCHOR_END: KDFContextAdversary

/-- Choose the label and retained state, then run the PRG experiment at that label. -/
-- ANCHOR: kdfContextExp
def kdfContextExp {K EpochKey : Type} (kdfOK : K → ℕ → EpochKey)
    [SampleableType K] [SampleableType EpochKey]
    (C : KDFContextAdversary EpochKey) (derived : Bool) : ProbComp Bool := do
  let (e, st) ← C.context
  kdfExp kdfOK e (C.guess st) derived
-- ANCHOR_END: kdfContextExp

/-- The distance between the output distributions for derived and uniform epoch keys. -/
-- ANCHOR: kdfAdvantage
noncomputable def kdfAdvantage {K EpochKey : Type} (kdfOK : K → ℕ → EpochKey)
    [SampleableType K] [SampleableType EpochKey] (C : KDFContextAdversary EpochKey) : ℝ :=
  (𝒟[kdfContextExp kdfOK C true].boolDist 𝒟[kdfContextExp kdfOK C false]).toReal
-- ANCHOR_END: kdfAdvantage

end Braid
