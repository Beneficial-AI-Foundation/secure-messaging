/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import VCVio.EvalDist.Defs.NeverFails

open OracleSpec OracleComp ENNReal

namespace KEMScheme.IncrementalStructure

variable {K PK SK C : Type} {kem : KEMScheme ProbComp K PK SK C}
  (inc : kem.IncrementalStructure) [DecidableEq K]

/-- Generate a key pair, then use that pair to choose whether to run the staged
correctness trial. A skipped trial returns `true`. For a header-dependent function
`selectHeader`, use `fun pk _ => selectHeader (inc.toHeader pk)`. -/
def selectedCorrectExp (select : PK → SK → ProbComp Bool) : ProbComp Bool := do
  let (pk, sk) ← kem.keygen
  let proceed ← select pk sk
  if proceed then do
    let (c, k) ← inc.stagedEncaps pk
    let k' ← kem.decaps sk c
    pure (decide (k' = some k))
  else
    pure true

/-- Sampling the staged trial before the pair-dependent decision preserves
the result distribution. -/
theorem evalDist_selectedCorrectExp (select : PK → SK → ProbComp Bool) :
    𝒟[inc.selectedCorrectExp select] =
      𝒟[do
        let (pk, sk) ← kem.keygen
        let (c, k) ← inc.stagedEncaps pk
        let k' ← kem.decaps sk c
        let proceed ← select pk sk
        pure (if proceed then decide (k' = some k) else true)] := by
  simp only [selectedCorrectExp]
  refine evalDist_bind_congr' kem.keygen ?_
  rintro ⟨pk, sk⟩
  let trial : ProbComp Bool := do
    let (c, k) ← inc.stagedEncaps pk
    let k' ← kem.decaps sk c
    pure (decide (k' = some k))
  calc
    _ = 𝒟[select pk sk >>= fun proceed =>
        trial >>= fun result => pure (if proceed then result else true)] := by
      refine evalDist_bind_congr' (select pk sk) ?_
      intro proceed
      cases proceed
      · apply evalDist_ext
        intro b
        simp only [Bool.false_eq_true, if_false]
        rw [probOutput_bind_const]
        simp
      · simp [trial]
    _ = _ := by
      simpa only [trial, bind_assoc, pure_bind] using
        evalDist_bind_bind_swap (select pk sk) trial
          (fun proceed result => pure (if proceed then result else true))

/-- Selection depending on the generated pair, in particular on its header,
cannot increase the unconditional failure probability of one fresh trial. -/
theorem probFailure_selectedCorrectExp_le (select : PK → SK → ProbComp Bool) :
    Pr[= false | inc.selectedCorrectExp select] ≤
      kem.correctnessError ProbCompRuntime.probComp := by
  change 𝒟[inc.selectedCorrectExp select] false ≤ _
  rw [inc.evalDist_selectedCorrectExp select]
  change
    Pr[= false | do
      let (pk, sk) ← kem.keygen
      let (c, k) ← inc.stagedEncaps pk
      let k' ← kem.decaps sk c
      let proceed ← select pk sk
      pure (if proceed then decide (k' = some k) else true)] ≤ _
  refine le_trans ?_ (inc.probFailure_correctExp_le ProbCompRuntime.probComp le_rfl)
  unfold CorrectExp
  refine probOutput_bind_mono ?_
  rintro ⟨pk, sk⟩ _
  refine probOutput_bind_mono ?_
  rintro ⟨c, k⟩ _
  refine probOutput_bind_mono ?_
  intro k' _
  calc
    Pr[= false | select pk sk >>= fun proceed =>
        pure (if proceed then decide (k' = some k) else true)] ≤
      Pr[= false | select pk sk >>= fun _ =>
        pure (decide (k' = some k))] := by
      refine probOutput_bind_mono ?_
      intro proceed _
      cases proceed <;> simp
    _ = Pr[= false | pure (decide (k' = some k))] := by
      rw [probOutput_bind_const]
      simp

end KEMScheme.IncrementalStructure
