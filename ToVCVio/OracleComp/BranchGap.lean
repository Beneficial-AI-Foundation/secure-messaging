/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.EvalDist.Monad.Basic

/-!
# Cancellation of common continuations

**Parameters.** Fix `sample : ProbComp α`, continuations
`left right : α → ProbComp Bool`, and a test `stop : α → Bool`.

**Statement.** If, for every `x : α` with `stop x = true`,
`Pr[left x = true] = Pr[right x = true]`, then replacing both continuations
by `pure false` at those `x` preserves the real-valued signed difference
`Pr[sample >>= left = true] - Pr[sample >>= right = true]`.

**Proof.** Split each acceptance probability into the contribution from
`stop = true` and the contribution from `stop = false`. The first contributions
are equal and cancel on subtraction. This supports reductions that terminate
on exposures for which the compared games have equal continuation probabilities.
-/

open OracleComp ENNReal

namespace ProbComp

/-- For every sampler `sample : ProbComp α`, continuations
`left right : α → ProbComp Bool`, and test `stop : α → Bool`, assume
`∀ x, stop x = true → Pr[left x = true] = Pr[right x = true]`.
Replacing each continuation by `pure false` on the selected values preserves
the signed real-valued acceptance gap of the two sampled experiments. -/
theorem signed_gap_eq_stop_false {α : Type} (sample : ProbComp α)
    (left right : α → ProbComp Bool) (stop : α → Bool)
    (hstop : ∀ x, stop x = true →
      Pr[= true | left x] = Pr[= true | right x]) :
    (Pr[= true | sample >>= left]).toReal -
        (Pr[= true | sample >>= right]).toReal =
      (Pr[= true | sample >>= fun x => if stop x then pure false else left x]).toReal -
        (Pr[= true | sample >>= fun x => if stop x then pure false else right x]).toReal := by
  let common : ProbComp Bool := sample >>= fun x => if stop x then left x else pure false
  let keptLeft : ProbComp Bool := sample >>= fun x => if stop x then pure false else left x
  let keptRight : ProbComp Bool := sample >>= fun x => if stop x then pure false else right x
  have hl : Pr[= true | sample >>= left] =
      Pr[= true | common] + Pr[= true | keptLeft] := by
    apply ToVCVio.probOutput_true_bind_add_of_pointwise
    intro x
    cases stop x <;> simp
  have hr : Pr[= true | sample >>= right] =
      Pr[= true | common] + Pr[= true | keptRight] := by
    apply ToVCVio.probOutput_true_bind_add_of_pointwise
    intro x
    cases hs : stop x
    · simp
    · simpa using (hstop x hs).symm
  have hlr := congrArg ENNReal.toReal hl
  have hrr := congrArg ENNReal.toReal hr
  rw [ENNReal.toReal_add (by simp) (by simp)] at hlr hrr
  change _ = (Pr[= true | keptLeft]).toReal - (Pr[= true | keptRight]).toReal
  linarith

end ProbComp
