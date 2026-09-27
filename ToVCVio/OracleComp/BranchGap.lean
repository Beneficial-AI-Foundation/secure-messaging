/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.EvalDist.Monad.Basic

/-!
# Discarding common paths in a distinguishing experiment

Two experiments first sample a common prefix `x`, then run continuations
`left x` and `right x`. If their acceptance probabilities agree whenever
`stop x = true`, replacing both continuations by `return false` on those
prefixes preserves their signed acceptance-probability difference. No bound
on the probability of stopping is needed.
-/

open OracleComp ENNReal

namespace ProbComp

/-- Let `X` be a shared prefix distribution and `L(x)`, `R(x)` two Boolean
continuations. Suppose `Pr[L(x) = true] = Pr[R(x) = true]` on prefixes
selected by `stop`. Replacing both continuations by `return false` on those
prefixes preserves `Pr[X >>= L = true] - Pr[X >>= R = true]`.

In a reduction, `stop` may select executions in which a target secret is
exposed and hence cannot be challenged. This lemma requires equality of the
two continuation probabilities on those executions, not merely the fact
that the stopping decision is independent of the challenge bit. -/
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
