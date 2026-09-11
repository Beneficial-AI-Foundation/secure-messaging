/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.EvalDist.TVDist

/-!
# Total Variation Distance — Extra Lemmas

Generic total-variation-distance (`tvDist`) facts that hold for any monad with an
evaluation distribution.

* `tvDist_bind_const_right` drops a never-failing, discarded trailing bind from the
  right-hand side of a total-variation distance.
-/

namespace ToVCVio

universe u v

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- Total-variation distance is unaffected by a trailing bind whose result is discarded: if `mx`
never fails, `mx >>= fun _ => my` has exactly the same distribution as `my`. -/
lemma tvDist_bind_const_right [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {β : Type u} (mx' : m β) (mx : m α) [NeverFail mx] (my : m β) :
    tvDist mx' (mx >>= fun _ => my) = tvDist mx' my := by
  unfold tvDist
  rw [evalDist_ext (mx := mx >>= fun _ => my) (mx' := my) fun y => by simp]

end ToVCVio
