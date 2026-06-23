/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.EvalDist.Monad.Basic

/-!
# Commuting two independent binds at the `evalDist` level (missing VCVio brick)

`oa >>= fun a => ob >>= fun b => f a b` and `ob >>= fun b => oa >>= fun a => f a b` are **not**
definitionally equal — and for a non-commutative monad `m` they are genuinely different
`m`-computations. But their *output distributions* always agree: the two samples are independent,
so the difference is invisible to `evalDist` (it reduces to `ENNReal.tsum_comm`). This holds for any
`m` with `[MonadLiftT m SPMF]`, since only the `SPMF` image is manipulated.

This generic fact is used in two places in `SecureMessaging.ToVCVio` (the discarded-query
resampling marginal and the forge-bit resampling kernel), which previously each carried a private
`ProbComp` copy. Hoisted here as one shared, generalized lemma.

TODO(upstream): contribute to VCVio alongside `EvalDist/Monad/Basic.lean`.
-/

open ENNReal

namespace ToVCVio

universe u v

variable {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

/-- `evalDist` commutes two independent binds. Although `oa >>= fun a => ob >>= …` and
`ob >>= fun b => oa >>= …` are not definitionally equal, their output distributions agree (the two
samples are independent). True for any `[MonadLiftT m SPMF]` — the proof only manipulates the `SPMF`
image, where bind commutes (`ENNReal.tsum_comm`). -/
theorem evalDist_bind_bind_comm {β γ δ : Type u}
    (oa : m β) (ob : m γ) (f : β → γ → m δ) :
    𝒟[oa >>= fun a => ob >>= fun b => f a b] =
      𝒟[ob >>= fun b => oa >>= fun a => f a b] := by
  refine evalDist_ext fun x => ?_
  simp only [probOutput_bind_eq_tsum]
  rw [show (∑' a, Pr[= a | oa] * ∑' b, Pr[= b | ob] * Pr[= x | f a b]) =
        ∑' a, ∑' b, Pr[= a | oa] * (Pr[= b | ob] * Pr[= x | f a b]) from
      tsum_congr fun a => (ENNReal.tsum_mul_left).symm,
    show (∑' b, Pr[= b | ob] * ∑' a, Pr[= a | oa] * Pr[= x | f a b]) =
        ∑' b, ∑' a, Pr[= b | ob] * (Pr[= a | oa] * Pr[= x | f a b]) from
      tsum_congr fun b => (ENNReal.tsum_mul_left).symm]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => ?_
  refine tsum_congr fun a => ?_
  rw [← mul_assoc, ← mul_assoc, mul_comm (Pr[= b | ob]) (Pr[= a | oa])]

end ToVCVio
