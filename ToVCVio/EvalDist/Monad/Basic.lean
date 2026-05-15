import VCVio.EvalDist.Monad.Basic

/-!
# `EvalDist` point-probability transport

Transports point probabilities `Pr[= x | _]` across equalities of evaluation
distributions `𝒟[_]`.
-/

universe u v

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- If `𝒟[mx] = 𝒟[my]` then `Pr[= x | mx] = Pr[= x | my]`: point-probability
congruence under equality of evaluation distributions. -/
lemma probOutput_eq_of_evalDist_eq [HasEvalSPMF m] {mx my : m α}
    (h : 𝒟[mx] = 𝒟[my]) (x : α) :
    Pr[= x | mx] = Pr[= x | my] := by
  simpa [probOutput] using congrFun (congrArg DFunLike.coe h) x
