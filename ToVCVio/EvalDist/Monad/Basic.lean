import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Bool

/-!
# `EvalDist` point-probability transport

Generic point-probability (`Pr[= x | _]`) facts that hold for any monad with an
evaluation distribution.

* `probOutput_eq_of_evalDist_eq` transports a point probability across an
  equality of evaluation distributions `𝒟[_]`;
* `probOutput_true_bind_add_of_pointwise` splits the `true`-output probability
  of a `bind` whose continuation splits pointwise;
* `abs_probOutput_true_not_map_gap_eq` absorbs a final Boolean negation into the
  absolute two-branch gap (for never-failing computations).
-/

universe u v

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- If `𝒟[mx] = 𝒟[my]` then `Pr[= x | mx] = Pr[= x | my]`: point-probability
congruence under equality of evaluation distributions. -/
lemma probOutput_eq_of_evalDist_eq [HasEvalSPMF m] {mx my : m α}
    (h : 𝒟[mx] = 𝒟[my]) (x : α) :
    Pr[= x | mx] = Pr[= x | my] := by
  simpa [probOutput] using congrFun (congrArg DFunLike.coe h) x

/-- Splitting a `bind`'s continuation pointwise splits the `true`-output
probability of the whole computation: if `Pr[= true | f z]` decomposes as
`Pr[= true | g z] + Pr[= true | h z]` for every `z`, the same decomposition
holds after binding each continuation against a shared `mx`. -/
lemma probOutput_true_bind_add_of_pointwise {β : Type} {n : Type → Type*}
    [Monad n] [HasEvalSPMF n] (mx : n β) (f g h : β → n Bool)
    (hpt : ∀ z, Pr[= true | f z] = Pr[= true | g z] + Pr[= true | h z]) :
    Pr[= true | mx >>= f] = Pr[= true | mx >>= g] + Pr[= true | mx >>= h] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_add]
  exact tsum_congr fun z => by rw [hpt z, mul_add]

/-- A final `(! ·)` map turns `true`-output probability into `false`-output
probability, so the absolute two-branch gap is unchanged by negating both
branches. For never-failing computations this is where a `Bool`-orientation
reversal disappears. -/
lemma abs_probOutput_true_not_map_gap_eq {n : Type → Type*}
    [Monad n] [LawfulMonad n] [HasEvalPMF n] (mx my : n Bool) :
    |(Pr[= true | (! ·) <$> mx]).toReal -
      (Pr[= true | (! ·) <$> my]).toReal| =
    |(Pr[= true | mx]).toReal - (Pr[= true | my]).toReal| := by
  simp [probOutput_false_eq_sub]
  ring_nf
  rw [show -Pr[= true | my].toReal + Pr[= true | mx].toReal =
      Pr[= true | mx].toReal - Pr[= true | my].toReal by ring]
  exact abs_sub_comm (Pr[= true | my].toReal) (Pr[= true | mx].toReal)
