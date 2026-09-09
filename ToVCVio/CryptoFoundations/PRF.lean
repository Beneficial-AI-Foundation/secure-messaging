/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.PRF

/-!
# Fixed-list forwarding for the PRF query implementations

Staging for upstream VCVio (mirrors `VCVio/CryptoFoundations/PRF.lean`): the fixed-list
generalizations of the singleton forwarding lemmas `PRFScheme.simulateQ_prfRealQueryImpl_inr`
and `PRFScheme.simulateQ_prfIdealQueryImpl_inr`.

A PRF distinguisher that queries its function oracle *eagerly* on a fixed list of points (a
non-adaptive reduction) runs `pts.mapM (fun t => liftM (query (Sum.inr t)))`. Under the real
handler that whole fetch loop collapses to `pure (pts.map (prf.eval k))`: the answers are a
deterministic function of the key, so the loop carries no probabilistic content. Under the
ideal handler it becomes the corresponding lazy-random-oracle `mapM` chain over the query
cache, which is where the sampling content of the ideal experiment lives.
-/

open OracleComp OracleSpec

namespace PRFScheme

variable {K D R : Type}

/-- `simulateQ_prfRealQueryImpl_inr` with the result type of the lifted query pinned to `R`
rather than the reducible `Range (Sum.inr d)`. The two spellings are definitionally equal
(hence the term-mode proof), but only the pinned one matches the `mapM` body syntactically:
inside `List.mapM` the element type is fixed by the list, so `rw`/`simp` cannot solve
`Range (Sum.inr ?d) =?= R` with `?d` still unassigned. -/
private lemma simulateQ_prfRealQueryImpl_inr' (prf : PRFScheme K D R) (k : K) (d : D) :
    simulateQ (prf.prfRealQueryImpl k)
      ((liftM (OracleSpec.query (Sum.inr d) : OracleQuery (PRFOracleSpec D R) R)) :
        OracleComp (PRFOracleSpec D R) R) =
      pure (prf.eval k d) :=
  simulateQ_prfRealQueryImpl_inr prf k d

/-- `simulateQ_prfIdealQueryImpl_inr` with the result type of the lifted query pinned to `R`;
see `simulateQ_prfRealQueryImpl_inr'`. -/
private lemma simulateQ_prfIdealQueryImpl_inr' [DecidableEq D] [SampleableType R] (d : D) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R))
      ((liftM (OracleSpec.query (Sum.inr d) : OracleQuery (PRFOracleSpec D R) R)) :
        OracleComp (PRFOracleSpec D R) R) =
      (D →ₒ R).randomOracle d :=
  simulateQ_prfIdealQueryImpl_inr d

/-- A fixed list of function (`Sum.inr`) queries under the real PRF handler collapses to
`pure` of the list of PRF evaluations: on the real side the eager fetch loop of a
non-adaptive reduction is a deterministic function of the key. -/
theorem simulateQ_prfRealQueryImpl_mapM_inr (prf : PRFScheme K D R) (k : K) (pts : List D) :
    simulateQ (prf.prfRealQueryImpl k)
      (pts.mapM (fun t => liftM (OracleSpec.query (Sum.inr t) :
        OracleQuery (PRFOracleSpec D R) R))) =
      pure (pts.map (prf.eval k)) := by
  induction pts with
  | nil => rw [List.mapM_nil, simulateQ_pure, List.map_nil]
  | cons t ts ih =>
      rw [List.mapM_cons]
      simp only [simulateQ_bind, simulateQ_prfRealQueryImpl_inr', pure_bind, ih, simulateQ_pure,
        List.map_cons]

/-- A fixed list of function (`Sum.inr`) queries under the ideal PRF handler is the
corresponding lazy-random-oracle `mapM` chain, threading the query cache. -/
theorem simulateQ_prfIdealQueryImpl_mapM_inr [DecidableEq D] [SampleableType R]
    (pts : List D) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R))
      (pts.mapM (fun t => liftM (OracleSpec.query (Sum.inr t) :
        OracleQuery (PRFOracleSpec D R) R))) =
      (pts.mapM ((D →ₒ R).randomOracle) :
        StateT ((D →ₒ R).QueryCache) ProbComp (List R)) := by
  induction pts with
  | nil => rw [List.mapM_nil, List.mapM_nil, simulateQ_pure]
  | cons t ts ih =>
      rw [List.mapM_cons, List.mapM_cons]
      simp only [simulateQ_bind, simulateQ_prfIdealQueryImpl_inr', ih, simulateQ_pure]

end PRFScheme
