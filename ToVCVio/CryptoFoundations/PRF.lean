/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Fixed-list forwarding for the PRF query implementations

A pseudorandom function (PRF) distinguisher that queries its function oracle on a fixed list
of points runs `pts.mapM (fun t => liftM (query (Sum.inr t)))`. This file lifts VCVio's
single-query forwarding lemmas `PRFScheme.simulateQ_prfRealQueryImpl_inr` and
`PRFScheme.simulateQ_prfIdealQueryImpl_inr` to such lists. Candidate for upstream VCVio.
-/

open OracleComp OracleSpec

namespace PRFScheme

variable {K D R : Type}

/-- `simulateQ_prfRealQueryImpl_inr` with the query's result type pinned to `R` rather than
`Range (Sum.inr d)`; only this spelling matches syntactically inside a `mapM` body. -/
private lemma simulateQ_prfRealQueryImpl_inr' (prf : PRFScheme K D R) (k : K) (d : D) :
    simulateQ (prf.prfRealQueryImpl k)
      ((liftM (OracleSpec.query (Sum.inr d) : OracleQuery (PRFOracleSpec D R) R)) :
        OracleComp (PRFOracleSpec D R) R) =
      pure (prf.eval k d) :=
  simulateQ_prfRealQueryImpl_inr prf k d

/-- `simulateQ_prfIdealQueryImpl_inr` with the query's result type pinned to `R`; see
`simulateQ_prfRealQueryImpl_inr'`. -/
private lemma simulateQ_prfIdealQueryImpl_inr' [DecidableEq D] [SampleableType R] (d : D) :
    simulateQ (prfIdealQueryImpl (D := D) (R := R))
      ((liftM (OracleSpec.query (Sum.inr d) : OracleQuery (PRFOracleSpec D R) R)) :
        OracleComp (PRFOracleSpec D R) R) =
      (D →ₒ R).randomOracle d :=
  simulateQ_prfIdealQueryImpl_inr d

/-- Under the real handler a fixed list of function queries is answered deterministically. -/
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

/-- Under the ideal handler a fixed list of function queries is the same list of queries to
the lazily sampled random oracle. -/
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

/-- `isQueryBoundP_query_iff` for a lifted function query, with the query's result type pinned
to `R` so that it applies inside a `mapM` body (cf. `simulateQ_prfRealQueryImpl_inr'`). -/
theorem isQueryBoundP_query_inr {p : ℕ ⊕ D → Prop} [DecidablePred p]
    (d : D) (n : ℕ) (h : p (Sum.inr d) → 0 < n) :
    IsQueryBoundP
      ((liftM (OracleSpec.query (Sum.inr d) : OracleQuery (PRFOracleSpec D R) R)) :
        OracleComp (PRFOracleSpec D R) R) p n :=
  (isQueryBoundP_query_iff p (Sum.inr d) n).mpr h

end PRFScheme
