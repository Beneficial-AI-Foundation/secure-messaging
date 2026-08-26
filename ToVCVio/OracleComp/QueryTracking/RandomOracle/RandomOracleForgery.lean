/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Lazy Random-Oracle One-Time Unforgeability

This file proves a query-budgeted unforgeability bound for an eval-and-verify
interface backed by a shared lazy random oracle.

An adversary has two interfaces to a shared lazy random function `ρ : D → R`:

- an **eval** oracle `D →ₒ R` returning `ρ(d)`; and
- a **verify** oracle `(D × R) →ₒ Bool` reporting whether `r = ρ(d)`. The
  verify oracle reveals only the accept/reject bit, not `ρ(d)`.

The `forged` flag is set by a successful verify query at a point absent from
the evaluated set. If the adversary makes at most `q` verify queries, then
`probForge_le_queryBound_div_card` bounds the forgery probability by `q / |R|`.
-/

open OracleComp OracleSpec ENNReal

namespace OracleComp

universe u

variable {D R : Type} [DecidableEq D] [DecidableEq R] [SampleableType R]

/-! ## Eval-and-verify lazy-RO unforgeability -/

/-- Oracle interface for a one-time-unforgeability adversary: uniform randomness, an **eval**
oracle returning `ρ(d)`, and a **verify** oracle reporting whether `r = ρ(d)`. -/
abbrev forgeSpec (D R : Type) := unifSpec + (D →ₒ R) + (D × R →ₒ Bool)

/-- Uniform-spec witness for `forgeSpec`: every oracle (uniform randomness, the eval random
oracle on `R`, the verify oracle on `Bool`) samples uniformly over a finite, inhabited range. -/
noncomputable instance [Fintype R] [Inhabited R] : IsUniformSpec (forgeSpec D R) :=
  IsUniformSpec.ofFintypeInhabited _

/-- A one-time-unforgeability adversary: outputs nothing observable; we only care whether it
made a successful verify query at a point absent from the set of evaluated points. -/
abbrev ForgeAdversary (D R : Type) := OracleComp (forgeSpec D R) Unit

/-- State for the forgery experiment: the lazy random-oracle cache for `D →ₒ R`, the set of
points already passed to the eval oracle, and a Boolean "forged" flag. -/
-- The `DecidableEq D` instance is unused in the state type itself but kept to
-- align with the oracles and experiment built on this state.
@[nolint unusedArguments]
abbrev ForgeState (D R : Type) [DecidableEq D] [SampleableType R] :=
  (D →ₒ R).QueryCache × Finset D × Bool

/-- The eval oracle: query the lazy random oracle at `d`, record `d` as eval'd, return `ρ(d)`. -/
noncomputable def evalRO :
    QueryImpl (D →ₒ R) (StateT (ForgeState D R) ProbComp) :=
  fun d => do
    let (cache, evald, forged) ← get
    let (resp, cache') ← ((D →ₒ R).randomOracle d).run cache
    set (cache', insert d evald, forged)
    return resp

/-- The verify oracle, backed by the same lazy random oracle on `D →ₒ R`.

On `(d, r)`: look up / sample `ρ(d)`, set the `forged` flag if `r = ρ(d)` **and `d` was not
eval'd before**, and return `r = ρ(d)`. -/
noncomputable def verifyAgainstRO :
    QueryImpl (D × R →ₒ Bool) (StateT (ForgeState D R) ProbComp) :=
  fun (d, r) => do
    let (cache, evald, forged) ← get
    let (resp, cache') ← ((D →ₒ R).randomOracle d).run cache
    let hit : Bool := r == resp
    set (cache', evald, forged || (hit && decide (d ∉ evald)))
    return hit

/-- Forward `unifSpec` queries through `ProbComp` to the forgery-experiment state monad. -/
noncomputable def forgeUnifImpl :
    QueryImpl unifSpec (StateT (ForgeState D R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ForgeState D R) ProbComp)

/-- Complete query implementation for the forgery experiment. -/
noncomputable def forgeImpl :
    QueryImpl (forgeSpec D R) (StateT (ForgeState D R) ProbComp) :=
  forgeUnifImpl (D := D) (R := R) + evalRO (D := D) (R := R) + verifyAgainstRO (D := D) (R := R)

/-- The index predicate selecting verify-oracle queries (the outer `Sum.inr`). -/
def isVerifyQuery : (forgeSpec D R).Domain → Prop := (· matches Sum.inr _)

instance : DecidablePred (isVerifyQuery (D := D) (R := R)) :=
  fun _ => by unfold isVerifyQuery; infer_instance

/-- Query-bound transfer for an `add` handler whose left side never matches the predicate.

The proof delegates to `simulateQ_run_of_step`, so it requires
`[IsUniformSpec spec']` only for the base oracle. It does not require finite or
inhabited ranges for the adversary spec `spec₁ + spec₂`, so the adversary
interface may contain unbounded query-domain or response types. -/
theorem simulateQ_run_add_inr_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec'] {σ α : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (hp_inl : ∀ t, ¬ p (.inl t))
    (h : IsQueryBoundP oa p n)
    (hstep_left : ∀ t s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_p₂ : ∀ t, p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 1)
    (hstep_np₂ : ∀ t, ¬ p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n :=
  IsQueryBoundP.simulateQ_run_of_step h
    (fun t hp s => by
      cases t with
      | inl t => exact absurd hp (hp_inl t)
      | inr t => exact hstep_p₂ t hp s)
    (fun t hnp s => by
      cases t with
      | inl t => exact hstep_left t s
      | inr t => exact hstep_np₂ t hnp s)
    s

/-! ### Generalized induction invariant

The induction generalizes over `cache` and `evald` under
`hnc : ∀ d, d ∉ evald → cache d = none`. Thus each verify query at a
non-evaluated point reads a fresh uniform value. The resampling lemmas below
remove the cached value from the forge-flag marginal before applying the
induction hypothesis.
-/

omit [DecidableEq R] in
/-- Normal form for the eval-oracle step's `StateT` run: sample `ρ(t)` at the lazy random
oracle, then record `t` in the eval'd set (the forge flag is carried through untouched). -/
private lemma evalRO_run (t : D) (cache : (D →ₒ R).QueryCache) (evald : Finset D) (fl : Bool) :
    (evalRO (D := D) (R := R) t).run (cache, evald, fl) =
      (((D →ₒ R).randomOracle t).run cache) >>=
        (fun rc => pure (rc.1, (rc.2, insert t evald, fl))) := by
  unfold evalRO
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set,
    OracleComp.liftM_run_StateT, bind_pure_comp, map_pure, StateT.run_map,
    Functor.map_map]

/-- Normal form for the verify-oracle step's `StateT` run: sample `ρ(d)`, set the forge flag
when `r = ρ(d)` at a non-eval'd point, and return the accept/reject bit. -/
private lemma verifyAgainstRO_run (d : D) (r : R)
    (cache : (D →ₒ R).QueryCache) (evald : Finset D) (fl : Bool) :
    (verifyAgainstRO (D := D) (R := R) (d, r)).run (cache, evald, fl) =
      (((D →ₒ R).randomOracle d).run cache) >>=
        (fun rc => pure ((r == rc.1),
          (rc.2, evald, fl || ((r == rc.1) && decide (d ∉ evald))))) := by
  unfold verifyAgainstRO
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set,
    OracleComp.liftM_run_StateT, bind_pure_comp, map_pure, StateT.run_map,
    Functor.map_map]

omit [DecidableEq R] in
/-- Decompose the forge probability of a fresh verify step over the uniform draw: the verify run
maps the uniform draw `u` to the response `(r == u)` and post-state, then feeds the continuation.
The forge probability is the `u`-average of the continuation's forge probability. Proven on a bare
goal (no `probEvent` wrapper to block `bind_assoc`). -/
private lemma probEvent_freshVerify_tsum {β : Type}
    (g : R → β) (cont : β → ProbComp (Unit × ForgeState D R)) :
    Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true | (g <$> ($ᵗ R : ProbComp R)) >>= cont] =
      ∑' u : R, Pr[= u | ($ᵗ R : ProbComp R)] *
        Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true | cont (g u)] := by
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp, pure_bind]
  rw [probEvent_bind_eq_tsum]

/-- When the response type `R` is empty, the forged flag can never be set: setting it would
require a verify (or eval) response `resp : R`, which does not exist. Hence the forge event has
probability `0`. This discharges the `|R| = 0` edge case of `probForge_le_queryBound_div_card`. -/
private theorem probForge_run_eq_zero_of_isEmpty [IsEmpty R]
    (oa : ForgeAdversary D R) (cache : (D →ₒ R).QueryCache) (evald : Finset D) :
    Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
        (simulateQ forgeImpl oa).run (cache, evald, false)] = 0 := by
  -- `forged` is `false` on every state in the support, since no query can produce an `R`.
  refine probEvent_eq_zero ?_
  intro z hz hforge
  -- The forged flag (third state component) stays `false` on every support element, because
  -- any eval/verify step must sample `$ᵗ R`, whose support is empty when `R` is empty.
  have hPres : QueryImpl.PreservesInv (forgeImpl (D := D) (R := R))
      (fun s : ForgeState D R => s.2.2 = false) := by
    rintro ((t | t) | t) ⟨c, ev, fl⟩ (hfl : fl = false) z hzmem
    · -- unif query: forwards through `ProbComp`, leaving the forge state component untouched.
      simp only [forgeImpl, QueryImpl.add_apply_inl, forgeUnifImpl,
        QueryImpl.liftTarget_apply] at hzmem
      erw [OracleComp.liftM_run_StateT] at hzmem
      rcases (mem_support_bind_iff _ _ _).1 hzmem with ⟨u, _, hz0⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz0
      subst hz0; exact hfl
    · -- eval query: the internal random-oracle sample produces an `R`, impossible when empty.
      exfalso
      simp only [forgeImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, evalRO] at hzmem
      -- Peel the leading `get`; the witness carries the internal random-oracle sample.
      rcases (mem_support_bind_iff _ _ _).1 hzmem with ⟨resp, _, _⟩
      exact isEmptyElim (α := R) (resp.1.1 : R)
    · -- verify query: same internal sample, producing an impossible `R`.
      exfalso
      obtain ⟨td, tr⟩ := t
      simp only [forgeImpl, QueryImpl.add_apply_inr, verifyAgainstRO] at hzmem
      rcases (mem_support_bind_iff _ _ _).1 hzmem with ⟨resp, _, _⟩
      exact isEmptyElim (α := R) (resp.1.1 : R)
  have := OracleComp.simulateQ_run_preservesInv (forgeImpl (D := D) (R := R))
    (fun s : ForgeState D R => s.2.2 = false) hPres oa (cache, evald, false) rfl z hz
  rw [this] at hforge; exact Bool.false_ne_true hforge

/-! ### Forge-resampling at a non-eval'd point (the lazy-sampling forgetting lemma)

For `d ∉ evald` and `cache d = none`, pre-sampling `u ← $ᵗ R` and starting
from `cache.cacheQuery d u` preserves the forge-flag distribution. This is a
marginal equality; the full state distributions differ at cache entry `d`. -/

/-- The forge-flag marginal of running `oa` from state `s`: the `ProbComp Bool` that returns the
final forge flag. The forge probability `Pr[forged | run]` is `Pr[= true | forgeBit oa s]`. -/
noncomputable def forgeBit (oa : OracleComp (forgeSpec D R) Unit) (s : ForgeState D R) :
    ProbComp Bool :=
  (fun z : Unit × ForgeState D R => z.2.2.2) <$> (simulateQ forgeImpl oa).run s

/-- `Pr[forged | run] = Pr[= true | forgeBit]`. -/
private lemma probEvent_forged_eq_probOutput_forgeBit (oa : ForgeAdversary D R)
    (s : ForgeState D R) :
    Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true | (simulateQ forgeImpl oa).run s] =
      Pr[= true | forgeBit oa s] := by
  rw [forgeBit, ← probEvent_eq_eq_probOutput, probEvent_map]
  rfl

/-- `forgeBit` of `pure x` ignores the output and returns the forge flag in the state. -/
private lemma forgeBit_pure (x : Unit) (s : ForgeState D R) :
    forgeBit (pure x : OracleComp (forgeSpec D R) Unit) s = (pure s.2.2 : ProbComp Bool) := by
  rw [forgeBit, simulateQ_pure, StateT.run_pure, map_pure]

/-- Recursion for `forgeBit` over one simulated query: run the `forgeImpl` step, then continue. -/
private lemma forgeBit_query_bind (t : (forgeSpec D R).Domain)
    (k : (forgeSpec D R).Range t → OracleComp (forgeSpec D R) Unit) (s : ForgeState D R) :
    forgeBit ((liftM (OracleSpec.query t) : OracleComp (forgeSpec D R) _) >>= k) s =
      (forgeImpl (D := D) (R := R) t).run s >>= fun z => forgeBit (k z.1) z.2 := by
  rw [forgeBit, simulateQ_bind, simulateQ_spec_query]
  simp only [StateT.run_bind, map_bind]
  rfl

/-- Run form for a `unif` step under `forgeImpl`, fused with a continuation: forward a uniform
sample, state unchanged. -/
private lemma forgeImpl_run_inl_bind {β : Type} (t : unifSpec.Domain) (s : ForgeState D R)
    (g : unifSpec.Range t × ForgeState D R → ProbComp β) :
    ((forgeImpl (D := D) (R := R) (Sum.inl (Sum.inl t))).run s >>= g) =
      (liftM (OracleSpec.query t) : ProbComp _) >>= fun u => g (u, s) := by
  have hrun : (forgeImpl (D := D) (R := R) (Sum.inl (Sum.inl t))).run s =
      (fun u => (u, s)) <$> (liftM (OracleSpec.query t) : ProbComp _) := by
    simp only [forgeImpl, QueryImpl.add_apply_inl, forgeUnifImpl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply]
    erw [OracleComp.liftM_run_StateT]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hrun, map_eq_bind_pure_comp]
  erw [bind_assoc]

/-- Run form for an `eval` step under `forgeImpl`. -/
private lemma forgeImpl_run_eval (t : D) (s : ForgeState D R) :
    (forgeImpl (D := D) (R := R) (Sum.inl (Sum.inr t))).run s =
      (((D →ₒ R).randomOracle t).run s.1) >>=
        (fun rc => pure (rc.1, (rc.2, insert t s.2.1, s.2.2))) := by
  rw [show forgeImpl (D := D) (R := R) (Sum.inl (Sum.inr t)) = evalRO t from by
    rw [forgeImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]]
  obtain ⟨c, ev, fl⟩ := s
  exact evalRO_run t c ev fl

/-- Run form for a `verify` step under `forgeImpl`. -/
private lemma forgeImpl_run_verify (d : D) (r : R) (s : ForgeState D R) :
    (forgeImpl (D := D) (R := R) (Sum.inr (d, r))).run s =
      (((D →ₒ R).randomOracle d).run s.1) >>=
        (fun rc => pure ((r == rc.1),
          (rc.2, s.2.1, s.2.2 || ((r == rc.1) && decide (d ∉ s.2.1))))) := by
  rw [show forgeImpl (D := D) (R := R) (Sum.inr (d, r)) = verifyAgainstRO (d, r) from by
    rw [forgeImpl, QueryImpl.add_apply_inr]]
  obtain ⟨c, ev, fl⟩ := s
  exact verifyAgainstRO_run d r c ev fl

/-- Eval step fused with a continuation: sample `ρ(t)`, record `t`, continue. -/
private lemma forgeImpl_run_eval_bind {β : Type} (t : D) (s : ForgeState D R)
    (g : R × ForgeState D R → ProbComp β) :
    ((forgeImpl (D := D) (R := R) (Sum.inl (Sum.inr t))).run s >>= g) =
      (((D →ₒ R).randomOracle t).run s.1) >>= fun rc =>
        g (rc.1, (rc.2, insert t s.2.1, s.2.2)) := by
  rw [forgeImpl_run_eval]
  erw [bind_assoc]
  exact bind_congr fun rc => pure_bind _ _

/-- Verify step fused with a continuation: sample `ρ(d)`, flag/return, continue. -/
private lemma forgeImpl_run_verify_bind {β : Type} (d : D) (r : R) (s : ForgeState D R)
    (g : Bool × ForgeState D R → ProbComp β) :
    ((forgeImpl (D := D) (R := R) (Sum.inr (d, r))).run s >>= g) =
      (((D →ₒ R).randomOracle d).run s.1) >>= fun rc =>
        g ((r == rc.1), (rc.2, s.2.1, s.2.2 || ((r == rc.1) && decide (d ∉ s.2.1)))) := by
  rw [forgeImpl_run_verify]
  erw [bind_assoc]
  exact bind_congr fun rc => pure_bind _ _

open scoped Classical in
/-- **Forge-bit resampling.** Pre-sampling a fresh uniform value at a non-eval'd, uncached point `d`
has the same forge-bit distribution as not pre-sampling. Proven by induction on the continuation,
generalizing `cache`, `evald`, `fl`, maintaining `cache d = none` and `d ∉ evald`. -/
private lemma evalDist_forgeBit_resample :
    ∀ (ob : ForgeAdversary D R) (cache : (D →ₒ R).QueryCache) (evald : Finset D) (fl : Bool)
      (d : D), cache d = none → d ∉ evald →
      𝒟[($ᵗ R : ProbComp R) >>= fun u => forgeBit ob (cache.cacheQuery d u, evald, fl)] =
        𝒟[forgeBit ob (cache, evald, fl)] := by
  intro ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
      intro cache evald fl d _ _
      simp only [forgeBit_pure]
      -- LHS: `($ᵗR) >>= fun _ => pure fl`; the constant marginal collapses.
      refine evalDist_ext fun y => ?_
      rw [probOutput_bind_const, probFailure_uniformSample]
      simp
  | query_bind t k ih =>
      intro cache evald fl d hcd hde
      -- Reduce both sides to the step-run of `forgeImpl t`, then continue with `forgeBit (k ·)`.
      simp only [forgeBit_query_bind]
      rcases t with (n | t) | ⟨td, tr⟩
      · -- Uniform-sampling query: state untouched; commute the presample, IH on continuation.
        simp only [forgeImpl_run_inl_bind]
        -- Both sides: `query n` then continue with state `(·, evald, fl)`.
        rw [evalDist_bind_bind_swap ($ᵗ R)
          (liftM (OracleSpec.query n) : ProbComp (unifSpec.Range n))
          (fun u w => forgeBit (k w) (cache.cacheQuery d u, evald, fl))]
        refine evalDist_ext fun x => ?_
        simp only [probOutput_bind_eq_tsum]
        refine tsum_congr fun w => ?_
        rw [← probOutput_bind_eq_tsum]
        exact congrArg (Pr[= w | (liftM (OracleSpec.query n) : ProbComp (unifSpec.Range n))] * ·)
          (congrFun (congrArg DFunLike.coe (ih w cache evald fl d hcd hde)) x)
      · -- Eval query at `t`.  Normalize the post-`pure` continuation away.
        simp only [forgeImpl_run_eval_bind]
        by_cases htd : t = d
        · -- `t = d`: presampled side hits cache; bare side samples fresh; rename the draws.
          subst htd
          have hL : (($ᵗ R) >>= fun u =>
                (((D →ₒ R).randomOracle t).run (cache.cacheQuery t u)) >>= fun rc =>
                  forgeBit (k rc.1) (rc.2, insert t evald, fl)) =
              (($ᵗ R) >>= fun u =>
                forgeBit (k u) (cache.cacheQuery t u, insert t evald, fl)) := by
            refine bind_congr fun u => ?_
            rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self cache t u), pure_bind]
          have hR : ((((D →ₒ R).randomOracle t).run cache) >>= fun rc =>
                forgeBit (k rc.1) (rc.2, insert t evald, fl)) =
              (($ᵗ R) >>= fun u =>
                forgeBit (k u) (cache.cacheQuery t u, insert t evald, fl)) := by
            rw [QueryImpl.withCaching_run_none _ hcd]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            rfl
          rw [hL, hR]
        · -- `t ≠ d`: the `d`-entry is untouched; continuation cache still misses `d`.
          have hmiss_t : ∀ u : R, (cache.cacheQuery d u) t = cache t := fun u =>
            QueryCache.cacheQuery_of_ne cache u htd
          by_cases hct : ∃ v, cache t = some v
          · -- `t` already cached: deterministic hit on both sides.
            obtain ⟨v, hv⟩ := hct
            rw [QueryImpl.withCaching_run_some _ hv, pure_bind]
            have hLrw : (($ᵗ R) >>= fun u =>
                  (((D →ₒ R).randomOracle t).run (cache.cacheQuery d u)) >>= fun rc =>
                    forgeBit (k rc.1) (rc.2, insert t evald, fl)) =
                (($ᵗ R) >>= fun u =>
                  forgeBit (k v) (cache.cacheQuery d u, insert t evald, fl)) := by
              refine bind_congr fun u => ?_
              rw [QueryImpl.withCaching_run_some _ (by rw [hmiss_t u]; exact hv), pure_bind]
            rw [hLrw]
            exact ih v cache (insert t evald) fl d hcd
              (fun h => hde (Finset.mem_insert.1 h |>.resolve_left (fun e => htd e.symm)))
          · -- `t` uncached: fresh sample on both sides; commute and apply IH.
            push Not at hct
            have hctn : cache t = none := by
              cases h : cache t with
              | none => rfl
              | some v => exact absurd h (by simpa using hct v)
            rw [QueryImpl.withCaching_run_none _ hctn]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            have hLrw : (($ᵗ R) >>= fun u =>
                  (((D →ₒ R).randomOracle t).run (cache.cacheQuery d u)) >>= fun rc =>
                    forgeBit (k rc.1) (rc.2, insert t evald, fl)) =
                (($ᵗ R) >>= fun u => ($ᵗ R) >>= fun w =>
                  forgeBit (k w) ((cache.cacheQuery d u).cacheQuery t w, insert t evald, fl)) := by
              refine bind_congr fun u => ?_
              rw [QueryImpl.withCaching_run_none _ (by rw [hmiss_t u]; exact hctn)]
              rw [map_eq_bind_pure_comp]
              erw [bind_assoc]
              exact bind_congr fun w => pure_bind _ _
            rw [hLrw]
            rw [evalDist_bind_bind_swap ($ᵗ R) ($ᵗ R)
              (fun u w => forgeBit (k w)
                ((cache.cacheQuery d u).cacheQuery t w, insert t evald, fl))]
            refine evalDist_ext fun x => ?_
            simp only [probOutput_bind_eq_tsum]
            refine tsum_congr fun w => ?_
            have hcomm : ∀ u : R, (cache.cacheQuery d u).cacheQuery t w =
                (cache.cacheQuery t w).cacheQuery d u := by
              intro u
              simp only [QueryCache.cacheQuery]
              exact Function.update_comm (fun h => htd h.symm) u w cache
            have hmiss_d : (cache.cacheQuery t w) d = none := by
              rw [QueryCache.cacheQuery_of_ne cache w (fun h => htd h.symm)]; exact hcd
            simp only [hcomm]
            rw [← probOutput_bind_eq_tsum]
            exact congrArg (Pr[= w | ($ᵗ R : ProbComp R)] * ·)
              (congrFun (congrArg DFunLike.coe
                (ih w (cache.cacheQuery t w) (insert t evald) fl d hmiss_d
                  (fun h => hde (Finset.mem_insert.1 h |>.resolve_left (fun e => htd e.symm))))) x)
      · -- Verify query at `(td, tr)`.  Normalize the post-`pure` continuation away.
        simp only [forgeImpl_run_verify_bind]
        by_cases htd : td = d
        · -- `td = d`: presampled side hits; bare side samples fresh; rename the draws.
          subst htd
          have hL : (($ᵗ R) >>= fun u =>
                (((D →ₒ R).randomOracle td).run (cache.cacheQuery td u)) >>= fun rc =>
                  forgeBit (k (tr == rc.1))
                    (rc.2, evald, fl || ((tr == rc.1) && decide (td ∉ evald)))) =
              (($ᵗ R) >>= fun u =>
                forgeBit (k (tr == u))
                  (cache.cacheQuery td u, evald, fl || ((tr == u) && decide (td ∉ evald)))) := by
            refine bind_congr fun u => ?_
            rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self cache td u), pure_bind]
          have hR : ((((D →ₒ R).randomOracle td).run cache) >>= fun rc =>
                forgeBit (k (tr == rc.1))
                  (rc.2, evald, fl || ((tr == rc.1) && decide (td ∉ evald)))) =
              (($ᵗ R) >>= fun u =>
                forgeBit (k (tr == u))
                  (cache.cacheQuery td u, evald, fl || ((tr == u) && decide (td ∉ evald)))) := by
            rw [QueryImpl.withCaching_run_none _ hcd]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            rfl
          rw [hL, hR]
        · -- `td ≠ d`: the `d`-entry is untouched; continuation cache still misses `d`.
          have hmiss_t : ∀ u : R, (cache.cacheQuery d u) td = cache td := fun u =>
            QueryCache.cacheQuery_of_ne cache u htd
          by_cases hct : ∃ v, cache td = some v
          · obtain ⟨v, hv⟩ := hct
            rw [QueryImpl.withCaching_run_some _ hv, pure_bind]
            have hLrw : (($ᵗ R) >>= fun u =>
                  (((D →ₒ R).randomOracle td).run (cache.cacheQuery d u)) >>= fun rc =>
                    forgeBit (k (tr == rc.1))
                      (rc.2, evald, fl || ((tr == rc.1) && decide (td ∉ evald)))) =
                (($ᵗ R) >>= fun u =>
                  forgeBit (k (tr == v))
                    (cache.cacheQuery d u, evald, fl || ((tr == v) && decide (td ∉ evald)))) := by
              refine bind_congr fun u => ?_
              rw [QueryImpl.withCaching_run_some _ (by rw [hmiss_t u]; exact hv), pure_bind]
            rw [hLrw]
            exact ih (tr == v) cache evald (fl || ((tr == v) && decide (td ∉ evald))) d hcd hde
          · push Not at hct
            have hctn : cache td = none := by
              cases h : cache td with
              | none => rfl
              | some v => exact absurd h (by simpa using hct v)
            rw [QueryImpl.withCaching_run_none _ hctn]
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            have hLrw : (($ᵗ R) >>= fun u =>
                  (((D →ₒ R).randomOracle td).run (cache.cacheQuery d u)) >>= fun rc =>
                    forgeBit (k (tr == rc.1))
                      (rc.2, evald, fl || ((tr == rc.1) && decide (td ∉ evald)))) =
                (($ᵗ R) >>= fun u => ($ᵗ R) >>= fun w =>
                  forgeBit (k (tr == w))
                    ((cache.cacheQuery d u).cacheQuery td w, evald,
                      fl || ((tr == w) && decide (td ∉ evald)))) := by
              refine bind_congr fun u => ?_
              rw [QueryImpl.withCaching_run_none _ (by rw [hmiss_t u]; exact hctn)]
              rw [map_eq_bind_pure_comp]
              erw [bind_assoc]
              exact bind_congr fun w => pure_bind _ _
            rw [hLrw]
            rw [evalDist_bind_bind_swap ($ᵗ R) ($ᵗ R)
              (fun u w => forgeBit (k (tr == w))
                ((cache.cacheQuery d u).cacheQuery td w, evald,
                  fl || ((tr == w) && decide (td ∉ evald))))]
            refine evalDist_ext fun x => ?_
            simp only [probOutput_bind_eq_tsum]
            refine tsum_congr fun w => ?_
            have hcomm : ∀ u : R, (cache.cacheQuery d u).cacheQuery td w =
                (cache.cacheQuery td w).cacheQuery d u := by
              intro u
              simp only [QueryCache.cacheQuery]
              exact Function.update_comm (fun h => htd h.symm) u w cache
            have hmiss_d : (cache.cacheQuery td w) d = none := by
              rw [QueryCache.cacheQuery_of_ne cache w (fun h => htd h.symm)]; exact hcd
            simp only [hcomm]
            rw [← probOutput_bind_eq_tsum]
            exact congrArg (Pr[= w | ($ᵗ R : ProbComp R)] * ·)
              (congrFun (congrArg DFunLike.coe
                (ih (tr == w) (cache.cacheQuery td w) evald
                  (fl || ((tr == w) && decide (td ∉ evald))) d hmiss_d hde)) x)

open scoped Classical in
/-- **Forge-resampling at a non-eval'd point.** For a cache that misses `d` and a point `d` not in
the eval'd set, the `u`-average over a fresh uniform sample `u` of the forge probability of the
continuation run from the cache extended with `d ↦ u` equals the forge probability run from the bare
cache. The eval'd set and forge flag are arbitrary (carried unchanged through the resampling). -/
private lemma forge_resample_run :
    ∀ (ob : ForgeAdversary D R) (cache : (D →ₒ R).QueryCache) (evald : Finset D) (fl : Bool)
      (d : D), cache d = none → d ∉ evald →
      (∑' u : R, Pr[= u | ($ᵗ R : ProbComp R)] *
        Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
          (simulateQ forgeImpl ob).run (cache.cacheQuery d u, evald, fl)]) =
      Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
        (simulateQ forgeImpl ob).run (cache, evald, fl)] := by
  intro ob cache evald fl d hcd hde
  simp only [probEvent_forged_eq_probOutput_forgeBit]
  rw [← probOutput_bind_eq_tsum]
  rw [probOutput_def, probOutput_def]
  exact congrFun (congrArg DFunLike.coe (evalDist_forgeBit_resample ob cache evald fl d hcd hde))
    true

open scoped Classical in
/-- If `oa` makes at most `n` verify queries and every point outside `evald`
is absent from `cache`, then the probability of setting the forge flag from
`false` is at most `n / |R|`. -/
private theorem probForge_run_le [Fintype R]
    (oa : ForgeAdversary D R) (n : ℕ)
    (cache : (D →ₒ R).QueryCache) (evald : Finset D)
    (hq : oa.IsQueryBoundP isVerifyQuery n)
    (hnc : ∀ d, d ∉ evald → cache d = none) :
    Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
        (simulateQ forgeImpl oa).run (cache, evald, false)] ≤
      (n : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing n cache evald with
  | pure a =>
      -- Forge stays unset: the event is impossible, probability `0`.
      have h0 : Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
          (simulateQ forgeImpl (pure a)).run (cache, evald, false)] = 0 := by
        refine probEvent_eq_zero ?_
        intro z hz hforge
        simp only [simulateQ_pure, StateT.run] at hz
        rw [hz] at hforge
        exact Bool.false_ne_true hforge
      rw [h0]; exact zero_le
  | query_bind t mx ih =>
      -- Unfold one simulated query; split on the oracle index.
      rw [simulateQ_query_bind]
      rcases t with (t | t) | t
      · -- unif query: state threaded unchanged, budget unchanged (not a verify index).
        -- Budget transfer: a non-verify query does not consume the verify budget `n`.
        have hnp : ¬ isVerifyQuery (Sum.inl (Sum.inl t) : (forgeSpec D R).Domain) := by
          simp [isVerifyQuery]
        rw [isQueryBoundP_query_bind_iff] at hq
        obtain ⟨_, hmx⟩ := hq
        have hmx' : ∀ u, IsQueryBoundP (mx u) isVerifyQuery n := by
          intro u; have := hmx u; rwa [if_neg hnp] at this
        -- The unif step forwards through `ProbComp`, threading the forge state unchanged.
        simp only [OracleQuery.input_query, forgeImpl,
          QueryImpl.add_apply_inl, forgeUnifImpl, QueryImpl.liftTarget_apply,
          QueryImpl.ofLift_apply, StateT.run_bind]
        erw [OracleComp.liftM_run_StateT]
        -- The forwarded uniform sample leaves the state at `(cache, evald, false)`; the IH
        -- gives `≤ n/|R|` uniformly over the sampled value.
        refine probEvent_bind_le_of_forall_le ?_
        rintro ⟨a, s⟩ hxsupp
        have hstate : s = (cache, evald, false) := by
          simp only [support_bind, support_pure, Set.mem_iUnion,
            Set.mem_singleton_iff] at hxsupp
          obtain ⟨a', _, ha⟩ := hxsupp
          exact (Prod.mk.injEq _ _ _ _ ▸ ha).2
        subst hstate
        exact ih a n cache evald (hmx' a) hnc
      · -- eval query: caches `ρ(t)`, records `t`; preserves `hnc`, budget unchanged.
        have hnp : ¬ isVerifyQuery (Sum.inl (Sum.inr t) : (forgeSpec D R).Domain) := by
          simp [isVerifyQuery]
        rw [isQueryBoundP_query_bind_iff] at hq
        obtain ⟨_, hmx⟩ := hq
        have hmx' : ∀ u, IsQueryBoundP (mx u) isVerifyQuery n := by
          intro u; have := hmx u; rwa [if_neg hnp] at this
        simp only [OracleQuery.input_query, StateT.run_bind, monadLift_self]
        -- The eval step is a random-oracle sample at `t` followed by recording `t`.
        have hstep : (forgeImpl (D := D) (R := R) (Sum.inl (Sum.inr t))).run
            (cache, evald, false) =
            (((D →ₒ R).randomOracle t).run cache) >>=
              (fun rc => pure (rc.1, (rc.2, insert t evald, false))) :=
          forgeImpl_run_eval t (cache, evald, false)
        rw [hstep]
        -- Bound over the eval step's post-state: forge remains `false`, and `t` is recorded
        -- in the set of evaluated points.
        refine probEvent_bind_le_of_forall_le ?_
        rintro ⟨resp, s'⟩ hxsupp
        -- Read off the post-state from the `pure` in `hstep`'s normal form.
        obtain ⟨⟨resp0, cache0⟩, hmem0, hpure⟩ := (mem_support_bind_iff _ _ _).1 hxsupp
        obtain ⟨rfl, rfl⟩ := by simpa only [mem_support_pure_iff, Prod.mk.injEq] using hpure
        -- `hnc` is preserved: every still-non-eval'd point `d ≠ t` is untouched by the RO step.
        have hnc' : ∀ d, d ∉ insert t evald → cache0 d = none := by
          intro d hd
          rw [Finset.mem_insert, not_or] at hd
          obtain ⟨hdt, hde⟩ := hd
          -- The random-oracle step writes at most the entry `t`; off `t` the cache is unchanged.
          have hoff : cache0 d = cache d := by
            cases hct : cache t with
            | some v =>
                rw [QueryImpl.withCaching_run_some _ hct, mem_support_pure_iff,
                  Prod.mk.injEq] at hmem0
                rw [hmem0.2]
            | none =>
                rw [QueryImpl.withCaching_run_none _ hct, support_map] at hmem0
                obtain ⟨u, _, hu⟩ := hmem0
                rw [Prod.mk.injEq] at hu
                rw [← hu.2, QueryCache.cacheQuery_of_ne _ _ hdt]
          rw [hoff]; exact hnc d hde
        exact ih resp n cache0 (insert t evald) (hmx' resp) hnc'
      · -- verify query `(d, r)`. This *consumes* one unit of verify budget.
        obtain ⟨d, r⟩ := t
        -- Budget: a verify query is a verify index, so `0 < n` and the continuation is bounded
        -- by `n - 1`.
        rw [isQueryBoundP_query_bind_iff] at hq
        have hpos : 0 < n := by
          rcases hq.1 with h | h
          · exact absurd (by simp [isVerifyQuery] : isVerifyQuery
              (Sum.inr (d, r) : (forgeSpec D R).Domain)) h
          · exact h
        have hmx' : ∀ u, IsQueryBoundP (mx u) isVerifyQuery (n - 1) := by
          intro u; have := hq.2 u
          rwa [if_pos (by simp [isVerifyQuery] :
            isVerifyQuery (Sum.inr (d, r) : (forgeSpec D R).Domain))] at this
        simp only [OracleQuery.input_query, StateT.run_bind, monadLift_self]
        have hstep : (forgeImpl (D := D) (R := R) (Sum.inr (d, r))).run (cache, evald, false) =
            (((D →ₒ R).randomOracle d).run cache) >>=
              (fun rc => pure ((r == rc.1),
                (rc.2, evald, (r == rc.1) && decide (d ∉ evald)))) := by
          simpa only [Bool.false_or] using forgeImpl_run_verify d r (cache, evald, false)
        by_cases hde : d ∈ evald
        · -- Eval'd point: `decide (d ∉ evald) = false`, so the forge flag stays `false`; the
          -- step only reads/caches. The continuation is bounded by the IH at `n - 1 ≤ n`.
          rw [hstep]
          simp only [hde, not_true, decide_false, Bool.and_false]
          refine le_trans (probEvent_bind_le_of_forall_le
            (ε := ((n - 1 : ℕ) : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹) ?_) ?_
          · rintro ⟨resp, s'⟩ hxsupp
            obtain ⟨⟨resp0, cache0⟩, hmem0, hpure⟩ := (mem_support_bind_iff _ _ _).1 hxsupp
            obtain ⟨rfl, rfl⟩ := by
              simpa only [mem_support_pure_iff, Prod.mk.injEq] using hpure
            -- `hnc` survives: a verify at an eval'd point `d` only (possibly) caches `d ∈ evald`,
            -- leaving every non-eval'd point untouched.
            have hnc' : ∀ d', d' ∉ evald → cache0 d' = none := by
              intro d' hd'
              have hd'd : d' ≠ d := fun h => hd' (h ▸ hde)
              have hoff : cache0 d' = cache d' := by
                cases hcd : cache d with
                | some v =>
                    rw [QueryImpl.withCaching_run_some _ hcd, mem_support_pure_iff,
                      Prod.mk.injEq] at hmem0
                    rw [hmem0.2]
                | none =>
                    rw [QueryImpl.withCaching_run_none _ hcd, support_map] at hmem0
                    obtain ⟨u, _, hu⟩ := hmem0
                    rw [Prod.mk.injEq] at hu
                    rw [← hu.2, QueryCache.cacheQuery_of_ne _ _ hd'd]
              rw [hoff]; exact hnc d' hd'
            exact ih (r == resp0) (n - 1) cache0 evald (hmx' _) hnc'
          · exact mul_le_mul' (by exact_mod_cast Nat.sub_le n 1) le_rfl
        · -- Non-eval'd point `d`.  Fuse the verify step into the continuation, then split on
          -- whether `ρ(d)` is already cached.
          rw [hstep]
          have hdde : decide (d ∉ evald) = true := by simp [hde]
          -- By the uncached invariant, the non-eval'd point `d` misses the cache.
          have hcd : cache d = none := hnc d hde
          -- **Fresh draw (NRS14 App. A.2 Case 1).**  `cache d = none`, so the lazy RO draws
          -- `u : R` uniformly and caches it.  `withCaching_run_none` rewrites the verify run as
          -- a uniform sample `$ᵗ R` followed by caching at `d`.
          rw [show (D →ₒ R).randomOracle d = uniformSampleImpl.withCaching d from rfl,
            QueryImpl.withCaching_run_none _ hcd,
            show (uniformSampleImpl (spec := (D →ₒ R)) d : ProbComp R) = $ᵗ R from rfl]
          -- Collapse the verify run to a single map `g <$> $ᵗ R`.
          have hmap : ((fun u => (u, cache.cacheQuery d u)) <$> ($ᵗ R : ProbComp R)) >>=
                (fun rc => pure ((r == rc.1),
                  (rc.2, evald, (r == rc.1) && decide (d ∉ evald)))) =
              (fun u => ((r == u),
                (cache.cacheQuery d u, evald, (r == u) && decide (d ∉ evald)))) <$>
                ($ᵗ R : ProbComp R) := by
            rw [map_eq_bind_pure_comp, bind_assoc]
            simp only [Function.comp, map_pure, bind_pure_comp]
          rw [hmap]
          erw [probEvent_freshVerify_tsum
            (g := fun u => ((r == u),
              (cache.cacheQuery d u, evald, (r == u) && decide (d ∉ evald))))
            (cont := fun p => (simulateQ forgeImpl
              (mx ((OracleSpec.query (Sum.inr (d, r))).cont p.1))).run p.2)]
          simp only []
          -- The summand at `u`: forge run of the continuation `mx (r == u)` from the cache extended
          -- by `d ↦ u`.  Split each summand into a hit slice (forge bound by `1`, weight `1/|R|`)
          -- and the bare miss contribution `Pr[=u] · Pr[forged | run (mx false) from cacheQuery]`.
          have hkey : ∀ u : R,
              Pr[= u | ($ᵗ R : ProbComp R)] *
                Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
                  (simulateQ forgeImpl (mx (r == u))).run
                    (cache.cacheQuery d u, evald,
                      (r == u) && decide (d ∉ evald))] ≤
              (if u = r then (Fintype.card R : ℝ≥0∞)⁻¹ else 0) +
                Pr[= u | ($ᵗ R : ProbComp R)] *
                  Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
                    (simulateQ forgeImpl (mx false)).run
                      (cache.cacheQuery d u, evald, false)] := by
            intro u
            by_cases hu : u = r
            · -- Hit: `Pr[=u] * (≤1) ≤ 1/|R|`.
              subst hu
              simp only []
              refine le_trans (mul_le_mul' le_rfl probEvent_le_one) ?_
              rw [mul_one, probOutput_uniformSample]
              exact le_add_right le_rfl
            · -- Miss: forge stays `false`; the post-state is `(cacheQuery d u, evald, false)`.
              simp only [if_neg hu, zero_add]
              have hru : (r == u) = false := by
                simp only [beq_eq_false_iff_ne]; exact fun h => hu h.symm
              rw [hru, Bool.false_and]
          -- Sum the per-draw bound: hit terms total `1/|R|`; the miss-shaped tail is the
          -- forge-resampling average, which the forgetting lemma collapses to the bare cache.
          refine le_trans (ENNReal.tsum_le_tsum hkey) ?_
          rw [ENNReal.tsum_add]
          have hhit : (∑' u : R, if u = r then (Fintype.card R : ℝ≥0∞)⁻¹ else 0)
              = (Fintype.card R : ℝ≥0∞)⁻¹ := by
            rw [tsum_eq_single r (fun u hu => by simp [hu]), if_pos rfl]
          rw [hhit]
          -- **Forgetting/resampling.**  Average over the fresh draw `u` of the continuation's forge
          -- probability equals the forge probability run from the bare uncached cache.
          rw [forge_resample_run (mx false) cache evald false d hcd hde]
          -- The bare-cache run is bounded by the IH at `n - 1` (the uncached invariant `hnc` is
          -- unchanged at `cache`).
          refine le_trans (add_le_add le_rfl (ih false (n - 1) cache evald (hmx' false) hnc)) ?_
          -- `1/|R| + (n-1)/|R| = n/|R|` since `0 < n`.
          rw [show (Fintype.card R : ℝ≥0∞)⁻¹ +
              ((n - 1 : ℕ) : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ =
              (1 + ((n - 1 : ℕ) : ℝ≥0∞)) * (Fintype.card R : ℝ≥0∞)⁻¹ from by
            rw [add_mul, one_mul]]
          refine mul_le_mul' (le_of_eq ?_) le_rfl
          rw [show (1 : ℝ≥0∞) + ((n - 1 : ℕ) : ℝ≥0∞) = ((1 + (n - 1) : ℕ) : ℝ≥0∞) from by
            push_cast; ring]
          congr 1
          omega

/-- **Lazy random-oracle one-time unforgeability (eval + verify).**

If `adv` makes at most `q` verify queries (`IsQueryBoundP` on the verify-oracle index), then
the probability that the `forged` flag ends up set — i.e. that some verify query `(d, r)` had
`r = ρ(d)` at a point `d` not eval'd before that query — is at most `q / |R|`.

The adversary starts from a fresh (empty) random-oracle cache, no eval'd points, and an unset
flag. It never observes `ρ`'s outputs through verify (only accept/reject), and forgery is not
counted at eval'd points; so each distinct non-eval'd point contributes at most
`(#tags tried there)/|R|` and the total is `q/|R|`.

See the module docstring for the per-distinct-point accounting argument. -/
theorem probForge_le_queryBound_div_card [Fintype R]
    (adv : ForgeAdversary D R) (q : ℕ)
    (hq : adv.IsQueryBoundP isVerifyQuery q) :
    (Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
        (simulateQ forgeImpl adv).run (∅, ∅, false)]).toReal ≤
      q * (Fintype.card R : ℝ)⁻¹ := by
  -- Reduce to the generalized induction kernel at the initial state.
  have hbound :
      Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
          (simulateQ forgeImpl adv).run (∅, ∅, false)] ≤
        (q : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ :=
    probForge_run_le adv q ∅ ∅ hq (by intro d _; rfl)
  -- Transfer the `ℝ≥0∞` bound to `ℝ` via `ENNReal.toReal`.
  rcases Nat.eq_zero_or_pos (Fintype.card R) with hcard | hcard
  · -- Empty range: `q / |R| = q / 0 = 0` in `ℝ`. The forge event has probability `0`
    -- because a verify response `resp : R` is impossible, so the flag is never set.
    have hR : IsEmpty R := Fintype.card_eq_zero_iff.mp hcard
    have h0 : Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
        (simulateQ forgeImpl adv).run (∅, ∅, false)] = 0 :=
      probForge_run_eq_zero_of_isEmpty adv ∅ ∅
    rw [hcard, h0]; simp
  have hfin : (q : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) ?_
    exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hcard.ne')
  calc (Pr[fun z : Unit × ForgeState D R => z.2.2.2 = true |
            (simulateQ forgeImpl adv).run (∅, ∅, false)]).toReal
      ≤ ((q : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹).toReal :=
        ENNReal.toReal_mono hfin hbound
    _ = q * (Fintype.card R : ℝ)⁻¹ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
        simp

end OracleComp
