/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.Games

/-!
# Encrypt-then-MAC — PRF hop (`game0` → `game1`)

Replace the PRF tag with a random oracle: `game0_game1_le_prf` bounds the gap by the PRF
advantage of `prfReduction`.
-/

namespace EtM

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

/-! ## Game-hop lemma signatures -/

omit [Inhabited C_e] [Inhabited T] in
/-- Game 0 equals the real AEAD experiment (NRS14 Lemma 3: starting game = real nAE experiment).

The skeleton's `(challenge, TagCache)` state projects via `Prod.fst` onto the AEAD game's
`Option C` challenge state, since the PRF `computeTag`/`verifyTag` never modify the `TagCache`.
(Proof: swap the independent `km`/`ke` samples, then apply `run'_simulateQ_eq_of_query_map_eq`.) -/
theorem game0_eq_real
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    Pr[= true | game0 se prf adv] =
      Pr[= true | AEADScheme.securityExpFixedBit (etmAEAD se prf) adv false] := by
  -- Tail helper: `(simulateQ impl adv).run s >>= take-fst = (simulateQ impl adv).run' s`.
  -- Unfold only `etmAEAD.keygen` (keep `aeadSecurityImpl` folded to match the RHS
  -- `securityExpFixedBit` impl).
  have hkg : (etmAEAD se prf).keygen
      = (se.keygen >>= fun ke => prf.keygen >>= fun km =>
          (pure (ke, km) : ProbComp (K_e × K_m))) := rfl
  unfold game0 etmGameSkeleton AEADScheme.securityExpFixedBit
  rw [hkg]
  simp only [bind_assoc, pure_bind]
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Swap the two independent key samplers so both sides start with `se.keygen`.
  simp only [← probEvent_eq_eq_probOutput]
  rw [probEvent_bind_bind_swap prf.keygen se.keygen]
  simp only [probEvent_eq_eq_probOutput]
  -- Descend under the two key binds; reduce to the per-key inner equality.
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  refine probOutput_bind_congr' prf.keygen true (fun km => ?_)
  -- Inner: project away the invariant `TagCache` via `Prod.fst`.
  rw [run'_simulateQ_eq_of_query_map_eq _
        (AEADScheme.aeadSecurityImpl (etmAEAD se prf) false (ke, km))
        Prod.fst ?hproj adv (none, ∅)]
  case hproj =>
    intro t s
    obtain ⟨ch, qc⟩ := s
    rcases t with (n | am) | ac
    · -- uniform-sampling oracle: state threaded unchanged on both sides
      simp [AEADScheme.aeadSecurityImpl, gameUnifImpl, AEADScheme.oracleUnif,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, Prod.map]
    · -- encryption oracle
      obtain ⟨ad, m⟩ := am
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleEncrypt, etmAEAD,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          map_pure, Prod.map]
    · -- decryption oracle
      obtain ⟨ad, c, t⟩ := ac
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleDecrypt, etmAEAD,
          QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure] <;>
        split_ifs <;>
        simp [StateT.run_pure, map_pure, Prod.map]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Game 0 → real PRF experiment: the `game0` distribution equals the real PRF experiment run on
`prfReduction`. The "real" half of NRS14 Lemma 3, eq. (4). -/
theorem game0_eq_prfRealExp
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    Pr[= true | game0 se prf adv] =
      Pr[= true | prf.prfRealExp (prfReduction se adv)] := by
  -- RHS: unfold the reduction + experiment, fold the inner skeleton run to `run'`,
  -- collapse the nested `simulateQ` via `mapStateTBase`, forward `liftComp se.keygen`
  -- using the `unifSpec`-transparency theorem `simulateQ_prfRealQueryImpl_liftComp`.
  unfold PRFScheme.prfRealExp prfReduction etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq, simulateQ_bind,
    QueryImpl.simulateQ_mapStateTBase_run', PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
  -- LHS: unfold game0 + skeleton, fold its run to `run'`.
  unfold game0 etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Both sides: `prf.keygen` then `se.keygen`, same order; descend both.
  refine probOutput_bind_congr' prf.keygen true (fun k => ?_)
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  -- Per-key inner equality: game0's oracle impl equals the mapped reduction impl
  -- (`computeTag`/`verifyTag` forward to the real PRF oracle = `pure (prf.eval k ·)`).
  -- Clean projection (proj = id): caches stay `∅` on both sides, no invariant needed.
  refine congrArg (fun o => Pr[= true | o]) ?_
  refine run'_simulateQ_eq_of_query_map_eq _ _ id ?hproj adv (none, ∅)
  case hproj =>
    intro t s
    obtain ⟨ch, qc⟩ := s
    rcases t with (n | am) | ac
    · -- uniform-sampling oracle: forwarded through both impls unchanged
      have hq : simulateQ (prf.prfRealQueryImpl k)
          (liftM (OracleSpec.query n) :
            OracleComp (unifSpec + ((AD × C_e) →ₒ T)) (unifSpec.Range n))
          = (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
        PRFScheme.simulateQ_prfRealQueryImpl_liftComp prf k
          (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
      simp [gameUnifImpl, QueryImpl.mapStateTBase, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, hq, StateT.run_monadLift,
        Functor.map_map]
    · -- encryption oracle: `se.encrypt ke m` + tag forwarded to `pure (prf.eval k (ad,c))`
      obtain ⟨ad, m⟩ := am
      cases ch <;>
        simp [QueryImpl.mapStateTBase,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          PRFScheme.prfRealQueryImpl, map_pure]
    · -- decryption oracle: verify forwards to `pure (prf.eval k (ad,c))`, compares tag
      obtain ⟨ad, c, t⟩ := ac
      cases ch <;>
        simp [QueryImpl.mapStateTBase, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          simulateQ_bind, PRFScheme.prfRealQueryImpl] <;>
        split_ifs <;>
        simp [*, StateT.run_pure, map_pure, simulateQ_bind,
          simulateQ_pure]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Game 1 → ideal PRF experiment: the `game1` distribution equals the ideal PRF experiment run
on `prfReduction`. The "ideal" half of NRS14 Lemma 3, eq. (4); this is the heavier of the two
halves, since it must relocate the outer lazy-RO cache into the (always-`∅`) inner `TagCache`. -/
theorem game1_eq_prfIdealExp
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    Pr[= true | game1 se adv] =
      Pr[= true | PRFScheme.prfIdealExp (prfReduction se adv)] := by
  -- RHS: collapse the nested `simulateQ`, forward keygen using the cache-threading
  -- `unifSpec`-transparency theorem `simulateQ_prfIdealQueryImpl_liftComp`,
  -- then push the outer `.run' ∅` through the `liftM se.keygen` bind so both sides start with
  -- `se.keygen` (the cache threads through unchanged).
  unfold PRFScheme.prfIdealExp prfReduction etmGameSkeleton
  -- Targeted push of `run'` through the `liftM se.keygen` bind. Stated as a local `have` (a
  -- one-line `simp` fact) rather than via the general `StateT.run'_bind'`, which unfolds *every*
  -- `run'`-of-bind and would dismantle the per-key `simulateQ … .run'` recovered below.
  have hpush : ∀ {β : Type} (G : K_e → StateT (TagCache AD C_e T) ProbComp β)
      (s : TagCache AD C_e T),
      ((liftM se.keygen : StateT (TagCache AD C_e T) ProbComp K_e) >>= G).run' s
        = se.keygen >>= fun a => (G a).run' s :=
    fun G s => by
      simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, bind_map_left, map_bind]
  simp only [bind_pure_comp, ← StateT.run'_eq, simulateQ_bind,
    QueryImpl.simulateQ_mapStateTBase_run', PRFScheme.simulateQ_prfIdealQueryImpl_liftComp,
    hpush]
  -- LHS: game1.
  unfold game1 etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- A forwarded function query `Sum.inr q` is answered by the lazy random oracle at `q`.
  -- `simulateQ_prfIdealQueryImpl_inr` proves this equality; the local statement pins the ambient
  -- spec annotation so it matches syntactically in the `simp only` decrypt branches below.
  have hroI : ∀ (q : AD × C_e),
      simulateQ (PRFScheme.prfIdealQueryImpl (D := AD × C_e) (R := T))
        (liftM (OracleSpec.query (Sum.inr q) :
            OracleQuery (unifSpec + ((AD × C_e) →ₒ T)) T) :
          OracleComp (unifSpec + ((AD × C_e) →ₒ T)) T)
        = (((AD × C_e) →ₒ T).randomOracle q :
            StateT ((AD × C_e →ₒ T).QueryCache) ProbComp T) :=
    fun q => PRFScheme.simulateQ_prfIdealQueryImpl_inr q
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  refine congrArg (fun o => Pr[= true | o]) ?_
  -- Flatten the nested `StateT EtmGameState (StateT QueryCache ProbComp)` into a single
  -- `StateT (EtmGameState × QueryCache) ProbComp`, then project the joint state back to
  -- game1's `EtmGameState`, RELOCATING the outer RO `QueryCache` into the (always-`∅`)
  -- inner `TagCache` slot, under the invariant "inner cache stays `∅`".
  conv_rhs => rw [StateT.run'_eq _ ((none, ∅) : EtmGameState AD C_e T)]
  rw [← simulateQ_flattenStateT_run']
  refine (run'_simulateQ_eq_of_query_map_eq_inv' _ _
      (fun s : EtmGameState AD C_e T × TagCache AD C_e T => s.1.2 = (∅ : TagCache AD C_e T))
      (fun s : EtmGameState AD C_e T × TagCache AD C_e T => (s.1.1, s.2))
      ?hinv ?hproj adv ((none, ∅), ∅) ?hs).symm
  case hs => rfl
  case hinv =>
    -- Inner-cache invariant: the reduction forwards every tag query to the *external* RO
    -- (the outer `QueryCache`) and never writes the inner `TagCache`, so the inner cache
    -- stays `∅` on every execution path of every oracle. With the composition-level Issue-4
    -- bricks (`flattenStateT_mapStateTBase_run_preserves_inv`) this reduces to a
    -- per-query invariant of the *reduction's own oracle body alone* — no peeling of
    -- `support` through `mapStateTBase`/`flattenStateT`/the outer `simulateQ`.
    -- `inner` is the `prfReduction` skeleton oracle handler (state `EtmGameState`), `outer`
    -- is `prfIdealQueryImpl` (state `QueryCache`); the invariant lives on the inner TagCache.
    intro t s hs
    refine flattenStateT_mapStateTBase_run_preserves_inv _ _
      (fun g : EtmGameState AD C_e T => g.2 = (∅ : TagCache AD C_e T)) ?_ t s hs
    -- Per-query inner invariant: each reduction oracle threads the inner TagCache unchanged
    -- (unif forwards via the lifted `unifSpec`; encrypt/decrypt forward their tag queries to
    -- the external oracle without writing the inner cache).
    clear hs s t
    intro t s hs y hy
    obtain ⟨ch, ic⟩ := s
    simp only at hs
    subst hs
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
    · simp only [add_apply_inl, StateT.run_pure, liftM_pure, StateT.run_monadLift,
        monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
        beq_iff_eq, StateT.run_map, Functor.map_map, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, support_map] at hy
      obtain ⟨a, _, rfl⟩ := hy; rfl
    · cases ch <;>
        simp only [add_apply_inl, add_apply_inr, StateT.run_pure, liftM_pure,
          StateT.run_monadLift, monadLift_self, bind_pure_comp, liftM_map, bind_map_left,
          pure_bind, Prod.mk.eta, beq_iff_eq, StateT.run_map, Functor.map_map,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
          StateT.run_set, map_pure, support_map, support_liftM, OracleQuery.input_query,
          OracleQuery.cont_query, Set.range_id, Set.image_univ, support_pure] at hy
      · obtain ⟨a, _, rfl⟩ := hy; rfl
      · subst hy; rfl
    · -- decryption oracle: `verifyTag` forwards to the external oracle and threads the inner
      -- cache unchanged; the verify `if … then pure … else pure …` keeps the cache `∅`.
      cases ch with
      | none =>
        simp only [add_apply_inr, StateT.run_pure, liftM_pure, StateT.run_monadLift,
          monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
          beq_iff_eq, StateT.run_map, Functor.map_map, ← apply_ite, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, reduceCtorEq, ↓reduceIte, StateT.run_set, map_pure,
          support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
          Set.range_id, Set.image_univ] at hy
        obtain ⟨a, _, rfl⟩ := hy; rfl
      | some val =>
        by_cases hv : val = c <;>
          simp only [add_apply_inr, StateT.run_pure, liftM_pure, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
            beq_iff_eq, StateT.run_map, Functor.map_map, ← apply_ite, QueryImpl.add_apply_inr, hv,
            StateT.run_bind, StateT.run_get, ↓reduceIte, support_pure, Option.some.injEq,
            StateT.run_set, map_pure, support_map, support_liftM, OracleQuery.input_query,
            OracleQuery.cont_query, Set.range_id, Set.image_univ] at hy
        · subst hy; rfl
        · obtain ⟨a, _, rfl⟩ := hy; rfl
  case hproj =>
    intro t s hs
    obtain ⟨⟨ch, ic⟩, oc⟩ := s
    simp only at hs
    subst hs
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
    · -- uniform-sampling oracle: forwarded through both impls; cache relocated unchanged
      have hq : simulateQ (PRFScheme.prfIdealQueryImpl (D := AD × C_e) (R := T))
          (liftM (OracleSpec.query n) :
            OracleComp (unifSpec + ((AD × C_e) →ₒ T)) (unifSpec.Range n))
          = (liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :
              StateT ((AD × C_e →ₒ T).QueryCache) ProbComp (unifSpec.Range n)) :=
        PRFScheme.simulateQ_prfIdealQueryImpl_liftComp
          (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
      rw [flattenStateT_mapStateTBase_apply_run]
      simp [gameUnifImpl,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, hq,
        StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
    · -- encryption oracle: `se.encrypt ke m` + tag = `randomOracle (ad,c)` on the relocated
      -- cache; the inner TagCache (∅) is dropped by proj
      rw [flattenStateT_mapStateTBase_apply_run]
      cases ch <;>
        simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift,
          StateT.run_pure, simulateQ_map, hroI, Prod.map, Functor.map_map]
    · -- decryption oracle: verify = `randomOracle (ad,c)` compare; same relocation.
      -- After the (shared) RO query, the verify result is a `pure`, so `simulateQ` is the
      -- identity and the nested-state reassoc lines up with game1's direct run.
      rw [flattenStateT_mapStateTBase_apply_run]
      cases ch with
      | none =>
        simp only [add_apply_inr, StateT.run_pure, liftM_pure, StateT.run_monadLift,
          monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
          beq_iff_eq, StateT.run_map, Functor.map_map, QueryImpl.add_apply_inr, StateT.run_bind,
          StateT.run_get, reduceCtorEq, ↓reduceIte, StateT.run_set, simulateQ_bind, hroI,
          QueryImpl.withCaching_apply, bind_assoc, map_bind, Prod.map, id_eq]
        refine bind_congr fun a => ?_
        split_ifs <;> simp [StateT.run_pure, simulateQ_pure]
      | some val =>
        by_cases hv : val = (c.1, c.2)
        · subst hv
          simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
            StateT.run_monadLift, StateT.run_pure,
            simulateQ_pure, Prod.map, Functor.map_map]
        · simp only [add_apply_inr, StateT.run_pure, liftM_pure, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
            beq_iff_eq, StateT.run_map, Functor.map_map, QueryImpl.add_apply_inr, StateT.run_bind,
            StateT.run_get, Option.some.injEq, hv, ↓reduceIte, StateT.run_set, simulateQ_bind,
            hroI, QueryImpl.withCaching_apply, bind_assoc, map_bind, Prod.map, id_eq]
          refine bind_congr fun a => ?_
          split_ifs <;> simp [StateT.run_pure, simulateQ_pure]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Game 0 → 1: PRF hop. Gap bounded by PRF advantage.

NRS14 Lemma 3, eq. (4): replace F^tag with random ρ. The two reduction-equals-experiment
equalities `game0_eq_prfRealExp` and `game1_eq_prfIdealExp` combine here, since both sides
share the same `prfAdvantage` shape. -/
theorem game0_game1_le_prf
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    |(Pr[= true | game0 se prf adv]).toReal -
     (Pr[= true | game1 se adv]).toReal| ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) := by
  unfold PRFScheme.prfAdvantage
  rw [game0_eq_prfRealExp se prf adv, game1_eq_prfIdealExp se adv]

end EtM
