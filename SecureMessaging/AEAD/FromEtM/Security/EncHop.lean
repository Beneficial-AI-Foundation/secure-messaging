/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.Games

/-!
# Encrypt-then-MAC — IND$-CPA hop (`game2` → `game3`)

`game2_game3_le_enc`: the gap is bounded by the IND$-CPA advantage of `encReduction`.
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

omit [Inhabited T] in
/-- Game 2 → 3: IND$-CPA hop. Gap bounded by encryption advantage.

NRS14 Lemma 3, privacy reduction D₁(A). Since `verifyTag = pure false` in
both game2 and game3, no decrypt query ever reaches `se.decrypt`. The
IND$-CPA reduction only needs to simulate encryption (forward to its oracle)
and decryption (always reject). The `computeTag` change from random oracle
to `$ᵗ T` is distributional equality: the cache is written but never read
(verify disabled), and a one-time fresh RO query is uniformly distributed. -/
theorem game2_game3_le_enc [Inhabited K_e]
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    |(Pr[= true | game2 se adv]).toReal -
     (Pr[= true | game3 se adv]).toReal| ≤
      DetSEAlg.distAdvantage se (encReduction se adv) := by
  -- NRS14 Lemma 3, privacy reduction D₁(A).
  -- RO-to-uniform: since verifyTag = pure false in both games, the TagCache
  -- is write-only. A fresh RO query on a never-read input is uniformly
  -- distributed, so replacing randomOracle with $ᵗ T preserves the distribution.
  -- After this substitution, game2 and game3 differ only in encryptMsg:
  --   game2: se.encrypt ke m (real)
  --   game3: $ᵗ C_e (random)
  -- This is exactly the IND$-CPA distinguishing experiment.
  -- game2 = DetSEAlg.securityExpFixedBit se (encReduction se adv) false
  -- game3 = DetSEAlg.securityExpFixedBit se (encReduction se adv) true
  --
  -- Discovered proof path (both directions are probOutput equalities, then `abs_sub_comm`):
  --   `securityExpFixedBit se (encReduction se adv) b` unfolds to a NESTED simulateQ:
  --   `simulateQ (indCPAImpl se b k) (encReduction…)`, where `encReduction` itself is
  --   `simulateQ encRedImpl adv` over `EtmGameState`. Collapse the nesting with
  --   `simulateQ_mapStateTBase_run` (VCVio `…/SimSemantics/StateT/Basic.lean`):
  --     simulateQ outer ((simulateQ inner oa).run s)
  --       = (simulateQ (outer.mapStateTBase inner) oa).run s
  --   giving a SINGLE `simulateQ (indCPAImpl.mapStateTBase encRedImpl) adv` over state
  --   `EtmGameState` with base monad `StateT Bool ProbComp` (the Bool = indCPA "encrypt
  --   called" flag). Split the leading `se.keygen` with `simulateQ_bind` +
  --   `simulateQ_liftComp` (forwarded). Then relate the combined impl to game3's impl via
  --   the invariant-gated projection `map_run_simulateQ_eq_of_query_map_eq_inv'`, with
  --   invariant `Bool = challenge.isSome` (the indCPA flag stays in sync with the skeleton's
  --   one-time challenge), projecting the Bool away.
  --   game3 direction: clean (encRedImpl tag = $ᵗ T already matches game3). game2 direction:
  --   additionally needs RO→uniform (game2's randomOracle tag = encRedImpl's $ᵗ T), justified
  --   as in `stepA` below (write-only cache, one-time fresh query uniform).
  have hg3 : Pr[= true | game3 se adv] =
      Pr[= true | DetSEAlg.securityExpFixedBit se (encReduction se adv) true] := by
    unfold DetSEAlg.securityExpFixedBit encReduction etmGameSkeleton
    -- Nested simulateQ collapses to a single `simulateQ (indCPAImpl.mapStateTBase encRedImpl)`.
    -- (Do the collapse alone — adding StateT.run_* here blocks `mapStateTBase_run` from firing.)
    simp only [simulateQ_bind, simulateQ_pure, pure_bind,
      QueryImpl.simulateQ_mapStateTBase_run]
    simp only [bind_pure_comp, ← StateT.run'_eq]
    unfold game3 etmGameSkeleton
    simp only [bind_pure_comp, ← StateT.run'_eq]
    refine probOutput_bind_congr' se.keygen true (fun key => ?_)
    -- Flatten the nested `StateT EtmGameState (StateT Bool ProbComp)` into a single
    -- `StateT (EtmGameState × Bool) ProbComp` (the indCPA "encrypt called" flag joins the state).
    conv_rhs => rw [StateT.run'_eq _ (none, ∅)]
    rw [← simulateQ_flattenStateT_run']
    -- Project the joint `(EtmGameState × Bool)` state back to `EtmGameState`, dropping the
    -- indCPA flag, under the invariant `flag = challenge.isSome`. The flattened reduction impl
    -- then agrees per-query with game3's impl, so the simulations coincide (impl₂ unifies with
    -- game3's oracle impl on the LHS).
    -- Forwarding helper (shared by `hinv`/`hproj`): the IND$-CPA outer impl passes a lifted
    -- `unifSpec` *computation* through unchanged (its uniform oracle is the identity; the
    -- indCPA flag is threaded).
    rw [← run'_simulateQ_eq_of_query_map_eq_inv'
          _ _ (fun s => s.2 = s.1.1.isSome) Prod.fst ?hinv ?hproj adv ((none, ∅), false) ?hs]
    case hs => rfl
    case hinv =>
      -- Each query preserves `flag = challenge.isSome`: the unif and decrypt oracles leave both
      -- `challenge` and the flag untouched; the one-time encryption query sets `challenge` to
      -- `some` and flips the indCPA flag to `true` in the same step.
      intro t s hs y hy
      obtain ⟨⟨ch, qc⟩, b⟩ := s
      simp only at hs
      subst hs
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
      · -- uniform-sampling oracle: state + flag unchanged
        have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            (liftM (OracleSpec.query n) :
              OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
            = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
          OracleComp.simulateQ_id'_liftTarget_add_liftComp _
            (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
        simp only [add_apply_inl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
          StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
          bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
          QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
          simulateQ_map, hq, StateT.run_mk, StateT.run_map, Functor.map_map, support_map,
          support_liftM, OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
          Set.image_univ] at hy
        obtain ⟨_, rfl⟩ := hy
        rfl
      · -- encryption oracle: challenge none→some sets the flag to true alongside
        have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            ((liftM ($ᵗ T : ProbComp T) :
                StateT (TagCache AD C_e T)
                  (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
            = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
          OracleComp.simulateQ_id'_liftTarget_add_liftComp _
            ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
        cases ch with
        | none =>
          simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk,
            Option.isSome_none, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
            DetSEAlg.oracleEncrypt, ↓reduceIte, map_bind, id_map, simulateQ_map, Bool.false_eq_true,
            simulateQ_pure, hqT, liftM_map, support_bind, support_uniformSample, Set.mem_univ,
            support_map, Set.image_univ, Set.iUnion_true] at hy
          obtain ⟨_, ⟨x, rfl⟩, a, rfl⟩ := hy
          rfl
        | some v =>
          simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk,
            Option.isSome_some, simulateQ_pure, map_pure, support_pure] at hy
          subst hy; rfl
      · -- decryption oracle: `verifyTag = pure false` rejects; state + flag unchanged
        cases ch with
        | none =>
          simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_none,
            reduceCtorEq, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
            support_pure] at hy
          subst hy; rfl
        | some v =>
          simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_some,
            Option.some.injEq, support_map] at hy
          split_ifs at hy <;>
            (simp only [StateT.run_map, StateT.run_set, map_pure, simulateQ_pure, StateT.run_pure,
              support_pure, Set.image_singleton] at hy
             obtain rfl := Set.eq_of_mem_singleton hy
             rfl)
    case hproj =>
      -- Per-query agreement: the flattened reduction impl, projected onto `EtmGameState`
      -- (dropping the indCPA flag), equals game3's oracle impl on states satisfying the invariant.
      intro t s hs
      obtain ⟨⟨ch, qc⟩, b⟩ := s
      simp only at hs
      subst hs
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
      · -- uniform-sampling oracle: forward the lifted sample, flag threaded unchanged
        have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            (liftM (OracleSpec.query n) :
              OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
            = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
          OracleComp.simulateQ_id'_liftTarget_add_liftComp _
            (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
        simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
          DetSEAlg.oracleUnif, gameUnifImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          hq, StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
      · -- encryption oracle: `oracleEncrypt true` samples `$ᵗ C_e` and sets the flag, matching
        -- game3's encrypt (challenge none→some); the `$ᵗ T` tag is forwarded unchanged
        have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            ((liftM ($ᵗ T : ProbComp T) :
                StateT (TagCache AD C_e T)
                  (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
            = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
          OracleComp.simulateQ_id'_liftTarget_add_liftComp _
            ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
        cases ch <;>
          simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
            DetSEAlg.oracleEncrypt, DetSEAlg.oracleUnif, QueryImpl.add_apply_inl,
            QueryImpl.add_apply_inr, hqT,
            StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
      · -- decryption oracle: `verifyTag = pure false` rejects; state and flag unchanged
        cases ch <;>
          simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, QueryImpl.add_apply_inr,
            StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
        split_ifs <;>
          simp [StateT.run_set, StateT.run_pure]
  have hg2 : Pr[= true | game2 se adv] =
      Pr[= true | DetSEAlg.securityExpFixedBit se (encReduction se adv) false] := by
    -- Step A (RO→uniform): replace game2's random-oracle tag with a fresh `$ᵗ T`. The cache is
    -- write-only (`verifyTag = pure false`) and the single encryption query hits a fresh point,
    -- so the tag is uniform; project the cache away (invariant `challenge = none → cache = ∅`).
    have stepA : Pr[= true | game2 se adv] =
        Pr[= true | (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
            (fun ke m => pure (se.encrypt ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
            (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool)] := by
      unfold game2 etmGameSkeleton
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine probOutput_bind_congr' se.keygen true (fun key => ?_)
      rw [run'_simulateQ_eq_of_query_map_eq_inv'
            _ _ (fun s => s.1 = none → s.2 = (∅ : TagCache AD C_e T))
            (fun s => (s.1, (∅ : TagCache AD C_e T))) ?hinv ?hproj adv (none, ∅) ?hs]
      case hs => intro _; rfl
      case hinv =>
        intro t s hs y hy
        obtain ⟨ch, qc⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: state unchanged, so `inv` is preserved (= `hs`)
          simp only [add_apply_inl, gameUnifImpl, QueryImpl.ofLift_eq_id', StateT.run_pure,
            liftM_pure, QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, Prod.mk.eta, beq_iff_eq, Bool.false_eq_true, ↓reduceIte,
            QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
            StateT.run_monadLift, monadLift_self, support_map, support_liftM,
            OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hy
          obtain ⟨_, rfl⟩ := hy
          exact hs
        · -- encryption oracle: challenge becomes `some`, so `inv` holds vacuously
          cases ch with
          | none =>
            have hqc : qc = (∅ : TagCache AD C_e T) := hs rfl
            subst hqc
            simp only [add_apply_inl, add_apply_inr, StateT.run_pure, liftM_pure,
              QueryImpl.withCaching_apply, uniformSampleImpl, StateT.run_bind, StateT.run_get,
              pure_bind, bind_pure_comp, Prod.mk.eta, beq_iff_eq, Bool.false_eq_true, ↓reduceIte,
              QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_monadLift,
              monadLift_self, StateT.run_modifyGet, Functor.map_map, liftM_map, bind_map_left,
              StateT.run_map, StateT.run_set, map_pure, support_map, support_uniformSample,
              Set.image_univ] at hy
            obtain ⟨a, rfl⟩ := hy
            simp
          | some v =>
            simp only [add_apply_inl, add_apply_inr, StateT.run_pure, liftM_pure,
              QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get, pure_bind,
              bind_pure_comp, Prod.mk.eta, beq_iff_eq, Bool.false_eq_true, ↓reduceIte,
              QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, support_pure] at hy
            obtain rfl := Set.eq_of_mem_singleton hy
            simp
        · -- decryption oracle: `verifyTag = pure false` rejects; state unchanged (= `hs`)
          cases ch with
          | none =>
            simp only [add_apply_inr, StateT.run_pure, liftM_pure, QueryImpl.withCaching_apply,
              StateT.run_bind, StateT.run_get, pure_bind, bind_pure_comp, Prod.mk.eta, beq_iff_eq,
              Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inr, reduceCtorEq, StateT.run_map,
              StateT.run_set, map_pure, support_pure] at hy
            obtain rfl := Set.eq_of_mem_singleton hy; exact hs
          | some v =>
            simp only [add_apply_inr, StateT.run_pure, liftM_pure, QueryImpl.withCaching_apply,
              StateT.run_bind, StateT.run_get, pure_bind, bind_pure_comp, Prod.mk.eta, beq_iff_eq,
              Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inr, Option.some.injEq] at hy
            split_ifs at hy <;>
              (obtain rfl := Set.eq_of_mem_singleton hy; exact hs)
      case hproj =>
        intro t s hs
        obtain ⟨ch, qc⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: state threaded unchanged on both sides, cache reset by proj
          simp [gameUnifImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
            StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
        · -- encryption oracle: at `ch = none` the cache is `∅` (invariant), so the random oracle
          -- query is fresh and equals `$ᵗ T`, matching the `$ᵗ T`-tag skeleton; the cache write
          -- is dropped by proj
          cases ch with
          | none =>
            have hqc : qc = (∅ : TagCache AD C_e T) := hs rfl
            subst hqc
            simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_set, StateT.run_monadLift, StateT.run_pure,
              uniformSampleImpl, Prod.map, Functor.map_map]
          | some v =>
            simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_monadLift, StateT.run_pure, Prod.map]
        · -- decryption oracle: `verifyTag = pure false` rejects; state unchanged, cache untouched
          cases ch <;>
            simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, Prod.map]
          split_ifs <;>
            simp [StateT.run_set, StateT.run_pure, Prod.map]
    -- Step B (`hg3` machinery at `b = false`): the `$ᵗ T`-tag game equals the IND$-CPA real
    -- experiment, since `oracleEncrypt false key m = se.encrypt key m` matches the game's encrypt.
    have stepB : Pr[= true | (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
            (fun ke m => pure (se.encrypt ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
            (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool)] =
        Pr[= true | DetSEAlg.securityExpFixedBit se (encReduction se adv) false] := by
      unfold DetSEAlg.securityExpFixedBit encReduction etmGameSkeleton
      simp only [simulateQ_bind, simulateQ_pure, pure_bind,
        QueryImpl.simulateQ_mapStateTBase_run]
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine probOutput_bind_congr' se.keygen true (fun key => ?_)
      conv_rhs => rw [StateT.run'_eq _ (none, ∅)]
      rw [← simulateQ_flattenStateT_run']
      rw [← run'_simulateQ_eq_of_query_map_eq_inv'
            _ _ (fun s => s.2 = s.1.1.isSome) Prod.fst ?hinv ?hproj adv ((none, ∅), false) ?hs]
      case hs => rfl
      case hinv =>
        intro t s hs y hy
        obtain ⟨⟨ch, qc⟩, b⟩ := s
        simp only at hs
        subst hs
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: state + flag unchanged
          have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              (liftM (OracleSpec.query n) :
                OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
              = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
            OracleComp.simulateQ_id'_liftTarget_add_liftComp _
              (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
          simp only [add_apply_inl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
            simulateQ_map, hq, StateT.run_mk, StateT.run_map, Functor.map_map, support_map,
            support_liftM, OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
            Set.image_univ] at hy
          obtain ⟨_, rfl⟩ := hy
          rfl
        · -- encryption oracle: challenge none→some sets the flag to true alongside
          have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              ((liftM ($ᵗ T : ProbComp T) :
                  StateT (TagCache AD C_e T)
                    (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
              = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
            OracleComp.simulateQ_id'_liftTarget_add_liftComp _
              ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
          cases ch with
          | none =>
            simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif,
              QueryImpl.ofLift_eq_id', StateT.run_bind, StateT.run_monadLift, monadLift_self,
              bind_pure_comp, bind_map_left, liftM_bind, bind_assoc, Prod.mk.eta, beq_iff_eq,
              StateT.run_pure, liftM_pure, ite_self, pure_bind, QueryImpl.add_apply_inl,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_none,
              StateT.run_map, StateT.run_set, map_pure, Functor.map_map, simulateQ_bind,
              simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
              DetSEAlg.oracleEncrypt, Bool.false_eq_true, ↓reduceIte, map_bind, id_map,
              simulateQ_map, simulateQ_pure, hqT, liftM_map, support_map, support_uniformSample,
              Set.image_univ] at hy
            obtain ⟨a, rfl⟩ := hy
            rfl
          | some v =>
            simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif,
              QueryImpl.ofLift_eq_id', StateT.run_bind, StateT.run_monadLift, monadLift_self,
              bind_pure_comp, bind_map_left, liftM_bind, bind_assoc, Prod.mk.eta, beq_iff_eq,
              StateT.run_pure, liftM_pure, ite_self, pure_bind, QueryImpl.add_apply_inl,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_some,
              simulateQ_pure, map_pure, support_pure] at hy
            obtain rfl := Set.eq_of_mem_singleton hy; rfl
        · -- decryption oracle: `verifyTag = pure false` rejects; state + flag unchanged
          cases ch with
          | none =>
            simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
              DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
              StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
              bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_none,
              reduceCtorEq, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
              support_pure] at hy
            subst hy; rfl
          | some v =>
            simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
              DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
              StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
              bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_some,
              Option.some.injEq, support_map] at hy
            split_ifs at hy <;>
              (simp only [StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
                  StateT.run_pure, support_pure, Set.image_singleton] at hy
               obtain rfl := Set.eq_of_mem_singleton hy
               rfl)
      case hproj =>
        intro t s hs
        obtain ⟨⟨ch, qc⟩, b⟩ := s
        simp only at hs
        subst hs
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: forward the lifted sample, flag threaded unchanged
          have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              (liftM (OracleSpec.query n) :
                OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
              = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
            OracleComp.simulateQ_id'_liftTarget_add_liftComp _
              (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
          simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
            DetSEAlg.oracleUnif, gameUnifImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
            hq, StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
        · -- encryption oracle: `oracleEncrypt false key m = se.encrypt key m` matches the game;
          -- the `$ᵗ T` tag is forwarded unchanged
          have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              ((liftM ($ᵗ T : ProbComp T) :
                  StateT (TagCache AD C_e T)
                    (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
              = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
            OracleComp.simulateQ_id'_liftTarget_add_liftComp _
              ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
          cases ch <;>
            simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
              DetSEAlg.oracleEncrypt, DetSEAlg.oracleUnif, QueryImpl.add_apply_inl,
              QueryImpl.add_apply_inr, hqT, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
        · -- decryption oracle: `verifyTag = pure false` rejects; state and flag unchanged
          cases ch <;>
            simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, QueryImpl.add_apply_inr,
              StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
          split_ifs <;>
            simp [StateT.run_set, StateT.run_pure]
    rw [stepA, stepB]
  unfold DetSEAlg.distAdvantage
  rw [hg2, hg3]
  exact le_of_eq (abs_sub_comm _ _)

