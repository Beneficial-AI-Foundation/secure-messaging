/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.Games
import ToVCVio.OracleComp.SimSemantics.StateT.LazyKey

/-!
# Encrypt-then-MAC — one-time secrecy hop (`game2` → `game3`)

`game2_game3_le_enc`: the gap is bounded by the one-time secrecy advantage of `encReduction`.
-/

namespace EtM

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [LenSampleable C_e] [SampleableType T]

/-- EtM game whose skeleton key slot is `()` and whose encryption answers with `enc m`. With
`enc = DetSEAlg.oracleEncrypt se b`, it samples the cipher key inside the encryption query. -/
private noncomputable def lazyKeyGame (enc : M → ProbComp C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    (pure ()) (fun _ _ => none) ∅
    (fun _ m => liftM (enc m))
    (fun _ => liftM ($ᵗ T : ProbComp T))
    (fun _ _ => pure false)
    gameUnifImpl
    adv

omit [Inhabited C_e] [Inhabited T] in
/-- The one-time secrecy experiment of `encReduction` is the lazy-key game: the experiment
answers the reduction's encryption query with `oracleEncrypt se b`. -/
private theorem securityExpFixedBit_encReduction (se : DetSEAlg K_e M C_e) (b : Bool)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    DetSEAlg.securityExpFixedBit se (encReduction se adv) b =
      lazyKeyGame (DetSEAlg.oracleEncrypt se b) adv := by
  unfold DetSEAlg.securityExpFixedBit encReduction lazyKeyGame etmGameSkeleton
  simp only [pure_bind, bind_pure_comp, ← StateT.run'_eq,
    QueryImpl.simulateQ_mapStateTBase_run']
  refine run'_simulateQ_eq_of_query_map_eq_inv' _ _ (fun _ => True) id
    (fun _ _ _ _ _ => trivial) ?_ adv _ trivial
  intro t s _
  rw [Prod.map_id, id_map]
  obtain ⟨ch, qc⟩ := s
  have hT0 : simulateQ (DetSEAlg.otsImpl se b)
      ((liftM ($ᵗ T : ProbComp T) :
        StateT (TagCache AD C_e T) (OracleComp (DetSEAlg.otsSpec M C_e)) T).run qc) =
        (fun x => (x, qc)) <$> ($ᵗ T : ProbComp T) := by
    have hrun : (liftM ($ᵗ T : ProbComp T) :
        StateT (TagCache AD C_e T) (OracleComp (DetSEAlg.otsSpec M C_e)) T).run qc =
          (liftM ((fun x => (x, qc)) <$> ($ᵗ T : ProbComp T)) :
            OracleComp (DetSEAlg.otsSpec M C_e) (T × TagCache AD C_e T)) := by
      change (liftM (liftM ($ᵗ T : ProbComp T) : StateT (TagCache AD C_e T) ProbComp T) :
        StateT (TagCache AD C_e T) (OracleComp (DetSEAlg.otsSpec M C_e)) T).run qc = _
      simp only [liftM_StateT_eq, StateT.run_monadLift, monadLift_self, bind_pure_comp,
          map_eq_bind_pure_comp, liftM_bind, Function.comp_apply, liftM_pure, StateT.run_mk]
    rw [hrun, DetSEAlg.otsImpl, QueryImpl.simulateQ_add_liftM_left, DetSEAlg.oracleUnif,
      QueryImpl.simulateQ_toQueryImpl]
  have hT : simulateQ (HasQuery.toQueryImpl + DetSEAlg.oracleEncrypt se b)
      ((monadLift ($ᵗ T : ProbComp T) :
        StateT (TagCache AD C_e T) (OracleComp (DetSEAlg.otsSpec M C_e)) T).run qc) =
        (fun x => (x, qc)) <$> ($ᵗ T : ProbComp T) := hT0
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩ <;> cases ch <;>
    simp only [add_apply_inl, QueryImpl.mapStateTBase, DetSEAlg.otsImpl, DetSEAlg.oracleUnif,
        ToVCVio.unifLiftStateT, liftM, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        liftM_map, bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self,
        pure_bind, QueryImpl.add_apply_inl, PFunctor.Handler.liftTarget_apply,
        ofPFunctor_toPFunctor, QueryImpl.ofLift_apply, simulateQ_map,
        QueryImpl.simulateQ_add_liftM_query_left, HasQuery.toQueryImpl_apply,
        HasQuery.instOfMonadLift_query, StateT.run_mk, gameUnifImpl, QueryImpl.ofLift_eq_id',
        QueryImpl.id'_apply, id_eq, add_apply_inr, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, StateT.run_map, StateT.run_set, map_pure, Functor.map_map, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, hT,
        simulateQ_pure] <;>
    (try split_ifs) <;>
    simp only [StateT.run_pure, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure]

omit [Inhabited C_e] [Inhabited T] [LenSampleable C_e] in
/-- Let `X k m` encrypt `m` under the cipher key `k`. Then the EtM game that samples `k` before
the adversary runs, and rejects every decryption query, has the same output distribution as
the lazy-key game that samples `k` inside the encryption query. -/
private theorem keyFirst_evalDistEq_lazyKeyGame (se : DetSEAlg K_e M C_e)
    (X : K_e → M → ProbComp C_e) (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
        (fun ke m => liftM (X ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
        (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool) =ᵈ
      lazyKeyGame (fun m => do let k ← se.keygen; X k m) adv := by
  unfold lazyKeyGame etmGameSkeleton
  simp only [pure_bind, ← bind_assoc]
  refine EvalDistEq.bind_left (keygen_bind_run_simulateQ_evalDistEq se.keygen _ _
    (fun s => s.1 = none) ?_ ?_ ?_ adv (none, ∅) rfl) _
  · intro t s hs
    obtain ⟨ch, qc⟩ := s
    simp only at hs
    subst hs
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
    · refine Or.inl ⟨fun _ => rfl, fun y hy => ?_⟩
      simp only [add_apply_inl, gameUnifImpl, liftM_bind, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_pure_comp, bind_map_left, liftM_map, bind_assoc, Prod.mk.eta,
          beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind, QueryImpl.add_apply_inl,
          PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.ofLift_apply,
          MonadAttach.support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
          Set.range_id, Set.image_univ, Set.mem_range] at hy
      obtain ⟨_, rfl⟩ := hy
      rfl
    · refine Or.inr ⟨?_, fun k y hy => ?_⟩
      · simp only [add_apply_inl, add_apply_inr, StateT.run_monadLift, monadLift_self,
          bind_pure_comp, liftM_map, bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure,
          liftM_pure, pure_bind, Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inl,
          QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
          map_pure, Functor.map_map, bind_assoc, liftM_bind, ite_self]
        exact EvalDistEq.rfl
      · simp only [add_apply_inl, add_apply_inr, StateT.run_monadLift, monadLift_self,
          bind_pure_comp, liftM_map, bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure,
          liftM_pure, pure_bind, Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inl,
          QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
          map_pure, Functor.map_map, MonadAttach.support_bind, MonadAttach.mem_support,
          MonadAttach.support_map, support_uniformSample, Set.image_univ, Set.mem_iUnion,
          Set.mem_range, exists_prop] at hy
        obtain ⟨_, _, _, rfl⟩ := hy
        simp only [reduceCtorEq, not_false_eq_true]
    · refine Or.inl ⟨fun _ => by simp only [add_apply_inr, StateT.run_monadLift, monadLift_self,
        bind_pure_comp, liftM_map, bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure,
        liftM_pure, pure_bind, Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, reduceCtorEq, StateT.run_map, StateT.run_set, map_pure,
        liftM_bind, bind_assoc, ite_self], fun y hy => ?_⟩
      simp only [add_apply_inr, liftM_bind, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          bind_pure_comp, bind_map_left, liftM_map, bind_assoc, Prod.mk.eta, beq_iff_eq,
          StateT.run_pure, liftM_pure, ite_self, pure_bind, QueryImpl.add_apply_inr, StateT.run_get,
          reduceCtorEq, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure,
          MonadAttach.support_pure, Set.mem_singleton_iff] at hy
      obtain rfl := hy
      rfl
  · intro t s k hs
    obtain ⟨ch, qc⟩ := s
    obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.mp hs
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
    · rfl
    · simp only [add_apply_inl, add_apply_inr, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        liftM_map, bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, pure_bind,
        Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, liftM_bind, bind_assoc, ite_self]
    · simp only [add_apply_inr, StateT.run_monadLift, monadLift_self, bind_pure_comp, liftM_map,
        bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, pure_bind,
        Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
        Option.some.injEq, liftM_bind, bind_assoc, ite_self]
  · intro t s k hs y hy
    obtain ⟨ch, qc⟩ := s
    obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.mp hs
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
    · simp only [add_apply_inl, gameUnifImpl, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        liftM_map, bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, pure_bind,
        Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inl, PFunctor.Handler.liftTarget_apply,
        ofPFunctor_toPFunctor, QueryImpl.ofLift_apply, MonadAttach.support_map, support_liftM,
        OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ,
        Set.mem_range] at hy
      obtain ⟨_, rfl⟩ := hy
      simp only [reduceCtorEq, not_false_eq_true]
    · simp only [add_apply_inl, add_apply_inr, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        liftM_map, bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, pure_bind,
        Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, MonadAttach.support_pure, Set.mem_singleton_iff] at hy
      obtain rfl := hy
      simp only [reduceCtorEq, not_false_eq_true]
    · simp only [add_apply_inr, StateT.run_monadLift, monadLift_self, bind_pure_comp, liftM_map,
        bind_map_left, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, pure_bind,
        Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
        Option.some.injEq, MonadAttach.mem_support] at hy
      split_ifs at hy <;> (obtain rfl := hy; simp only [reduceCtorEq, not_false_eq_true])

omit [Inhabited C_e] [Inhabited T] [LenSampleable C_e] in
/-- Probability form of `keyFirst_evalDistEq_lazyKeyGame`. -/
private theorem prEvent_keyFirst_eq_lazyKeyGame (se : DetSEAlg K_e M C_e)
    (X : K_e → M → ProbComp C_e) (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    Pr{let x ← (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
        (fun ke m => liftM (X ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
        (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool)}[x = true] =
      Pr{let x ← lazyKeyGame (fun m => do let k ← se.keygen; X k m) adv}[x = true] :=
  (keyFirst_evalDistEq_lazyKeyGame se X adv).prEvent_eq _

omit [Inhabited C_e] [Inhabited T] in
theorem game2_game3_le_enc
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    |(Pr{let x ← game2 se adv}[x = true]).toReal -
     (Pr{let x ← game3 se adv}[x = true]).toReal| ≤
      DetSEAlg.distAdvantage se (encReduction se adv) := by
  -- NRS14 Lemma 3, privacy reduction D₁(A).
  -- `game2` and `game3` sample the cipher key before the adversary runs, and the one-time
  -- secrecy experiment of `encReduction` samples it inside the encryption query. Both games
  -- reject every decryption query and answer at most one encryption query, so the key is read
  -- once, and `prEvent_keyFirst_eq_lazyKeyGame` moves its sample into that query. The result is
  -- the lazy-key game, which `securityExpFixedBit_encReduction` identifies with the experiment.
  -- `game2` first needs its random-oracle tag replaced by a uniform one (`stepA`).
  have hg3 : Pr{let x ← game3 se adv}[x = true] =
      Pr{let x ← DetSEAlg.securityExpFixedBit se (encReduction se adv) true}[x = true] := by
    rw [securityExpFixedBit_encReduction]
    exact prEvent_keyFirst_eq_lazyKeyGame se
      (fun k m => LenSampleable.unifSameLen (se.encrypt k m)) adv
  have hg2 : Pr{let x ← game2 se adv}[x = true] =
      Pr{let x ← DetSEAlg.securityExpFixedBit se (encReduction se adv) false}[x = true] := by
    -- Step A (RO→uniform): replace game2's random-oracle tag with a fresh `$ᵗ T`. The cache is
    -- write-only (`verifyTag = pure false`) and the single encryption query hits a fresh point,
    -- so the tag is uniform; project the cache away (invariant `challenge = none → cache = ∅`).
    have stepA : Pr{let x ← game2 se adv}[x = true] =
        Pr{let x ← (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
            (fun ke m => pure (se.encrypt ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
            (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool)}[x = true] := by
      unfold game2 etmGameSkeleton
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine prEvent_bind_congr se.keygen _ _ _ _ (fun key => ?_)
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
              monadLift_self, Functor.map_map, StateT.run_map, StateT.run_set, map_pure,
              support_map] at hy
            obtain ⟨a, _, rfl⟩ := hy
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
          simp [gameUnifImpl, QueryImpl.add_apply_inl,
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
    -- Step B: move the key sample into the encryption query, as for `hg3`.
    have stepB : Pr{let x ← (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
            (fun ke m => pure (se.encrypt ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
            (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool)}[x = true] =
        Pr{let x ← DetSEAlg.securityExpFixedBit se (encReduction se adv) false}[x = true] := by
      rw [securityExpFixedBit_encReduction]
      exact prEvent_keyFirst_eq_lazyKeyGame se (fun k m => pure (se.encrypt k m)) adv
    rw [stepA, stepB]
  unfold DetSEAlg.distAdvantage
  rw [hg2, hg3]
  exact le_of_eq (abs_sub_comm _ _)

end EtM
