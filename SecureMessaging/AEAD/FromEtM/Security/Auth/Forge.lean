/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.Auth.Defs
import ToVCVio.ProgramLogic.Relational.IdenticalUntilBad

/-!
# Encrypt-then-MAC — auth hop: forge-probability bound

The `game2' = game2` discard step and the chain bounding the instrumented bad-flag probability
by the forge reduction (`tvDist_authInst_le_probForge`, `probForge_authInst_le_forgeReduction`,
`forgeReduction_isQueryBoundP`).
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Step C of the auth hop: `game2'` (verify queries the RO then rejects unconditionally)
has the same output distribution as `game2` (rejects directly). The discarded verify RO query
reveals nothing, so removing it preserves the distribution
(`etmAEAD.evalDist_simulateQ_run'_discardRO`, the RO-mediated discarded-query brick), lifted
through the skeleton. -/
theorem game2'_eq_game2
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) :
    Pr[= true | game2' se adv] = Pr[= true | game2 se adv] := by
  -- Fold the skeleton tail `let (b', _) ← run; return b'` to `run'`.
  -- Both games: `se.keygen` then the per-key skeleton run; descend through keygen.
  unfold game2' game2 etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq]
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  -- Per key: the two interpreters differ only in `decImpl`'s `verifyTag` — `game2'` makes a
  -- discarded random-oracle query at `(ad, c)` before rejecting, `game2` rejects directly.
  -- Reduce the `Pr` equality to a `𝒟` equality and apply the generic discarded-query brick.
  rw [probOutput_def, probOutput_def]
  refine congrFun (congrArg DFunLike.coe ?_) true
  refine etmAEAD.evalDist_simulateQ_run'_discardRO
    (D := AD × C_e) (R := T) _ _ ?h₁ ?hstep adv none ∅
  case h₁ =>
    -- `game2`'s interpreter respects the RO: the only cache access is `computeTag = randomOracle`
    -- inside `encrypt`; `verifyTag = pure false` and the unif oracle never touch the cache.
    -- Exhibit the body `B` that recomputes each oracle's response/state as an `OracleComp` over
    -- `unifSpec + ((AD × C_e) →ₒ T)` (uniform sampling for unif, an RO query for the challenge
    -- tag, pure transitions everywhere else).
    refine ⟨fun t s => ?_, fun t s qc => ?_⟩
    · -- The body `B t s`.
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
      · -- unif: forward a uniform sample, state unchanged.
        exact (do
          let u ← liftM ((unifSpec + ((AD × C_e) →ₒ T)).query (Sum.inl n))
          pure (u, s))
      · -- encrypt: if challenge set return none; else encrypt + RO-tag, set challenge.
        exact (match s with
          | some _ => pure (none, s)
          | none => do
            let t' ← liftM ((unifSpec + ((AD × C_e) →ₒ T)).query
              (Sum.inr (ad, se.encrypt ke m)))
            pure (some (se.encrypt ke m, t'), some (se.encrypt ke m, t')))
      · -- decrypt: reject unconditionally (`verifyTag = pure false`), state unchanged.
        exact pure (none, s)
    · -- The body matches the first interpreter's run, reshaped.
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
      · -- unif: both sides forward a uniform sample, cache + challenge unchanged.
        simp only [QueryImpl.add_apply_inl, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, simulateQ_pure, StateT.run_pure]
        rw [show ((etmAEAD.roImpl (AD × C_e) T) (Sum.inl n)).run qc =
              (fun u => (u, qc)) <$> (liftM (OracleSpec.query (spec := unifSpec) n) :
                ProbComp ((unifSpec + ((AD × C_e) →ₒ T)).Range (Sum.inl n))) from by
            rw [etmAEAD.roImpl, QueryImpl.add_apply_inl]; unfold unifFwdImpl
            rw [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl]
            simp [StateT.run_monadLift, bind_pure_comp, HasQuery.query]]
        unfold gameUnifImpl
        simp only [QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
          bind_pure_comp, Functor.map_map]
        erw [OracleComp.liftM_run_StateT]
        simp only [bind_pure_comp]
        rfl
      · -- encrypt: case on whether the challenge is already set.
        cases s <;>
          simp [etmAEAD.roImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
            StateT.run_bind, StateT.run_get,
            StateT.run_set, StateT.run_pure, map_bind, Functor.map_map]
      · -- decrypt: reject unconditionally; case on the challenge guard, both reject identically.
        by_cases hg : s = some (c, tg) <;>
          simp [etmAEAD.roImpl, QueryImpl.add_apply_inr,
            StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, map_pure,
            beq_iff_eq, hg]
  case hstep =>
    -- Per-query disjunction over the adversary spec sum `(unif + encrypt) + decrypt`.
    intro t s qc
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
    · -- uniform-sampling oracle: identical handlers (left disjunct)
      left; rfl
    · -- encryption oracle: identical handlers (`computeTag`/`encryptMsg` unchanged)
      left
      cases s <;>
        simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure]
    · -- decryption oracle: `verifyTag` differs. On the challenge guard both reject without a
      -- query (left disjunct); otherwise `game2'` prepends a discarded RO query at `(ad, c)`
      -- (right disjunct).
      by_cases hg : s = some (c, tg)
      · left
        simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_pure,
          beq_iff_eq, hg]
      · right
        refine ⟨(ad, c), ?_⟩
        simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_set,
          StateT.run_pure, beq_iff_eq, hg, map_bind, Functor.map_map]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Per-key identical-until-bad bound (auth hop, brick 3): the flag-instrumented `b = true`
and `b = false` simulations agree on every non-forged transition (they differ only in the
verify return when `ok = true`, which also sets the monotone `forged` flag), so the per-key TV
distance between them is at most the forge probability of the `b = true` simulation
(the generic `tvDist_simulateQ_le_probEvent_output_bad_base` at `spec₂ := unifSpec`). -/
theorem tvDist_authInst_le_probForge
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) (ke : K_e) :
    tvDist ((simulateQ (authInstImpl se true ke) adv).run' ((none, ∅), false))
        ((simulateQ (authInstImpl se false ke) adv).run' ((none, ∅), false)) ≤
      (Pr[fun z : Bool × (EtmGameState AD C_e T × Bool) => z.2.2 = true |
          (simulateQ (authInstImpl se true ke) adv).run ((none, ∅), false)]).toReal := by
  -- Bad-flag monotonicity: the flag is only ever replaced by `forged` or `forged || ok`,
  -- so once `true` it stays `true`, for both `b = true` and `b = false`.
  have hmono : ∀ (b : Bool) (t : (aeadOneTimeCCASpec AD M (C_e × T)).Domain)
      (p : EtmGameState AD C_e T × Bool), p.2 = true →
      ∀ z ∈ support ((authInstImpl se b ke t).run p), z.2.2 = true := by
    intro b t p hp z hz
    obtain ⟨⟨ch, qc⟩, fl⟩ := p
    simp only at hp; subst hp
    -- In every branch the output state's flag is `true` (threaded `forged`, or `forged || ok`
    -- with `forged = true`), so the support membership pins `z` to a tuple with `z.2.2 = true`.
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
    · -- uniform-sampling oracle: state (hence flag) threaded unchanged
      simp only [add_apply_inl, authInstImpl, authUnifImpl, QueryImpl.ofLift_eq_id',
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, support_map, support_liftM,
        OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hz
      obtain ⟨a, rfl⟩ := hz; rfl
    · -- encryption oracle: flag written back unchanged (`forged = true`)
      simp only [authInstImpl, authEncImpl, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr] at hz
      cases ch with
      | none =>
        simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, bind_pure_comp, StateT.run_monadLift, monadLift_self,
          StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map] at hz
        obtain ⟨a, _, rfl⟩ := hz; rfl
      | some val =>
        simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, bind_pure_comp, StateT.run_pure, support_pure] at hz
        obtain rfl := hz; rfl
    · -- decryption oracle: flag becomes `forged || ok = true`
      simp only [authInstImpl, authDecImpl, QueryImpl.add_apply_inr] at hz
      cases ch with
      | none =>
        simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, ← apply_ite, bind_pure_comp, reduceCtorEq, ↓reduceIte,
          Bool.true_or, StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_set,
          map_pure, Functor.map_map, support_map] at hz
        obtain ⟨a, _, rfl⟩ := hz; rfl
      | some val =>
        by_cases hguard : val = (c, tg)
        · simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
            StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure, support_pure] at hz
          obtain rfl := hz; rfl
        · simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
            StateT.run_get, pure_bind, ← apply_ite, bind_pure_comp, Option.some.injEq, hguard,
            ↓reduceIte, Bool.true_or, StateT.run_monadLift, monadLift_self, StateT.run_map,
            StateT.run_set, map_pure, Functor.map_map, support_map] at hz
          obtain ⟨a, _, rfl⟩ := hz; rfl
  -- Agreement off the bad step: the `b = true`/`b = false` impls differ only in the
  -- decrypt return on `ok = true`, which also sets the flag to `true`. So for outputs with
  -- flag `false` the two impls have equal probability (unif/encrypt: `b` unused; decrypt:
  -- the `ok = true` branch yields flag `true`, excluded; the `ok = false` branch returns
  -- `none` regardless of `b`).
  have hagree : ∀ (t : (aeadOneTimeCCASpec AD M (C_e × T)).Domain)
      (s : EtmGameState AD C_e T) (u : (aeadOneTimeCCASpec AD M (C_e × T)).Range t)
      (s' : EtmGameState AD C_e T),
      Pr[= (u, (s', false)) | (authInstImpl se true ke t).run (s, false)] =
        Pr[= (u, (s', false)) | (authInstImpl se false ke t).run (s, false)] := by
    intro t s u s'
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
    · -- uniform-sampling oracle: `b` unused, impls identical at this index
      simp [authInstImpl, QueryImpl.add_apply_inl]
    · -- encryption oracle: `b` unused, impls identical at this index
      simp [authInstImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    · -- decryption oracle
      obtain ⟨ch, qc⟩ := s
      simp only [authInstImpl, QueryImpl.add_apply_inr, authDecImpl]
      by_cases hg : ch = some (c, tg)
      · -- challenge-guard rejects: `pure none`, `b` unused
        simp [hg, StateT.run_bind, StateT.run_get, StateT.run_pure]
      · -- verify: equal probability per random-oracle sample
        simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, ↓reduceIte, hg, Bool.false_or, StateT.run_monadLift,
          monadLift_self, bind_pure_comp, StateT.run_set, bind_map_left, Bool.false_eq_true,
          ite_self, StateT.run_map, map_pure, Functor.map_map]
        refine probOutput_bind_congr' _ _ fun p => ?_
        obtain ⟨t', qc'⟩ := p
        -- `tg = t'` (forged): both outputs have flag `true` ≠ target flag `false` → both 0;
        -- `tg ≠ t'` (reject): output `none` regardless of `b`.
        by_cases hok : tg = t' <;>
          simp [hok, ← OracleComp.pure_def, probOutput_pure_eq_indicator,
            Set.mem_singleton_iff, Prod.ext_iff]
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_output_bad_base
    (authInstImpl se true ke) (authInstImpl se false ke) adv (none, ∅)
    hagree (hmono true) (hmono false)

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Per-key forge-probability collapse (auth hop, the heaviest sub-proof): the per-key game's
forge probability (the `b = true` simulation's `forged` flag) is at most the `forged`
probability of the eval+verify lazy-RO forge experiment run on `forgeReduction`. The proof
collapses the nested forge `simulateQ` to the single combined handler `forgeJointImpl` over the
same adversary `adv`, then applies the generic coupling lemma
`OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_simulateQ_run` with a joint-state
invariant (NRS14 App. A.2). -/
theorem probForge_authInst_le_forgeReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) (ke : K_e) :
    (Pr[fun z : Bool × (EtmGameState AD C_e T × Bool) => z.2.2 = true |
        (simulateQ (authInstImpl se true ke) adv).run ((none, ∅), false)]).toReal ≤
      (Pr[fun z : Unit × etmAEAD.ForgeState (AD × C_e) T => z.2.2.2 = true |
          (simulateQ etmAEAD.forgeImpl (forgeReduction se adv ke)).run
            (∅, ∅, false)]).toReal := by
  -- The proof relates the two experiments at the ENNReal level (`.toReal` is monotone on
  -- the relevant non-⊤ probabilities), then collapses the nested forge `simulateQ` to a
  -- single combined handler over the SAME adversary `adv`, and finally applies the generic
  -- coupling lemma `probEvent_le_of_relTriple_simulateQ_run` with a joint-state invariant.
  --
  -- Combined RHS handler: the AEAD oracles forwarded into the joint state
  -- `EtmGameState × ForgeState` (the `simulateQ`-collapse target for the forge run).
  set impl₂ :
      QueryImpl (aeadOneTimeCCASpec AD M (C_e × T))
        (StateT (EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T) ProbComp) :=
    forgeJointImpl se ke with himpl₂
  -- Joint-state invariant coupling the instrumented-game state `(EtmGameState × Bool)` with
  -- the combined RHS state `(EtmGameState × ForgeState)`: the challenge slot and the lazy-RO
  -- cache agree, the set of eval'd points is contained in the challenge ciphertext, the RO
  -- maps the challenge point to the challenge tag, and the game's bad flag implies the
  -- forge `forged` flag.
  set R_state :
      (EtmGameState AD C_e T × Bool) →
        (EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T) → Prop :=
    fun s₁ s₂ =>
      -- challenge agrees
      s₁.1.1 = s₂.1.1 ∧
      -- RO cache agrees (game's TagCache = forge's RO cache)
      s₁.1.2 = s₂.2.1 ∧
      -- eval'd points ⊆ challenge ciphertext (with matching RO value)
      (∀ p ∈ s₂.2.2.1, ∃ c t, s₂.1.1 = some (c, t) ∧ p = (Prod.fst p, c) ∧
          s₂.2.1 (Prod.fst p, c) = some t) ∧
      -- game bad flag ⟹ forge forged flag
      (s₁.2 = true → s₂.2.2.2 = true)
    with hR_state
  -- ENNReal-level event inequality, then transport to `.toReal`.
  refine ENNReal.toReal_mono ?hne ?hle
  case hne =>
    exact ne_top_of_le_ne_top one_ne_top probEvent_le_one
  case hle =>
    -- (i) Reduction collapse: rewrite the forge run as a `simulateQ impl₂ adv` run.
    have hRHScollapse :
        Pr[fun z : Unit × etmAEAD.ForgeState (AD × C_e) T => z.2.2.2 = true |
            (simulateQ etmAEAD.forgeImpl (forgeReduction se adv ke)).run (∅, ∅, false)] =
          Pr[fun z : Bool × (EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T) =>
                z.2.2.2.2 = true |
            (simulateQ impl₂ adv).run ((none, ∅), (∅, ∅, false))] := by
      -- Mechanical nested-`simulateQ` collapse: `forgeReduction = const () <$> skeleton`,
      -- the skeleton ends `let (b',_) ← (simulateQ inner adv).run (none,∅); return b'`, and
      -- `simulateQ forgeImpl ((simulateQ inner adv).run s)` flattens to
      -- `simulateQ ((forgeImpl.mapStateTBase inner).flattenStateT) adv` via
      -- `simulateQ_mapStateTBase_run` + `simulateQ_flattenStateT_run` (cf. `hideal`).
      -- The forge event `z.2.2.2` on `Unit × ForgeState` matches `z.2.2.2.2` on the joint
      -- output `Bool × (EtmGameState × ForgeState)` after reassociating the states.
      -- `hflat` proves the flattened collapsed handler equals `forgeJointImpl` per query
      -- (unif/encrypt/decrypt forward to the corresponding `forgeImpl` summand); the event
      -- composition then reindexes definitionally to the joint `forged` flag.
      unfold forgeReduction etmGameSkeleton
      simp only [pure_bind, simulateQ_map, StateT.run_map, probEvent_map,
        Function.const, StateT.run_bind, StateT.run_pure,
        bind_pure_comp]
      rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
      -- The flattened collapsed handler equals the hand-written joint handler
      -- `forgeJointImpl`.
      rw [show (etmAEAD.forgeImpl.mapStateTBase _).flattenStateT
            = forgeJointImpl se ke from ?hflat,
        ← himpl₂, probEvent_map]
      case hflat =>
        funext t
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
        · -- unif oracle: both handlers forward `query n` to the same lifted uniform sample
          have hufwd : simulateQ etmAEAD.forgeImpl
              (liftM (OracleSpec.query n) :
                OracleComp (etmAEAD.forgeSpec (AD × C_e) T) (unifSpec.Range n))
              = etmAEAD.forgeUnifImpl n := by
            have hq : (liftM (OracleSpec.query n) :
                  OracleComp (etmAEAD.forgeSpec (AD × C_e) T) (unifSpec.Range n))
                = (OracleSpec.query (spec := etmAEAD.forgeSpec (AD × C_e) T)
                    (Sum.inl (Sum.inl n))) := rfl
            rw [hq]
            simp [etmAEAD.forgeImpl, QueryImpl.add_apply_inl]
          ext ⟨eg, fs⟩ : 2
          simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
            forgeJointImpl,
            StateT.run_monadLift, StateT.run_mk,
                  
            bind_pure_comp, Functor.map_map,
            monadLift_self]
          erw [OracleComp.liftM_run_StateT, OracleComp.liftM_run_StateT]
          rw [simulateQ_bind]
          erw [hufwd]
          simp only [simulateQ_pure, etmAEAD.forgeUnifImpl, QueryImpl.liftTarget_apply,
            QueryImpl.ofLift_apply, StateT.run_bind, StateT.run_pure,
            bind_assoc, pure_bind,
            ← bind_pure_comp]
          erw [OracleComp.liftM_run_StateT]
          simp only [Functor.map_map, bind_pure_comp,
            ]
        · -- encrypt oracle: forwards the tag query to the shared eval RO, records challenge
          have hefwd : ∀ q : AD × C_e, simulateQ etmAEAD.forgeImpl
              (liftM (OracleSpec.query (spec := etmAEAD.forgeSpec (AD × C_e) T)
                  (Sum.inl (Sum.inr q))) :
                OracleComp (etmAEAD.forgeSpec (AD × C_e) T) T)
              = etmAEAD.evalRO q := by
            intro q
            simp [etmAEAD.forgeImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
          ext ⟨⟨ch, qc⟩, fs⟩ : 2
          rw [flattenStateT_mapStateTBase_apply_run]
          cases ch <;>
            simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, forgeJointImpl,
              StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, simulateQ_map,
              simulateQ_pure, hefwd, etmAEAD.evalRO, bind_pure_comp, map_bind,
              Functor.map_map, pure_bind]
        · -- decrypt oracle: forwards the verify query to the shared verify RO
          have hvfwd : ∀ p : (AD × C_e) × T, simulateQ etmAEAD.forgeImpl
              (liftM (OracleSpec.query (spec := etmAEAD.forgeSpec (AD × C_e) T)
                  (Sum.inr p)) :
                OracleComp (etmAEAD.forgeSpec (AD × C_e) T) Bool)
              = etmAEAD.verifyAgainstRO p := by
            intro p
            simp [etmAEAD.forgeImpl, QueryImpl.add_apply_inr]
          ext ⟨⟨ch, qc⟩, fs⟩ : 2
          rw [flattenStateT_mapStateTBase_apply_run]
          by_cases heq : ch = some (c, tg)
          · simp [heq, QueryImpl.add_apply_inr, forgeJointImpl,
              StateT.run_bind, StateT.run_get,
              StateT.run_monadLift, StateT.run_pure,
              simulateQ_pure, bind_pure_comp, Functor.map_map,
              pure_bind]
          · simp only [add_apply_inr, liftM_pure, Prod.mk.eta, StateT.run_monadLift,
              monadLift_self, bind_pure_comp, Functor.map_map, liftM_map, bind_map_left, pure_bind,
              beq_iff_eq, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, heq,
              ↓reduceIte, StateT.run_set, simulateQ_bind, hvfwd, etmAEAD.verifyAgainstRO,
              QueryImpl.withCaching_apply, decide_not, bind_assoc, map_bind, forgeJointImpl,
              QueryImpl.ofLift_eq_id']
            refine bind_congr fun a => ?_
            by_cases hok : tg = a.1 <;>
              simp [hok, StateT.run_pure, simulateQ_pure,
                ]
      -- The composed event reindexes to the forge `forged` flag on the joint output.
      rfl
    rw [hRHScollapse]
    -- (ii) Coupling lemma: the game's flag (`z.2.2 = true`) implies the forge flag
    -- (`z.2.2.2.2 = true`) under `R_state`, which is preserved per-query.
    refine OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_simulateQ_run
      (authInstImpl se true ke) impl₂ R_state adv ?himpl
      ((none, ∅), false) ((none, ∅), (∅, ∅, false)) ?hs
      (p := fun z => z.2.2 = true)
      (q := fun z => z.2.2.2.2 = true)
      ?himp
    case hs =>
      -- initial states are related: challenges/caches both empty, no eval'd points, flags off
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro p hp; simp at hp
      · intro h; exact absurd h (by simp)
    case himp =>
      -- flag implication is the last conjunct of `R_state` (output equality is unused here)
      intro _z₁ _z₂ _heq hR hflag; exact hR.2.2.2 hflag
    case himpl =>
      -- Per-query relational correspondence: each AEAD oracle, run under the instrumented
      -- game handler and under the combined forge handler from `R_state`-related states,
      -- produces equal output bits and `R_state`-related successor states. The unif oracle
      -- threads both states unchanged; encrypt forwards the tag query to the shared RO and
      -- records the challenge as the unique eval'd point (re-establishing `evald ⊆ challenge`
      -- and `ρ(challenge)=tag`); decrypt forwards the verify to the shared RO — on a
      -- non-challenge `ok` it sets the game flag and, since `evald ⊆ challenge` forces the
      -- point to be non-eval'd, also sets the forge `forged` flag (NRS14 App. A.2).
      -- [scheme-specific coupling; the genuine crypto invariant of the auth hop]
      intro t s₁ s₂ hRs
      obtain ⟨⟨ch₁, qc₁⟩, fl₁⟩ := s₁
      obtain ⟨⟨ch₂, qc₂⟩, fs₂⟩ := s₂
      obtain ⟨hch, hqc, hev, hflagimp⟩ := hRs
      simp only at hch hqc
      subst hch; subst hqc
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
      · -- unif oracle: both handlers thread state unchanged and sample the same uniform value
        -- Both handlers forward the same `liftM (query n)` and thread their states
        -- unchanged, so couple the shared uniform sample diagonally and re-use the
        -- incoming `R_state` components for the unchanged successor states.
        simp only [himpl₂, hR_state, forgeJointImpl, authInstImpl, authUnifImpl,
          QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
        refine ProgramLogic.Relational.relTriple_bind
          (ProgramLogic.Relational.relTriple_refl _) ?_
        intro a b hab
        simp only [ProgramLogic.Relational.EqRel] at hab; subst hab
        exact ProgramLogic.Relational.relTriple_pure_pure
          ⟨rfl, rfl, rfl, hev, hflagimp⟩
      · -- encrypt oracle: forwards the tag to the shared RO; records the challenge as the
        -- unique eval'd point, re-establishing `evald ⊆ challenge` and `ρ(challenge)=tag`
        simp only [himpl₂, hR_state, forgeJointImpl, authInstImpl, authEncImpl,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        cases ch₁ with
        | some val =>
            -- challenge already set: both handlers return `pure none`, state unchanged,
            -- so the postcondition is the incoming eval'd/flag clauses of `R_state`.
            simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
              StateT.run_get, pure_bind, bind_pure_comp, StateT.run_pure, Prod.forall,
              Prod.mk.injEq, true_and, ↓existsAndEq, ProgramLogic.Relational.relTriple_iff_relWP,
              MAlgRelOrdered.relWP_pure, Option.some.injEq]
            simp only at hev hflagimp
            refine ⟨fun a b hab => ?_, hflagimp⟩
            obtain ⟨c, t, hsome, hpeq, hcache⟩ := hev (a, b) hab
            obtain rfl : b = c := by simpa using congrArg Prod.snd hpeq
            exact ⟨t, by simpa using hsome, hcache⟩
        | none =>
            -- old challenge `none` ⇒ the eval'd set is empty (`hev` is vacuous), and both
            -- handlers query the SAME random oracle on the SAME cache `fs₂.1`. Couple that
            -- sample diagonally; the successor challenge/cache agree and the only eval'd
            -- point `(ad, c)` matches the new challenge with `ρ(ad,c) = tag`.
            simp only at hev
            have hevald : fs₂.2.1 = (∅ : Finset (AD × C_e)) := by
              by_contra hne
              obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hne
              obtain ⟨c, t, hcontra, -, -⟩ := hev p hp
              exact absurd hcontra (by simp)
            simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
              StateT.run_get, pure_bind, bind_pure_comp, StateT.run_monadLift, monadLift_self,
              StateT.run_map, StateT.run_set, map_pure, Functor.map_map, hevald, insert_empty_eq,
              Prod.forall, Prod.mk.injEq, true_and, ↓existsAndEq,
              ProgramLogic.Relational.relTriple_iff_relWP,
              ProgramLogic.Relational.relWP_iff_couplingPost]
            rw [← ProgramLogic.Relational.relWP_iff_couplingPost,
              ← ProgramLogic.Relational.relTriple_iff_relWP]
            -- couple the shared random-oracle sample diagonally, casing on cache hit/miss
            -- so the new cache is explicit and `ρ(ad,c) = tag` is available
            cases hca : fs₂.1 (ad, se.encrypt ke m) with
            | some u =>
                -- cache hit: the RO returns the cached `u`, cache unchanged; the new eval'd
                -- point `(ad, c)` is consistent because `fs₂.1 (ad, c) = some u`.
                simp only [StateT.run_pure, map_pure]
                refine ProgramLogic.Relational.relTriple_pure_pure
                  ⟨rfl, rfl, rfl, ?_, hflagimp⟩
                intro a₁ b hmem
                rw [Finset.mem_singleton] at hmem
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hmem
                exact ⟨u, rfl, hca⟩
            | none =>
                -- cache miss: sample the tag, insert into the cache via `cacheQuery`; couple
                -- the shared uniform sample diagonally. The new cache maps the new eval'd
                -- point `(ad, c)` to the freshly sampled tag (`cacheQuery_self`).
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  StateT.run_modifyGet, bind_pure_comp,
                  Functor.map_map]
                rw [← bind_pure_comp, ← bind_pure_comp]
                refine ProgramLogic.Relational.relTriple_bind
                  (ProgramLogic.Relational.relTriple_refl _) ?_
                intro a b hab
                simp only [ProgramLogic.Relational.EqRel] at hab; subst hab
                refine ProgramLogic.Relational.relTriple_pure_pure
                  ⟨rfl, rfl, rfl, ?_, hflagimp⟩
                intro a₁ b hmem
                rw [Finset.mem_singleton, Prod.mk.injEq] at hmem
                obtain ⟨hb1, hb2⟩ := hmem
                subst hb1; subst hb2
                exact ⟨a, rfl, QueryCache.cacheQuery_self fs₂.1 (a₁, se.encrypt ke m) a⟩
      · -- decrypt oracle: forwards verify to the shared RO; on a non-challenge `ok` sets the
        -- game flag, and (since `evald ⊆ challenge`) the point is not eval'd so
        -- `forged` fires
        simp only at hev hflagimp
        simp only [himpl₂, hR_state]
        simp only [authInstImpl, authDecImpl, forgeJointImpl, QueryImpl.add_apply_inr]
        erw [StateT.run_bind, StateT.run_bind, StateT.run_get, StateT.run_get]
        simp only [pure_bind]
        by_cases hg : ch₁ = some (c, tg)
        · simp only [hg, beq_self_eq_true, if_true]
          exact ProgramLogic.Relational.relTriple_pure_pure
            ⟨rfl, rfl, rfl, hg ▸ hev, hflagimp⟩
        · simp only [beq_iff_eq, hg, if_false]
          set ro := (((AD × C_e) →ₒ T).randomOracle (ad, c)).run fs₂.1 with hro
          -- Support facts for the shared RO query: the resulting cache extends `fs₂.1`
          -- (existing entries persist) and maps the queried point `(ad, c)` to the response.
          have hsupp : ∀ p ∈ support ro,
              fs₂.1 ≤ p.2 ∧ p.2 (ad, c) = some p.1 := by
            intro p hp
            rw [hro] at hp
            rcases hlk : fs₂.1 (ad, c) with _ | u
            · -- cache miss: the RO samples and inserts `(ad, c) ↦ p.1`
              rw [QueryImpl.withCaching_run_none _ hlk] at hp
              rw [support_map] at hp
              obtain ⟨v, _, rfl⟩ := hp
              refine ⟨QueryCache.le_cacheQuery (cache := fs₂.1) hlk, ?_⟩
              simp only [QueryCache.cacheQuery_self]
            · -- cache hit: the RO returns the cached value, leaving the cache unchanged
              rw [QueryImpl.withCaching_run_some _ hlk] at hp
              rw [support_pure] at hp
              simp only [Set.mem_singleton_iff] at hp
              subst hp
              exact ⟨le_refl _, hlk⟩
          erw [StateT.run_bind, StateT.run_bind,
            OracleComp.liftM_run_StateT, OracleComp.liftM_run_StateT]
          simp only [bind_assoc, pure_bind, if_true]
          -- Diagonal coupling of the shared RO query carrying the support facts.
          have hcouple : ProgramLogic.Relational.RelTriple ro ro
              (fun a b => a = b ∧ fs₂.1 ≤ a.2 ∧ a.2 (ad, c) = some a.1) := by
            rw [ProgramLogic.Relational.relTriple_iff_relWP,
              ProgramLogic.Relational.relWP_iff_couplingPost]
            refine ⟨_root_.SPMF.Coupling.refl (𝒟[ro]), ?_⟩
            intro z hz
            rcases (mem_support_bind_iff (𝒟[ro])
              (fun a => (pure (a, a) : SPMF _)) z).1 hz with ⟨a, ha, hz'⟩
            have ha_supp : a ∈ support ro :=
              (mem_support_iff (mx := ro) (x := a)).2
                (by simpa [probOutput_def] using
                  (mem_support_iff (mx := 𝒟[ro]) (x := a)).1 ha)
            have hzEq : z = (a, a) := by
              simpa [support_pure, Set.mem_singleton_iff] using hz'
            subst hzEq
            exact ⟨rfl, hsupp a ha_supp⟩
          refine ProgramLogic.Relational.relTriple_bind hcouple ?_
          rintro ⟨t', qc'⟩ ⟨resp, cache'⟩ ⟨hEq, hmono, hqcc⟩
          simp only [Prod.mk.injEq] at hEq
          obtain ⟨rfl, rfl⟩ := hEq
          erw [StateT.run_bind, StateT.run_bind, StateT.run_set, StateT.run_set]
          simp only [pure_bind]
          -- The successor evald-clause: existing eval'd points persist in the grown cache
          -- `qc'` (cache monotonicity), with the challenge slot unchanged at `ch₁`.
          have hevald : ∀ p ∈ fs₂.2.1, ∃ c_1 t, ch₁ = some (c_1, t) ∧
              p = (p.1, c_1) ∧ qc' (p.1, c_1) = some t := by
            intro p hp
            obtain ⟨c_1, t, hchal, hpeq, hlk⟩ := hev p hp
            exact ⟨c_1, t, hchal, hpeq, hmono hlk⟩
          by_cases hok : tg = t'
          · -- `ok = true`: the queried point `(ad, c)` is NOT eval'd (NRS14 App. A.2), so the
            -- forge `forged` flag fires; outputs both equal `se.decrypt ke c`.
            have hnotin : (ad, c) ∉ fs₂.2.1 := by
              intro hin
              obtain ⟨c_1, t, hchal, hpeq, hlk⟩ := hev (ad, c) hin
              -- `hpeq : (ad, c) = (ad, c_1)` forces `c_1 = c`
              simp only [Prod.mk.injEq, true_and] at hpeq
              subst hpeq
              -- the queried point is cached with value `t` in `fs₂.1`, hence in `qc'`
              have hqt : qc' (ad, c) = some t := hmono hlk
              -- so `t = t'`; with `tg = t'` we get `ch₁ = some (c, tg)`, contradicting `hg`
              have htt : t = t' := by
                have := hqt.symm.trans hqcc
                rwa [Option.some.injEq] at this
              apply hg
              rw [hchal, htt, hok]
            subst hok
            simp only [if_true]
            refine ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, rfl, rfl, hevald, ?_⟩
            intro _
            simp only [beq_self_eq_true, hnotin, not_false_eq_true, decide_true,
              Bool.and_true, Bool.or_true]
          · -- `ok = false`: verification fails, both reject (`none`); flags threaded
            -- unchanged.
            simp only [hok, if_false]
            have hbeq : (tg == t') = false := by
              simp only [beq_eq_false_iff_ne, ne_eq, hok, not_false_eq_true]
            simp only [hbeq, Bool.or_false, Bool.false_and]
            refine ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, rfl, rfl, hevald, ?_⟩
            intro hfl
            exact hflagimp hfl

omit [Inhabited C_e] [SampleableType C_e] in
/-- Query-bound transfer (auth hop adapter): each decrypt query of `adv` becomes exactly one
verify query in `forgeReduction`, so the reduction makes at most `q_d` verify queries whenever
`adv` makes at most `q_d` decrypt queries. -/
theorem forgeReduction_isQueryBoundP
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) (ke : K_e)
    (q_d : ℕ) (hqd : AEADScheme.decryptQueryBound adv q_d) :
    (forgeReduction se adv ke).IsQueryBoundP
      (etmAEAD.isVerifyQuery (D := AD × C_e) (R := T)) q_d := by
  -- `forgeSpec`'s `IsUniformSpec` witness (needed by the query-bound lemma) wants `Fintype T`;
  -- the tag type is sampleable, so it is finite.
  letI : Fintype T := SampleableType.Fintype T
  unfold forgeReduction etmGameSkeleton
  simp only [pure_bind, bind_pure_comp, Functor.map_map]
  rw [isQueryBoundP_def, isQueryBound_map_iff, ← isQueryBoundP_def]
  -- Split the adversary spec sum `(unifSpec+encrypt)+decrypt`: only decrypt (`Sum.inr`)
  -- satisfies the bound predicate, so the left (unif/encrypt) handlers issue 0 verify
  -- queries and the decrypt handler issues exactly 1. Each handler is discharged by
  -- per-handler `.run`-unwrapping (StateT `MonadLiftT` fusion of the `ofLift` forwarder),
  -- then `isQueryBoundP_query_iff` (encrypt eval / decrypt verify) and
  -- `IsQueryBoundP.liftComp_subSpec` (cross-spec unif lift). Cf. VCVio `CmaToNma` `hfwd`.
  refine etmAEAD.simulateQ_run_add_inr_of_step (fun t => by simp) hqd ?hleft ?hdec
    (fun t hnp => absurd (by simp) hnp) (none, ∅)
  case hleft =>
    intro t s
    rcases t with n | ⟨ad, m⟩
    · -- unif forwarder: one (lifted) unif query, not a verify query
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
      erw [OracleComp.liftM_run_StateT]
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      -- the lift sends `query n : OracleQuery unifSpec` to `forgeSpec` at
      -- `Sum.inl (Sum.inl n)`,
      -- which never `matches Sum.inr _`, so the forwarder makes no verify queries
      change (liftM (OracleSpec.query
          (Sum.inl (Sum.inl n) : (etmAEAD.forgeSpec (AD × C_e) T).Domain) :
            OracleQuery (etmAEAD.forgeSpec (AD × C_e) T) _) :
          OracleComp (etmAEAD.forgeSpec (AD × C_e) T) _).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_iff]
      simp [etmAEAD.isVerifyQuery]
    · -- encrypt forwarder: one eval query `Sum.inl (Sum.inr _)`, not a verify query
      simp only [QueryImpl.add_apply_inr]
      obtain ⟨ch, qc⟩ := s
      cases ch with
      | none =>
          simp only [add_apply_inr, StateT.run_pure, liftM_pure, bind_pure, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, StateT.run_bind,
            StateT.run_get, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            isQueryBoundP_map_iff]
          exact (isQueryBoundP_query_iff
              (p := etmAEAD.isVerifyQuery (D := AD × C_e) (R := T))
              (Sum.inl (Sum.inr (ad, se.encrypt ke m))) 0).mpr
            (fun h => absurd h (by simp [etmAEAD.isVerifyQuery]))
      | some val =>
          simp [StateT.run_bind, StateT.run_get, StateT.run_pure]
  case hdec =>
    -- decrypt forwarder: one verify query `Sum.inr _`
    intro t hp s; obtain ⟨ad, c, tg⟩ := t; obtain ⟨ch, qc⟩ := s
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hg : ch = some (c, tg)
    · simp only [hg, beq_self_eq_true, ↓reduceIte, StateT.run_pure]
      exact isQueryBoundP_pure etmAEAD.isVerifyQuery (none, some (c, tg), qc) 1
    · simp only [beq_iff_eq, hg, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind]
      erw [OracleComp.liftM_run_StateT, OracleComp.liftM_run_StateT]
      simp only [StateT.run_pure, bind_assoc, pure_bind]
      refine (isQueryBoundP_bind (m := 0)
        ((isQueryBoundP_query_iff (p := etmAEAD.isVerifyQuery)
          (Sum.inr ((ad, c), tg)) 1).mpr (fun _ => Nat.one_pos))
        (fun x _ => ?_)).mono (le_refl 1)
      rcases hb : (x : Bool) with _ | _ <;>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, isQueryBoundP_pure]

