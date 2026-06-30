/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.Auth.Forge

/-!
# Encrypt-then-MAC — auth hop (`game1` → `game2`)

`game1_game2_le_auth`: the gap is bounded by `q_d / |T|` via the forge bound.
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

omit [Inhabited C_e] [SampleableType C_e] in
/-- Game 1 → 2: auth bound. Gap bounded by `q_d` times tag-guessing probability.

NRS14 Appendix A.2, A5 Case 1: each decrypt query at a fresh random oracle
point verifies with probability `1/|T|`. Union bound over `q_d` decrypt
queries gives `q_d/|T|`. The hypothesis `hqd` ties `q_d` to the adversary
via `IsQueryBoundP`: `adv` makes at most `q_d` decrypt-oracle queries
(structurally, on every execution path). -/
theorem game1_game2_le_auth
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d) :
    |(Pr[= true | game1 se adv]).toReal -
     (Pr[= true | game2 se adv]).toReal| ≤
      ↑q_d * (Fintype.card T : ℝ)⁻¹ := by
  -- NRS14 Appendix A.2, A5 Case 1. Couple `game1` and `game2` through the intermediate
  -- `game2'` (verify queries the RO then rejects unconditionally):
  --   |Pr[game1] - Pr[game2]|
  --     = |Pr[game1] - Pr[game2']|          (hC: game2' = game2, discarded-query brick)
  --     ≤ tvDist(game1, game2')             (abs_probOutput_toReal_sub_le_tvDist)
  --     ≤ q_d/|T|                           (htv: identical-until-bad + forge brick)
  -- Step C: `game2' = game2`. game2' rejects unconditionally, so its verify RO query reveals
  -- nothing — removing it preserves the distribution (`evalDist_simulateQ_run'_discardRO`, the
  -- RO-mediated discarded-query brick), lifted through the skeleton.
  have hC : Pr[= true | game2' se adv] = Pr[= true | game2 se adv] :=
    game2'_eq_game2 se adv
  -- Steps A+B: identical-until-bad (game1 vs game2' agree off the forge step) bounds the TV
  -- distance by the forge probability; the eval+verify forge brick bounds that by q_d/|T|.
  have htv : tvDist (game1 se adv) (game2' se adv) ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ := by
    -- Per-key flag-instrumented simulations: `Y₁ ke` ≈ game1 (real return on verify),
    -- `Y₂ ke` ≈ game2' (always reject), both threading the `forged` flag.
    set Y₁ : K_e → ProbComp Bool :=
      fun ke => (simulateQ (authInstImpl se true ke) adv).run' ((none, ∅), false) with hY₁
    set Y₂ : K_e → ProbComp Bool :=
      fun ke => (simulateQ (authInstImpl se false ke) adv).run' ((none, ∅), false) with hY₂
    -- Abbreviation: the forge probability of the `b = true` instrumented simulation per key.
    set forgeProb : K_e → ℝ := fun ke =>
      (Pr[fun z : Bool × (EtmGameState AD C_e T × Bool) => z.2.2 = true |
          (simulateQ (authInstImpl se true ke) adv).run ((none, ∅), false)]).toReal
      with hforgeProb
    -- Fold the skeleton's `let (b', _) ← run; return b'` to `run'`.
    -- (1) Flag projection: each game = keygen >>= per-key flag-instrumented sim. The `forged`
    -- flag is write-only (does not affect the state transition or the output bit), so dropping
    -- it via `proj = Prod.fst` recovers the un-instrumented game
    -- (`run'_simulateQ_eq_of_query_map_eq`).
    -- The per-oracle `hproj` obligation: unif/encrypt thread the flag unchanged; decrypt's
    -- flag-write is dropped by `Prod.fst`, leaving the same state transition and output bit.
    have hproj_unif : ∀ (b : Bool) (ke : K_e) (n : ℕ) (s : EtmGameState AD C_e T × Bool),
        Prod.map id Prod.fst <$>
            (authInstImpl se b ke (Sum.inl (Sum.inl n))).run s =
          (gameUnifImpl (AD := AD) (C_e := C_e) (T := T) n).run (Prod.fst s) := by
      intro b ke n s
      obtain ⟨⟨ch, qc⟩, fl⟩ := s
      simp [authInstImpl, authUnifImpl, gameUnifImpl, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, StateT.run_monadLift, Prod.map, Functor.map_map]
    have hflag1 : game1 se adv = se.keygen >>= Y₁ := by
      rw [hY₁]
      unfold game1 etmGameSkeleton
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine bind_congr fun ke => ?_
      refine (run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst ?hproj adv ((none, ∅), false)).symm
      case hproj =>
        intro t s
        obtain ⟨⟨ch, qc⟩, fl⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
        · exact hproj_unif true ke n ((ch, qc), fl)
        · -- encryption oracle: flag threaded unchanged, dropped by `Prod.fst`
          cases ch <;>
            simp [authInstImpl, authEncImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
              StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map,
              Functor.map_map]
        · -- decryption oracle (b = true): RO + compare, real return on `ok`, flag dropped
          cases ch with
          | none =>
            simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map,
              ← apply_ite]
          | some val =>
            by_cases hguard : val = (c, tg) <;>
              simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
                StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map,
                ← apply_ite, beq_iff_eq, hguard]
    have hflag2 : game2' se adv = se.keygen >>= Y₂ := by
      rw [hY₂]
      unfold game2' etmGameSkeleton
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine bind_congr fun ke => ?_
      refine (run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst ?hproj adv ((none, ∅), false)).symm
      case hproj =>
        intro t s
        obtain ⟨⟨ch, qc⟩, fl⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
        · exact hproj_unif false ke n ((ch, qc), fl)
        · cases ch <;>
            simp [authInstImpl, authEncImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
              StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map,
              Functor.map_map]
        · -- decryption oracle (b = false): RO then reject unconditionally, flag dropped
          cases ch with
          | none =>
            simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map]
          | some val =>
            by_cases hguard : val = (c, tg) <;>
              simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
                StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map,
                beq_iff_eq, hguard]
    rw [hflag1, hflag2]
    -- (3) Per-key identical-until-bad (brick 3): the `b = true`/`b = false` impls agree on every
    -- non-forged transition (they differ only in the verify return when `ok = true`, which also
    -- sets the flag) and the flag is monotone, so the per-key TV distance is ≤ forge probability.
    have hbad : ∀ ke, tvDist (Y₁ ke) (Y₂ ke) ≤ forgeProb ke := by
      intro ke
      rw [hY₁, hY₂, hforgeProb]
      exact tvDist_authInst_le_probForge se adv ke
    -- (4) Per-key forge bound (forge reduction + brick 1): the forge event reduces to the
    -- eval+verify lazy-RO forgery experiment, bounded by `q_d/|T|` via `hqd`.
    have hforge : ∀ ke, forgeProb ke ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ := by
      intro ke
      rw [hforgeProb]
      exact le_trans (probForge_authInst_le_forgeReduction se adv ke)
        (OracleComp.probForge_le_queryBound_div_card (forgeReduction se adv ke) q_d
          (forgeReduction_isQueryBoundP se adv ke q_d hqd))
    -- Combine (3)+(4): per-key TV ≤ q_d/|T|.
    have htv_ke : ∀ ke, tvDist (Y₁ ke) (Y₂ ke) ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ :=
      fun ke => le_trans (hbad ke) (hforge ke)
    -- Convexity over the key: a per-key TV bound lifts through the `se.keygen` bind
    -- (`tvDist_bind_left_le_const'`, the unrestricted real-valued companion of VCVio's
    -- `ofReal_tvDist_bind_left_le_const'`).
    exact tvDist_bind_left_le_const' se.keygen Y₁ Y₂ _ htv_ke
  calc |(Pr[= true | game1 se adv]).toReal - (Pr[= true | game2 se adv]).toReal|
      = |(Pr[= true | game1 se adv]).toReal - (Pr[= true | game2' se adv]).toReal| := by
        rw [hC]
    _ ≤ tvDist (game1 se adv) (game2' se adv) :=
        abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ := htv

