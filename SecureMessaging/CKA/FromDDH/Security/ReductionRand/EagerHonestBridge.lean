/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.ReductionRand.RelStep

/-!
# CKA from DDH — Reduction (rand) — Eager-Honest Bridge

This file proves that two presentations of the random CKA game have the same
output distribution.

On the left, the game samples `a, b ←$ F` and `gT ←$ G` before running the
adversary, then passes them to `honestImpl_param_rand gp gen a b gT`.
On the right, the regular random CKA oracle stack
`ckaSecurityImpl gp true (ddhCKA F G gen)` samples the corresponding values
inside the oracle calls.

The proof is by induction on the adversary. Non-firing oracle calls are
pointwise-equal passthrough cases. At the embedding send event, the external
`a` is coupled with the oracle's internal scalar sample. At the challenge event,
`b` is coupled with the internal challenge scalar, and `gT` with the internal
random output key.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme DiffieHellman ckaSecuritySpec

variable [DecidableEq G]

section Step2
variable [Inhabited F]
variable [Fintype G]

omit [Inhabited F] [Fintype G] in
/-- Rand-branch passthrough step for pointwise-equal oracle cases. -/
lemma evalDist_eager_honest_rand_eq_step_passthrough
    (gp : GameParams) (s : GameState (CKAState F G) G G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range t →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_impl_eq : ∀ (a b : F) (gT : G),
      (honestImpl_param_rand gp gen a b gT t).run s =
      (ckaSecurityImpl gp true (ddhCKA F G gen) t).run s)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range t)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen a b gT) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImpl_param_rand gp gen a b gT)
        (OracleSpec.query t >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
      (OracleSpec.query t >>= k)).run' s) := by
  let sample : ProbComp (F × F × G) := do
    let a ← ($ᵗ F : ProbComp F)
    let b ← ($ᵗ F : ProbComp F)
    let gT ← ($ᵗ G : ProbComp G)
    pure (a, b, gT)
  have h_sampled_param := evalDist_sample_param_query_bind_passthrough
    (sample := sample)
    (impl := fun param => honestImpl_param_rand gp gen param.1 param.2.1 param.2.2)
    (base := ckaSecurityImpl gp true (ddhCKA F G gen))
    (Inv := fun _ : GameState (CKAState F G) G G => True)
    (s := s) (t := t) (k := k)
    (h_impl_eq := fun param => h_impl_eq param.1 param.2.1 param.2.2)
    (h_preserves := by
      intro p hp_support
      trivial)
    (h_ih := by
      intro u s' hs'
      simpa [sample, bind_assoc] using h_ih u s')
  simpa [sample, bind_assoc] using h_sampled_param

omit [Inhabited F] [Fintype G] in
/-- Rand sendA step at the on-party embedding event. -/
lemma evalDist_eager_honest_rand_eq_step_at_sendA_chal_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OSendA →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OSendA)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen a b gT) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImpl_param_rand gp gen a b gT)
        (OracleSpec.query
          (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
      (OracleSpec.query
        (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) := by
  by_cases h_fire :
      (validStep s.lastAction CKAAction.sendA &&
        isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = true
  · have h_split : validStep s.lastAction CKAAction.sendA = true ∧
        isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = true := by
      simpa using h_fire
    obtain ⟨h_v, h_o⟩ := h_split
    have h_tA_eq : s.tA + 1 = gp.challengeEpoch - 1 := by
      simp only [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other,
        beq_iff_eq] at h_o
      exact_mod_cast h_o
    have h_challengeEpoch_pos : 1 ≤ gp.challengeEpoch := by omega
    cases h_stA : s.stA with
    | recvReady x =>
      refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
        (fun a _ _ => ?_) h_ih
      change (honestSendA_param (F := F) gp gen a ()).run s =
        (oracleSendA (ddhCKA F G gen) ()).run s
      have h_o' : isOtherSendBeforeChall gp
          { s with stA := (.recvReady x : CKAState F G), tA := s.tA + 1 } = true := by
        simp only [isOtherSendBeforeChall] at h_o ⊢
        convert h_o using 2
      simp [honestSendA_param, oracleSendA, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_cp, h_o', h_stA, ddhCKA, send]
    | sendReady h =>
      let post : F → GameState (CKAState F G) G G := fun v =>
        { s with
          stA := (CKAState.recvReady v : CKAState F G),
          rhoA := some (v • gen),
          keyA := some (v • h),
          lastAction := some .sendA,
          tA := s.tA + 1 }
      have h_eager_call :
          (ckaSecurityImpl gp true (ddhCKA F G gen)
              (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x => pure (some (x • gen, x • h), post x)) := by
        change (oracleSendA (ddhCKA F G gen) ()).run s = _
        simp [oracleSendA, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp, h_v, h_stA, ddhCKA, send, post]
      apply evalDist_ext
      intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₃_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (sample₃ := ($ᵗ G : ProbComp G))
        (impl := fun a b gT => honestImpl_param_rand gp gen a b gT)
        (s := s)
        (t := (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun a _ _ => some (a • gen, a • h))
        (post := fun a _ _ => post a)
        (h_run := fun a _ _ => by
          change (honestSendA_param (F := F) gp gen a ()).run s =
            pure (some (a • gen, a • h), post a)
          simpa [post] using honestSendA_param_run_eq_at_chal_B_inr (gen := gen)
            gp h_cp a h s h_v h_o h_stA) y
      have eq_rhs := probOutput_handler_sample_pure_eq
        (sample := ($ᵗ F : ProbComp F))
        (impl := ckaSecurityImpl gp true (ddhCKA F G gen))
        (s := s)
        (t := (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x => some (x • gen, x • h))
        (post := post)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch - 1 ≤ (post v).tA := fun _ => by
        change gp.challengeEpoch - 1 ≤ s.tA + 1
        omega
      exact probOutput_rand_send_coupling (gen := gen) gp h post k h_ih
        (fun x b a gT => simulateQ_honest_param_rand_a_indep_post_sendA (gen := gen) gp h_cp b gT
          (k (some (x • gen, x • h))) (post x) (h_post_inv x) a x) y
  · have h_pred_false :
        (validStep s.lastAction CKAAction.sendA &&
         (gp.challengedParty == CKAParty.B) &&
         isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
      (fun a _ _ => ?_) h_ih
    change (honestSendA_param (F := F) gp gen a ()).run s =
      (oracleSendA (ddhCKA F G gen) ()).run s
    exact honestSendA_param_run_eq_when_pred_false gp a s h_pred_false

omit [Inhabited F] [Fintype G] in
/-- Rand sendB step at the on-party embedding event. -/
lemma evalDist_eager_honest_rand_eq_step_at_sendB_chal_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OSendB →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OSendB)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen a b gT) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImpl_param_rand gp gen a b gT)
        (OracleSpec.query
          (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
      (OracleSpec.query
        (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) := by
  by_cases h_fire :
      (validStep s.lastAction CKAAction.sendB &&
        isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = true
  · have h_split : validStep s.lastAction CKAAction.sendB = true ∧
        isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = true := by
      simpa using h_fire
    obtain ⟨h_v, h_o⟩ := h_split
    have h_tB_eq : s.tB + 1 = gp.challengeEpoch - 1 := by
      simp only [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other,
        beq_iff_eq] at h_o
      exact_mod_cast h_o
    have h_challengeEpoch_pos : 1 ≤ gp.challengeEpoch := by omega
    cases h_stB : s.stB with
    | recvReady x =>
      refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
        (fun a _ _ => ?_) h_ih
      change (honestSendB_param (F := F) gp gen a ()).run s =
        (oracleSendB (ddhCKA F G gen) ()).run s
      have h_o' : isOtherSendBeforeChall gp
          { s with stB := (.recvReady x : CKAState F G), tB := s.tB + 1 } = true := by
        simp only [isOtherSendBeforeChall] at h_o ⊢
        convert h_o using 2
      simp [honestSendB_param, oracleSendB, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_cp, h_o', h_stB, ddhCKA, send]
    | sendReady h =>
      let post : F → GameState (CKAState F G) G G := fun v =>
        { s with
          stB := (CKAState.recvReady v : CKAState F G),
          rhoB := some (v • gen),
          keyB := some (v • h),
          lastAction := some .sendB,
          tB := s.tB + 1 }
      have h_eager_call :
          (ckaSecurityImpl gp true (ddhCKA F G gen)
              (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x => pure (some (x • gen, x • h), post x)) := by
        change (oracleSendB (ddhCKA F G gen) ()).run s = _
        simp [oracleSendB, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp, h_v, h_stB, ddhCKA, send, post]
      apply evalDist_ext
      intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₃_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (sample₃ := ($ᵗ G : ProbComp G))
        (impl := fun a b gT => honestImpl_param_rand gp gen a b gT)
        (s := s)
        (t := (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun a _ _ => some (a • gen, a • h))
        (post := fun a _ _ => post a)
        (h_run := fun a _ _ => by
          change (honestSendB_param (F := F) gp gen a ()).run s =
            pure (some (a • gen, a • h), post a)
          simpa [post] using honestSendB_param_run_eq_at_chal_A_inr (gen := gen)
            gp h_cp a h s h_v h_o h_stB) y
      have eq_rhs := probOutput_handler_sample_pure_eq
        (sample := ($ᵗ F : ProbComp F))
        (impl := ckaSecurityImpl gp true (ddhCKA F G gen))
        (s := s)
        (t := (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x => some (x • gen, x • h))
        (post := post)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch - 1 ≤ (post v).tB := fun _ => by
        change gp.challengeEpoch - 1 ≤ s.tB + 1
        omega
      exact probOutput_rand_send_coupling (gen := gen) gp h post k h_ih
        (fun x b a gT => simulateQ_honest_param_rand_a_indep_post_sendB (gen := gen) gp h_cp b gT
          (k (some (x • gen, x • h))) (post x) (h_post_inv x) a x) y
  · have h_pred_false :
        (validStep s.lastAction CKAAction.sendB &&
         (gp.challengedParty == CKAParty.A) &&
         isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
      (fun a _ _ => ?_) h_ih
    change (honestSendB_param (F := F) gp gen a ()).run s =
      (oracleSendB (ddhCKA F G gen) ()).run s
    exact honestSendB_param_run_eq_when_pred_false gp a s h_pred_false

omit [Inhabited F] [Fintype G] in
/-- Rand challA step at the on-party challenge event. -/
lemma evalDist_eager_honest_rand_eq_step_at_challA_chal_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OChallA →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OChallA)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen a b gT) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImpl_param_rand gp gen a b gT)
        (OracleSpec.query
          (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
      (OracleSpec.query
        (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) := by
  by_cases h_fire :
      (validStep s.lastAction CKAAction.challA &&
        isChallengeEpoch gp { s with tA := s.tA + 1 }) = true
  · have h_split : validStep s.lastAction CKAAction.challA = true ∧
        isChallengeEpoch gp { s with tA := s.tA + 1 } = true := by
      simpa using h_fire
    obtain ⟨h_v, h_e⟩ := h_split
    have h_tA_eq : s.tA + 1 = gp.challengeEpoch := by
      simp only [isChallengeEpoch, GameState.tP, h_cp, beq_iff_eq] at h_e
      exact_mod_cast h_e
    cases h_stA : s.stA with
    | recvReady x =>
      refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ b gT => ?_) h_ih
      change (honestChallA_param_rand (F := F) gp gen b gT ()).run s =
        (oracleChallA gp true (ddhCKA F G gen) ()).run s
      have h_e' : isChallengeEpoch gp
          { s with stA := (.recvReady x : CKAState F G),
                   tA := s.tA + 1 } = true := by
        simp only [isChallengeEpoch] at h_e ⊢
        convert h_e using 2
      have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
      simp [honestChallA_param_rand, oracleChallA, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_beq, h_e', h_stA, ddhCKA, send]
    | sendReady h =>
      let post : F → GameState (CKAState F G) G G := fun v =>
        { s with
          stA := (CKAState.recvReady v : CKAState F G),
          rhoA := some (v • gen),
          keyA := some (v • h),
          lastAction := some .challA,
          tA := s.tA + 1 }
      have h_e_post : isChallengeEpoch gp
          { s with stA := (CKAState.sendReady h : CKAState F G),
                   tA := s.tA + 1 } = true := by
        simp [isChallengeEpoch, GameState.tP, h_cp, h_tA_eq]
      have h_eager_call :
          (ckaSecurityImpl gp true (ddhCKA F G gen)
              (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x =>
            ($ᵗ G : ProbComp G) >>= fun outKey => pure (some (x • gen, outKey), post x)) := by
        change (oracleChallA gp true (ddhCKA F G gen) ()).run s = _
        have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
        simp [oracleChallA, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp,
          h_v, h_beq, h_e_post, h_stA, ddhCKA, send, post]
      apply evalDist_ext
      intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₃_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (sample₃ := ($ᵗ G : ProbComp G))
        (impl := fun a b gT => honestImpl_param_rand gp gen a b gT)
        (s := s)
        (t := (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun _ b gT => some (b • gen, gT))
        (post := fun _ b _ => post b)
        (h_run := fun _ b gT => by
          change (honestChallA_param_rand (F := F) gp gen b gT ()).run s =
            pure (some (b • gen, gT), post b)
          simpa [honestChallA_param_rand, post] using
            honestChallA_param_mode_run_eq_at_chal_A_inr (gen := gen)
              HonestChallengeMode.rand gp h_cp b gT h s h_v h_e h_stA) y
      have eq_rhs := probOutput_handler_sample₂_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ G : ProbComp G))
        (impl := ckaSecurityImpl gp true (ddhCKA F G gen))
        (s := s)
        (t := (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x outKey => some (x • gen, outKey))
        (post := fun x _ => post x)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch ≤ (post v).tA := fun _ => by
        change gp.challengeEpoch ≤ s.tA + 1
        omega
      exact probOutput_rand_challenge_coupling (gen := gen) gp post k h_ih
        (fun x outKey a b gT =>
          simulateQ_honest_param_rand_b_indep_post_challA (gen := gen) gp h_cp a gT
            (k (some (x • gen, outKey))) (post x) (h_post_inv x) b x)
        (fun x outKey a gT =>
          simulateQ_honest_param_rand_gT_indep_post_challA (gen := gen) gp h_cp a x
            (k (some (x • gen, outKey))) (post x) (h_post_inv x) gT outKey) y
  · have h_pred_false :
        (validStep s.lastAction CKAAction.challA &&
         (gp.challengedParty == CKAParty.A) &&
         isChallengeEpoch gp { s with tA := s.tA + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
      (fun _ b gT => ?_) h_ih
    change (honestChallA_param_rand (F := F) gp gen b gT ()).run s =
      (oracleChallA gp true (ddhCKA F G gen) ()).run s
    exact honestChallA_param_rand_run_eq_when_pred_false gp b gT s h_pred_false

omit [Inhabited F] [Fintype G] in
/-- Rand challB step at the on-party challenge event. -/
lemma evalDist_eager_honest_rand_eq_step_at_challB_chal_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OChallB →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OChallB)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen a b gT) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImpl_param_rand gp gen a b gT)
        (OracleSpec.query
          (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
      (OracleSpec.query
        (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) := by
  by_cases h_fire :
      (validStep s.lastAction CKAAction.challB &&
        isChallengeEpoch gp { s with tB := s.tB + 1 }) = true
  · have h_split : validStep s.lastAction CKAAction.challB = true ∧
        isChallengeEpoch gp { s with tB := s.tB + 1 } = true := by
      simpa using h_fire
    obtain ⟨h_v, h_e⟩ := h_split
    have h_tB_eq : s.tB + 1 = gp.challengeEpoch := by
      simp only [isChallengeEpoch, GameState.tP, h_cp, beq_iff_eq] at h_e
      exact_mod_cast h_e
    cases h_stB : s.stB with
    | recvReady x =>
      refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ b gT => ?_) h_ih
      change (honestChallB_param_rand (F := F) gp gen b gT ()).run s =
        (oracleChallB gp true (ddhCKA F G gen) ()).run s
      have h_e' : isChallengeEpoch gp
          { s with stB := (.recvReady x : CKAState F G),
                   tB := s.tB + 1 } = true := by
        simp only [isChallengeEpoch] at h_e ⊢
        convert h_e using 2
      have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
      simp [honestChallB_param_rand, oracleChallB, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_beq, h_e', h_stB, ddhCKA, send]
    | sendReady h =>
      let post : F → GameState (CKAState F G) G G := fun v =>
        { s with
          stB := (CKAState.recvReady v : CKAState F G),
          rhoB := some (v • gen),
          keyB := some (v • h),
          lastAction := some .challB,
          tB := s.tB + 1 }
      have h_e_post : isChallengeEpoch gp
          { s with stB := (CKAState.sendReady h : CKAState F G),
                   tB := s.tB + 1 } = true := by
        simp [isChallengeEpoch, GameState.tP, h_cp, h_tB_eq]
      have h_eager_call :
          (ckaSecurityImpl gp true (ddhCKA F G gen)
              (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x =>
            ($ᵗ G : ProbComp G) >>= fun outKey => pure (some (x • gen, outKey), post x)) := by
        change (oracleChallB gp true (ddhCKA F G gen) ()).run s = _
        have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
        simp [oracleChallB, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp,
          h_v, h_beq, h_e_post, h_stB, ddhCKA, send, post]
      apply evalDist_ext
      intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₃_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (sample₃ := ($ᵗ G : ProbComp G))
        (impl := fun a b gT => honestImpl_param_rand gp gen a b gT)
        (s := s)
        (t := (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun _ b gT => some (b • gen, gT))
        (post := fun _ b _ => post b)
        (h_run := fun _ b gT => by
          change (honestChallB_param_rand (F := F) gp gen b gT ()).run s =
            pure (some (b • gen, gT), post b)
          simpa [honestChallB_param_rand, post] using
            honestChallB_param_mode_run_eq_at_chal_B_inr (gen := gen)
              HonestChallengeMode.rand gp h_cp b gT h s h_v h_e h_stB) y
      have eq_rhs := probOutput_handler_sample₂_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ G : ProbComp G))
        (impl := ckaSecurityImpl gp true (ddhCKA F G gen))
        (s := s)
        (t := (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x outKey => some (x • gen, outKey))
        (post := fun x _ => post x)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch ≤ (post v).tB := fun _ => by
        change gp.challengeEpoch ≤ s.tB + 1
        omega
      exact probOutput_rand_challenge_coupling (gen := gen) gp post k h_ih
        (fun x outKey a b gT =>
          simulateQ_honest_param_rand_b_indep_post_challB (gen := gen) gp h_cp a gT
            (k (some (x • gen, outKey))) (post x) (h_post_inv x) b x)
        (fun x outKey a gT =>
          simulateQ_honest_param_rand_gT_indep_post_challB (gen := gen) gp h_cp a x
            (k (some (x • gen, outKey))) (post x) (h_post_inv x) gT outKey) y
  · have h_pred_false :
        (validStep s.lastAction CKAAction.challB &&
         (gp.challengedParty == CKAParty.B) &&
         isChallengeEpoch gp { s with tB := s.tB + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s _ k
      (fun _ b gT => ?_) h_ih
    change (honestChallB_param_rand (F := F) gp gen b gT ()).run s =
      (oracleChallB gp true (ddhCKA F G gen) ()).run s
    exact honestChallB_param_rand_run_eq_when_pred_false gp b gT s h_pred_false

set_option maxHeartbeats 4000000 in
-- The rand bridge induction tracks three top-level samples and all oracle
-- cases, which exceeds the default heartbeat limit during elaboration.
omit [Inhabited F] [Fintype G] in
/-- **Rand game-oracle bridge.** Sampling `(a, b, gT)` before running the
adversary under `honestImpl_param_rand` gives the same output distribution as
running the adversary under the regular random CKA oracle stack
`ckaSecurityImpl gp true`.

At embedding events, the external `a` is coupled with the oracle's internal
scalar sample. At challenge events, the external `b` is coupled with the
internal challenge scalar, and the external `gT` is coupled with the internal
random output key. -/
lemma evalDist_eager_honest_rand_eq
    (gp : GameParams) (s : GameState (CKAState F G) G G)
    (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run' s) := by
    induction adversary using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run'_pure']
    exact evalDist_sample_bind₃_eq_of_forall_eq
      (f := fun _a _b _gT => (pure x : ProbComp Bool))
      (p := pure x)
      (fun _ _ _ => rfl)
  | query_bind t k ih =>
    let pass := evalDist_eager_honest_rand_eq_step_passthrough (gen := gen) gp s
    match t with
    | OUnif _ | ORecvA | ORecvB | OCorruptA | OCorruptB =>
      exact pass _ k (fun _ _ _ => rfl) ih
    | OSendA_rleak =>
      exact pass _ k (fun _ _ _ => rfl) ih
    | OSendB_rleak =>
      exact pass _ k (fun _ _ _ => rfl) ih
    | OSendA =>
      cases h_cp : gp.challengedParty with
      | A =>
        refine pass _ k (fun a _ _ => ?_) ih
        exact honestSendA_param_run_eq_at_chal_A (gen := gen) gp h_cp a s
      | B =>
        exact evalDist_eager_honest_rand_eq_step_at_sendA_chal_B
          (gen := gen) gp h_cp s k ih
    | OSendB =>
      cases h_cp : gp.challengedParty with
      | A =>
        exact evalDist_eager_honest_rand_eq_step_at_sendB_chal_A
          (gen := gen) gp h_cp s k ih
      | B =>
        refine pass _ k (fun a _ _ => ?_) ih
        exact honestSendB_param_run_eq_at_chal_B (gen := gen) gp h_cp a s
    | OChallA =>
      cases h_cp : gp.challengedParty with
      | A =>
        exact evalDist_eager_honest_rand_eq_step_at_challA_chal_A
          (gen := gen) gp h_cp s k ih
      | B =>
        refine pass _ k (fun _ b gT => ?_) ih
        exact honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b gT s (by simp [h_cp])
    | OChallB =>
      cases h_cp : gp.challengedParty with
      | A =>
        refine pass _ k (fun _ b gT => ?_) ih
        exact honestChallB_param_rand_run_eq_when_pred_false (gen := gen) gp b gT s (by simp [h_cp])
      | B =>
        exact evalDist_eager_honest_rand_eq_step_at_challB_chal_B
          (gen := gen) gp h_cp s k ih


end Step2

end ddhCKA
