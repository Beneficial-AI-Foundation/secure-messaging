/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.GameOracles.SimulateQ

/-!
# CKA from DDH — Game Oracles — Per-Event Step Lemmas

This file proves the per-query lemmas used in `GameOracles/Bridge.lean`.
That bridge proves equality of full adversary executions by induction on
`simulateQ`. At a step `query t >>= k`, each oracle first handles query `t`; if
it returns response `u` and post-state `s'`, the remaining program is `k u` run
from `s'`.

The lemmas compare the Boolean output distributions of these one-query prefixes
for two handlers:

* `honestImpl_param_real` / `honestImpl_param_rand`, where the DDH scalars
  `a`, `b`, and in the random branch `gT`, are sampled outside the handler;
* `ckaSecurityImpl`, where the corresponding values are sampled inside the CKA
  oracle.

Most query indices are passthrough cases: if the query is not the party/epoch
where the DDH value is embedded, the lazy and eager handlers reduce to the same
`run` result, and the bridge step is just the induction hypothesis. The active
`OSend*` and `OChall*` cases are the embedding/challenge events. There we first
unfold the handler call to its concrete response and post-state (`pure ...` or
an internal sample), then use generic probability lemmas to couple the lazy
outer samples with the eager samples produced inside `ckaSecurityImpl`.
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
/-- One step of `evalDist_eager_honest_lazy_eq` for oracles where lazy and
eager are pointwise equal. Notation:
* `t : ckaSecuritySpec.Domain` is any oracle index.
* `k : Range t → OracleComp ckaSecuritySpec Bool` is the continuation.
* `u : Range t` is an oracle response, `s'` a post-state.

Given the impl-equality
  `∀ a, b. (honest_param a b t).run s = (eager t).run s`
and the IH
  `∀ u s'. 𝒟[do b, a ← $ᵗ F; sim(honest_param a b)(k u).run' s']
        = 𝒟[sim(eager)(k u).run' s']`,
prove
  `𝒟[do b, a ← $ᵗ F; sim(honest_param a b)(query t >>= k).run' s]
 = 𝒟[sim(eager)(query t >>= k).run' s]`.

Discharges the 5 non-divergence indices (`OUnif`, `ORecv{A,B}`,
`OCorrupt{A,B}`) of the bridge induction's `query_bind` case, and also
the off-party branch of `OSend{A,B}` / `OChall{A,B}` (where lazy
delegates to eager pointwise). -/
lemma evalDist_eager_honest_lazy_eq_step_passthrough
    (gp : GameParams) (s : GameState (CKAState F G) G G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range t →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_impl_eq : ∀ (a b : F),
      (honestImpl_param_real gp gen a b t).run s =
      (ckaSecurityImpl gp false (ddhCKA F G gen) t).run s)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range t)
          (s' : GameState (CKAState F G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b)
        (OracleSpec.query t >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
      (OracleSpec.query t >>= k)).run' s) := by
  let sample : ProbComp (F × F) := do
    let b ← ($ᵗ F : ProbComp F)
    let a ← ($ᵗ F : ProbComp F)
    pure (a, b)
  have h_sampled_param := evalDist_sample_param_query_bind_passthrough
    (sample := sample)
    (impl := fun param => honestImpl_param_real gp gen param.1 param.2)
    (base := ckaSecurityImpl gp false (ddhCKA F G gen))
    (Inv := fun _ : GameState (CKAState F G) G G => True)
    (s := s) (t := t) (k := k)
    (h_impl_eq := fun param => h_impl_eq param.1 param.2)
    (h_preserves := by
      intro p hp_support
      exact trivial)
    (h_ih := by
      intro u s' hs'
      simpa [sample, bind_assoc] using h_ih u s')
  simpa [sample, bind_assoc] using h_sampled_param

omit [Inhabited F] [Fintype G] in
lemma bool_and_insert_true_eq_false {a b c : Bool}
    (hb : b = true) (h : (a && c) = false) :
    (a && b && c) = false := by
  rw [hb]
  simp [h]

omit [Inhabited F] [Fintype G] in
/-- Final step used by the real-branch active send proofs.

Proves equality of the output point probabilities for the lazy send step and
the eager send step. In the lazy step, the answer and post-state use the outer
parameter `a`; in the eager step, the handler samples the same scalar internally.
This is the real-branch instance of `probOutput_two_sample_active_param_eq`:
`h_ih` compares continuations at a fixed send scalar `x`, and `h_a_indep`
replaces the lazy active-send parameter by `x` after `post x`. -/
lemma probOutput_real_send_coupling
    (gp : GameParams) (peer : G)
    (post : F → GameState (CKAState F G) G G)
    (k : Option (G × G) → OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : Option (G × G)) (s' : GameState (CKAState F G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) (k u)).run' s'))
    (h_a_indep : ∀ x b a : F,
      evalDist ((simulateQ (honestImpl_param_real gp gen a b)
        (k (some (x • gen, x • peer)))).run (post x)) =
      evalDist ((simulateQ (honestImpl_param_real gp gen x b)
        (k (some (x • gen, x • peer)))).run (post x)))
    (y : Bool) :
    Pr[= y | do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      let (out, _state) ←
        (simulateQ (honestImpl_param_real gp gen a b)
          (k (some (a • gen, a • peer)))).run (post a)
      pure out] =
    Pr[= y | do
      let x ← ($ᵗ F : ProbComp F)
      let (out, _state) ←
        (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
          (k (some (x • gen, x • peer)))).run (post x)
      pure out] := by
  exact probOutput_two_sample_active_param_eq
    (lazy := fun a b x => Prod.fst <$> (simulateQ (honestImpl_param_real gp gen a b)
      (k (some (x • gen, x • peer)))).run (post x))
    (base := fun x => Prod.fst <$> (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
      (k (some (x • gen, x • peer)))).run (post x)) y
    (h_ih := fun x => by
    have hi := h_ih (some (x • gen, x • peer)) (post x)
    simp only [StateT.run'_eq] at hi
    exact probOutput_eq_of_evalDist_eq hi.symm y)
    (h_indep := fun x b a =>
      probOutput_map_eq_of_evalDist_eq (h_a_indep x b a) Prod.fst y)

omit [Inhabited F] [Fintype G] in
/-- Final step used by the rand-branch active send proofs.

Proves equality of the output point probabilities for the lazy send step and
the eager send step. In the lazy step, the answer and post-state use the outer
parameter `a`; in the eager step, the handler samples the same scalar internally.
This is the rand-branch instance of `probOutput_three_sample_active_param_eq`:
`h_ih` compares continuations at a fixed send scalar `x`, and `h_a_indep`
replaces the lazy active-send parameter by `x` after `post x`. -/
lemma probOutput_rand_send_coupling
    (gp : GameParams) (peer : G)
    (post : F → GameState (CKAState F G) G G)
    (k : Option (G × G) → OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : Option (G × G)) (s' : GameState (CKAState F G) G G),
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen a b gT) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) (k u)).run' s'))
    (h_a_indep : ∀ (x b a : F) (gT : G),
      evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT)
        (k (some (x • gen, x • peer)))).run (post x)) =
      evalDist ((simulateQ (honestImpl_param_rand gp gen x b gT)
        (k (some (x • gen, x • peer)))).run (post x)))
    (y : Bool) :
    Pr[= y | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      let (out, _state) ←
        (simulateQ (honestImpl_param_rand gp gen a b gT)
          (k (some (a • gen, a • peer)))).run (post a)
      pure out] =
    Pr[= y | do
      let x ← ($ᵗ F : ProbComp F)
      let (out, _state) ←
        (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
          (k (some (x • gen, x • peer)))).run (post x)
      pure out] := by
  exact probOutput_three_sample_active_param_eq
    (lazy := fun a b gT x => Prod.fst <$> (simulateQ (honestImpl_param_rand gp gen a b gT)
      (k (some (x • gen, x • peer)))).run (post x))
    (base := fun x => Prod.fst <$> (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
      (k (some (x • gen, x • peer)))).run (post x)) y
    (h_ih := fun x => by
    have hi := h_ih (some (x • gen, x • peer)) (post x)
    simp only [StateT.run'_eq] at hi
    exact probOutput_eq_of_evalDist_eq hi.symm y)
    (h_indep := fun x b a gT =>
      probOutput_map_eq_of_evalDist_eq (h_a_indep x b a gT) Prod.fst y)

omit [Inhabited F] [Fintype G] in
/-- One step of `evalDist_eager_honest_lazy_eq` for `query OSendA >>= k`
when the challenged party is `B` (the on-party embedding event). Notation:
* `k : Option (G × G) → OracleComp ckaSecuritySpec Bool` is the
  continuation of the adversary's program after the `sendA` query,
  receiving the oracle's response.
* `u : Option (G × G) = Range OSendA` is a possible oracle response.
* `s'` is a possible post-state.

Given the IH

  `∀ u s'. 𝒟[do b, a ← $ᵗ F; sim(honest_param a b)(k u).run' s']
        = 𝒟[sim(eager)(k u).run' s']`,

prove

  `𝒟[do b, a ← $ᵗ F; sim(honest_param a b)(query OSendA >>= k).run' s]
 = 𝒟[sim(eager)(query OSendA >>= k).run' s]`
-/
lemma evalDist_eager_honest_lazy_eq_step_at_sendA_chal_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OSendA →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OSendA)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b)
        (OracleSpec.query
          (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
      (OracleSpec.query
        (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) := by
  -- Case-split on whether the embedding fires at this query. The firing
  -- predicate `validStep ∧ isOtherSendBeforeChall` is the only condition
  -- under which `honestSendA_param` substitutes `a`; outside it, lazy and
  -- eager are pointwise equal and the passthrough helper applies.
  by_cases h_fire :
      (validStep s.lastAction CKAAction.sendA &&
        isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = true
  · -- Firing case: bijection + post-event a-indep + IH.
    -- From `h_fire` we extract: validStep is true, isOtherSendBeforeChall is true.
    -- The firing post-state satisfies `s'.tA = s.tA + 1 = gp.challengeEpoch - 1`, so
    -- `simulateQ_honest_param_a_indep_post_sendA`'s precondition holds.
    have h_split : validStep s.lastAction CKAAction.sendA = true ∧
        isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = true := by
      simpa using h_fire
    obtain ⟨h_v, h_o⟩ := h_split
    -- From `isOther = true`: `s.tP challengedParty.other = gp.challengeEpoch - 1`.
    -- Here challengedParty.other = .A (since h_cp: challengedParty = .B), so
    -- `(s with tA := s.tA + 1).tA = gp.challengeEpoch - 1`, i.e.
    -- `s.tA + 1 = gp.challengeEpoch - 1`. Hence `gp.challengeEpoch ≥ 1`
    -- (else equation has no Nat solution) and post-state's tA = gp.challengeEpoch - 1.
    have h_tA_eq : s.tA + 1 = gp.challengeEpoch - 1 := by
      simp only [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other,
        beq_iff_eq] at h_o
      exact_mod_cast h_o
    have h_challengeEpoch_pos : 1 ≤ gp.challengeEpoch := by omega
    -- Sub-case-split on `s.stA`:
    -- * `.recvReady _`: at firing-predicate-true with `s.stA = .recvReady _`, both lazy
    --   and eager reduce to `pure (none, s)` — lazy = eager pointwise. Use
    --   the passthrough helper.
    -- * `.sendReady h`: the actual embedding fires; lazy uses `a` deterministically,
    --   eager samples `x ← $ᵗ F`. Bijection coupling needed.
    cases h_stA : s.stA with
    | recvReady x =>
      -- Lazy/eager both produce `(none, s)`; predicate-false dispatch by way
      -- of the contradictory match: in both impls, `state.stA = .recvReady x` makes
      -- the embedding return `pure none` without `set`-ing.
      refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun a _ => ?_) h_ih
      change (honestSendA_param (F := F) gp gen a ()).run s =
        (oracleSendA (ddhCKA F G gen) ()).run s
      have h_o' : isOtherSendBeforeChall gp
          { s with stA := (.recvReady x : CKAState F G), tA := s.tA + 1 } = true := by
        simp only [isOtherSendBeforeChall] at h_o ⊢
        convert h_o using 2
      simp [honestSendA_param, oracleSendA, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_cp, h_o', h_stA, ddhCKA, send]
    | sendReady h =>
      -- Firing-fires-truly sub-case. Bijection coupling between LHS's outer
      -- `a ← $ᵗ F` and RHS's internal sample inside `oracleSendA` at the
      -- embedding event, plus post-event a-indep on the continuation, plus
      -- IH on `(k u)` at the post-state.
      have h_o' : isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = true := h_o
      -- Post-state shape after the firing event, parameterized by the
      -- substituted scalar `v ∈ F` (which is `a` on LHS, `x` on RHS).
      let post : F → GameState (CKAState F G) G G := fun v =>
        { s with
          stA := (CKAState.recvReady v : CKAState F G),
          rhoA := some (v • gen),
          keyA := some (v • h),
          lastAction := some .sendA,
          tA := s.tA + 1 }
      -- Concrete reduction of the eager impl call: samples `x ← $F` and
      -- substitutes it into the analogous post-state shape.
      have h_eager_call :
          (ckaSecurityImpl gp false (ddhCKA F G gen)
              (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x => pure (some (x • gen, x • h), post x)) := by
        change (oracleSendA (ddhCKA F G gen) ()).run s = _
        simp [oracleSendA, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp,
          h_v, h_stA, ddhCKA, send, post]
      apply evalDist_ext; intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₂_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (impl := fun b a => honestImpl_param_real gp gen a b)
        (s := s)
        (t := (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun b a => some (a • gen, a • h))
        (post := fun b a => post a)
        (h_run := fun b a => by
          change (honestSendA_param (F := F) gp gen a ()).run s =
            pure (some (a • gen, a • h), post a)
          simpa [post] using honestSendA_param_run_eq_at_chal_B_inr (gen := gen)
            gp h_cp a h s h_v h_o h_stA) y
      have eq_rhs := probOutput_handler_sample_pure_eq
        (sample := ($ᵗ F : ProbComp F))
        (impl := ckaSecurityImpl gp false (ddhCKA F G gen))
        (s := s)
        (t := (OSendA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x => some (x • gen, x • h))
        (post := post)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch - 1 ≤ (post v).tA := fun _ => by
        change gp.challengeEpoch - 1 ≤ s.tA + 1; omega
      exact probOutput_real_send_coupling (gen := gen) gp h post k h_ih
        (fun x b a => simulateQ_honest_param_a_indep_post_sendA (gen := gen) gp h_cp b
          (k (some (x • gen, x • h))) (post x) (h_post_inv x) a x) y
  · -- Non-firing case: lazy = eager pointwise; reduce to passthrough.
    have h_pred_false :
        (validStep s.lastAction CKAAction.sendA &&
         (gp.challengedParty == CKAParty.B) &&
         isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
      (fun a _ => ?_) h_ih
    -- Goal: `(honestImpl_param_real gp gen a b OSendA).run s =
    --        (ckaSecurityImpl gp false (ddhCKA F G gen) OSendA).run s`
    -- Reduce both sides to their underlying oracle: the OSendA index in
    -- `honestImpl_param_real` resolves to `honestSendA_param gp gen a` and in
    -- `ckaSecurityImpl` to `oracleSendA (ddhCKA F G gen)`.
    change (honestSendA_param (F := F) gp gen a ()).run s =
      (oracleSendA (ddhCKA F G gen) ()).run s
    exact honestSendA_param_run_eq_when_pred_false gp a s h_pred_false

omit [Inhabited F] [Fintype G] in
/-- Mirror of `evalDist_eager_honest_lazy_eq_step_at_sendA_chal_B` for the
on-party `sendB` embedding at `challengedParty = .A`. Same recipe, with `tA ↔ tB` and
`stA ↔ stB` swapped. -/
lemma evalDist_eager_honest_lazy_eq_step_at_sendB_chal_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OSendB →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OSendB)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b)
        (OracleSpec.query
          (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
      (OracleSpec.query
        (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) := by
  by_cases h_fire :
      (validStep s.lastAction CKAAction.sendB &&
        isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = true
  · -- Firing case.
    have h_split : validStep s.lastAction CKAAction.sendB = true ∧
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
      refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun a _ => ?_) h_ih
      change (honestSendB_param (F := F) gp gen a ()).run s =
        (oracleSendB (ddhCKA F G gen) ()).run s
      have h_o' : isOtherSendBeforeChall gp
          { s with stB := (.recvReady x : CKAState F G), tB := s.tB + 1 } = true := by
        simp only [isOtherSendBeforeChall] at h_o ⊢
        convert h_o using 2
      simp [honestSendB_param, oracleSendB, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_cp, h_o', h_stB, ddhCKA, send]
    | sendReady h =>
      have h_o' : isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = true := h_o
      let post : F → GameState (CKAState F G) G G := fun v =>
        { s with
          stB := (CKAState.recvReady v : CKAState F G),
          rhoB := some (v • gen),
          keyB := some (v • h),
          lastAction := some .sendB,
          tB := s.tB + 1 }
      have h_eager_call :
          (ckaSecurityImpl gp false (ddhCKA F G gen)
              (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x => pure (some (x • gen, x • h), post x)) := by
        change (oracleSendB (ddhCKA F G gen) ()).run s = _
        simp [oracleSendB, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp,
          h_v, h_stB, ddhCKA, send, post]
      apply evalDist_ext; intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₂_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (impl := fun b a => honestImpl_param_real gp gen a b)
        (s := s)
        (t := (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun b a => some (a • gen, a • h))
        (post := fun b a => post a)
        (h_run := fun b a => by
          change (honestSendB_param (F := F) gp gen a ()).run s =
            pure (some (a • gen, a • h), post a)
          simpa [post] using honestSendB_param_run_eq_at_chal_A_inr (gen := gen)
            gp h_cp a h s h_v h_o h_stB) y
      have eq_rhs := probOutput_handler_sample_pure_eq
        (sample := ($ᵗ F : ProbComp F))
        (impl := ckaSecurityImpl gp false (ddhCKA F G gen))
        (s := s)
        (t := (OSendB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x => some (x • gen, x • h))
        (post := post)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch - 1 ≤ (post v).tB := fun _ => by
        change gp.challengeEpoch - 1 ≤ s.tB + 1; omega
      exact probOutput_real_send_coupling (gen := gen) gp h post k h_ih
        (fun x b a => simulateQ_honest_param_a_indep_post_sendB (gen := gen) gp h_cp b
          (k (some (x • gen, x • h))) (post x) (h_post_inv x) a x) y
  · -- Non-firing case.
    have h_pred_false :
        (validStep s.lastAction CKAAction.sendB &&
         (gp.challengedParty == CKAParty.A) &&
         isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
      (fun a _ => ?_) h_ih
    change (honestSendB_param (F := F) gp gen a ()).run s =
      (oracleSendB (ddhCKA F G gen) ()).run s
    exact honestSendB_param_run_eq_when_pred_false gp a s h_pred_false

omit [Inhabited F] [Fintype G] in
/-- Final step used by the real-branch active challenge proofs.

Proves equality of the output point probabilities for the lazy challenge step
and the eager challenge step. In the lazy step, the answer and post-state use
the outer parameter `b`; in the eager step, the handler samples the same scalar
internally. This is the real-branch instance of
`probOutput_two_sample_second_param_eq`: `h_ih` compares continuations at a
fixed challenge scalar `x`, and `h_b_indep` replaces the lazy challenge
parameter by `x` after `post x`. -/
lemma probOutput_real_challenge_coupling
    (gp : GameParams) (peer : G)
    (post : F → GameState (CKAState F G) G G)
    (k : Option (G × G) → OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : Option (G × G)) (s' : GameState (CKAState F G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) (k u)).run' s'))
    (h_b_indep : ∀ x a b : F,
      evalDist ((simulateQ (honestImpl_param_real gp gen a b)
        (k (some (x • gen, x • peer)))).run (post x)) =
      evalDist ((simulateQ (honestImpl_param_real gp gen a x)
        (k (some (x • gen, x • peer)))).run (post x)))
    (y : Bool) :
    Pr[= y | do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      let (out, _state) ←
        (simulateQ (honestImpl_param_real gp gen a b)
          (k (some (b • gen, b • peer)))).run (post b)
      pure out] =
    Pr[= y | do
      let x ← ($ᵗ F : ProbComp F)
      let (out, _state) ←
        (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
          (k (some (x • gen, x • peer)))).run (post x)
      pure out] := by
  exact probOutput_two_sample_second_param_eq
    (lazy := fun a b x => Prod.fst <$> (simulateQ (honestImpl_param_real gp gen a b)
      (k (some (x • gen, x • peer)))).run (post x))
    (base := fun x => Prod.fst <$> (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
      (k (some (x • gen, x • peer)))).run (post x)) y
    (h_ih := fun x => by
    have hi := h_ih (some (x • gen, x • peer)) (post x)
    simp only [StateT.run'_eq] at hi
    exact probOutput_eq_of_evalDist_eq hi.symm y)
    (h_indep := fun x a b =>
      probOutput_map_eq_of_evalDist_eq (h_b_indep x a b) Prod.fst y)

omit [Inhabited F] [Fintype G] in
/-- Final step used by the rand-branch active challenge proofs.

This is the CKA instance of `probOutput_three_sample_second_third_param_eq`,
the coupling for three independent samples when the second and third samples
are also used to build the response passed to the continuation.

In the generic lemma, the lazy side has the form
`lazy first second third x outKey`: `first`, `second`, and `third` are sampled
lazy parameters, while `x` and `outKey` are used to build the response
`some (x • gen, outKey)` passed to `k`. The eager side has the form
`base x outKey`.

Assume, for every pair `(x, outKey)`, that `base x outKey` matches
`lazy first second third x outKey` with fresh `first`, `second`, and `third`,
and that this lazy continuation is independent of sampled `second` and `third`
once `x` and `outKey` are fixed. Then using the outside samples `(b, gT)` as
the values in the response `some (b • gen, gT)` has the same point probability
as sampling `(x, outKey)` directly on the eager side. -/
lemma probOutput_rand_challenge_coupling
  (gp : GameParams)
    -- `post x`: state after the challenge response uses scalar `x`.
    (post : F → GameState (CKAState F G) G G)
    -- `k`: continuation run after the challenge response.
    (k : Option (G × G) → OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    -- `h_ih`: instantiate the generic eager/lazy-continuation match at any
    -- fixed response `u` and post-state `s'`.
    (h_ih : ∀ (u : Option (G × G)) (s' : GameState (CKAState F G) G G),
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen a b gT) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) (k u)).run' s'))
    -- `h_b_indep`: generic second-parameter independence. With response
    -- `some (x • gen, outKey)` and state `post x` fixed, change the lazy
    -- challenge scalar from sampled `b` to the scalar `x` used in the response.
    (h_b_indep : ∀ (x : F) (outKey : G) (a b : F) (gT : G),
      evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT)
        (k (some (x • gen, outKey)))).run (post x)) =
      evalDist ((simulateQ (honestImpl_param_rand gp gen a x gT)
        (k (some (x • gen, outKey)))).run (post x)))
    -- `h_gT_indep`: generic third-parameter independence. With the same fixed
    -- response and state, and lazy scalar already `x`, change the lazy random
    -- group sample from sampled `gT` to the key `outKey` used in the response.
    (h_gT_indep : ∀ (x : F) (outKey : G) (a : F) (gT : G),
      evalDist ((simulateQ (honestImpl_param_rand gp gen a x gT)
        (k (some (x • gen, outKey)))).run (post x)) =
      evalDist ((simulateQ (honestImpl_param_rand gp gen a x outKey)
        (k (some (x • gen, outKey)))).run (post x)))
    -- `y`: output bit whose point probability is compared.
    (y : Bool) :
    -- Lazy conclusion: generic `first, second, third` are `a, b, gT`; the
    -- response passed to `k` is built from the outside samples `b, gT`.
    Pr[= y | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      let (out, _state) ←
        (simulateQ (honestImpl_param_rand gp gen a b gT)
          (k (some (b • gen, gT)))).run (post b)
      pure out] =
    -- Eager conclusion: after reducing the CKA oracle call, its internal
    -- samples `x` and `outKey` build the response passed to `k`.
    Pr[= y | do
      let x ← ($ᵗ F : ProbComp F)
      let outKey ← ($ᵗ G : ProbComp G)
      let (out, _state) ←
        (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
          (k (some (x • gen, outKey)))).run (post x)
      pure out] := by
  exact probOutput_three_sample_second_third_param_eq
    -- `lazy a b gT x outKey`: run the lazy continuation with sampled
    -- parameters `a`, `b`, `gT` and fixed response parameters `x`, `outKey`.
    (lazy := fun a b gT x outKey =>
      Prod.fst <$> (simulateQ (honestImpl_param_rand gp gen a b gT)
        (k (some (x • gen, outKey)))).run (post x))
    -- `base x outKey`: run the eager continuation after the eager challenge
    -- samples have reduced to `x` and `outKey`.
    (base := fun x outKey =>
      Prod.fst <$> (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen))
        (k (some (x • gen, outKey)))).run (post x)) y
    (h_ih := fun x outKey => by
      have hi := h_ih (some (x • gen, outKey)) (post x)
      simp only [StateT.run'_eq] at hi
      exact probOutput_eq_of_evalDist_eq hi.symm y)
    (h_second_indep := fun x outKey a b gT =>
      probOutput_map_eq_of_evalDist_eq (h_b_indep x outKey a b gT) Prod.fst y)
    (h_third_indep := fun x outKey a gT =>
      probOutput_map_eq_of_evalDist_eq (h_gT_indep x outKey a gT) Prod.fst y)

omit [Inhabited F] [Fintype G] in
/-- Mirror of the send firing helpers for the on-party `challA` event at
`challengedParty = .A` on the real branch. The eager `oracleChallA` skips the random-branch
`outKey ←$ G` sample and matches the lazy parameter `b`. -/
lemma evalDist_eager_honest_lazy_eq_step_at_challA_chal_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OChallA →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OChallA)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b)
        (OracleSpec.query
          (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
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
    have h_challengeEpoch_pos : 1 ≤ gp.challengeEpoch := by omega
    cases h_stA : s.stA with
    | recvReady x =>
      refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ b => ?_) h_ih
      change (honestChallA_param (F := F) gp gen b ()).run s =
        (oracleChallA gp false (ddhCKA F G gen) ()).run s
      have h_e' : isChallengeEpoch gp
          { s with stA := (.recvReady x : CKAState F G),
                   tA := s.tA + 1 } = true := by
        simp only [isChallengeEpoch] at h_e ⊢
        convert h_e using 2
      have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
      simp [honestChallA_param, oracleChallA, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_beq, h_e', h_stA, ddhCKA, send]
    | sendReady h =>
      have h_e' : isChallengeEpoch gp { s with tA := s.tA + 1 } = true := h_e
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
          (ckaSecurityImpl gp false (ddhCKA F G gen)
              (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x => pure (some (x • gen, x • h), post x)) := by
        change (oracleChallA gp false (ddhCKA F G gen) ()).run s = _
        have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
        simp [oracleChallA, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp,
          h_v, h_beq, h_e_post, h_stA, ddhCKA, send, post]
      apply evalDist_ext; intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₂_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (impl := fun b a => honestImpl_param_real gp gen a b)
        (s := s)
        (t := (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun b a => some (b • gen, b • h))
        (post := fun b a => post b)
        (h_run := fun b a => by
          change (honestChallA_param (F := F) gp gen b ()).run s =
            pure (some (b • gen, b • h), post b)
          simpa [honestChallA_param, post] using
            honestChallA_param_mode_run_eq_at_chal_A_inr (gen := gen)
              HonestChallengeMode.real gp h_cp b gen h s h_v h_e h_stA) y
      have eq_rhs := probOutput_handler_sample_pure_eq
        (sample := ($ᵗ F : ProbComp F))
        (impl := ckaSecurityImpl gp false (ddhCKA F G gen))
        (s := s)
        (t := (OChallA : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x => some (x • gen, x • h))
        (post := post)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch ≤ (post v).tA := fun _ => by
        change gp.challengeEpoch ≤ s.tA + 1; omega
      exact probOutput_real_challenge_coupling (gen := gen) gp h post k h_ih
        (fun x a b => simulateQ_honest_param_b_indep_post_challA (gen := gen) gp h_cp a
          (k (some (x • gen, x • h))) (post x) (h_post_inv x) b x) y
  · have h_pred_false :
        (validStep s.lastAction CKAAction.challA &&
         (gp.challengedParty == CKAParty.A) &&
         isChallengeEpoch gp { s with tA := s.tA + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
      (fun _ b => ?_) h_ih
    change (honestChallA_param (F := F) gp gen b ()).run s =
      (oracleChallA gp false (ddhCKA F G gen) ()).run s
    exact honestChallA_param_run_eq_when_pred_false gp b s h_pred_false

omit [Inhabited F] [Fintype G] in
/-- Mirror of `_step_at_challA_chal_A` for the on-party `challB` event at
`challengedParty = .B`. Same structure with tA↔tB and stA↔stB swapped. -/
lemma evalDist_eager_honest_lazy_eq_step_at_challB_chal_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (s : GameState (CKAState F G) G G)
    (k : (ckaSecuritySpec (CKAState F G) G G F).Range OChallB →
         OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (h_ih : ∀ (u : (ckaSecuritySpec (CKAState F G) G G F).Range OChallB)
            (s' : GameState (CKAState F G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b)
        (OracleSpec.query
          (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain) >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen))
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
    have h_challengeEpoch_pos : 1 ≤ gp.challengeEpoch := by omega
    cases h_stB : s.stB with
    | recvReady x =>
      refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ b => ?_) h_ih
      change (honestChallB_param (F := F) gp gen b ()).run s =
        (oracleChallB gp false (ddhCKA F G gen) ()).run s
      have h_e' : isChallengeEpoch gp
          { s with stB := (.recvReady x : CKAState F G),
                   tB := s.tB + 1 } = true := by
        simp only [isChallengeEpoch] at h_e ⊢
        convert h_e using 2
      have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
      simp [honestChallB_param, oracleChallB, StateT.run_bind, StateT.run_get,
        pure_bind, h_v, h_beq, h_e', h_stB, ddhCKA, send]
    | sendReady h =>
      have h_e' : isChallengeEpoch gp { s with tB := s.tB + 1 } = true := h_e
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
          (ckaSecurityImpl gp false (ddhCKA F G gen)
              (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain)).run s =
          (($ᵗ F : ProbComp F) >>= fun x => pure (some (x • gen, x • h), post x)) := by
        change (oracleChallB gp false (ddhCKA F G gen) ()).run s = _
        have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
        simp [oracleChallB, StateT.run_bind, StateT.run_get, StateT.run_set,
          pure_bind, bind_pure_comp,
          h_v, h_beq, h_e_post, h_stB, ddhCKA, send, post]
      apply evalDist_ext; intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have eq_lhs := probOutput_sample_param₂_handler_pure_eq
        (sample₁ := ($ᵗ F : ProbComp F))
        (sample₂ := ($ᵗ F : ProbComp F))
        (impl := fun b a => honestImpl_param_real gp gen a b)
        (s := s)
        (t := (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun b a => some (b • gen, b • h))
        (post := fun b a => post b)
        (h_run := fun b a => by
          change (honestChallB_param (F := F) gp gen b ()).run s =
            pure (some (b • gen, b • h), post b)
          simpa [honestChallB_param, post] using
            honestChallB_param_mode_run_eq_at_chal_B_inr (gen := gen)
              HonestChallengeMode.real gp h_cp b gen h s h_v h_e h_stB) y
      have eq_rhs := probOutput_handler_sample_pure_eq
        (sample := ($ᵗ F : ProbComp F))
        (impl := ckaSecurityImpl gp false (ddhCKA F G gen))
        (s := s)
        (t := (OChallB : (ckaSecuritySpec (CKAState F G) G G F).Domain))
        (k := k)
        (out := fun x => some (x • gen, x • h))
        (post := post)
        h_eager_call y
      rw [eq_lhs, eq_rhs]
      have h_post_inv : ∀ v : F, gp.challengeEpoch ≤ (post v).tB := fun _ => by
        change gp.challengeEpoch ≤ s.tB + 1; omega
      exact probOutput_real_challenge_coupling (gen := gen) gp h post k h_ih
        (fun x a b => simulateQ_honest_param_b_indep_post_challB (gen := gen) gp h_cp a
          (k (some (x • gen, x • h))) (post x) (h_post_inv x) b x) y
  · have h_pred_false :
        (validStep s.lastAction CKAAction.challB &&
         (gp.challengedParty == CKAParty.B) &&
         isChallengeEpoch gp { s with tB := s.tB + 1 }) = false := by
      exact bool_and_insert_true_eq_false (by simp [h_cp]) (Bool.eq_false_iff.mpr h_fire)
    refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
      (fun _ b => ?_) h_ih
    change (honestChallB_param (F := F) gp gen b ()).run s =
      (oracleChallB gp false (ddhCKA F G gen) ()).run s
    exact honestChallB_param_run_eq_when_pred_false gp b s h_pred_false

end Step2

end ddhCKA
