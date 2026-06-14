/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.GameOracles.PerQuery
import ToVCVio.ProgramLogic.Relational.SimulateQ

/-!
# CKA from DDH — Game Oracles — simulateQ Wrappers and Marginalization

Distribution-level facts that lift the per-query reasoning from
`GameOracles/PerQuery.lean` to complete adversary executions.
Here `simulateQ impl adversary` means: run the CKA adversary, answering each of
its oracle queries with the oracle implementation `impl`.

This file proves parameter-independence facts for such adversary executions,
the special post-`challA` invariant preservation needed in the random branch,
and per-event marginalization lemmas relating the parameterized honest oracles
to the regular CKA security oracles.
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
/-- At `challengedParty = .B` and `gp.challengeEpoch - 1 ≤ s.tA` (post-`sendA`-firing state), the
lazy honest simulation is `a`-independent. Lifts the per-query a-indep via
`relTriple_simulateQ_run_of_impl_eq_preservesInv` + `tA` monotonicity. -/
lemma simulateQ_honest_param_a_indep_post_sendA
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b : F)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch - 1 ≤ s.tA) (a₁ a₂ : F) :
    evalDist ((simulateQ (honestImpl_param_real gp gen a₁ b) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_real gp gen a₂ b) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_real gp gen a₁ b)
    (impl₂ := honestImpl_param_real gp gen a₂ b)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch - 1 ≤ s'.tA)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_real_a_indep_post_sendA (gen := gen) gp h_cp b t s'
        (next_ne_prev_epoch_of_prev_epoch_le h_pre) a₁ a₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_real_t_monotone (gen := gen) gp a₂ b t s' z hz).1)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- At `challengedParty = .A` and `gp.challengeEpoch - 1 ≤ s.tB` (post-`sendB`-firing state), the
lazy honest simulation is `a`-independent. -/
lemma simulateQ_honest_param_a_indep_post_sendB
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (b : F)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch - 1 ≤ s.tB) (a₁ a₂ : F) :
    evalDist ((simulateQ (honestImpl_param_real gp gen a₁ b) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_real gp gen a₂ b) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_real gp gen a₁ b)
    (impl₂ := honestImpl_param_real gp gen a₂ b)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch - 1 ≤ s'.tB)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_real_a_indep_post_sendB (gen := gen) gp h_cp b t s'
        (next_ne_prev_epoch_of_prev_epoch_le h_pre) a₁ a₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_real_t_monotone (gen := gen) gp a₂ b t s' z hz).2)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- At `challengedParty = .A` and `gp.challengeEpoch ≤ s.tA` (post-`challA`-firing state), the
lazy honest simulation is `b`-independent. -/
lemma simulateQ_honest_param_b_indep_post_challA
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (a : F)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tA) (b₁ b₂ : F) :
    evalDist ((simulateQ (honestImpl_param_real gp gen a b₁) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_real gp gen a b₂) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_real gp gen a b₁)
    (impl₂ := honestImpl_param_real gp gen a b₂)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s'.tA)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_real_b_indep_post_challA (gen := gen) gp h_cp a t s'
        (next_ne_epoch_of_epoch_le h_pre) b₁ b₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_real_t_monotone (gen := gen) gp a b₂ t s' z hz).1)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- At `challengedParty = .B` and `gp.challengeEpoch ≤ s.tB` (post-`challB`-firing state), the
lazy honest simulation is `b`-independent. -/
lemma simulateQ_honest_param_b_indep_post_challB
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a : F)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tB) (b₁ b₂ : F) :
    evalDist ((simulateQ (honestImpl_param_real gp gen a b₁) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_real gp gen a b₂) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_real gp gen a b₁)
    (impl₂ := honestImpl_param_real gp gen a b₂)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s'.tB)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_real_b_indep_post_challB (gen := gen) gp h_cp a t s'
        (next_ne_epoch_of_epoch_le h_pre) b₁ b₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_real_t_monotone (gen := gen) gp a b₂ t s' z hz).2)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- Rand simulation is `a`-independent after the A-side embedding window. -/
lemma simulateQ_honest_param_rand_a_indep_post_sendA
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b : F) (gT : G)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch - 1 ≤ s.tA) (a₁ a₂ : F) :
    evalDist ((simulateQ (honestImpl_param_rand gp gen a₁ b gT) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a₂ b gT) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_rand gp gen a₁ b gT)
    (impl₂ := honestImpl_param_rand gp gen a₂ b gT)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch - 1 ≤ s'.tA)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_rand_a_indep_post_sendA (gen := gen) gp h_cp b gT t s'
        (next_ne_prev_epoch_of_prev_epoch_le h_pre) a₁ a₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_rand_t_monotone (gen := gen) gp a₂ b gT t s' z hz).1)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- Rand simulation is `a`-independent after the B-side embedding window. -/
lemma simulateQ_honest_param_rand_a_indep_post_sendB
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (b : F) (gT : G)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch - 1 ≤ s.tB) (a₁ a₂ : F) :
    evalDist ((simulateQ (honestImpl_param_rand gp gen a₁ b gT) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a₂ b gT) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_rand gp gen a₁ b gT)
    (impl₂ := honestImpl_param_rand gp gen a₂ b gT)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch - 1 ≤ s'.tB)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_rand_a_indep_post_sendB (gen := gen) gp h_cp b gT t s'
        (next_ne_prev_epoch_of_prev_epoch_le h_pre) a₁ a₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_rand_t_monotone (gen := gen) gp a₂ b gT t s' z hz).2)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- Rand simulation is `b`-independent after A's challenge window. -/
lemma simulateQ_honest_param_rand_b_indep_post_challA
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (a : F) (gT : G)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tA) (b₁ b₂ : F) :
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b₁ gT) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b₂ gT) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_rand gp gen a b₁ gT)
    (impl₂ := honestImpl_param_rand gp gen a b₂ gT)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s'.tA)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_rand_b_indep_post_challA (gen := gen) gp h_cp a gT t s'
        (next_ne_epoch_of_epoch_le h_pre) b₁ b₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_rand_t_monotone (gen := gen) gp a b₂ gT t s' z hz).1)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- Rand simulation is `b`-independent after B's challenge window. -/
lemma simulateQ_honest_param_rand_b_indep_post_challB
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a : F) (gT : G)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tB) (b₁ b₂ : F) :
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b₁ gT) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b₂ gT) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_rand gp gen a b₁ gT)
    (impl₂ := honestImpl_param_rand gp gen a b₂ gT)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s'.tB)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_rand_b_indep_post_challB (gen := gen) gp h_cp a gT t s'
        (next_ne_epoch_of_epoch_le h_pre) b₁ b₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_rand_t_monotone (gen := gen) gp a b₂ gT t s' z hz).2)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- Rand simulation is `gT`-independent after A's challenge window. -/
lemma simulateQ_honest_param_rand_gT_indep_post_challA
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (a b : F)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tA) (gT₁ gT₂ : G) :
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT₁) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT₂) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_rand gp gen a b gT₁)
    (impl₂ := honestImpl_param_rand gp gen a b gT₂)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s'.tA)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_rand_gT_indep_post_challA (gen := gen) gp h_cp a b t s'
        (next_ne_epoch_of_epoch_le h_pre) gT₁ gT₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_rand_t_monotone (gen := gen) gp a b gT₂ t s' z hz).1)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- Rand simulation is `gT`-independent after B's challenge window. -/
lemma simulateQ_honest_param_rand_gT_indep_post_challB
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a b : F)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tB) (gT₁ gT₂ : G) :
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT₁) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT₂) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_rand gp gen a b gT₁)
    (impl₂ := honestImpl_param_rand gp gen a b gT₂)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s'.tB)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_rand_gT_indep_post_challB (gen := gen) gp h_cp a b t s'
        (next_ne_epoch_of_epoch_le h_pre) gT₁ gT₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_param_rand_t_monotone (gen := gen) gp a b gT₂ t s' z hz).2)
    s h_post

omit [Inhabited F] [Fintype G] in
/-- In the special rand case, once A has reached the challenge epoch, future
oracle steps preserve the invariant `gp.challengeEpoch ≤ tA`. -/
lemma honestImpl_param_rand_preserves_post_challA_special
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (a b : F) (gT : G) :
    QueryImpl.PreservesInv (honestImpl_param_rand gp gen a b gT)
      (fun s : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s.tA) := by
  intro t s hs z hz
  rcases h_special_case with ⟨h_challengeEpoch, h_cp⟩
  match t with
  | OSendB_rleak =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendB_rleak).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b OSendB_rleak s z hz').1
  | OSendA_rleak =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendA_rleak).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b OSendA_rleak s z hz').1
  | OChallA =>
      have h_epoch_false : isChallengeEpoch gp { s with tA := s.tA + 1 } = false := by
        simp [isChallengeEpoch, GameState.tP, h_cp, h_challengeEpoch] at hs ⊢
        omega
      have h_pred_false :
          (validStep s.lastAction CKAAction.challA &&
            (gp.challengedParty == CKAParty.A) &&
            isChallengeEpoch gp { s with tA := s.tA + 1 }) = false := by
        simp [h_cp, h_epoch_false]
      have h_run :
          (honestImpl_param_rand gp gen a b gT OChallA).run s =
            (pure (none, s) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
        simp only [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        calc
          (honestChallA_param_rand (F := F) gp gen b gT ()).run s =
              (oracleChallA gp true (ddhCKA F G gen) ()).run s :=
            honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b gT s h_pred_false
          _ = (pure (none, s) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
            unfold oracleChallA
            rw [StateT.run_get_bind]
            simp [h_epoch_false]
      rw [h_run] at hz
      have hz_eq : z = (none, s) := by
        simpa [support_pure] using hz
      simpa [hz_eq] using hs
  | OChallB =>
      have h_run :
          (honestImpl_param_rand gp gen a b gT OChallB).run s =
            (pure (none, s) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
        simp only [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        have h_pred_false :
            (validStep s.lastAction CKAAction.challB &&
              (gp.challengedParty == CKAParty.B) &&
              isChallengeEpoch gp { s with tB := s.tB + 1 }) = false := by
          simp [h_cp]
        calc
          (honestChallB_param_rand (F := F) gp gen b gT ()).run s =
              (oracleChallB gp true (ddhCKA F G gen) ()).run s :=
            honestChallB_param_rand_run_eq_when_pred_false (gen := gen) gp b gT s h_pred_false
          _ = (pure (none, s) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
            unfold oracleChallB
            rw [StateT.run_get_bind]
            simp [h_cp]
      rw [h_run] at hz
      have hz_eq : z = (none, s) := by
        simpa [support_pure] using hz
      simpa [hz_eq] using hs
  | OCorruptB =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b OCorruptB).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b OCorruptB s z hz').1
  | OCorruptA =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b OCorruptA).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b OCorruptA s z hz').1
  | ORecvB =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b ORecvB).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b ORecvB s z hz').1
  | OSendB =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendB).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b OSendB s z hz').1
  | ORecvA =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b ORecvA).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b ORecvA s z hz').1
  | OSendA =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendA).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b OSendA s z hz').1
  | OUnif n =>
      have hz' : z ∈ support ((honestImpl_param_real gp gen a b (OUnif n)).run s) := by
        simpa [honestImpl_param_rand, honestImpl_param_real] using hz
      exact hs.trans
        (honestImpl_param_real_t_monotone (gen := gen) gp a b (OUnif n) s z hz').1

omit [Inhabited F] [Fintype G] in
/-- In the special rand case, once A has already challenged, the full honest
simulation is independent of the challenge scalar parameter `b`. -/
lemma simulateQ_honest_param_rand_b_indep_post_challA_special
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (a : F) (gT : G)
    (adv : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tA)
    (b₁ b₂ : F) :
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b₁ gT) adv).run s) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b₂ gT) adv).run s) := by
  exact evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    (impl₁ := honestImpl_param_rand gp gen a b₁ gT)
    (impl₂ := honestImpl_param_rand gp gen a b₂ gT)
    (Inv := fun s' : GameState (CKAState F G) G G => gp.challengeEpoch ≤ s'.tA)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_param_rand_b_indep_post_challA_special (gen := gen)
        gp h_special_case a gT t s' h_pre b₁ b₂)
    (hpres₂ := honestImpl_param_rand_preserves_post_challA_special
      (gen := gen) gp h_special_case a b₂ gT)
    s h_post

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- At `challengedParty = .B`, pre-sampling `a ← $ᵗ F` for `honestSendA_param` yields the same
distribution as `oracleSendA`'s internal sample. -/
lemma evalDist_marginalized_honestSendA_param_eq_oracleSendA_at_chal_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (s : GameState (CKAState F G) G G) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      (honestSendA_param (F := F) gp gen a ()).run s) =
    evalDist ((oracleSendA (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
  -- Strategy: case-split on whether the impl call uses parameter `a`.
  -- Outside the firing case, lazy = eager pointwise (a unused).
  -- In the firing case, lazy uses `a`, eager samples `x` — bijection.
  by_cases h_fire :
      validStep s.lastAction CKAAction.sendA = true ∧
      isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = true ∧
      ∃ h : G, s.stA = .sendReady h
  · -- Firing case: bijection
    obtain ⟨h_v, h_o, h, h_stA⟩ := h_fire
    rw [h_stA] at h_o
    have h_eq : (do let a ← ($ᵗ F : ProbComp F)
                    (honestSendA_param (F := F) gp gen a ()).run s) =
                ((oracleSendA (ddhCKA F G gen) ()).run s) := by
      simp [honestSendA_param, oracleSendA, StateT.run_bind, StateT.run_get,
        pure_bind, bind_pure_comp,
        h_v, h_beq, h_stA, h_o, ddhCKA, send]
    rw [h_eq]
  · -- Non-firing case: lazy delegates to eager pointwise (a unused).
    have h_param_eq_eager : ∀ a : F,
        (honestSendA_param (F := F) gp gen a ()).run s =
        (oracleSendA (ddhCKA F G gen) ()).run s := by
      intro a
      cases h_v : validStep s.lastAction CKAAction.sendA with
      | false =>
        simp [honestSendA_param, oracleSendA, StateT.run_bind, StateT.run_get,
          pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        -- The key observation: in honestSendA_param at validStep=true, the if-condition
        -- only depends on `state'.stA = s.stA` via OtherSendBeforeChall (which depends
        -- on tA only, NOT on stA). So we can split on stA and OtherSend without
        -- worrying about state-rewriting.
        cases h_o : isOtherSendBeforeChall gp { s with tA := s.tA + 1 } with
        | false =>
          -- !OtherSend: lazy delegates to else (oracleSendA cka ()). Eager runs same.
          simp [honestSendA_param, oracleSendA, StateT.run_bind, StateT.run_get,
            pure_bind, h_v, h_beq, h_o, ddhCKA, send]
        | true =>
          cases h_stA : s.stA with
          | recvReady x =>
            -- Lazy: match .recvReady _ → pure none. Eager via send .recvReady _ = pure none.
            -- Note: the goal has the embedding's if-condition with `state'.stA = .recvReady x`;
            -- since `isOtherSendBeforeChall` only reads tA (not stA), it agrees with `h_o`.
            have h_o' : isOtherSendBeforeChall gp
                { s with stA := (.recvReady x : CKAState F G), tA := s.tA + 1 } = true := by
              simp only [isOtherSendBeforeChall] at h_o ⊢
              convert h_o using 2
            simp [honestSendA_param, oracleSendA, StateT.run_bind, StateT.run_get,
              pure_bind, h_v, h_beq, h_o', h_stA, ddhCKA, send]
          | sendReady h =>
            -- Contradicts h_fire (which says NOT all of validStep ∧ OtherSend ∧ stA=.sendReady).
            push Not at h_fire
            exact absurd h_stA (h_fire h_v h_o h)
    exact evalDist_sample_bind_eq_of_forall_eq
      (f := fun a => (honestSendA_param (F := F) gp gen a ()).run s)
      (p := (oracleSendA (ddhCKA F G gen) ()).run s)
      h_param_eq_eager

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- At `challengedParty = .A`, pre-sampling `a ← $ᵗ F` for `honestSendB_param`
yields the same distribution as `oracleSendB`'s internal sample. -/
lemma evalDist_marginalized_honestSendB_param_eq_oracleSendB_at_chal_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (s : GameState (CKAState F G) G G) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      (honestSendB_param (F := F) gp gen a ()).run s) =
    evalDist ((oracleSendB (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
  by_cases h_fire :
      validStep s.lastAction CKAAction.sendB = true ∧
      isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = true ∧
      ∃ h : G, s.stB = .sendReady h
  · obtain ⟨h_v, h_o, h, h_stB⟩ := h_fire
    rw [h_stB] at h_o
    have h_eq : (do let a ← ($ᵗ F : ProbComp F)
                    (honestSendB_param (F := F) gp gen a ()).run s) =
                ((oracleSendB (ddhCKA F G gen) ()).run s) := by
      simp [honestSendB_param, oracleSendB, StateT.run_bind, StateT.run_get,
         pure_bind, bind_pure_comp,
        h_v, h_beq, h_stB, h_o, ddhCKA, send]
    rw [h_eq]
  · have h_param_eq_eager : ∀ a : F,
        (honestSendB_param (F := F) gp gen a ()).run s =
        (oracleSendB (ddhCKA F G gen) ()).run s := by
      intro a
      cases h_v : validStep s.lastAction CKAAction.sendB with
      | false =>
        simp [honestSendB_param, oracleSendB, StateT.run_bind, StateT.run_get,
          pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        cases h_o : isOtherSendBeforeChall gp { s with tB := s.tB + 1 } with
        | false =>
          simp [honestSendB_param, oracleSendB, StateT.run_bind, StateT.run_get,
            pure_bind, h_v, h_beq, h_o, ddhCKA, send]
        | true =>
          cases h_stB : s.stB with
          | recvReady x =>
            have h_o' : isOtherSendBeforeChall gp
                { s with stB := (.recvReady x : CKAState F G), tB := s.tB + 1 } = true := by
              simp only [isOtherSendBeforeChall] at h_o ⊢
              convert h_o using 2
            simp [honestSendB_param, oracleSendB, StateT.run_bind, StateT.run_get,
              pure_bind, h_v, h_beq, h_o', h_stB, ddhCKA, send]
          | sendReady h =>
            push Not at h_fire
            exact absurd h_stB (h_fire h_v h_o h)
    exact evalDist_sample_bind_eq_of_forall_eq
      (f := fun a => (honestSendB_param (F := F) gp gen a ()).run s)
      (p := (oracleSendB (ddhCKA F G gen) ()).run s)
      h_param_eq_eager

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- At `challengedParty = .A`, pre-sampling `b ← $ᵗ F` for `honestChallA_param`
yields the same distribution as `oracleChallA gp false` (real branch). -/
lemma evalDist_marginalized_honestChallA_param_eq_oracleChallA_at_chal_A
  (gp : GameParams) (h_cp : gp.challengedParty = .A)
  (s : GameState (CKAState F G) G G) :
    evalDist (do
      let b' ← ($ᵗ F : ProbComp F)
      (honestChallA_param (F := F) gp gen b' ()).run s) =
    evalDist ((oracleChallA gp false (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
  by_cases h_fire :
      validStep s.lastAction CKAAction.challA = true ∧
      isChallengeEpoch gp { s with tA := s.tA + 1 } = true ∧
      ∃ h : G, s.stA = .sendReady h
  · obtain ⟨h_v, h_e, h, h_stA⟩ := h_fire
    rw [h_stA] at h_e
    have h_eq : (do let b' ← ($ᵗ F : ProbComp F)
                    (honestChallA_param (F := F) gp gen b' ()).run s) =
                ((oracleChallA gp false (ddhCKA F G gen) ()).run s) := by
      simp [honestChallA_param, oracleChallA, StateT.run_bind, StateT.run_get,
        pure_bind, bind_pure_comp,
        h_v, h_beq, h_stA, h_e, ddhCKA, send]
    rw [h_eq]
  · have h_param_eq_eager : ∀ b' : F,
        (honestChallA_param (F := F) gp gen b' ()).run s =
        (oracleChallA gp false (ddhCKA F G gen) ()).run s := by
      intro b'
      cases h_v : validStep s.lastAction CKAAction.challA with
      | false =>
        simp [honestChallA_param, oracleChallA, StateT.run_bind, StateT.run_get,
          pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        cases h_e : isChallengeEpoch gp { s with tA := s.tA + 1 } with
        | false =>
          simp [honestChallA_param, oracleChallA, StateT.run_bind, StateT.run_get,
            pure_bind, h_v, h_beq, h_e, ddhCKA, send]
        | true =>
          cases h_stA : s.stA with
          | recvReady x =>
            have h_e' : isChallengeEpoch gp
                { s with stA := (.recvReady x : CKAState F G), tA := s.tA + 1 } = true := by
              simp only [isChallengeEpoch] at h_e ⊢
              convert h_e using 2
            simp [honestChallA_param, oracleChallA, StateT.run_bind, StateT.run_get,
              pure_bind, h_v, h_beq, h_e', h_stA, ddhCKA, send]
          | sendReady h =>
            push Not at h_fire
            exact absurd h_stA (h_fire h_v h_e h)
    exact evalDist_sample_bind_eq_of_forall_eq
      (f := fun b' => (honestChallA_param (F := F) gp gen b' ()).run s)
      (p := (oracleChallA gp false (ddhCKA F G gen) ()).run s)
      h_param_eq_eager

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- At `challengedParty = .A`, pre-sampling both the challenge scalar
`b' ← $ᵗ F` and the random challenge key `gT ← $ᵗ G` for `honestChallA_param_rand`
yields the same distribution as `oracleChallA gp true` (rand branch). -/
lemma evalDist_marginalized_honestChallA_param_rand_eq_oracleChallA_at_chal_A
  (gp : GameParams) (h_cp : gp.challengedParty = .A)
  (s : GameState (CKAState F G) G G) :
    evalDist (do
      let b' ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (honestChallA_param_rand (F := F) gp gen b' gT ()).run s) =
    evalDist ((oracleChallA gp true (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
  by_cases h_fire :
      validStep s.lastAction CKAAction.challA = true ∧
      isChallengeEpoch gp { s with tA := s.tA + 1 } = true ∧
      ∃ h : G, s.stA = .sendReady h
  · obtain ⟨h_v, h_e, h, h_stA⟩ := h_fire
    rw [h_stA] at h_e
    have h_eq : (do
          let b' ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (honestChallA_param_rand (F := F) gp gen b' gT ()).run s) =
        ((oracleChallA gp true (ddhCKA F G gen) ()).run s) := by
      simp [honestChallA_param_rand, oracleChallA, StateT.run_bind, StateT.run_get,
        pure_bind, bind_pure_comp,
        h_v, h_beq, h_stA, h_e, ddhCKA, send]
    rw [h_eq]
  · have h_param_eq_eager : ∀ b' : F, ∀ gT : G,
        (honestChallA_param_rand (F := F) gp gen b' gT ()).run s =
        (oracleChallA gp true (ddhCKA F G gen) ()).run s := by
      intro b' gT
      cases h_v : validStep s.lastAction CKAAction.challA with
      | false =>
        simp [honestChallA_param_rand, oracleChallA, StateT.run_bind, StateT.run_get,
          pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        cases h_e : isChallengeEpoch gp { s with tA := s.tA + 1 } with
        | false =>
          simp [honestChallA_param_rand, oracleChallA, StateT.run_bind, StateT.run_get,
            pure_bind, h_v, h_beq, h_e, ddhCKA, send]
        | true =>
          cases h_stA : s.stA with
          | recvReady x =>
            have h_e' : isChallengeEpoch gp
                { s with stA := (.recvReady x : CKAState F G), tA := s.tA + 1 } = true := by
              simp only [isChallengeEpoch] at h_e ⊢
              convert h_e using 2
            simp [honestChallA_param_rand, oracleChallA, StateT.run_bind, StateT.run_get,
              pure_bind, h_v, h_beq, h_e', h_stA, ddhCKA,
              send]
          | sendReady h =>
            push Not at h_fire
            exact absurd h_stA (h_fire h_v h_e h)
    exact evalDist_sample_bind₂_eq_of_forall_eq
      (f := fun b' gT => (honestChallA_param_rand (F := F) gp gen b' gT ()).run s)
      (p := (oracleChallA gp true (ddhCKA F G gen) ()).run s)
      h_param_eq_eager

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- At `challengedParty = .B`, pre-sampling `b ← $ᵗ F` for `honestChallB_param`
yields the same distribution as `oracleChallB gp false` (real branch). -/
lemma evalDist_marginalized_honestChallB_param_eq_oracleChallB_at_chal_B
  (gp : GameParams) (h_cp : gp.challengedParty = .B)
  (s : GameState (CKAState F G) G G) :
    evalDist (do
      let b' ← ($ᵗ F : ProbComp F)
      (honestChallB_param (F := F) gp gen b' ()).run s) =
    evalDist ((oracleChallB gp false (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
  by_cases h_fire :
      validStep s.lastAction CKAAction.challB = true ∧
      isChallengeEpoch gp { s with tB := s.tB + 1 } = true ∧
      ∃ h : G, s.stB = .sendReady h
  · obtain ⟨h_v, h_e, h, h_stB⟩ := h_fire
    rw [h_stB] at h_e
    have h_eq : (do let b' ← ($ᵗ F : ProbComp F)
                    (honestChallB_param (F := F) gp gen b' ()).run s) =
                ((oracleChallB gp false (ddhCKA F G gen) ()).run s) := by
      simp [honestChallB_param, oracleChallB, StateT.run_bind, StateT.run_get,
        pure_bind, bind_pure_comp,
        h_v, h_beq, h_stB, h_e, ddhCKA, send]
    rw [h_eq]
  · have h_param_eq_eager : ∀ b' : F,
        (honestChallB_param (F := F) gp gen b' ()).run s =
        (oracleChallB gp false (ddhCKA F G gen) ()).run s := by
      intro b'
      cases h_v : validStep s.lastAction CKAAction.challB with
      | false =>
        simp [honestChallB_param, oracleChallB, StateT.run_bind, StateT.run_get,
          pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        cases h_e : isChallengeEpoch gp { s with tB := s.tB + 1 } with
        | false =>
          simp [honestChallB_param, oracleChallB, StateT.run_bind, StateT.run_get,
            pure_bind, h_v, h_beq, h_e, ddhCKA, send]
        | true =>
          cases h_stB : s.stB with
          | recvReady x =>
            have h_e' : isChallengeEpoch gp
                { s with stB := (.recvReady x : CKAState F G), tB := s.tB + 1 } = true := by
              simp only [isChallengeEpoch] at h_e ⊢
              convert h_e using 2
            simp [honestChallB_param, oracleChallB, StateT.run_bind, StateT.run_get,
              pure_bind, h_v, h_beq, h_e', h_stB, ddhCKA, send]
          | sendReady h =>
            push Not at h_fire
            exact absurd h_stB (h_fire h_v h_e h)
    exact evalDist_sample_bind_eq_of_forall_eq
      (f := fun b' => (honestChallB_param (F := F) gp gen b' ()).run s)
      (p := (oracleChallB gp false (ddhCKA F G gen) ()).run s)
      h_param_eq_eager



end Step2

end ddhCKA
