/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.GameOracles.Defs
import ToVCVio.Control.StateT

/-!
# CKA from DDH — Game Oracles — Per-Query Reasoning

The ordinary CKA send/challenge oracles sample Diffie-Hellman scalars inside the
handler. The parameterized honest oracles make the relevant samples explicit:
`a` for the embedding send, `b` for the real challenge, and `gT` for the random
challenge output key. Away from those selected events, they agree with the
regular CKA oracle.

For each parameterized send/challenge query, the cases are:

* **off-party**: the query is for the branch not selected by
  `gp.challengedParty`;
* **off-event**: the branch matches, but the timing or previous-action guard is
  false;
* **active**: the selected send or challenge event fires, so the parameterized
  oracle actually uses its external parameter.

The lemmas below prove the corresponding dispatch equalities, active run
equations, post-event parameter independence facts, and state/counter
preservation facts used by the whole-adversary bridge.
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

/-! ### Off-party dispatch

Each `O_param` oracle, when the firing party of the oracle does not match
`challengedParty`, is pointwise equal to the regular CKA oracle. -/

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- When the challenged party is `A` (so `sendA` is not the embedding
side), `honestSendA_param` is pointwise equal to `oracleSendA (ddhCKA F G gen)`. -/
lemma honestSendA_param_run_eq_at_chal_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (a : F) (s : GameState (CKAState F G) G G) :
    (honestSendA_param (F := F) gp gen a ()).run s =
    (oracleSendA (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.B) = false := by simp [h_cp]
  simp [honestSendA_param, StateT.run, h_beq]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Off-party dispatch: at `challengedParty = .B`, `honestSendB_param` is pointwise equal
to `oracleSendB (ddhCKA F G gen)`. -/
lemma honestSendB_param_run_eq_at_chal_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (a : F) (s : GameState (CKAState F G) G G) :
    (honestSendB_param (F := F) gp gen a ()).run s =
    (oracleSendB (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.A) = false := by simp [h_cp]
  simp [honestSendB_param, StateT.run, h_beq]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Off-party dispatch: at `challengedParty = .B`, `honestChallA_param` is pointwise equal
to `oracleChallA gp (ddhCKA F G gen)`. -/
lemma honestChallA_param_run_eq_at_chal_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (b : F) (s : GameState (CKAState F G) G G) :
    (honestChallA_param (F := F) gp gen b ()).run s =
  (oracleChallA gp false (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.A) = false := by simp [h_cp]
  unfold honestChallA_param honestChallA_param_mode
  simp [h_beq]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Off-party dispatch: at `challengedParty = .A`, `honestChallB_param` is pointwise equal
to `oracleChallB gp (ddhCKA F G gen)`. -/
lemma honestChallB_param_run_eq_at_chal_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (b : F) (s : GameState (CKAState F G) G G) :
    (honestChallB_param (F := F) gp gen b ()).run s =
  (oracleChallB gp false (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.B) = false := by simp [h_cp]
  unfold honestChallB_param honestChallB_param_mode
  simp [h_beq]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-! ### Predicate-false dispatch (send oracles)

When the firing predicate (conjunction of valid-step + party match +
event-timing) is false at a query, the `O_param` `send` oracle reduces to the
regular CKA `send` oracle. The two `_param` `send` lemmas below cover both
parties; the analogous `chall` lemmas appear in the chall section. -/

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- **Generic predicate-false dispatch for `sendA`.**

Lazy `sendA` equals eager `oracleSendA` at any state where the
embedding-firing predicate is false. -/
lemma honestSendA_param_run_eq_when_pred_false
    (gp : GameParams) (a : F) (s : GameState (CKAState F G) G G)
    (h_pred : (validStep s.lastAction CKAAction.sendA &&
               (gp.challengedParty == CKAParty.B) &&
               isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = false) :
    (honestSendA_param (F := F) gp gen a ()).run s =
    (oracleSendA (ddhCKA F G gen) ()).run s := by
  unfold honestSendA_param
  exact StateT.run_get_bind_ite_eq_else_of_pred_false _ _ _ s h_pred

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Symmetric: lazy `sendB` equals eager when the on-party (`challengedParty = .A`)
embedding predicate is false. -/
lemma honestSendB_param_run_eq_when_pred_false
    (gp : GameParams) (a : F) (s : GameState (CKAState F G) G G)
    (h_pred : (validStep s.lastAction CKAAction.sendB &&
               (gp.challengedParty == CKAParty.A) &&
               isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = false) :
    (honestSendB_param (F := F) gp gen a ()).run s =
    (oracleSendB (ddhCKA F G gen) ()).run s := by
  unfold honestSendB_param
  exact StateT.run_get_bind_ite_eq_else_of_pred_false _ _ _ s h_pred

/-! ### Active-firing run equations (send oracles)

When the selected send event fires, `honestSend{A,B}_param` does not sample a
fresh scalar. It uses the external scalar `a` and reduces to a pure
answer/post-state pair. -/

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Active `sendA` run equation at `challengedParty = .B`.

If `sendA` is valid, the send-before-challenge guard holds after incrementing
`tA`, and `s.stA = .sendReady h`, then the handler returns
`some (a • gen, a • h)` and moves A to the corresponding receive-ready
post-state. -/
lemma honestSendA_param_run_eq_at_chal_B_inr
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (a : F) (h : G) (s : GameState (CKAState F G) G G)
    (h_valid : validStep s.lastAction CKAAction.sendA = true)
    (h_other : isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = true)
    (h_stA : s.stA = CKAState.sendReady h) :
    (honestSendA_param (F := F) gp gen a ()).run s =
      pure (some (a • gen, a • h),
        { s with
          stA := (.recvReady a : CKAState F G),
          rhoA := some (a • gen),
          keyA := some (a • h),
          lastAction := some .sendA,
          tA := s.tA + 1 }) := by
  have h_other' :
      isOtherSendBeforeChall gp { s with stA := CKAState.sendReady h, tA := s.tA + 1 } = true := by
    simpa [h_stA] using h_other
  simp [honestSendA_param, StateT.run_bind, StateT.run_get, StateT.run_set,
    pure_bind, h_valid, h_cp, h_other', h_stA]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Active `sendB` run equation at `challengedParty = .A`.

If `sendB` is valid, the send-before-challenge guard holds after incrementing
`tB`, and `s.stB = .sendReady h`, then the handler returns
`some (a • gen, a • h)` and moves B to the corresponding receive-ready
post-state. -/
lemma honestSendB_param_run_eq_at_chal_A_inr
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (a : F) (h : G) (s : GameState (CKAState F G) G G)
    (h_valid : validStep s.lastAction CKAAction.sendB = true)
    (h_other : isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = true)
    (h_stB : s.stB = CKAState.sendReady h) :
    (honestSendB_param (F := F) gp gen a ()).run s =
      pure (some (a • gen, a • h),
        { s with
          stB := (.recvReady a : CKAState F G),
          rhoB := some (a • gen),
          keyB := some (a • h),
          lastAction := some .sendB,
          tB := s.tB + 1 }) := by
  have h_other' :
      isOtherSendBeforeChall gp { s with stB := CKAState.sendReady h, tB := s.tB + 1 } = true := by
    simpa [h_stB] using h_other
  simp [honestSendB_param, StateT.run_bind, StateT.run_get, StateT.run_set,
    pure_bind, h_valid, h_cp, h_other', h_stB]

/-! ### Special-case impl-level independence (real branch)

When `challengeEpoch = 1` and `challengedParty = .A`, the embedding event
(`sendB` at `t* − 1 = 0`) is unreachable, so `honestImpl_param_real` never
consumes `a`. The lemma below states `a`-independence of the full impl at
every state, with no state precondition. -/

omit [Inhabited F] [Fintype G] in
/-- In the special case `challengeEpoch = 1`, `challengedParty = A`, the output
of `honestImpl_param_real` does not depend on the parameter `a` at any query. -/
lemma honestImpl_param_real_a_indep_special
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (b : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (a₁ a₂ : F) :
    (honestImpl_param_real gp gen a₁ b t).run s =
    (honestImpl_param_real gp gen a₂ b t).run s := by
  rcases h_special_case with ⟨h_challengeEpoch, h_cp⟩
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestChallB_param, honestChallB_param_mode]
  | OChallA =>
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestChallA_param, honestChallA_param_mode]
  | ORecvB => rfl
  | OSendB =>
    change (honestSendB_param gp gen a₁ ()).run s = (honestSendB_param gp gen a₂ ()).run s
    have h_pred_false :
        (validStep s.lastAction CKAAction.sendB &&
          (gp.challengedParty == CKAParty.A) &&
          isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = false := by
      have h_other_false :
          isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = false := by
        simp [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other, h_challengeEpoch]
      simp [h_cp, h_other_false]
    rw [honestSendB_param_run_eq_when_pred_false (gen := gen) gp a₁ s h_pred_false,
      honestSendB_param_run_eq_when_pred_false (gen := gen) gp a₂ s h_pred_false]
  | ORecvA => rfl
  | OSendA =>
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestSendA_param]
  | OUnif _ => rfl

/-! ### Predicate-false dispatch (chall oracles, real and rand)

Counterpart of the `send`-side predicate-false section above: when the
challenge-firing predicate is false, each `O_param` `chall` oracle (in
both `_real` and `_rand` modes) reduces to the regular `oracleChall`. -/

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Lazy `challA` equals eager when the challenge-firing predicate is false. -/
lemma honestChallA_param_run_eq_when_pred_false
    (gp : GameParams) (b : F) (s : GameState (CKAState F G) G G)
    (h_pred : (validStep s.lastAction CKAAction.challA &&
               (gp.challengedParty == CKAParty.A) &&
               isChallengeEpoch gp { s with tA := s.tA + 1 }) = false) :
    (honestChallA_param (F := F) gp gen b ()).run s =
    (oracleChallA gp false (ddhCKA F G gen) ()).run s := by
  unfold honestChallA_param honestChallA_param_mode
  exact StateT.run_get_bind_ite_eq_else_of_pred_false _ _ _ s h_pred

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Lazy `challB` equals eager when the challenge-firing predicate is false. -/
lemma honestChallB_param_run_eq_when_pred_false
    (gp : GameParams) (b : F) (s : GameState (CKAState F G) G G)
    (h_pred : (validStep s.lastAction CKAAction.challB &&
               (gp.challengedParty == CKAParty.B) &&
               isChallengeEpoch gp { s with tB := s.tB + 1 }) = false) :
    (honestChallB_param (F := F) gp gen b ()).run s =
    (oracleChallB gp false (ddhCKA F G gen) ()).run s := by
  unfold honestChallB_param honestChallB_param_mode
  exact StateT.run_get_bind_ite_eq_else_of_pred_false _ _ _ s h_pred

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Rand lazy `challA` equals eager when the challenge-firing predicate is false. -/
lemma honestChallA_param_rand_run_eq_when_pred_false
    (gp : GameParams) (b : F) (gT : G) (s : GameState (CKAState F G) G G)
    (h_pred : (validStep s.lastAction CKAAction.challA &&
               (gp.challengedParty == CKAParty.A) &&
               isChallengeEpoch gp { s with tA := s.tA + 1 }) = false) :
    (honestChallA_param_rand (F := F) gp gen b gT ()).run s =
    (oracleChallA gp true (ddhCKA F G gen) ()).run s := by
  unfold honestChallA_param_rand honestChallA_param_mode
  exact StateT.run_get_bind_ite_eq_else_of_pred_false _ _ _ s h_pred

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Rand lazy `challB` equals eager when the challenge-firing predicate is false. -/
lemma honestChallB_param_rand_run_eq_when_pred_false
    (gp : GameParams) (b : F) (gT : G) (s : GameState (CKAState F G) G G)
    (h_pred : (validStep s.lastAction CKAAction.challB &&
               (gp.challengedParty == CKAParty.B) &&
               isChallengeEpoch gp { s with tB := s.tB + 1 }) = false) :
    (honestChallB_param_rand (F := F) gp gen b gT ()).run s =
    (oracleChallB gp true (ddhCKA F G gen) ()).run s := by
  unfold honestChallB_param_rand honestChallB_param_mode
  exact StateT.run_get_bind_ite_eq_else_of_pred_false _ _ _ s h_pred

/-! ### Active-firing run equations (chall oracles)

Mirror of the active-firing run equations for the `send` oracles for
the challenge oracles. At the firing event the oracle is deterministic in
the external `b` (the state update is identical to that of a CKA challA/B
with internal sample `x = b`); the value returned to the adversary depends on
`mode` (real: `b • h`, rand: external `gT`). -/
omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Active branch-mode `challA` run equation at `challengedParty = A` with
`s.stA = .sendReady h` for some `h : G`. The state update is shared by real and
rand modes; only `mode.outputKey` changes the value returned to the adversary. -/
lemma honestChallA_param_mode_run_eq_at_chal_A_inr
    (mode : HonestChallengeMode) (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (b : F) (gT h : G) (s : GameState (CKAState F G) G G)
    (h_valid : validStep s.lastAction CKAAction.challA = true)
    (h_epoch : isChallengeEpoch gp { s with tA := s.tA + 1 } = true)
    (h_stA : s.stA = CKAState.sendReady h) :
    (honestChallA_param_mode (F := F) mode gp gen b gT ()).run s =
      pure (some (b • gen, mode.outputKey b h gT),
        { s with
          stA := (.recvReady b : CKAState F G),
          rhoA := some (b • gen),
          keyA := some (b • h),
          lastAction := some .challA,
          tA := s.tA + 1 }) := by
  have h_epoch' :
      isChallengeEpoch gp
        { s with stA := CKAState.sendReady h, tA := s.tA + 1 } = true := by
    simpa [h_stA] using h_epoch
  simp [honestChallA_param_mode, StateT.run_bind, StateT.run_get, StateT.run_set,
    pure_bind, h_valid, h_cp, h_epoch', h_stA]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Active branch-mode `challB` run equation at `challengedParty = B`, symmetric to
`honestChallA_param_mode_run_eq_at_chal_A_inr`. -/
lemma honestChallB_param_mode_run_eq_at_chal_B_inr
    (mode : HonestChallengeMode) (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (b : F) (gT h : G) (s : GameState (CKAState F G) G G)
    (h_valid : validStep s.lastAction CKAAction.challB = true)
    (h_epoch : isChallengeEpoch gp { s with tB := s.tB + 1 } = true)
    (h_stB : s.stB = CKAState.sendReady h) :
    (honestChallB_param_mode (F := F) mode gp gen b gT ()).run s =
      pure (some (b • gen, mode.outputKey b h gT),
        { s with
          stB := (.recvReady b : CKAState F G),
          rhoB := some (b • gen),
          keyB := some (b • h),
          lastAction := some .challB,
          tB := s.tB + 1 }) := by
  have h_epoch' :
      isChallengeEpoch gp
        { s with stB := CKAState.sendReady h, tB := s.tB + 1 } = true := by
     simpa [h_stB] using h_epoch
  simp [honestChallB_param_mode, StateT.run_bind, StateT.run_get, StateT.run_set,
    pure_bind, h_valid, h_cp, h_epoch', h_stB]

/-! ### Special-case impl-level independence (rand branch) -/

omit [Inhabited F] [Fintype G] in
/-- Rand special case: the output of `honestImpl_param_rand` does not depend
on the embedding parameter `a`, for the same reason as in
`honestImpl_param_real_a_indep_special`. -/
lemma honestImpl_param_rand_a_indep_special
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (b : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (a₁ a₂ : F) :
    (honestImpl_param_rand gp gen a₁ b gT t).run s =
    (honestImpl_param_rand gp gen a₂ b gT t).run s := by
  rcases h_special_case with ⟨h_challengeEpoch, h_cp⟩
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestChallB_param_rand, honestChallB_param_mode]
  | OChallA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestChallA_param_rand, honestChallA_param_mode]
  | ORecvB => rfl
  | OSendB =>
    change (honestSendB_param gp gen a₁ ()).run s = (honestSendB_param gp gen a₂ ()).run s
    have h_pred_false :
        (validStep s.lastAction CKAAction.sendB &&
          (gp.challengedParty == CKAParty.A) &&
          isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = false := by
      have h_other_false :
          isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = false := by
        simp [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other, h_challengeEpoch]
      simp [h_cp, h_other_false]
    rw [honestSendB_param_run_eq_when_pred_false (gen := gen) gp a₁ s h_pred_false,
      honestSendB_param_run_eq_when_pred_false (gen := gen) gp a₂ s h_pred_false]
  | ORecvA => rfl
  | OSendA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestSendA_param]
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Special rand case: once A has reached the challenge epoch (`gp.challengeEpoch ≤ s.tA`),
the output of `honestImpl_param_rand` no longer depends on the challenge
parameter `b`, because no further `challA` can fire. -/
lemma honestImpl_param_rand_b_indep_post_challA_special
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (a : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : gp.challengeEpoch ≤ s.tA)
    (b₁ b₂ : F) :
    (honestImpl_param_rand gp gen a b₁ gT t).run s =
    (honestImpl_param_rand gp gen a b₂ gT t).run s := by
  rcases h_special_case with ⟨h_challengeEpoch, h_cp⟩
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestChallB_param_rand, honestChallB_param_mode]
  | OChallA =>
    change (honestChallA_param_rand gp gen b₁ gT ()).run s =
      (honestChallA_param_rand gp gen b₂ gT ()).run s
    have h_epoch_false : isChallengeEpoch gp { s with tA := s.tA + 1 } = false := by
      simp [isChallengeEpoch, GameState.tP, h_cp, h_challengeEpoch] at h_post ⊢
      omega
    have h_pred_false :
        (validStep s.lastAction CKAAction.challA &&
          (gp.challengedParty == CKAParty.A) &&
          isChallengeEpoch gp { s with tA := s.tA + 1 }) = false := by
      simp [h_cp, h_epoch_false]
    rw [honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b₁ gT s h_pred_false,
      honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b₂ gT s h_pred_false]
  | ORecvB => rfl
  | OSendB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestSendB_param]
  | ORecvA => rfl
  | OSendA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, h_cp,
      honestSendA_param]
  | OUnif _ => rfl

/-! ### Per-oracle parameter independence

For each individual `O_param` oracle, the output is unchanged when the
external scalar (`a`, `b`, or `gT`) varies, off the firing event. These are
the *handler-local* `hindep` lemmas used by `consumeLazy`'s parameter-
independence hypothesis, and by the full-impl lemmas below. -/

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- When the challenged party is `B`, `honestSendA_param` is `a`-independent
at any state where the embedding cannot fire (`s.tA + 1 ≠ gp.challengeEpoch - 1`,
i.e., this `sendA` call is not the one that would substitute `a`). -/
lemma honestSendA_param_a_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a₁ a₂ : F)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch - 1) :
    (honestSendA_param (F := F) gp gen a₁ ()).run s =
    (honestSendA_param (F := F) gp gen a₂ ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.sendA &&
       (gp.challengedParty == CKAParty.B) &&
       isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = false := by
    have h_o : isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = false := by
      simp only [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other]
      exact decide_eq_false h_post
    simp [h_o]
  rw [honestSendA_param_run_eq_when_pred_false gp a₁ s h_pred_false,
      honestSendA_param_run_eq_when_pred_false gp a₂ s h_pred_false]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Mirror of `honestSendA_param_a_indep_post_event` at `challengedParty = .A`: after the
sendB embedding has fired, further sendB calls are `a`-independent. -/
lemma honestSendB_param_a_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (a₁ a₂ : F)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch - 1) :
    (honestSendB_param (F := F) gp gen a₁ ()).run s =
    (honestSendB_param (F := F) gp gen a₂ ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.sendB &&
       (gp.challengedParty == CKAParty.A) &&
       isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = false := by
    have h_o : isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = false := by
      simp only [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other]
      exact decide_eq_false h_post
    simp [h_o]
  rw [honestSendB_param_run_eq_when_pred_false gp a₁ s h_pred_false,
      honestSendB_param_run_eq_when_pred_false gp a₂ s h_pred_false]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- After the `challA` challenge has fired (`s.tA ≥ gp.challengeEpoch`), further
challA calls are `b`-independent. -/
lemma honestChallA_param_b_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (b₁ b₂ : F)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch) :
    (honestChallA_param (F := F) gp gen b₁ ()).run s =
    (honestChallA_param (F := F) gp gen b₂ ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.challA &&
       (gp.challengedParty == CKAParty.A) &&
       isChallengeEpoch gp { s with tA := s.tA + 1 }) = false := by
    have h_e : isChallengeEpoch gp { s with tA := s.tA + 1 } = false := by
      simp only [isChallengeEpoch, GameState.tP, h_cp]
      exact decide_eq_false h_post
    simp [h_e]
  rw [honestChallA_param_run_eq_when_pred_false gp b₁ s h_pred_false,
      honestChallA_param_run_eq_when_pred_false gp b₂ s h_pred_false]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- After the `challB` challenge has fired (`s.tB ≥ gp.challengeEpoch`), further
challB calls are `b`-independent. -/
lemma honestChallB_param_b_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b₁ b₂ : F)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch) :
    (honestChallB_param (F := F) gp gen b₁ ()).run s =
    (honestChallB_param (F := F) gp gen b₂ ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.challB &&
       (gp.challengedParty == CKAParty.B) &&
       isChallengeEpoch gp { s with tB := s.tB + 1 }) = false := by
    have h_e : isChallengeEpoch gp { s with tB := s.tB + 1 } = false := by
      simp only [isChallengeEpoch, GameState.tP, h_cp]
      exact decide_eq_false h_post
    simp [h_e]
  rw [honestChallB_param_run_eq_when_pred_false gp b₁ s h_pred_false,
      honestChallB_param_run_eq_when_pred_false gp b₂ s h_pred_false]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Rand challenge handler is `b`-independent after A's challenge window. -/
lemma honestChallA_param_rand_b_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (b₁ b₂ : F) (gT : G)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch) :
    (honestChallA_param_rand (F := F) gp gen b₁ gT ()).run s =
    (honestChallA_param_rand (F := F) gp gen b₂ gT ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.challA &&
       (gp.challengedParty == CKAParty.A) &&
       isChallengeEpoch gp { s with tA := s.tA + 1 }) = false := by
    have h_e : isChallengeEpoch gp { s with tA := s.tA + 1 } = false := by
      simp only [isChallengeEpoch, GameState.tP, h_cp]
      exact decide_eq_false h_post
    simp [h_e]
  rw [honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b₁ gT s h_pred_false,
      honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b₂ gT s h_pred_false]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Rand challenge handler is `b`-independent after B's challenge window. -/
lemma honestChallB_param_rand_b_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b₁ b₂ : F) (gT : G)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch) :
    (honestChallB_param_rand (F := F) gp gen b₁ gT ()).run s =
    (honestChallB_param_rand (F := F) gp gen b₂ gT ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.challB &&
       (gp.challengedParty == CKAParty.B) &&
       isChallengeEpoch gp { s with tB := s.tB + 1 }) = false := by
    have h_e : isChallengeEpoch gp { s with tB := s.tB + 1 } = false := by
      simp only [isChallengeEpoch, GameState.tP, h_cp]
      exact decide_eq_false h_post
    simp [h_e]
  rw [honestChallB_param_rand_run_eq_when_pred_false (gen := gen) gp b₁ gT s h_pred_false,
      honestChallB_param_rand_run_eq_when_pred_false (gen := gen) gp b₂ gT s h_pred_false]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Rand challenge handler is `gT`-independent after A's challenge window. -/
lemma honestChallA_param_rand_gT_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (b : F) (gT₁ gT₂ : G)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch) :
    (honestChallA_param_rand (F := F) gp gen b gT₁ ()).run s =
    (honestChallA_param_rand (F := F) gp gen b gT₂ ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.challA &&
       (gp.challengedParty == CKAParty.A) &&
       isChallengeEpoch gp { s with tA := s.tA + 1 }) = false := by
    have h_e : isChallengeEpoch gp { s with tA := s.tA + 1 } = false := by
      simp only [isChallengeEpoch, GameState.tP, h_cp]
      exact decide_eq_false h_post
    simp [h_e]
  rw [honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b gT₁ s h_pred_false,
      honestChallA_param_rand_run_eq_when_pred_false (gen := gen) gp b gT₂ s h_pred_false]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Rand challenge handler is `gT`-independent after B's challenge window. -/
lemma honestChallB_param_rand_gT_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b : F) (gT₁ gT₂ : G)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch) :
    (honestChallB_param_rand (F := F) gp gen b gT₁ ()).run s =
    (honestChallB_param_rand (F := F) gp gen b gT₂ ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.challB &&
       (gp.challengedParty == CKAParty.B) &&
       isChallengeEpoch gp { s with tB := s.tB + 1 }) = false := by
    have h_e : isChallengeEpoch gp { s with tB := s.tB + 1 } = false := by
      simp only [isChallengeEpoch, GameState.tP, h_cp]
      exact decide_eq_false h_post
    simp [h_e]
  rw [honestChallB_param_rand_run_eq_when_pred_false (gen := gen) gp b gT₁ s h_pred_false,
      honestChallB_param_rand_run_eq_when_pred_false (gen := gen) gp b gT₂ s h_pred_false]

omit [Inhabited F] [Fintype G] in
/-! ### Full-impl parameter independence

Per-oracle independence above promoted to the full `honestImpl_param_real` /
`honestImpl_param_rand` set: under a state invariant ensuring no further
firing event can happen, the output at every oracle index is independent of
the corresponding parameter. Together with the special-case lemmas, these
provide the `hindep` hypotheses that `consumeLazy` requires in
`evalDist_ckaSecurityImpl_lazy_eq_eager`. -/

omit [Inhabited F] [Fintype G] in
/-- **Full impl-level `a`-independence at `challengedParty = .B`, post-`sendA`-event.**

Lazy honest impl is `a`-independent at every oracle index, given the
state invariant `s.tA + 1 ≠ gp.challengeEpoch - 1` (no further sendA embedding
can fire). -/
lemma honestImpl_param_real_a_indep_post_sendA
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch - 1)
    (a₁ a₂ : F) :
    (honestImpl_param_real gp gen a₁ b t).run s =
    (honestImpl_param_real gp gen a₂ b t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl  -- corruptB
  | OCorruptA => rfl  -- corruptA
  | OChallB =>  -- challB at h_cp = .B uses parameter b, not a
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_param, honestChallB_param_mode, h_cp]
  | OChallA =>  -- challA at h_cp = .B is off-party
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_param, honestChallA_param_mode, h_cp]
  | ORecvB => rfl  -- recvB
  | OSendB =>  -- sendB at h_cp = .B is off-party
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestSendB_param, h_cp]
  | ORecvA => rfl  -- recvA
  | OSendA =>  -- sendA: hit at challengedParty=B
    change (honestSendA_param gp gen a₁ ()).run s = (honestSendA_param gp gen a₂ ()).run s
    exact honestSendA_param_a_indep_post_event (gen := gen) gp h_cp a₁ a₂ s h_post
  | OUnif _ => rfl  -- oracleUnif

omit [Inhabited F] [Fintype G] in
/-- Mirror of `honestImpl_param_real_a_indep_post_sendA` at `challengedParty = .A`. Lazy
honest impl is `a`-independent at every oracle index, given the state
invariant `s.tB + 1 ≠ gp.challengeEpoch - 1` (no further sendB embedding can fire). -/
lemma honestImpl_param_real_a_indep_post_sendB
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (b : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch - 1)
    (a₁ a₂ : F) :
    (honestImpl_param_real gp gen a₁ b t).run s =
    (honestImpl_param_real gp gen a₂ b t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>  -- challB at h_cp = .A is off-party
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_param, honestChallB_param_mode, h_cp]
  | OChallA =>  -- challA at h_cp = .A uses parameter b, not a
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_param, honestChallA_param_mode, h_cp]
  | ORecvB => rfl
  | OSendB =>  -- sendB: hit at challengedParty=A
    change (honestSendB_param gp gen a₁ ()).run s = (honestSendB_param gp gen a₂ ()).run s
    exact honestSendB_param_a_indep_post_event (gen := gen) gp h_cp a₁ a₂ s h_post
  | ORecvA => rfl
  | OSendA =>  -- sendA at h_cp = .A is off-party
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestSendA_param, h_cp]
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Mirror of `honestImpl_param_real_a_indep_post_sendA` for the post-`challA`
event at `challengedParty = .A`: the impl is `b`-independent at every oracle index. -/
lemma honestImpl_param_real_b_indep_post_challA
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (a : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch)
    (b₁ b₂ : F) :
    (honestImpl_param_real gp gen a b₁ t).run s =
    (honestImpl_param_real gp gen a b₂ t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>  -- challB at h_cp = .A is off-party
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_param, honestChallB_param_mode, h_cp]
  | OChallA =>  -- challA: hit at challengedParty=A
    change (honestChallA_param gp gen b₁ ()).run s = (honestChallA_param gp gen b₂ ()).run s
    exact honestChallA_param_b_indep_post_event (gen := gen) gp h_cp b₁ b₂ s h_post
  | ORecvB => rfl
  | OSendB =>  -- sendB uses parameter `a`, not `b`
    rfl
  | ORecvA => rfl
  | OSendA =>  -- sendA uses parameter `a`, not `b`
    rfl
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Mirror of `honestImpl_param_real_a_indep_post_sendA` for the post-`challB`
event at `challengedParty = .B`: the impl is `b`-independent at every oracle index. -/
lemma honestImpl_param_real_b_indep_post_challB
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch)
    (b₁ b₂ : F) :
    (honestImpl_param_real gp gen a b₁ t).run s =
    (honestImpl_param_real gp gen a b₂ t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallA =>  -- challA at h_cp = .B is off-party
    simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_param, honestChallA_param_mode, h_cp]
  | OChallB =>  -- challB: hit at challengedParty=B
    change (honestChallB_param gp gen b₁ ()).run s = (honestChallB_param gp gen b₂ ()).run s
    exact honestChallB_param_b_indep_post_event (gen := gen) gp h_cp b₁ b₂ s h_post
  | ORecvB => rfl
  | OSendA =>  -- sendA uses parameter `a`, not `b`
    rfl
  | ORecvA => rfl
  | OSendB =>  -- sendB uses parameter `a`, not `b`
    rfl
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Rand impl is `a`-independent after the A-side embedding window. -/
lemma honestImpl_param_rand_a_indep_post_sendA
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch - 1)
    (a₁ a₂ : F) :
    (honestImpl_param_rand gp gen a₁ b gT t).run s =
    (honestImpl_param_rand gp gen a₂ b gT t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_param_rand, honestChallB_param_mode, h_cp]
  | OChallA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_param_rand, honestChallA_param_mode, h_cp]
  | ORecvB => rfl
  | OSendB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestSendB_param, h_cp]
  | ORecvA => rfl
  | OSendA =>
    change (honestSendA_param gp gen a₁ ()).run s =
      (honestSendA_param gp gen a₂ ()).run s
    exact honestSendA_param_a_indep_post_event (gen := gen) gp h_cp a₁ a₂ s h_post
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Rand impl is `a`-independent after the B-side embedding window. -/
lemma honestImpl_param_rand_a_indep_post_sendB
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (b : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch - 1)
    (a₁ a₂ : F) :
    (honestImpl_param_rand gp gen a₁ b gT t).run s =
    (honestImpl_param_rand gp gen a₂ b gT t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_param_rand, honestChallB_param_mode, h_cp]
  | OChallA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_param_rand, honestChallA_param_mode, h_cp]
  | ORecvB => rfl
  | OSendB =>
    change (honestSendB_param gp gen a₁ ()).run s =
      (honestSendB_param gp gen a₂ ()).run s
    exact honestSendB_param_a_indep_post_event (gen := gen) gp h_cp a₁ a₂ s h_post
  | ORecvA => rfl
  | OSendA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestSendA_param, h_cp]
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Rand impl is `b`-independent after A's challenge window. -/
lemma honestImpl_param_rand_b_indep_post_challA
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (a : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch)
    (b₁ b₂ : F) :
    (honestImpl_param_rand gp gen a b₁ gT t).run s =
    (honestImpl_param_rand gp gen a b₂ gT t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_param_rand, honestChallB_param_mode, h_cp]
  | OChallA =>
    change (honestChallA_param_rand gp gen b₁ gT ()).run s =
      (honestChallA_param_rand gp gen b₂ gT ()).run s
    exact honestChallA_param_rand_b_indep_post_event (gen := gen) gp h_cp b₁ b₂ gT s h_post
  | ORecvB => rfl
  | OSendB => rfl
  | ORecvA => rfl
  | OSendA => rfl
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Rand impl is `b`-independent after B's challenge window. -/
lemma honestImpl_param_rand_b_indep_post_challB
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch)
    (b₁ b₂ : F) :
    (honestImpl_param_rand gp gen a b₁ gT t).run s =
    (honestImpl_param_rand gp gen a b₂ gT t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_param_rand, honestChallA_param_mode, h_cp]
  | OChallB =>
    change (honestChallB_param_rand gp gen b₁ gT ()).run s =
      (honestChallB_param_rand gp gen b₂ gT ()).run s
    exact honestChallB_param_rand_b_indep_post_event (gen := gen) gp h_cp b₁ b₂ gT s h_post
  | ORecvB => rfl
  | OSendA => rfl
  | ORecvA => rfl
  | OSendB => rfl
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Rand impl is `gT`-independent after A's challenge window. -/
lemma honestImpl_param_rand_gT_indep_post_challA
    (gp : GameParams) (h_cp : gp.challengedParty = .A) (a b : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tA + 1 ≠ gp.challengeEpoch)
    (gT₁ gT₂ : G) :
    (honestImpl_param_rand gp gen a b gT₁ t).run s =
    (honestImpl_param_rand gp gen a b gT₂ t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_param_rand, honestChallB_param_mode, h_cp]
  | OChallA =>
    change (honestChallA_param_rand gp gen b gT₁ ()).run s =
      (honestChallA_param_rand gp gen b gT₂ ()).run s
    exact honestChallA_param_rand_gT_indep_post_event (gen := gen) gp h_cp b gT₁ gT₂ s h_post
  | ORecvB => rfl
  | OSendB => rfl
  | ORecvA => rfl
  | OSendA => rfl
  | OUnif _ => rfl

omit [Inhabited F] [Fintype G] in
/-- Rand impl is `gT`-independent after B's challenge window. -/
lemma honestImpl_param_rand_gT_indep_post_challB
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a b : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (h_post : s.tB + 1 ≠ gp.challengeEpoch)
    (gT₁ gT₂ : G) :
    (honestImpl_param_rand gp gen a b gT₁ t).run s =
    (honestImpl_param_rand gp gen a b gT₂ t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallA =>
    simp [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_param_rand, honestChallA_param_mode, h_cp]
  | OChallB =>
    change (honestChallB_param_rand gp gen b gT₁ ()).run s =
      (honestChallB_param_rand gp gen b gT₂ ()).run s
    exact honestChallB_param_rand_gT_indep_post_event (gen := gen) gp h_cp b gT₁ gT₂ s h_post
  | ORecvB => rfl
  | OSendA => rfl
  | ORecvA => rfl
  | OSendB => rfl
  | OUnif _ => rfl

/-! ### State preservation and auxiliary

Invariants of the game state preserved by individual (non-`O_param`) oracles —
corruption queries don't change state, receive queries preserve the
reachable-shape invariant — and counter-monotonicity lemmas for the
parameterized impl, plus small arithmetic helpers used elsewhere. -/

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G]
  [Module F G] [SampleableType G] [DecidableEq G] [Inhabited F] [Fintype G] in
/-- Helper: corruption oracles don't modify state. -/
lemma oracleCorrupt_state_unchanged
    (gp : GameParams) (party : CKAParty) (s : GameState (CKAState F G) G G)
    (z : Option (CKAState F G) × GameState (CKAState F G) G G) :
    z ∈ support (((match party with
      | .A => oracleCorruptA gp (CKAState F G) G G
      | .B => oracleCorruptB gp (CKAState F G) G G) ()).run s) → z.2 = s := by
  cases party
  · unfold oracleCorruptA
    rw [StateT.run_get_bind]
    intro hz
    split_ifs at hz <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        exact congrArg Prod.snd hz
  · unfold oracleCorruptB
    rw [StateT.run_get_bind]
    intro hz
    split_ifs at hz <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        exact congrArg Prod.snd hz

/-- Lifting a probabilistic computation into `StateT` can change only the returned value;
the state component of every supported output remains the initial state. -/
lemma stateT_liftM_preserves_state {σ α : Type} (oa : ProbComp α)
    (s : σ) (z : α × σ)
    (hz : z ∈ support ((liftM oa : StateT σ ProbComp α).run s)) :
    z.2 = s := by
  rw [OracleComp.liftM_run_StateT] at hz
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hz
  rcases hz with ⟨_, _, hzu⟩
  exact congrArg Prod.snd hzu

lemma validStep_challB_eq_true_iff (last : Option CKAAction) :
    validStep last CKAAction.challB = true ↔ last = some CKAAction.recvB := by
  cases last with
  | none => simp [validStep]
  | some action => cases action <;> simp [validStep]

lemma validStep_challA_eq_true_iff (last : Option CKAAction) :
    validStep last CKAAction.challA = true ↔
      last = none ∨ last = some CKAAction.recvA := by
  cases last with
  | none => simp [validStep]
  | some action => cases action <;> simp [validStep]

omit [Inhabited F] [Fintype G] in
/-- Shape-only version of the DDH-CKA `recvB` preservation fact. Unlike the
correctness proof's invariant, this deliberately ignores the `correct` flag. -/
lemma oracleRecvB_preserves_reachableShape :
    QueryImpl.PreservesInv (oracleRecvB (ddhCKA F G gen)) (reachableShape gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
  cases hGuard : validStep last .recvB
  · have : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩) := by
      simpa [oracleRecvB, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this
    exact hσ
  · rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals
      rcases (by simpa [reachableShape, epochCounterInv, stateShapeInv] using hσ) with
        ⟨hphase, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have : z = ((), ⟨.recvReady y, .sendReady (y • gen),
          none, none, none, none, correct,
          some .recvB, epA, epB + 1⟩) := by
        simpa [oracleRecvB, validStep,
          ddhCKA, recv, smul_comm x y gen,
          StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst this
      refine ⟨?_, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simpa [epochCounterInv] using hphase

omit [Inhabited F] [Fintype G] in
/-- Shape-only version of the DDH-CKA `recvA` preservation fact. Unlike the
correctness proof's invariant, this deliberately ignores the `correct` flag. -/
lemma oracleRecvA_preserves_reachableShape :
    QueryImpl.PreservesInv (oracleRecvA (ddhCKA F G gen)) (reachableShape gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
  cases hGuard : validStep last .recvA
  · have : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩) := by
      simpa [oracleRecvA, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this
    exact hσ
  · rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals
      rcases (by simpa [reachableShape, epochCounterInv, stateShapeInv] using hσ) with
        ⟨hphase, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have : z = ((), ⟨.sendReady (x • gen), .recvReady x,
          none, none, none, none, correct,
          some .recvA, epA + 1, epB⟩) := by
        simpa [oracleRecvA, validStep,
          ddhCKA, recv, smul_comm y x gen,
          StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst this
      refine ⟨?_, x, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simpa [epochCounterInv] using hphase.symm

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G]
  [Module F G] [SampleableType G] [DecidableEq G] [Inhabited F] [Fintype G] in
/-- If corruption is still allowed after incrementing B's counter, it was already
allowed before the increment. -/
lemma allowCorr_of_allowCorr_tB_succ
    (gp : GameParams) (s : GameState (CKAState F G) G G)
    (h : allowCorrPCS gp { s with tB := s.tB + 1 } = true) :
    allowCorrPCS gp s = true := by
  simp [allowCorrPCS] at h ⊢
  omega

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G]
  [Module F G] [SampleableType G] [DecidableEq G] [Inhabited F] [Fintype G] in
/-- If corruption is still allowed after incrementing A's counter, it was already
allowed before the increment. -/
lemma allowCorr_of_allowCorr_tA_succ
    (gp : GameParams) (s : GameState (CKAState F G) G G)
    (h : allowCorrPCS gp { s with tA := s.tA + 1 } = true) :
    allowCorrPCS gp s = true := by
  simp [allowCorrPCS] at h ⊢
  omega

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G]
  [Module F G] [SampleableType G] [DecidableEq G] [Inhabited F] [Fintype G] in
/-- Transport a relational triple across pointwise reductions to pure computations.
Useful after unfolding stateful oracle bodies: prove each `.run` is a `pure`
state/result pair, then close with the desired postcondition. -/
lemma relTriple_of_eq_pure_pure
    {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {a : α} {b : β} {R : α → β → Prop}
    (hoa : oa = pure a) (hob : ob = pure b) (hR : R a b) :
    OracleComp.ProgramLogic.Relational.RelTriple oa ob R := by
  rw [hoa, hob]
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure
    (spec₁ := unifSpec) (spec₂ := unifSpec) hR

omit [Inhabited F] [Fintype G] in
/-- **Per-query `tA`/`tB` monotonicity.**

Every oracle in `honestImpl_param_real` either leaves `state.tA` /
`state.tB` unchanged, or increments exactly one of them by `1`. The
two are orthogonal: A-side oracles (`oracleSendA`, `oracleRecvA`,
`oracleChallA`, `honestSendA_param`, `honestChallA_param`) only touch
`tA`; B-side oracles (`oracleSendB`, `oracleRecvB`, `oracleChallB`,
`honestSendB_param`, `honestChallB_param`) only touch `tB`. Both
inequalities underpin the post-event `a`/`b`-independence arguments. -/
lemma honestImpl_param_real_t_monotone
    (gp : GameParams) (a b : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G)
    (z : (ckaSecuritySpec (CKAState F G) G G F).Range t × GameState (CKAState F G) G G)
    (hz : z ∈ support ((honestImpl_param_real gp gen a b t).run s)) :
    s.tA ≤ z.2.tA ∧ s.tB ≤ z.2.tB := by
  match t with
  | OSendB_rleak =>
    change z ∈ support ((oracleSendB_rleak gp (ddhCKA F G gen) ()).run s) at hz
    unfold oracleSendB_rleak at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [ddhCKA, send_rleak] at hz ⊢
    split_ifs at hz
    all_goals
      cases sB <;>
      simp_all only [StateT.run_pure, StateT.run_set, support_pure,
        StateT.run_bind, StateT.run_map, StateT.run_monadLift,
        monadLift_self, pure_bind, bind_pure_comp, map_pure, liftM_map,
        bind_map_left, Functor.map_map, support_map, support_uniformSample,
        Set.image_univ]
      <;> (first
        | have hpair := Set.mem_singleton_iff.mp hz
          cases hpair
          simp
        | rcases hz with ⟨_, rfl⟩
          simp)
  | OSendA_rleak =>
    change z ∈ support ((oracleSendA_rleak gp (ddhCKA F G gen) ()).run s) at hz
    unfold oracleSendA_rleak at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [ddhCKA, send_rleak] at hz ⊢
    split_ifs at hz
    all_goals
      cases sA <;>
      simp_all only [StateT.run_pure, StateT.run_set, support_pure,
        StateT.run_bind, StateT.run_map, StateT.run_monadLift,
        monadLift_self, pure_bind, bind_pure_comp, map_pure, liftM_map,
        bind_map_left, Functor.map_map, support_map, support_uniformSample,
        Set.image_univ]
      <;> (first
        | have hpair := Set.mem_singleton_iff.mp hz
          cases hpair
          simp
        | rcases hz with ⟨_, rfl⟩
          simp)
  | OCorruptB =>
    -- oracleCorruptB: state unchanged
    simp only [honestImpl_param_real] at hz
    have h_eq := oracleCorrupt_state_unchanged gp .B s z hz
    rw [h_eq]
    exact ⟨le_refl _, le_refl _⟩
  | OCorruptA =>
    -- oracleCorruptA: state unchanged
    simp only [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hz
    have h_eq := oracleCorrupt_state_unchanged gp .A s z hz
    rw [h_eq]
    exact ⟨le_refl _, le_refl _⟩
  | OChallB =>
    change z ∈ support ((honestChallB_param (F := F) gp gen b ()).run s) at hz
    unfold honestChallB_param at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [oracleChallB, pure_bind, bind_pure_comp, ddhCKA, send] at hz ⊢
    split_ifs at hz
    all_goals
      cases sB <;>
      by_cases hv : validStep last CKAAction.challB = true <;>
      by_cases hcp : gp.challengedParty = CKAParty.B <;>
      simp_all only [Bool.true_and,
        Bool.false_and, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true, not_false_eq_true, StateT.run_bind,
        StateT.run_get, StateT.run_map, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, ↓reduceIte, support_pure]
      <;> (have hpair := Set.mem_singleton_iff.mp hz; cases hpair; simp)
  | OChallA =>
    change z ∈ support ((honestChallA_param (F := F) gp gen b ()).run s) at hz
    unfold honestChallA_param at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [oracleChallA, pure_bind, bind_pure_comp, ddhCKA, send] at hz ⊢
    split_ifs at hz
    all_goals
      cases sA <;>
      by_cases hv : validStep last CKAAction.challA = true <;>
      by_cases hcp : gp.challengedParty = CKAParty.A <;>
      simp_all only [Bool.true_and,
        Bool.false_and, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true, not_false_eq_true, StateT.run_bind,
        StateT.run_get, StateT.run_map, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, ↓reduceIte, support_pure]
      <;> (have hpair := Set.mem_singleton_iff.mp hz; cases hpair; simp)
  | ORecvB =>
    change z ∈ support ((oracleRecvB (ddhCKA F G gen) ()).run s) at hz
    unfold oracleRecvB at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [ddhCKA, recv] at hz ⊢
    split_ifs at hz
    all_goals
      cases ρA <;>
      cases sB <;>
      simp_all only [StateT.run_set, StateT.run_pure, support_pure]
      <;> (have hpair := Set.mem_singleton_iff.mp hz; cases hpair; simp)
  | OSendB =>
    change z ∈ support ((honestSendB_param (F := F) gp gen a ()).run s) at hz
    unfold honestSendB_param at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [oracleSendB, bind_pure_comp, ddhCKA, send] at hz ⊢
    split_ifs at hz
    all_goals
      cases sB <;>
      by_cases hv : validStep last CKAAction.sendB = true <;>
      simp_all only [Bool.true_and, Bool.and_eq_true, beq_iff_eq, StateT.run_pure,
        support_pure, Bool.false_and, Bool.false_eq_true, StateT.run_map, StateT.run_set,
        map_pure, not_and, Bool.not_eq_true, StateT.run_bind, StateT.run_get, pure_bind,
        ↓reduceIte, liftM_pure, not_false_eq_true, liftM_map, bind_map_left,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ]
      <;> (first
        | have hpair := Set.mem_singleton_iff.mp hz
          cases hpair
          simp
        | rcases hz with ⟨_, rfl⟩
          simp)
  | ORecvA =>
    change z ∈ support ((oracleRecvA (ddhCKA F G gen) ()).run s) at hz
    unfold oracleRecvA at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [ddhCKA, recv] at hz ⊢
    split_ifs at hz
    all_goals
      cases ρB <;>
      cases sA <;>
      simp_all only [StateT.run_set, StateT.run_pure, support_pure]
      <;> (have hpair := Set.mem_singleton_iff.mp hz; cases hpair; simp)
  | OSendA =>
    change z ∈ support ((honestSendA_param (F := F) gp gen a ()).run s) at hz
    unfold honestSendA_param at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [oracleSendA, bind_pure_comp, ddhCKA, send] at hz ⊢
    split_ifs at hz
    all_goals
      cases sA <;>
      by_cases hv : validStep last CKAAction.sendA = true <;>
      simp_all only [Bool.true_and, Bool.and_eq_true, beq_iff_eq, StateT.run_pure,
        support_pure, Bool.false_and, Bool.false_eq_true, StateT.run_map, StateT.run_set,
        map_pure, not_and, Bool.not_eq_true, StateT.run_bind, StateT.run_get, pure_bind,
        ↓reduceIte, liftM_pure, not_false_eq_true, liftM_map, bind_map_left,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ]
      <;> (first
        | have hpair := Set.mem_singleton_iff.mp hz
          cases hpair
          simp
        | rcases hz with ⟨_, rfl⟩
          simp)
  | OUnif n =>
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [honestImpl_param_real, QueryImpl.add_apply_inl, oracleUnif,
      QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply] at hz
    set s0 : GameState (CKAState F G) G G :=
      { stA := sA, stB := sB, rhoA := ρA, rhoB := ρB, keyA := kA, keyB := kB,
        correct := correct, lastAction := last, tA := epA, tB := epB }
      with hs0
    set probInner : ProbComp ((ckaSecuritySpec (CKAState F G) G G F).Range (OUnif n)) :=
      liftM (OracleSpec.query (spec := unifSpec) n) with hpi
    have hz_state : z.2 = s0 :=
      stateT_liftM_preserves_state (oa := probInner) (s := s0) (z := z) hz
    rw [hz_state]
    exact ⟨le_refl _, le_refl _⟩

omit [Inhabited F] [Fintype G] in
/-- The rand honest stack preserves monotonicity of both local counters. -/
lemma honestImpl_param_rand_t_monotone
    (gp : GameParams) (a b : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G)
    (z : (ckaSecuritySpec (CKAState F G) G G F).Range t × GameState (CKAState F G) G G)
    (hz : z ∈ support ((honestImpl_param_rand gp gen a b gT t).run s)) :
    s.tA ≤ z.2.tA ∧ s.tB ≤ z.2.tB := by
  match t with
  | OSendB_rleak =>
    have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendB_rleak).run s) := hz
    exact honestImpl_param_real_t_monotone (gen := gen) gp a b OSendB_rleak s z hz'
  | OSendA_rleak =>
    have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendA_rleak).run s) := hz
    exact honestImpl_param_real_t_monotone (gen := gen) gp a b OSendA_rleak s z hz'
  | OCorruptB =>
    simp only [honestImpl_param_rand] at hz
    have h_eq := oracleCorrupt_state_unchanged gp .B s z hz
    rw [h_eq]
    exact ⟨le_refl _, le_refl _⟩
  | OCorruptA =>
    simp only [honestImpl_param_rand, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hz
    have h_eq := oracleCorrupt_state_unchanged gp .A s z hz
    rw [h_eq]
    exact ⟨le_refl _, le_refl _⟩
  | OChallB =>
    change z ∈ support ((honestChallB_param_rand (F := F) gp gen b gT ()).run s) at hz
    unfold honestChallB_param_rand at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [oracleChallB, pure_bind, bind_pure_comp, ddhCKA, send] at hz ⊢
    split_ifs at hz
    all_goals
      cases sB <;>
      by_cases hv : validStep last CKAAction.challB = true <;>
      by_cases hcp : gp.challengedParty = CKAParty.B <;>
      simp_all only [Bool.true_and,
        Bool.false_and, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true, not_false_eq_true, StateT.run_bind,
        StateT.run_get, StateT.run_map, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, ↓reduceIte, support_pure]
      <;> (have hpair := Set.mem_singleton_iff.mp hz; cases hpair; simp)
  | OChallA =>
    change z ∈ support ((honestChallA_param_rand (F := F) gp gen b gT ()).run s) at hz
    unfold honestChallA_param_rand at hz
    rw [StateT.run_get_bind] at hz
    rcases s with ⟨sA, sB, ρA, ρB, kA, kB, correct, last, epA, epB⟩
    simp only [oracleChallA, pure_bind, bind_pure_comp, ddhCKA, send] at hz ⊢
    split_ifs at hz
    all_goals
      cases sA <;>
      by_cases hv : validStep last CKAAction.challA = true <;>
      by_cases hcp : gp.challengedParty = CKAParty.A <;>
      simp_all only [Bool.true_and,
        Bool.false_and, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true, not_false_eq_true, StateT.run_bind,
        StateT.run_get, StateT.run_map, StateT.run_set, StateT.run_pure,
        pure_bind, map_pure, ↓reduceIte, support_pure]
      <;> (have hpair := Set.mem_singleton_iff.mp hz; cases hpair; simp)
  | ORecvB =>
    have hz' : z ∈ support ((honestImpl_param_real gp gen a b ORecvB).run s) := hz
    exact honestImpl_param_real_t_monotone (gen := gen) gp a b ORecvB s z hz'
  | OSendB =>
    have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendB).run s) := hz
    exact honestImpl_param_real_t_monotone (gen := gen) gp a b OSendB s z hz'
  | ORecvA =>
    have hz' : z ∈ support ((honestImpl_param_real gp gen a b ORecvA).run s) := hz
    exact honestImpl_param_real_t_monotone (gen := gen) gp a b ORecvA s z hz'
  | OSendA =>
    have hz' : z ∈ support ((honestImpl_param_real gp gen a b OSendA).run s) := hz
    exact honestImpl_param_real_t_monotone (gen := gen) gp a b OSendA s z hz'
  | OUnif n =>
    have hz' : z ∈ support ((honestImpl_param_real gp gen a b (OUnif n)).run s) := hz
    exact honestImpl_param_real_t_monotone (gen := gen) gp a b (OUnif n) s z hz'

/-- If a counter has already reached `epoch - 1`, the next counter value cannot still be
`epoch - 1`. This discharges the post-send embedding-window side conditions. -/
lemma next_ne_prev_epoch_of_prev_epoch_le {epoch counter : Nat}
    (h : epoch - 1 ≤ counter) : counter + 1 ≠ epoch - 1 := by
  omega

/-- If a counter has already reached `epoch`, the next counter value cannot still be `epoch`.
This discharges the post-challenge side conditions. -/
lemma next_ne_epoch_of_epoch_le {epoch counter : Nat}
    (h : epoch ≤ counter) : counter + 1 ≠ epoch := by
  omega

end Step2

end ddhCKA
