/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.ReductionReal.Bridge
import SecureMessaging.CKA.FromDDH.Security.ReductionCommon

/-!
# CKA from DDH — Reduction (rand) — State Relation and Per-Query Step

This file defines a state relation between game states obtained
from the reduction game and game states obtained from the parameterized honest CKA game.
It proves that this relation is an invariant, i.e. it is preserved by each oracle query.

For

- `R := reductionHonestRel_rand gp gen a b gT`,
- a reduction state `sR`, and
- a parameterized honest CKA state `sH`

the relation `R sR sH` synchronizes counters, last action, public messages, and
corruption-visible local states between `sR` and `sH`.

The step theorem proves, for each oracle query `t`,

```lean
RelTriple
  ((reductionOracleImpl gp gen (a • gen) (b • gen) gT t).run sR)
  ((honestImpl_param_rand gp gen a b gT t).run sH)
  (fun pR pH => pR.1 = pH.1 ∧ R pR.2 pH.2)
```

from any states satisfying `R sR sH`, i.e. the two one-query runs return
the same visible answer and their post-states again satisfy `R`.

`ReductionRand/EagerHonestBridge.lean` uses this as the inductive step for `simulateQ`:
at an adversary node `query t >>= k`, the step lemma handles query `t`, and the
induction hypothesis applies to the continuation `k` at the related post-state.
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

omit [Fintype G] in
/-- Rand-branch simulation invariant between reduction and honest states. -/
def reductionHonestRel_rand (gp : GameParams) (gen : G) (a b : F) (_gT : G)
    (sR sH : GameState (CKAState F G) G G) : Prop :=
  reachableShape gen sH ∧
  sR.tA = sH.tA ∧
  sR.tB = sH.tB ∧
  sR.lastAction = sH.lastAction ∧
  sR.rhoA = sH.rhoA ∧
  sR.rhoB = sH.rhoB ∧
  (sR.lastAction = none → sR.tA = 0 ∧ sR.tB = 0) ∧
  (sR.stA = sH.stA ∨
    (gp.challengedParty = .B ∧ sR.tA = gp.challengeEpoch - 1 ∧
      sR.stA = (.recvReady 0 : CKAState F G) ∧ sH.stA = .recvReady a) ∨
    (gp.challengedParty = .A ∧ sR.tA = gp.challengeEpoch ∧
      sR.stA = (.recvReady 0 : CKAState F G) ∧ sH.stA = .recvReady b)) ∧
  (sR.stB = sH.stB ∨
    (gp.challengedParty = .A ∧ sR.tB = gp.challengeEpoch - 1 ∧
      sR.stB = (.recvReady 0 : CKAState F G) ∧ sH.stB = .recvReady a) ∨
    (gp.challengedParty = .B ∧ sR.tB = gp.challengeEpoch ∧
      sR.stB = (.recvReady 0 : CKAState F G) ∧ sH.stB = .recvReady b)) ∧
  (gp.challengedParty = .B → sR.tA = gp.challengeEpoch - 1 →
    (sR.lastAction = some .sendA ∨ sR.lastAction = some .challA ∨
      sR.lastAction = some .recvB) →
    sR.stA = (.recvReady 0 : CKAState F G) ∧ sH.stA = .recvReady a) ∧
  (gp.challengedParty = .A → sR.tB + 1 = gp.challengeEpoch →
    (sR.lastAction = none ∨ sR.lastAction = some .sendB ∨ sR.lastAction = some .challB ∨
      sR.lastAction = some .recvA) →
    sR.stB = (.recvReady 0 : CKAState F G) ∧ sH.stB = .recvReady a) ∧
  ((allowCorrPCS gp sR || allowCorrFS gp sR .A) = true → sR.stA = sH.stA) ∧
  ((allowCorrPCS gp sR || allowCorrFS gp sR .B) = true → sR.stB = sH.stB)

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G]
  [DecidableEq G] [Inhabited F] [Fintype G] in
/-- Preservation of `reductionHonestRel_rand` by a successful `recvB` step.

After B receives A's value `y`, both executions set B's local state to
`.sendReady (y • gen)`. The B-state part of the relation is therefore equality;
the assumptions record what is still needed for A's state. -/
private lemma reductionHonestRel_rand_after_recvB
    (gp : GameParams) (a b y : F) (gT : G) (cR cH : Bool)
    (sR sH : GameState (CKAState F G) G G)
    (h_phase : sH.tA = sH.tB + 1)
    (h_stAH : sH.stA = (.recvReady y : CKAState F G))
    (h_rhoBH : sH.rhoB = none)
    (h_keyBH : sH.keyB = none)
    (h_tA : sR.tA = sH.tA) (h_tB : sR.tB = sH.tB)
    (h_rhoB : sR.rhoB = sH.rhoB)
    (h_stA : sR.stA = sH.stA ∨
      (gp.challengedParty = .B ∧ sR.tA = gp.challengeEpoch - 1 ∧
        sR.stA = (.recvReady 0 : CKAState F G) ∧ sH.stA = .recvReady a) ∨
      (gp.challengedParty = .A ∧ sR.tA = gp.challengeEpoch ∧
        sR.stA = (.recvReady 0 : CKAState F G) ∧ sH.stA = .recvReady b))
    (h_pendingA : gp.challengedParty = .B → sR.tA = gp.challengeEpoch - 1 →
      sR.stA = (.recvReady 0 : CKAState F G) ∧ sH.stA = .recvReady a)
    (h_safeA : (allowCorrPCS gp sR || allowCorrFS gp sR .A) = true →
      sR.stA = sH.stA) :
    reductionHonestRel_rand gp gen a b gT
      { sR with
        tB := sR.tB + 1, stB := .sendReady (y • gen),
        rhoA := none, keyA := none, correct := cR,
        lastAction := some .recvB }
      { sH with
        tB := sH.tB + 1, stB := .sendReady (y • gen),
        rhoA := none, keyA := none, correct := cH,
        lastAction := some .recvB } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
  · refine ⟨?_, y, ?_, rfl, rfl, ?_, rfl, ?_⟩
    · simpa [epochCounterInv] using h_phase
    · simpa using h_stAH
    · simpa using h_rhoBH
    · simpa using h_keyBH
  · simp [h_tA]
  · simp [h_tB]
  · rfl
  · rfl
  · simp [h_rhoB]
  · intro h
    simp at h
  · simp [h_stA]
  · exact Or.inl rfl
  · intro h_cp h_tA _h_last
    exact h_pendingA h_cp h_tA
  · intro _h_cp _h_tB h_last
    simp at h_last
  · intro h
    apply h_safeA
    by_cases h_allow_post :
        allowCorrPCS gp
          ({ sR with
            tB := sR.tB + 1, stB := .sendReady (y • gen),
            rhoA := none, keyA := none, correct := cR,
            lastAction := some .recvB } :
            GameState (CKAState F G) G G) = true
    · have h_allow_succ :
          allowCorrPCS gp {sR with tB := sR.tB + 1} = true := by
        simpa [allowCorr, allowCorrPCS] using h_allow_post
      have h_allow_pre := allowCorr_of_allowCorr_tB_succ gp sR h_allow_succ
      simp [h_allow_pre]
    · have h_allow_post_false :
          allowCorrPCS gp
            ({ sR with
              tB := sR.tB + 1, stB := .sendReady (y • gen),
              rhoA := none, keyA := none, correct := cR,
              lastAction := some .recvB } :
              GameState (CKAState F G) G G) = false :=
        Bool.eq_false_iff.mpr h_allow_post
      have h_finished_post :
          allowCorrFS gp
            ({ sR with
              tB := sR.tB + 1, stB := .sendReady (y • gen),
              rhoA := none, keyA := none, correct := cR,
              lastAction := some .recvB } :
              GameState (CKAState F G) G G) .A = true := by
        simpa [h_allow_post_false] using h
      have h_finished_pre : allowCorrFS gp sR .A = true := by
        simpa [allowCorrFS] using h_finished_post
      simp [h_finished_pre]
  · intro _h
    rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G]
  [DecidableEq G] [Inhabited F] [Fintype G] in
/-- Preservation of `reductionHonestRel_rand` by a successful `recvA` step.

After A receives B's value `x`, both executions set A's local state to
`.sendReady (x • gen)`. The A-state part of the relation is therefore equality;
the assumptions record what is still needed for B's state. -/
private lemma reductionHonestRel_rand_after_recvA
    (gp : GameParams) (a b x : F) (gT : G) (cR cH : Bool)
    (sR sH : GameState (CKAState F G) G G)
    (h_phase : sH.tB = sH.tA + 1)
    (h_stBH : sH.stB = (.recvReady x : CKAState F G))
    (h_rhoAH : sH.rhoA = none)
    (h_keyAH : sH.keyA = none)
    (h_tA : sR.tA = sH.tA) (h_tB : sR.tB = sH.tB)
    (h_rhoA : sR.rhoA = sH.rhoA)
    (h_stB : sR.stB = sH.stB ∨
      (gp.challengedParty = .A ∧ sR.tB = gp.challengeEpoch - 1 ∧
        sR.stB = (.recvReady 0 : CKAState F G) ∧ sH.stB = .recvReady a) ∨
      (gp.challengedParty = .B ∧ sR.tB = gp.challengeEpoch ∧
        sR.stB = (.recvReady 0 : CKAState F G) ∧ sH.stB = .recvReady b))
    (h_pendingB : gp.challengedParty = .A → sR.tB + 1 = gp.challengeEpoch →
      sR.stB = (.recvReady 0 : CKAState F G) ∧ sH.stB = .recvReady a)
    (h_safeB : (allowCorrPCS gp sR || allowCorrFS gp sR .B) = true →
      sR.stB = sH.stB) :
    reductionHonestRel_rand gp gen a b gT
      { sR with
        tA := sR.tA + 1, stA := .sendReady (x • gen),
        rhoB := none, keyB := none, correct := cR,
        lastAction := some .recvA }
      { sH with
        tA := sH.tA + 1, stA := .sendReady (x • gen),
        rhoB := none, keyB := none, correct := cH,
        lastAction := some .recvA } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
  · refine ⟨?_, x, rfl, ?_, ?_, rfl, ?_, rfl⟩
    · simpa [epochCounterInv] using h_phase.symm
    · simpa using h_stBH
    · simpa using h_rhoAH
    · simpa using h_keyAH
  · simp [h_tA]
  · simp [h_tB]
  · rfl
  · simp [h_rhoA]
  · rfl
  · intro h
    simp at h
  · exact Or.inl rfl
  · simp [h_stB]
  · intro _h_cp _h_tA h_last
    simp at h_last
  · intro h_cp h_tB _h_last
    exact h_pendingB h_cp h_tB
  · intro _h
    rfl
  · intro h
    apply h_safeB
    by_cases h_allow_post :
        allowCorrPCS gp
          ({ sR with
            tA := sR.tA + 1, stA := .sendReady (x • gen),
            rhoB := none, keyB := none, correct := cR,
            lastAction := some .recvA } :
            GameState (CKAState F G) G G) = true
    · have h_allow_succ :
          allowCorrPCS gp {sR with tA := sR.tA + 1} = true := by
        simpa [allowCorr, allowCorrPCS] using h_allow_post
      have h_allow_pre := allowCorr_of_allowCorr_tA_succ gp sR h_allow_succ
      simp [h_allow_pre]
    · have h_allow_post_false :
          allowCorrPCS gp
            ({ sR with
              tA := sR.tA + 1, stA := .sendReady (x • gen),
              rhoB := none, keyB := none, correct := cR,
              lastAction := some .recvA } :
              GameState (CKAState F G) G G) = false :=
        Bool.eq_false_iff.mpr h_allow_post
      have h_finished_post :
          allowCorrFS gp
            ({ sR with
              tA := sR.tA + 1, stA := .sendReady (x • gen),
              rhoB := none, keyB := none, correct := cR,
              lastAction := some .recvA } :
              GameState (CKAState F G) G G) .B = true := by
        simpa [h_allow_post_false] using h
      have h_finished_pre : allowCorrFS gp sR .B = true := by
        simpa [allowCorrFS] using h_finished_post
      simp [h_finished_pre]

omit [Inhabited F] [Fintype G] in
/-- Per-query preservation for the random-branch `corruptB` oracle case. -/
private lemma reduction_honest_param_rand_corruptB_rel
    (gp : GameParams) (a b : F) (gT : G)
    (sR sH : GameState (CKAState F G) G G)
    (h_tA : sR.tA = sH.tA) (h_tB : sR.tB = sH.tB)
    (h_safeB : (allowCorrPCS gp sR || allowCorrFS gp sR .B) = true →
      sR.stB = sH.stB)
    (hrel : reductionHonestRel_rand gp gen a b gT sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionOracleImpl gp gen (a • gen) (b • gen) gT OCorruptB).run sR)
      ((honestImpl_param_rand gp gen a b gT OCorruptB).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2) := by
  simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr]
  exact relTriple_oracleCorruptB_of_state_rel
    (gp := gp)
    (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
    (sL := sR) (sR := sH) h_tA h_tB h_safeB hrel

omit [Inhabited F] [Fintype G] in
/-- Per-query preservation for the random-branch `corruptA` oracle case. -/
private lemma reduction_honest_param_rand_corruptA_rel
    (gp : GameParams) (a b : F) (gT : G)
    (sR sH : GameState (CKAState F G) G G)
    (h_tA : sR.tA = sH.tA) (h_tB : sR.tB = sH.tB)
    (h_safeA : (allowCorrPCS gp sR || allowCorrFS gp sR .A) = true →
      sR.stA = sH.stA)
    (hrel : reductionHonestRel_rand gp gen a b gT sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionOracleImpl gp gen (a • gen) (b • gen) gT OCorruptA).run sR)
      ((honestImpl_param_rand gp gen a b gT OCorruptA).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2) := by
  simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr]
  exact relTriple_oracleCorruptA_of_state_rel
    (gp := gp)
    (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
    (sL := sR) (sR := sH) h_tA h_tB h_safeA hrel

omit [Inhabited F] [Fintype G] in
/-- Per-query preservation for the random-branch uniform oracle case. -/
private lemma reduction_honest_param_rand_unif_rel
    (gp : GameParams) (a b : F) (gT : G) (n : unifSpec.Domain)
    (sR sH : GameState (CKAState F G) G G)
    (hrel : reductionHonestRel_rand gp gen a b gT sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionOracleImpl gp gen (a • gen) (b • gen) gT (OUnif n)).run sR)
      ((honestImpl_param_rand gp gen a b gT (OUnif n)).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2) := by
  simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl]
  exact relTriple_oracleUnif_of_state_rel
    (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
    (n := n) (sL := sR) (sR := sH) hrel

omit [Inhabited F] [Fintype G] in
/-- Per-query preservation of the random-branch relation `reductionHonestRel_rand`. -/
lemma reduction_honest_param_rand_step_rel
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (a b : F) (gT : G)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (sR sH : GameState (CKAState F G) G G)
    (hrel : reductionHonestRel_rand gp gen a b gT sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionOracleImpl gp gen (a • gen) (b • gen) gT t).run sR)
      ((honestImpl_param_rand gp gen a b gT t).run sH)
      (fun pR pH => pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2) := by
  rcases hrel with
    ⟨h_shape, h_tA, h_tB, h_last, h_rhoA, h_rhoB,
      h_none, h_stA, h_stB,
      h_pendingA, h_pendingB, h_safeA, h_safeB⟩
  have hrel_self : reductionHonestRel_rand gp gen a b gT sR sH := by
    exact
      ⟨h_shape, h_tA, h_tB, h_last, h_rhoA, h_rhoB,
        h_none, h_stA, h_stB,
        h_pendingA, h_pendingB, h_safeA, h_safeB⟩
  match t with
  | OCorruptB =>
      exact reduction_honest_param_rand_corruptB_rel
        (gen := gen) gp a b gT sR sH h_tA h_tB h_safeB hrel_self
  | OCorruptA =>
      exact reduction_honest_param_rand_corruptA_rel
        (gen := gen) gp a b gT sR sH h_tA h_tB h_safeA hrel_self
  | OChallB =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      by_cases h_cp : gp.challengedParty = CKAParty.B
      · by_cases h_v : validStep sR.lastAction CKAAction.challB = true
        · have h_vH : validStep sH.lastAction CKAAction.challB = true := by
            rw [← h_last]
            exact h_v
          by_cases h_epoch :
              isChallengeEpoch gp {sR with tB := sR.tB + 1} = true
          · have h_epochH :
                isChallengeEpoch gp {sH with tB := sH.tB + 1} = true := by
              simpa [isChallengeEpoch, GameState.tP, h_cp, h_tB] using h_epoch
            have h_lastH : sH.lastAction = some CKAAction.recvB :=
              (validStep_challB_eq_true_iff sH.lastAction).mp h_vH
            all_goals
              rcases (by
                simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
                  using h_shape) with
                ⟨h_phase, y, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
              have h_tB_chall : sR.tB + 1 = gp.challengeEpoch := by
                simpa [isChallengeEpoch, GameState.tP, h_cp] using h_epoch
              have h_tA_embed : sR.tA = gp.challengeEpoch - 1 := by
                have h_phaseR : sR.tA = sR.tB := by omega
                omega
              have h_pending :=
                h_pendingA h_cp h_tA_embed (by rw [h_last, h_lastH]; simp)
              rcases h_pending with ⟨h_stAR, h_stAH_dead⟩
              have hy : y = a := by
                rw [h_stAH] at h_stAH_dead
                exact CKAState.recvReady.inj h_stAH_dead
              subst y
              have h_runR :
                  (reductionChallB (F := F) gp (b • gen) gT ()).run sR =
                    (pure (some (b • gen, gT),
                      { sR with
                        tB := sR.tB + 1, stB := (.recvReady 0 : CKAState F G),
                        rhoB := some (b • gen), keyB := some gT,
                        lastAction := some .challB }) :
                      ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
                unfold reductionChallB
                rw [StateT.run_get_bind]
                simp [h_cp, h_v, h_epoch]
              have h_epochH_nat : sH.tB + 1 = gp.challengeEpoch := by
                simpa [isChallengeEpoch, GameState.tP, h_cp] using h_epochH
              have h_runH :
                  (honestChallB_param_rand (F := F) gp gen b gT ()).run sH =
                    (pure (some (b • gen, gT),
                      { sH with
                        tB := sH.tB + 1, stB := (.recvReady b : CKAState F G),
                        rhoB := some (b • gen), keyB := some (b • (a • gen)),
                        lastAction := some .challB }) :
                      ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
                unfold honestChallB_param_rand
                rw [StateT.run_get_bind]
                simp [h_lastH, validStep, h_cp, h_epochH_nat, h_stBH,
                  isChallengeEpoch, GameState.tP]
              refine relTriple_of_eq_pure_pure
                (oa := (reductionChallB (F := F) gp (b • gen) gT ()).run sR)
                (ob := (honestChallB_param_rand (F := F) gp gen b gT ()).run sH)
                (R := fun pR pH =>
                  pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
                (a := (some (b • gen, gT),
                  { sR with
                    tB := sR.tB + 1, stB := (.recvReady 0 : CKAState F G),
                    rhoB := some (b • gen), keyB := some gT,
                    lastAction := some .challB }))
                (b := (some (b • gen, gT),
                  { sH with
                    tB := sH.tB + 1, stB := (.recvReady b : CKAState F G),
                    rhoB := some (b • gen), keyB := some (b • (a • gen)),
                    lastAction := some .challB }))
                h_runR h_runH ?_
              refine ⟨rfl, ?_⟩
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
              · refine ⟨?_, b, a, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simpa [epochCounterInv] using h_phase.symm
                · simpa using h_stAH_dead
                · rfl
                · simpa [h_rhoA] using h_rhoAH
                · rfl
                · simp [h_keyAH]
                · rfl
              · simp [h_tA]
              · simp [h_tB]
              · rfl
              · simp [h_rhoA]
              · rfl
              · intro h
                simp at h
              · exact Or.inr (Or.inl ⟨h_cp, h_tA_embed, h_stAR, h_stAH_dead⟩)
              · exact Or.inr (Or.inr ⟨h_cp, h_tB_chall, rfl, rfl⟩)
              · intro _h_cp _h_tA h_last_post
                simp at h_last_post
              · intro h_cpA _h_tB _h_last_post
                simp [h_cp] at h_cpA
              · intro hsafe
                exfalso
                simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
                omega
              · intro hsafe
                exfalso
                simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
                omega
          · have h_epochR :
                isChallengeEpoch gp {sR with tB := sR.tB + 1} = false :=
              Bool.eq_false_iff.mpr h_epoch
            have h_epochH :
                isChallengeEpoch gp {sH with tB := sH.tB + 1} = false := by
              simpa [isChallengeEpoch, GameState.tP, h_cp, h_tB] using h_epochR
            exact relTriple_reductionChallB_pred_false_of_state_rel
              (mode := .rand) (gp := gp) (gen := gen) (b := b)
              (gB := b • gen) (gT := gT) (gTH := gT)
              (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
              (sL := sR) (sR := sH)
              (by simp [h_cp, h_v, h_epochR])
              (by simp [h_vH, h_cp, h_epochH])
              hrel_self
        · have h_vR : validStep sR.lastAction CKAAction.challB = false :=
            Bool.eq_false_iff.mpr h_v
          have h_vH : validStep sH.lastAction CKAAction.challB = false := by
            rw [← h_last]
            exact h_vR
          exact relTriple_reductionChallB_pred_false_of_state_rel
            (mode := .rand) (gp := gp) (gen := gen) (b := b)
            (gB := b • gen) (gT := gT) (gTH := gT)
            (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
            (sL := sR) (sR := sH)
            (by simp [h_cp, h_vR])
            (by simp [h_vH])
            hrel_self
      · have h_cp_ne : (gp.challengedParty == CKAParty.B) = false := by
          cases h_party : gp.challengedParty <;> simp [h_party] at h_cp ⊢
        exact relTriple_reductionChallB_pred_false_of_state_rel
          (mode := .rand) (gp := gp) (gen := gen) (b := b)
          (gB := b • gen) (gT := gT) (gTH := gT)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH)
          (by simp [h_cp_ne])
          (by simp [h_cp_ne])
          hrel_self
  | OChallA =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      by_cases h_cp : gp.challengedParty = CKAParty.A
      · by_cases h_v : validStep sR.lastAction CKAAction.challA = true
        · have h_vH : validStep sH.lastAction CKAAction.challA = true := by
            rw [← h_last]
            exact h_v
          by_cases h_epoch :
              isChallengeEpoch gp {sR with tA := sR.tA + 1} = true
          · have h_epochH :
                isChallengeEpoch gp {sH with tA := sH.tA + 1} = true := by
              simpa [isChallengeEpoch, GameState.tP, h_cp, h_tA] using h_epoch
            rcases (validStep_challA_eq_true_iff sH.lastAction).mp h_vH with h_lastH | h_lastH
            all_goals
              rcases (by
                simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
                  using h_shape) with
                ⟨h_phase, x, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
              have h_tA_chall : sR.tA + 1 = gp.challengeEpoch := by
                simpa [isChallengeEpoch, GameState.tP, h_cp] using h_epoch
              have h_tB_embed : sR.tB = gp.challengeEpoch - 1 := by
                have h_phaseR : sR.tB = sR.tA := by omega
                omega
              have h_last_embed :
                  sR.lastAction = none ∨
                  sR.lastAction = some CKAAction.sendB ∨
                    sR.lastAction = some CKAAction.challB ∨
                      sR.lastAction = some CKAAction.recvA := by
                rw [h_last, h_lastH]
                simp
              have h_pending :=
                h_pendingB h_cp (by omega) h_last_embed
              rcases h_pending with ⟨h_stBR, h_stBH_dead⟩
              have hx : x = a := by
                rw [h_stBH] at h_stBH_dead
                exact CKAState.recvReady.inj h_stBH_dead
              subst x
              have h_runR :
                  (reductionChallA (F := F) gp (b • gen) gT ()).run sR =
                    (pure (some (b • gen, gT),
                      { sR with
                        tA := sR.tA + 1, stA := (.recvReady 0 : CKAState F G),
                        rhoA := some (b • gen), keyA := some gT,
                        lastAction := some .challA }) :
                      ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
                unfold reductionChallA
                rw [StateT.run_get_bind]
                simp [h_cp, h_v, h_epoch]
              have h_epochH_nat : sH.tA + 1 = gp.challengeEpoch := by
                simpa [isChallengeEpoch, GameState.tP, h_cp] using h_epochH
              have h_runH :
                  (honestChallA_param_rand (F := F) gp gen b gT ()).run sH =
                    (pure (some (b • gen, gT),
                      { sH with
                        tA := sH.tA + 1, stA := (.recvReady b : CKAState F G),
                        rhoA := some (b • gen), keyA := some (b • (a • gen)),
                        lastAction := some .challA }) :
                      ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
                unfold honestChallA_param_rand
                rw [StateT.run_get_bind]
                simp [h_lastH, validStep, h_cp, h_epochH_nat, h_stAH,
                  isChallengeEpoch, GameState.tP]
              refine relTriple_of_eq_pure_pure
                (oa := (reductionChallA (F := F) gp (b • gen) gT ()).run sR)
                (ob := (honestChallA_param_rand (F := F) gp gen b gT ()).run sH)
                (R := fun pR pH =>
                  pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
                (a := (some (b • gen, gT),
                  { sR with
                    tA := sR.tA + 1, stA := (.recvReady 0 : CKAState F G),
                    rhoA := some (b • gen), keyA := some gT,
                    lastAction := some .challA }))
                (b := (some (b • gen, gT),
                  { sH with
                    tA := sH.tA + 1, stA := (.recvReady b : CKAState F G),
                    rhoA := some (b • gen), keyA := some (b • (a • gen)),
                    lastAction := some .challA }))
                h_runR h_runH ?_
              refine ⟨rfl, ?_⟩
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
              · refine ⟨?_, a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simpa [epochCounterInv] using h_phase
                · rfl
                · simpa using h_stBH_dead
                · rfl
                · simpa [h_rhoB] using h_rhoBH
                · rfl
                · simp [h_keyBH]
              · simp [h_tA]
              · simp [h_tB]
              · rfl
              · rfl
              · simp [h_rhoB]
              · intro h
                simp at h
              · exact Or.inr (Or.inr ⟨h_cp, h_tA_chall, rfl, rfl⟩)
              · exact Or.inr (Or.inl ⟨h_cp, h_tB_embed, h_stBR, h_stBH_dead⟩)
              · intro h_cpB _h_tA _h_last_post
                simp [h_cp] at h_cpB
              · intro _h_cp _h_tB h_last_post
                simp at h_last_post
              · intro hsafe
                exfalso
                simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
                omega
              · intro hsafe
                exfalso
                simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
                omega
          · have h_epochR :
                isChallengeEpoch gp {sR with tA := sR.tA + 1} = false :=
              Bool.eq_false_iff.mpr h_epoch
            have h_epochH :
                isChallengeEpoch gp {sH with tA := sH.tA + 1} = false := by
              simpa [isChallengeEpoch, GameState.tP, h_cp, h_tA] using h_epochR
            exact relTriple_reductionChallA_pred_false_of_state_rel
              (mode := .rand) (gp := gp) (gen := gen) (b := b)
              (gB := b • gen) (gT := gT) (gTH := gT)
              (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
              (sL := sR) (sR := sH)
              (by simp [h_cp, h_v, h_epochR])
              (by simp [h_vH, h_cp, h_epochH])
              hrel_self
        · have h_vR : validStep sR.lastAction CKAAction.challA = false :=
            Bool.eq_false_iff.mpr h_v
          have h_vH : validStep sH.lastAction CKAAction.challA = false := by
            rw [← h_last]
            exact h_vR
          exact relTriple_reductionChallA_pred_false_of_state_rel
            (mode := .rand) (gp := gp) (gen := gen) (b := b)
            (gB := b • gen) (gT := gT) (gTH := gT)
            (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
            (sL := sR) (sR := sH)
            (by simp [h_cp, h_vR])
            (by simp [h_vH])
            hrel_self
      · have h_cp_ne : (gp.challengedParty == CKAParty.A) = false := by
          cases h_party : gp.challengedParty <;> simp [h_party] at h_cp ⊢
        exact relTriple_reductionChallA_pred_false_of_state_rel
          (mode := .rand) (gp := gp) (gen := gen) (b := b)
          (gB := b • gen) (gT := gT) (gTH := gT)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH)
          (by simp [h_cp_ne])
          (by simp [h_cp_ne])
          hrel_self
  | OUnif n =>
      exact reduction_honest_param_rand_unif_rel
        (gen := gen) gp a b gT n sR sH hrel_self
  | OSendB =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      by_cases h_v : validStep sR.lastAction CKAAction.sendB = true
      · have h_vH : validStep sH.lastAction CKAAction.sendB = true := by
          rw [← h_last]
          exact h_v
        rcases h_lastH : sH.lastAction with _ | (_ | _ | _ | _ | _ | _) <;>
          simp [h_lastH, validStep] at h_vH
        all_goals
          rcases (by
            simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
              using h_shape) with
            ⟨h_phase, y, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
          have h_stBR : sR.stB = (.sendReady (y • gen) : CKAState F G) := by
            rcases h_stB with h_eq | h_dead | h_dead
            · rw [h_eq, h_stBH]
            · rcases h_dead with ⟨_, _, _, h_stBH_dead⟩
              rw [h_stBH] at h_stBH_dead
              cases h_stBH_dead
            · rcases h_dead with ⟨_, _, _, h_stBH_dead⟩
              rw [h_stBH] at h_stBH_dead
              cases h_stBH_dead
          have h_key_eq : y • (a • gen) = a • (y • gen) := by
            rw [smul_smul, smul_smul, mul_comm]
          by_cases h_embed :
              ((gp.challengedParty == CKAParty.A) &&
                isOtherSendBeforeChall gp {sR with tB := sR.tB + 1}) = true
          · have h_cpA : gp.challengedParty = CKAParty.A := by
              cases h_party : gp.challengedParty <;> simp [h_party] at h_embed ⊢
            have h_other :
                isOtherSendBeforeChall gp {sR with tB := sR.tB + 1} = true := by
              simpa [h_cpA] using h_embed
            have h_tB_embed : sR.tB + 1 = gp.challengeEpoch - 1 := by
              simpa [isOtherSendBeforeChall, GameState.tP, h_cpA] using h_other
            have h_tB_embedH : sH.tB + 1 = gp.challengeEpoch - 1 := by
              omega
            have h_stAR : sR.stA = (.recvReady y : CKAState F G) := by
              rcases h_stA with h_eq | h_dead | h_dead
              · rw [h_eq, h_stAH]
              · rcases h_dead with ⟨h_cpB, _, _, _⟩
                simp [h_cpA] at h_cpB
              · rcases h_dead with ⟨_, h_tA_dead, _, _⟩
                have h_phaseR : sR.tA = sR.tB := by omega
                omega
            have h_embed_prop :
                gp.challengedParty = CKAParty.A ∧
                  isOtherSendBeforeChall gp {sR with tB := sR.tB + 1} = true :=
              ⟨h_cpA, h_other⟩
            have h_runR :
                (reductionSendB (F := F) gp gen (a • gen) ()).run sR =
                  (pure (some (a • gen, y • (a • gen)),
                    { sR with
                      tB := sR.tB + 1, stB := (.recvReady 0 : CKAState F G),
                      rhoB := some (a • gen), keyB := some (y • (a • gen)),
                      lastAction := some .sendB }) :
                    ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
              unfold reductionSendB
              rw [StateT.run_get_bind]
              simp [h_v, h_cpA, h_tB_embed, h_stAR,
                isOtherSendBeforeChall, GameState.tP, CKAParty.other]
            have h_predH :
                (validStep sH.lastAction CKAAction.sendB &&
                  (gp.challengedParty == CKAParty.A) &&
                  isOtherSendBeforeChall gp {sH with tB := sH.tB + 1}) = true := by
              simp [h_lastH, validStep, h_cpA, h_tB_embedH,
                isOtherSendBeforeChall, GameState.tP, CKAParty.other]
            have h_runH :
                (honestSendB_param (F := F) gp gen a ()).run sH =
                  (pure (some (a • gen, a • (y • gen)),
                    { sH with
                      tB := sH.tB + 1, stB := (.recvReady a : CKAState F G),
                      rhoB := some (a • gen), keyB := some (a • (y • gen)),
                      lastAction := some .sendB }) :
                    ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
              unfold honestSendB_param
              rw [StateT.run_get_bind]
              simp [h_lastH, validStep, h_cpA, h_tB_embedH, h_stBH,
                isOtherSendBeforeChall, GameState.tP, CKAParty.other]
            refine relTriple_of_eq_pure_pure
              (oa := (reductionSendB (F := F) gp gen (a • gen) ()).run sR)
              (ob := (honestSendB_param (F := F) gp gen a ()).run sH)
              (R := fun pR pH =>
                pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
              (a := (some (a • gen, y • (a • gen)),
                { sR with
                  tB := sR.tB + 1, stB := (.recvReady 0 : CKAState F G),
                  rhoB := some (a • gen), keyB := some (y • (a • gen)),
                  lastAction := some .sendB }))
              (b := (some (a • gen, a • (y • gen)),
                { sH with
                  tB := sH.tB + 1, stB := (.recvReady a : CKAState F G),
                  rhoB := some (a • gen), keyB := some (a • (y • gen)),
                  lastAction := some .sendB }))
              h_runR h_runH ?_
            refine ⟨by simp [h_key_eq], ?_⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
            · refine ⟨?_, a, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [epochCounterInv] using h_phase.symm
              · simpa using h_stAH
              · rfl
              · simpa [h_rhoA] using h_rhoAH
              · rfl
              · simp [h_keyAH]
              · rfl
            · simp [h_tA]
            · simp [h_tB]
            · rfl
            · simp [h_rhoA]
            · rfl
            · intro h
              simp at h
            · simp [h_stA]
            · exact Or.inr (Or.inl ⟨h_cpA, h_tB_embed, rfl, rfl⟩)
            · intro _h_cp _h_tA h_last_post
              simp at h_last_post
            · intro _h_cp _h_tB _h_last_post
              exact ⟨rfl, rfl⟩
            · intro hsafe
              exfalso
              simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
              omega
            · intro hsafe
              exfalso
              simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
              omega
          · have h_embed_false :
                ((gp.challengedParty == CKAParty.A) &&
                  isOtherSendBeforeChall gp {sR with tB := sR.tB + 1}) = false :=
              Bool.eq_false_iff.mpr h_embed
            have h_predH :
                (validStep sH.lastAction CKAAction.sendB &&
                  (gp.challengedParty == CKAParty.A) &&
                  isOtherSendBeforeChall gp {sH with tB := sH.tB + 1}) = false := by
              cases h_party : gp.challengedParty
              · have h_otherR_false :
                    isOtherSendBeforeChall gp {sR with tB := sR.tB + 1} = false := by
                  have h_embed_false' := h_embed_false
                  simp only [h_party] at h_embed_false'
                  exact h_embed_false'
                have h_tB_not : ¬ sR.tB + 1 = gp.challengeEpoch - 1 := by
                  simpa [isOtherSendBeforeChall, GameState.tP, CKAParty.other, h_party]
                    using h_otherR_false
                have h_otherH_false :
                    isOtherSendBeforeChall gp {sH with tB := sH.tB + 1} = false := by
                  apply Bool.eq_false_iff.mpr
                  intro h_otherH_true
                  apply h_tB_not
                  simpa [isOtherSendBeforeChall, GameState.tP, CKAParty.other, h_party, h_tB]
                    using h_otherH_true
                simpa [h_lastH, validStep, h_party, isOtherSendBeforeChall,
                  GameState.tP, CKAParty.other] using h_otherH_false
              · simp [h_lastH, validStep]
            have h_embed_prop_false :
                ¬ (gp.challengedParty = CKAParty.A ∧
                  isOtherSendBeforeChall gp {sR with tB := sR.tB + 1} = true) := by
              intro hprop
              rcases hprop with ⟨h_cpA', h_other'⟩
              simp [h_cpA', h_other'] at h_embed_false
            have h_runR :
                (reductionSendB (F := F) gp gen (a • gen) ()).run sR =
                  ((fun x =>
                    (some (x • gen, x • (y • gen)),
                      { sR with
                        tB := sR.tB + 1, stB := (.recvReady x : CKAState F G),
                        rhoB := some (x • gen), keyB := some (x • (y • gen)),
                        lastAction := some .sendB })) <$> ($ᵗ F : ProbComp F)) := by
              unfold reductionSendB
              rw [StateT.run_get_bind]
              cases h_party : gp.challengedParty
              · simp [h_v, h_party, h_stBR, send,
                  isOtherSendBeforeChall, GameState.tP, CKAParty.other] at h_embed_false ⊢
                simp [h_embed_false]
              · simp [h_v, h_party, h_stBR, send,
                  isOtherSendBeforeChall, GameState.tP, CKAParty.other]
            have h_runH :
                (honestSendB_param (F := F) gp gen a ()).run sH =
                  ((fun x =>
                    (some (x • gen, x • (y • gen)),
                      { sH with
                        tB := sH.tB + 1, stB := (.recvReady x : CKAState F G),
                        rhoB := some (x • gen), keyB := some (x • (y • gen)),
                        lastAction := some .sendB })) <$> ($ᵗ F : ProbComp F)) := by
              rw [honestSendB_param_run_eq_when_pred_false (gen := gen) gp a sH h_predH]
              unfold oracleSendB
              rw [StateT.run_get_bind]
              simp [h_lastH, validStep, h_stBH, ddhCKA, send]
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runR) ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right ?_
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runH.symm)
            refine OracleComp.ProgramLogic.Relational.relTriple_map ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_post_mono
              (OracleComp.ProgramLogic.Relational.relTriple_refl
                (spec₁ := unifSpec) (oa := ($ᵗ F : ProbComp F))) ?_
            intro xR xH hx
            subst hx
            refine ⟨rfl, ?_⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
            · refine ⟨?_, xR, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [epochCounterInv] using h_phase.symm
              · simpa using h_stAH
              · rfl
              · simpa [h_rhoA] using h_rhoAH
              · rfl
              · simp [h_keyAH]
              · rfl
            · simp [h_tA]
            · simp [h_tB]
            · rfl
            · simp [h_rhoA]
            · rfl
            · intro h
              simp at h
            · simp [h_stA]
            · exact Or.inl rfl
            · intro _h_cp _h_tA h_last_post
              simp at h_last_post
            · intro h_cpA h_tB_embed _h_last_post
              have h_tB_embed' : sR.tB + 1 + 1 = gp.challengeEpoch := by
                simpa using h_tB_embed
              have h_tB_prev : sR.tB + 1 = gp.challengeEpoch - 1 := by
                rw [← h_tB_embed']
                omega
              exact False.elim (h_embed_prop_false ⟨h_cpA, by
                simpa only [isOtherSendBeforeChall, GameState.tP, CKAParty.other, h_cpA,
                  beq_iff_eq] using h_tB_prev⟩)
            · intro hsafe
              apply h_safeA
              by_cases h_allow_post :
                  allowCorrPCS gp
                    ({ sR with
                      tB := sR.tB + 1, stB := (.recvReady xR : CKAState F G),
                      rhoB := some (xR • gen), keyB := some (xR • (y • gen)),
                      lastAction := some .sendB } :
                      GameState (CKAState F G) G G) = true
              · have h_allow_succ :
                    allowCorrPCS gp {sR with tB := sR.tB + 1} = true := by
                  simpa [allowCorr, allowCorrPCS] using h_allow_post
                have h_allow_pre := allowCorr_of_allowCorr_tB_succ gp sR h_allow_succ
                simp [h_allow_pre]
              · have h_allow_post_false :
                    allowCorrPCS gp
                      ({ sR with
                        tB := sR.tB + 1, stB := (.recvReady xR : CKAState F G),
                        rhoB := some (xR • gen), keyB := some (xR • (y • gen)),
                        lastAction := some .sendB } :
                        GameState (CKAState F G) G G) = false :=
                  Bool.eq_false_iff.mpr h_allow_post
                have h_finished_post :
                    allowCorrFS gp
                      ({ sR with
                        tB := sR.tB + 1, stB := (.recvReady xR : CKAState F G),
                        rhoB := some (xR • gen), keyB := some (xR • (y • gen)),
                        lastAction := some .sendB } :
                        GameState (CKAState F G) G G) .A = true := by
                  simpa [h_allow_post_false] using hsafe
                have h_finished_pre : allowCorrFS gp sR .A = true := by
                  simpa [allowCorrFS] using h_finished_post
                simp [h_finished_pre]
            · intro _hsafe
              rfl
      · exact relTriple_reductionSendB_invalid_of_state_rel
          (gp := gp) (gen := gen) (a := a)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH) h_last h_v hrel_self
  | OSendA =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      by_cases h_v : validStep sR.lastAction CKAAction.sendA = true
      · have h_vH : validStep sH.lastAction CKAAction.sendA = true := by
          rw [← h_last]
          exact h_v
        rcases h_lastH : sH.lastAction with _ | (_ | _ | _ | _ | _ | _) <;>
          simp [h_lastH, validStep] at h_vH
        all_goals
          rcases (by
            simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
              using h_shape) with
            ⟨h_phase, x, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
          have h_stAR : sR.stA = (.sendReady (x • gen) : CKAState F G) := by
            rcases h_stA with h_eq | h_dead | h_dead
            · rw [h_eq, h_stAH]
            · rcases h_dead with ⟨_, _, _, h_stAH_dead⟩
              rw [h_stAH] at h_stAH_dead
              cases h_stAH_dead
            · rcases h_dead with ⟨_, _, _, h_stAH_dead⟩
              rw [h_stAH] at h_stAH_dead
              cases h_stAH_dead
          have h_key_eq : x • (a • gen) = a • (x • gen) := by
            rw [smul_smul, smul_smul, mul_comm]
          by_cases h_embed :
              ((gp.challengedParty == CKAParty.B) &&
                isOtherSendBeforeChall gp {sR with tA := sR.tA + 1}) = true
          · have h_cpB : gp.challengedParty = CKAParty.B := by
              cases h_party : gp.challengedParty <;> simp [h_party] at h_embed ⊢
            have h_other :
                isOtherSendBeforeChall gp {sR with tA := sR.tA + 1} = true := by
              simpa [h_cpB] using h_embed
            have h_tA_embed : sR.tA + 1 = gp.challengeEpoch - 1 := by
              simpa [isOtherSendBeforeChall, GameState.tP, h_cpB, CKAParty.other] using h_other
            have h_tA_embedH : sH.tA + 1 = gp.challengeEpoch - 1 := by
              omega
            have h_stBR : sR.stB = (.recvReady x : CKAState F G) := by
              rcases h_stB with h_eq | h_dead | h_dead
              · rw [h_eq, h_stBH]
              · rcases h_dead with ⟨h_cpA, _, _, _⟩
                simp [h_cpB] at h_cpA
              · rcases h_dead with ⟨_, h_tB_dead, _, h_stBH_dead⟩
                have h_phaseR : sR.tA = sR.tB := by omega
                omega
            have h_runR :
                (reductionSendA (F := F) gp gen (a • gen) ()).run sR =
                  (pure (some (a • gen, x • (a • gen)),
                    { sR with
                      tA := sR.tA + 1, stA := (.recvReady 0 : CKAState F G),
                      rhoA := some (a • gen), keyA := some (x • (a • gen)),
                      lastAction := some .sendA }) :
                    ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
              unfold reductionSendA
              rw [StateT.run_get_bind]
              simp [h_v, h_cpB, h_tA_embed, h_stBR, isOtherSendBeforeChall,
                GameState.tP, CKAParty.other]
            have h_predH :
                (validStep sH.lastAction CKAAction.sendA &&
                  (gp.challengedParty == CKAParty.B) &&
                  isOtherSendBeforeChall gp {sH with tA := sH.tA + 1}) = true := by
              simp [h_lastH, validStep, h_cpB, h_tA_embedH,
                isOtherSendBeforeChall, GameState.tP, CKAParty.other]
            have h_runH :
                (honestSendA_param (F := F) gp gen a ()).run sH =
                  (pure (some (a • gen, a • (x • gen)),
                    { sH with
                      tA := sH.tA + 1, stA := (.recvReady a : CKAState F G),
                      rhoA := some (a • gen), keyA := some (a • (x • gen)),
                      lastAction := some .sendA }) :
                    ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
              unfold honestSendA_param
              rw [StateT.run_get_bind]
              simp [h_lastH, validStep, h_cpB, h_tA_embedH, h_stAH,
                isOtherSendBeforeChall, GameState.tP, CKAParty.other]
            refine relTriple_of_eq_pure_pure
              (oa := (reductionSendA (F := F) gp gen (a • gen) ()).run sR)
              (ob := (honestSendA_param (F := F) gp gen a ()).run sH)
              (R := fun pR pH =>
                pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
              (a := (some (a • gen, x • (a • gen)),
                { sR with
                  tA := sR.tA + 1, stA := (.recvReady 0 : CKAState F G),
                  rhoA := some (a • gen), keyA := some (x • (a • gen)),
                  lastAction := some .sendA }))
              (b := (some (a • gen, a • (x • gen)),
                { sH with
                  tA := sH.tA + 1, stA := (.recvReady a : CKAState F G),
                  rhoA := some (a • gen), keyA := some (a • (x • gen)),
                  lastAction := some .sendA }))
              h_runR h_runH ?_
            refine ⟨by simp [h_key_eq], ?_⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
            · refine ⟨?_, x, a, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [epochCounterInv] using h_phase
              · rfl
              · simpa using h_stBH
              · rfl
              · simpa [h_rhoB] using h_rhoBH
              · rfl
              · simp [h_keyBH]
            · simp [h_tA]
            · simp [h_tB]
            · rfl
            · rfl
            · simp [h_rhoB]
            · intro h
              simp at h
            · exact Or.inr (Or.inl ⟨h_cpB, h_tA_embed, rfl, rfl⟩)
            · simp [h_stB]
            · intro _h_cp _h_tA _h_last_post
              exact ⟨rfl, rfl⟩
            · intro h_cpA _h_tB h_last_post
              simp at h_last_post
            · intro hsafe
              exfalso
              simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
              omega
            · intro hsafe
              exfalso
              simp [allowCorrPCS, allowCorrFS, hΔFS, hΔPCS] at hsafe
              omega
          · have h_embed_false :
                ((gp.challengedParty == CKAParty.B) &&
                  isOtherSendBeforeChall gp {sR with tA := sR.tA + 1}) = false :=
              Bool.eq_false_iff.mpr h_embed
            have h_predH :
                (validStep sH.lastAction CKAAction.sendA &&
                  (gp.challengedParty == CKAParty.B) &&
                  isOtherSendBeforeChall gp {sH with tA := sH.tA + 1}) = false := by
              cases h_party : gp.challengedParty
              · simp [h_lastH, validStep]
              · have h_otherR_false :
                    isOtherSendBeforeChall gp {sR with tA := sR.tA + 1} = false := by
                  have h_embed_false' := h_embed_false
                  simp only [h_party] at h_embed_false'
                  exact h_embed_false'
                have h_tA_not : ¬ sR.tA + 1 = gp.challengeEpoch - 1 := by
                  simpa [isOtherSendBeforeChall, GameState.tP, CKAParty.other, h_party]
                    using h_otherR_false
                have h_otherH_false :
                    isOtherSendBeforeChall gp {sH with tA := sH.tA + 1} = false := by
                  apply Bool.eq_false_iff.mpr
                  intro h_otherH_true
                  apply h_tA_not
                  simpa [isOtherSendBeforeChall, GameState.tP, CKAParty.other, h_party, h_tA]
                    using h_otherH_true
                simpa [h_lastH, validStep, h_party, isOtherSendBeforeChall,
                  GameState.tP, CKAParty.other] using h_otherH_false
            have h_runR :
                (reductionSendA (F := F) gp gen (a • gen) ()).run sR =
                  ((fun y =>
                    (some (y • gen, y • (x • gen)),
                      { sR with
                        tA := sR.tA + 1, stA := (.recvReady y : CKAState F G),
                        rhoA := some (y • gen), keyA := some (y • (x • gen)),
                        lastAction := some .sendA })) <$> ($ᵗ F : ProbComp F)) := by
              unfold reductionSendA
              rw [StateT.run_get_bind]
              cases h_party : gp.challengedParty
              · simp [h_v, h_party, h_stAR, send,
                  isOtherSendBeforeChall, GameState.tP, CKAParty.other]
              · simp [h_v, h_party, h_stAR, send,
                  isOtherSendBeforeChall, GameState.tP, CKAParty.other] at h_embed_false ⊢
                simp [h_embed_false]
            have h_runH :
                (honestSendA_param (F := F) gp gen a ()).run sH =
                  ((fun y =>
                    (some (y • gen, y • (x • gen)),
                      { sH with
                        tA := sH.tA + 1, stA := (.recvReady y : CKAState F G),
                        rhoA := some (y • gen), keyA := some (y • (x • gen)),
                        lastAction := some .sendA })) <$> ($ᵗ F : ProbComp F)) := by
              rw [honestSendA_param_run_eq_when_pred_false (gen := gen) gp a sH h_predH]
              unfold oracleSendA
              rw [StateT.run_get_bind]
              simp [h_lastH, validStep, h_stAH, ddhCKA, send]
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runR) ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right ?_
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runH.symm)
            refine OracleComp.ProgramLogic.Relational.relTriple_map ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_post_mono
              (OracleComp.ProgramLogic.Relational.relTriple_refl
                (spec₁ := unifSpec) (oa := ($ᵗ F : ProbComp F))) ?_
            intro yR yH hy
            subst hy
            refine ⟨rfl, ?_⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ , ?_⟩
            · refine ⟨?_, x, yR, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [epochCounterInv] using h_phase
              · rfl
              · simpa using h_stBH
              · rfl
              · simpa [h_rhoB] using h_rhoBH
              · rfl
              · simp [h_keyBH]
            · simp [h_tA]
            · simp [h_tB]
            · rfl
            · rfl
            · simp [h_rhoB]
            · intro h
              simp at h
            · exact Or.inl rfl
            · simp [h_stB]
            · intro h_cpB h_tA_embed _h_last_post
              exfalso
              apply h_embed
              simp [h_cpB, isOtherSendBeforeChall, GameState.tP, CKAParty.other]
              simpa using h_tA_embed
            · intro h_cpA _h_tB h_last_post
              simp at h_last_post
            · intro _hsafe
              rfl
            · intro hsafe
              apply h_safeB
              by_cases h_allow_post :
                  allowCorrPCS gp
                    ({ sR with
                      tA := sR.tA + 1, stA := (.recvReady yR : CKAState F G),
                      rhoA := some (yR • gen), keyA := some (yR • (x • gen)),
                      lastAction := some .sendA } :
                      GameState (CKAState F G) G G) = true
              · have h_allow_succ :
                    allowCorrPCS gp {sR with tA := sR.tA + 1} = true := by
                  simpa [allowCorr, allowCorrPCS] using h_allow_post
                have h_allow_pre := allowCorr_of_allowCorr_tA_succ gp sR h_allow_succ
                simp [h_allow_pre]
              · have h_allow_post_false :
                    allowCorrPCS gp
                      ({ sR with
                        tA := sR.tA + 1, stA := (.recvReady yR : CKAState F G),
                        rhoA := some (yR • gen), keyA := some (yR • (x • gen)),
                        lastAction := some .sendA } :
                        GameState (CKAState F G) G G) = false :=
                  Bool.eq_false_iff.mpr h_allow_post
                have h_finished_post :
                    allowCorrFS gp
                      ({ sR with
                        tA := sR.tA + 1, stA := (.recvReady yR : CKAState F G),
                        rhoA := some (yR • gen), keyA := some (yR • (x • gen)),
                        lastAction := some .sendA } :
                        GameState (CKAState F G) G G) .B = true := by
                  simpa [h_allow_post_false] using hsafe
                have h_finished_pre : allowCorrFS gp sR .B = true := by
                  simpa [allowCorrFS] using h_finished_post
                simp [h_finished_pre]
      · exact relTriple_reductionSendA_invalid_of_state_rel
          (gp := gp) (gen := gen) (a := a)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH) h_last h_v hrel_self
  | ORecvB =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      by_cases h_v : validStep sR.lastAction CKAAction.recvB = true
      · have h_vH : validStep sH.lastAction CKAAction.recvB = true := by
          rw [← h_last]
          exact h_v
        rcases h_lastH : sH.lastAction with _ | (_ | _ | _ | _ | _ | _) <;>
          simp [h_lastH, validStep] at h_vH
        all_goals
          rcases (by
            simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
              using h_shape) with
            ⟨h_phase, x, y, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
          have h_stBR_inl : ∃ xR : F, sR.stB = (.recvReady xR : CKAState F G) := by
            rcases h_stB with h_eq | h_dead | h_dead
            · exact ⟨x, by rw [h_eq, h_stBH]⟩
            · rcases h_dead with ⟨_, _, h_stBR, _⟩
              exact ⟨0, h_stBR⟩
            · rcases h_dead with ⟨_, _, h_stBR, _⟩
              exact ⟨0, h_stBR⟩
          rcases h_stBR_inl with ⟨xR, h_stBR⟩
          have h_rhoAR : sR.rhoA = some (y • gen) := by
            rw [h_rhoA, h_rhoAH]
          let cR : Bool :=
            sR.correct && (sR.keyA == some (xR • (y • gen)))
          let cH : Bool :=
            sH.correct && (sH.keyA == some (x • (y • gen)))
          have h_runR :
              (oracleRecvB (ddhCKA F G gen) ()).run sR =
                (pure ((), { sR with
                  tB := sR.tB + 1, stB := .sendReady (y • gen),
                  rhoA := none, keyA := none, correct := cR,
                  lastAction := some .recvB }) :
                  ProbComp (Unit × GameState (CKAState F G) G G)) := by
            unfold oracleRecvB
            rw [StateT.run_get_bind]
            simp [h_v, h_stBR, h_rhoAR, ddhCKA, recv, cR]
          have h_runH :
              (oracleRecvB (ddhCKA F G gen) ()).run sH =
                (pure ((), { sH with
                  tB := sH.tB + 1, stB := .sendReady (y • gen),
                  rhoA := none, keyA := none, correct := cH,
                  lastAction := some .recvB }) :
                  ProbComp (Unit × GameState (CKAState F G) G G)) := by
            unfold oracleRecvB
            rw [StateT.run_get_bind]
            simp [h_lastH, validStep, h_stBH, h_rhoAH, h_keyAH, ddhCKA, recv, cH]
          refine relTriple_of_eq_pure_pure
            (oa := (oracleRecvB (ddhCKA F G gen) ()).run sR)
            (ob := (oracleRecvB (ddhCKA F G gen) ()).run sH)
            (R := fun pR pH =>
              pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
            (a := ((), { sR with
              tB := sR.tB + 1, stB := .sendReady (y • gen),
              rhoA := none, keyA := none, correct := cR,
              lastAction := some .recvB }))
            (b := ((), { sH with
              tB := sH.tB + 1, stB := .sendReady (y • gen),
              rhoA := none, keyA := none, correct := cH,
              lastAction := some .recvB }))
            h_runR h_runH ?_
          exact ⟨rfl, reductionHonestRel_rand_after_recvB (gen := gen) gp a b y gT cR cH
            sR sH h_phase h_stAH h_rhoBH h_keyBH h_tA h_tB h_rhoB
            h_stA
            (by
              intro h_cp h_tA_embed
              exact h_pendingA h_cp h_tA_embed (by rw [h_last, h_lastH]; simp))
            h_safeA⟩
      · exact relTriple_oracleRecvB_invalid_of_state_rel
          (gen := gen)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH) h_last h_v hrel_self
  | ORecvA =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      by_cases h_v : validStep sR.lastAction CKAAction.recvA = true
      · have h_vH : validStep sH.lastAction CKAAction.recvA = true := by
          rw [← h_last]
          exact h_v
        rcases h_lastH : sH.lastAction with _ | (_ | _ | _ | _ | _ | _) <;>
          simp [h_lastH, validStep] at h_vH
        all_goals
          rcases (by
            simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
              using h_shape) with
            ⟨h_phase, x, y, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
          have h_stAR_inl : ∃ yR : F, sR.stA = (.recvReady yR : CKAState F G) := by
            rcases h_stA with h_eq | h_dead | h_dead
            · exact ⟨y, by rw [h_eq, h_stAH]⟩
            · rcases h_dead with ⟨_, _, h_stAR, _⟩
              exact ⟨0, h_stAR⟩
            · rcases h_dead with ⟨_, _, h_stAR, _⟩
              exact ⟨0, h_stAR⟩
          rcases h_stAR_inl with ⟨yR, h_stAR⟩
          have h_rhoBR : sR.rhoB = some (x • gen) := by
            rw [h_rhoB, h_rhoBH]
          let cR : Bool :=
            sR.correct && (sR.keyB == some (yR • (x • gen)))
          let cH : Bool :=
            sH.correct && (sH.keyB == some (y • (x • gen)))
          have h_runR :
              (oracleRecvA (ddhCKA F G gen) ()).run sR =
                (pure ((), { sR with
                  tA := sR.tA + 1, stA := .sendReady (x • gen),
                  rhoB := none, keyB := none, correct := cR,
                  lastAction := some .recvA }) :
                  ProbComp (Unit × GameState (CKAState F G) G G)) := by
            unfold oracleRecvA
            rw [StateT.run_get_bind]
            simp [h_v, h_stAR, h_rhoBR, ddhCKA, recv, cR]
          have h_runH :
              (oracleRecvA (ddhCKA F G gen) ()).run sH =
                (pure ((), { sH with
                  tA := sH.tA + 1, stA := .sendReady (x • gen),
                  rhoB := none, keyB := none, correct := cH,
                  lastAction := some .recvA }) :
                  ProbComp (Unit × GameState (CKAState F G) G G)) := by
            unfold oracleRecvA
            rw [StateT.run_get_bind]
            simp [h_lastH, validStep, h_stAH, h_rhoBH, h_keyBH, ddhCKA, recv, cH]
          refine relTriple_of_eq_pure_pure
            (oa := (oracleRecvA (ddhCKA F G gen) ()).run sR)
            (ob := (oracleRecvA (ddhCKA F G gen) ()).run sH)
            (R := fun pR pH =>
              pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
            (a := ((), { sR with
              tA := sR.tA + 1, stA := .sendReady (x • gen),
              rhoB := none, keyB := none, correct := cR,
              lastAction := some .recvA }))
            (b := ((), { sH with
              tA := sH.tA + 1, stA := .sendReady (x • gen),
              rhoB := none, keyB := none, correct := cH,
              lastAction := some .recvA }))
            h_runR h_runH ?_
          exact ⟨rfl, reductionHonestRel_rand_after_recvA (gen := gen) gp a b x gT cR cH
            sR sH h_phase h_stBH h_rhoAH h_keyAH h_tA h_tB h_rhoA
            h_stB
            (by
              intro h_cp h_tB_embed
              exact h_pendingB h_cp h_tB_embed (by rw [h_last, h_lastH]; simp))
            h_safeB⟩
      · exact relTriple_oracleRecvA_invalid_of_state_rel
          (gen := gen)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH) h_last h_v hrel_self
  | OSendA_rleak =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      by_cases h_v : validStep sR.lastAction CKAAction.sendA = true
      · have h_vH : validStep sH.lastAction CKAAction.sendA = true := by
          rw [← h_last]
          exact h_v
        by_cases h_allow : allowCorrPCS gp {sR with tA := sR.tA + 1} = true
        · have h_allowH : allowCorrPCS gp {sH with tA := sH.tA + 1} = true := by
            simpa [allowCorr, allowCorrPCS, h_tA, h_tB] using h_allow
          have h_allow_pre := allowCorr_of_allowCorr_tA_succ gp sR h_allow
          have h_stA_eq : sR.stA = sH.stA := h_safeA (by simp [h_allow_pre])
          rcases h_lastH : sH.lastAction with _ | (_ | _ | _ | _ | _ | _) <;>
            simp [h_lastH, validStep] at h_vH
          all_goals
            rcases (by
              simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
                using h_shape) with
              ⟨h_phase, x, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
            have h_stAR : sR.stA = (.sendReady (x • gen) : CKAState F G) := by
              rw [h_stA_eq, h_stAH]
            have h_runR :
                (oracleSendA_rleak gp (ddhCKA F G gen) ()).run sR =
                  ((fun y =>
                    (some (y • gen, y • (x • gen), y),
                      { sR with
                        tA := sR.tA + 1, stA := (.recvReady y : CKAState F G),
                        rhoA := some (y • gen), keyA := some (y • (x • gen)),
                        lastAction := some .sendA })) <$> ($ᵗ F : ProbComp F)) := by
              unfold oracleSendA_rleak
              rw [StateT.run_get_bind]
              rw [if_pos h_v]
              rw [if_pos h_allow]
              simp [h_stAR, ddhCKA, send_rleak]
            have h_runH :
                (oracleSendA_rleak gp (ddhCKA F G gen) ()).run sH =
                  ((fun y =>
                    (some (y • gen, y • (x • gen), y),
                      { sH with
                        tA := sH.tA + 1, stA := (.recvReady y : CKAState F G),
                        rhoA := some (y • gen), keyA := some (y • (x • gen)),
                        lastAction := some .sendA })) <$> ($ᵗ F : ProbComp F)) := by
              unfold oracleSendA_rleak
              rw [StateT.run_get_bind]
              rw [if_pos (by simp [h_lastH, validStep])]
              rw [if_pos h_allowH]
              simp [h_stAH, ddhCKA, send_rleak]
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runR) ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right ?_
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runH.symm)
            refine OracleComp.ProgramLogic.Relational.relTriple_map ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_post_mono
              (OracleComp.ProgramLogic.Relational.relTriple_refl
                (spec₁ := unifSpec) (oa := ($ᵗ F : ProbComp F))) ?_
            intro yR yH hy
            subst hy
            refine ⟨rfl, ?_⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · refine ⟨?_, x, yR, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [epochCounterInv] using h_phase
              · rfl
              · simpa using h_stBH
              · rfl
              · simpa [h_rhoB] using h_rhoBH
              · rfl
              · simp [h_keyBH]
            · simp [h_tA]
            · simp [h_tB]
            · rfl
            · rfl
            · simp [h_rhoB]
            · intro h
              simp at h
            · exact Or.inl rfl
            · simp [h_stB]
            · intro _h_cp h_tA_embed _h_last_post
              exfalso
              simp at h_tA_embed
              have h_le_max : max (sR.tA + 1) sR.tB + gp.ΔPCS ≤ gp.challengeEpoch := by
                simpa [allowCorr, allowCorrPCS] using h_allow
              have h_le_tA : sR.tA + 1 + gp.ΔPCS ≤ gp.challengeEpoch :=
                le_trans (Nat.add_le_add_right (le_max_left (sR.tA + 1) sR.tB) gp.ΔPCS)
                  h_le_max
              simp [hΔPCS] at h_le_tA
              omega
            · intro _h_cp _h_tB h_last_post
              simp at h_last_post
            · intro _hsafe
              rfl
            · intro hsafe
              apply h_safeB
              by_cases h_allow_post :
                  allowCorrPCS gp
                    ({ sR with
                      tA := sR.tA + 1, stA := (.recvReady yR : CKAState F G),
                      rhoA := some (yR • gen), keyA := some (yR • (x • gen)),
                      lastAction := some .sendA } :
                      GameState (CKAState F G) G G) = true
              · have h_allow_succ :
                    allowCorrPCS gp {sR with tA := sR.tA + 1} = true := by
                  simpa [allowCorr, allowCorrPCS] using h_allow_post
                have h_allow_pre := allowCorr_of_allowCorr_tA_succ gp sR h_allow_succ
                simp [h_allow_pre]
              · have h_allow_post_false :
                    allowCorrPCS gp
                      ({ sR with
                        tA := sR.tA + 1, stA := (.recvReady yR : CKAState F G),
                        rhoA := some (yR • gen), keyA := some (yR • (x • gen)),
                        lastAction := some .sendA } :
                        GameState (CKAState F G) G G) = false :=
                  Bool.eq_false_iff.mpr h_allow_post
                have h_finished_post :
                    allowCorrFS gp
                      ({ sR with
                        tA := sR.tA + 1, stA := (.recvReady yR : CKAState F G),
                        rhoA := some (yR • gen), keyA := some (yR • (x • gen)),
                        lastAction := some .sendA } :
                        GameState (CKAState F G) G G) .B = true := by
                  simpa [h_allow_post_false] using hsafe
                have h_finished_pre : allowCorrFS gp sR .B = true := by
                  simpa [allowCorrFS] using h_finished_post
                simp [h_finished_pre]
        · have h_allowR : allowCorrPCS gp {sR with tA := sR.tA + 1} = false :=
            Bool.eq_false_iff.mpr h_allow
          have h_allowH : allowCorrPCS gp {sH with tA := sH.tA + 1} = false := by
            simpa [allowCorr, allowCorrPCS, h_tA, h_tB] using h_allowR
          have h_runR :
              (oracleSendA_rleak gp (ddhCKA F G gen) ()).run sR =
                (pure (none, sR) :
                  ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
            unfold oracleSendA_rleak
            rw [StateT.run_get_bind]
            simp [h_v, h_allowR]
          have h_runH :
              (oracleSendA_rleak gp (ddhCKA F G gen) ()).run sH =
                (pure (none, sH) :
                  ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
            unfold oracleSendA_rleak
            rw [StateT.run_get_bind]
            simp [h_vH, h_allowH]
          refine relTriple_of_eq_pure_pure
            (R := fun pR pH =>
              pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
            (a := (none, sR)) (b := (none, sH)) h_runR h_runH ⟨rfl, hrel_self⟩
      · exact relTriple_oracleSendA_rleak_invalid_of_state_rel
          (gp := gp) (gen := gen)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH) h_last h_v hrel_self
  | OSendB_rleak =>
      simp only [reductionOracleImpl, honestImpl_param_rand, QueryImpl.add_apply_inr]
      by_cases h_v : validStep sR.lastAction CKAAction.sendB = true
      · have h_vH : validStep sH.lastAction CKAAction.sendB = true := by
          rw [← h_last]
          exact h_v
        by_cases h_allow : allowCorrPCS gp {sR with tB := sR.tB + 1} = true
        · have h_allowH : allowCorrPCS gp {sH with tB := sH.tB + 1} = true := by
            simpa [allowCorr, allowCorrPCS, h_tA, h_tB] using h_allow
          have h_allow_pre := allowCorr_of_allowCorr_tB_succ gp sR h_allow
          have h_stB_eq : sR.stB = sH.stB := h_safeB (by simp [h_allow_pre])
          rcases h_lastH : sH.lastAction with _ | (_ | _ | _ | _ | _ | _) <;>
            simp [h_lastH, validStep] at h_vH
          all_goals
            rcases (by
              simpa [reachableShape, epochCounterInv, stateShapeInv, h_lastH]
                using h_shape) with
              ⟨h_phase, y, h_stAH, h_stBH, h_rhoAH, h_rhoBH, h_keyAH, h_keyBH⟩
            have h_stBR : sR.stB = (.sendReady (y • gen) : CKAState F G) := by
              rw [h_stB_eq, h_stBH]
            have h_runR :
                (oracleSendB_rleak gp (ddhCKA F G gen) ()).run sR =
                  ((fun x =>
                    (some (x • gen, x • (y • gen), x),
                      { sR with
                        tB := sR.tB + 1, stB := (.recvReady x : CKAState F G),
                        rhoB := some (x • gen), keyB := some (x • (y • gen)),
                        lastAction := some .sendB })) <$> ($ᵗ F : ProbComp F)) := by
              unfold oracleSendB_rleak
              rw [StateT.run_get_bind]
              rw [if_pos h_v]
              rw [if_pos h_allow]
              simp [h_stBR, ddhCKA, send_rleak]
            have h_runH :
                (oracleSendB_rleak gp (ddhCKA F G gen) ()).run sH =
                  ((fun x =>
                    (some (x • gen, x • (y • gen), x),
                      { sH with
                        tB := sH.tB + 1, stB := (.recvReady x : CKAState F G),
                        rhoB := some (x • gen), keyB := some (x • (y • gen)),
                        lastAction := some .sendB })) <$> ($ᵗ F : ProbComp F)) := by
              unfold oracleSendB_rleak
              rw [StateT.run_get_bind]
              rw [if_pos (by simp [h_lastH, validStep])]
              rw [if_pos h_allowH]
              simp [h_stBH, ddhCKA, send_rleak]
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runR) ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right ?_
              (OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq h_runH.symm)
            refine OracleComp.ProgramLogic.Relational.relTriple_map ?_
            refine OracleComp.ProgramLogic.Relational.relTriple_post_mono
              (OracleComp.ProgramLogic.Relational.relTriple_refl
                (spec₁ := unifSpec) (oa := ($ᵗ F : ProbComp F))) ?_
            intro xR xH hx
            subst hx
            refine ⟨rfl, ?_⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · refine ⟨?_, xR, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [epochCounterInv] using h_phase.symm
              · simpa using h_stAH
              · rfl
              · simpa [h_rhoA] using h_rhoAH
              · rfl
              · simp [h_keyAH]
              · rfl
            · simp [h_tA]
            · simp [h_tB]
            · rfl
            · simp [h_rhoA]
            · rfl
            · intro h
              simp at h
            · simp [h_stA]
            · exact Or.inl rfl
            · intro _h_cp _h_tA h_last_post
              simp at h_last_post
            · intro _h_cp h_tB_embed _h_last_post
              exfalso
              simp at h_tB_embed
              have h_le_max : max sR.tA (sR.tB + 1) + gp.ΔPCS ≤ gp.challengeEpoch := by
                simpa [allowCorr, allowCorrPCS] using h_allow
              have h_le_tB : sR.tB + 1 + gp.ΔPCS ≤ gp.challengeEpoch :=
                le_trans (Nat.add_le_add_right (le_max_right sR.tA (sR.tB + 1)) gp.ΔPCS)
                  h_le_max
              simp [hΔPCS] at h_le_tB
              omega
            · intro hsafe
              apply h_safeA
              by_cases h_allow_post :
                  allowCorrPCS gp
                    ({ sR with
                      tB := sR.tB + 1, stB := (.recvReady xR : CKAState F G),
                      rhoB := some (xR • gen), keyB := some (xR • (y • gen)),
                      lastAction := some .sendB } :
                      GameState (CKAState F G) G G) = true
              · have h_allow_succ :
                    allowCorrPCS gp {sR with tB := sR.tB + 1} = true := by
                  simpa [allowCorr, allowCorrPCS] using h_allow_post
                have h_allow_pre := allowCorr_of_allowCorr_tB_succ gp sR h_allow_succ
                simp [h_allow_pre]
              · have h_allow_post_false :
                    allowCorrPCS gp
                      ({ sR with
                        tB := sR.tB + 1, stB := (.recvReady xR : CKAState F G),
                        rhoB := some (xR • gen), keyB := some (xR • (y • gen)),
                        lastAction := some .sendB } :
                        GameState (CKAState F G) G G) = false :=
                  Bool.eq_false_iff.mpr h_allow_post
                have h_finished_post :
                    allowCorrFS gp
                      ({ sR with
                        tB := sR.tB + 1, stB := (.recvReady xR : CKAState F G),
                        rhoB := some (xR • gen), keyB := some (xR • (y • gen)),
                        lastAction := some .sendB } :
                        GameState (CKAState F G) G G) .A = true := by
                  simpa [h_allow_post_false] using hsafe
                have h_finished_pre : allowCorrFS gp sR .A = true := by
                  simpa [allowCorrFS] using h_finished_post
                simp [h_finished_pre]
            · intro _hsafe
              rfl
        · have h_allowR : allowCorrPCS gp {sR with tB := sR.tB + 1} = false :=
            Bool.eq_false_iff.mpr h_allow
          have h_allowH : allowCorrPCS gp {sH with tB := sH.tB + 1} = false := by
            simpa [allowCorr, allowCorrPCS, h_tA, h_tB] using h_allowR
          have h_runR :
              (oracleSendB_rleak gp (ddhCKA F G gen) ()).run sR =
                (pure (none, sR) :
                  ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
            unfold oracleSendB_rleak
            rw [StateT.run_get_bind]
            simp [h_v, h_allowR]
          have h_runH :
              (oracleSendB_rleak gp (ddhCKA F G gen) ()).run sH =
                (pure (none, sH) :
                  ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
            unfold oracleSendB_rleak
            rw [StateT.run_get_bind]
            simp [h_vH, h_allowH]
          refine relTriple_of_eq_pure_pure
            (R := fun pR pH =>
              pR.1 = pH.1 ∧ reductionHonestRel_rand gp gen a b gT pR.2 pH.2)
            (a := (none, sR)) (b := (none, sH)) h_runR h_runH ⟨rfl, hrel_self⟩
      · exact relTriple_oracleSendB_rleak_invalid_of_state_rel
          (gp := gp) (gen := gen)
          (R := fun sR sH => reductionHonestRel_rand gp gen a b gT sR sH)
          (sL := sR) (sR := sH) h_last h_v hrel_self


omit [DecidableEq F] [DecidableEq G] [Inhabited F] [Fintype F] [Fintype G] in
/-- Rand-branch outer DDH sample rewrite: replace `c ← $ᵗ F; c • gen` by an
equivalent direct sample `gT ← $ᵗ G` using the bijection `c ↦ c • gen`. -/
lemma probOutput_reduction_rand_sample_gT
    (hg : Function.Bijective (· • gen : F → G))
  {γ : Type} [Finite F]
    (m : G → ProbComp γ) (z : γ) :
    Pr[= z | do
      let c ← ($ᵗ F : ProbComp F)
      m (c • gen)] =
    Pr[= z | do
      let gT ← ($ᵗ G : ProbComp G)
      m gT] := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  exact probOutput_bind_bijective_uniform_cross (α := F) (β := G) (γ := γ)
    (f := fun c : F => c • gen) hg m z

omit [Inhabited F] [Fintype G] in
/-- Fixed-parameter random-branch reduction/honest bridge.

In the general case, the reduction stack with fixed DDH inputs
`(a • gen, b • gen, gT)` is observationally equivalent to the parameterized
honest random stack `honestImpl_param_rand gp gen a b gT` from the same initial
state. The state relation `reductionHonestRel_rand` carries the per-query
simulation. -/
lemma evalDist_reduction_honest_param_rand_eq
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
  (h_general_case : ¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A))
    (x₀ a b : F) (gT : G)
    (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool) :
    evalDist ((simulateQ
        (reductionOracleImpl gp gen (a • gen) (b • gen) gT) adversary).run'
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        (CKAState.recvReady x₀ : CKAState F G))) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run'
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        (CKAState.recvReady x₀ : CKAState F G))) := by
  apply OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run'_eq_of_state_rel
    (R := reductionHonestRel_rand gp gen a b gT)
  · intro t sR sH hrel
    exact reduction_honest_param_rand_step_rel
      (gen := gen) gp hΔFS hΔPCS a b gT t sR sH hrel
  · change reductionHonestRel_rand gp gen a b gT
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        (CKAState.recvReady x₀ : CKAState F G))
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        (CKAState.recvReady x₀ : CKAState F G))
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rfl
      · exact ⟨x₀, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro _
      exact ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · intro _ _ h_last
      rcases h_last with h_last | h_last | h_last <;> cases h_last
    · intro h_cp h_tB _h_last
      have h_challengeEpoch : gp.challengeEpoch = 1 := by
        simpa [initGameState] using h_tB.symm
      exact False.elim (h_general_case ⟨h_challengeEpoch, h_cp⟩)
    · intro _
      rfl
    · intro _
      rfl


end Step2

end ddhCKA
