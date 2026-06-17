import SecureMessaging.CKA.FromDDH.Security.GameOracles.Bridge

/-!
# Shared Left/Right Per-Query Relational Lemmas

This file factors out per-query relational lemmas with a left/right interface.

The common shape is left/right:

```lean
R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop
hrel : R sL sR

RelTriple (leftOracleCall.run sL) (rightOracleCall.run sR)
  (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
```

Each lemma couples one left oracle call with one right oracle call, proves that
their visible answers agree, and preserves an abstract state relation `R`.
The callers choose the concrete relation and discharge any premises about
counters, guards, or local state agreement.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

open CKAScheme DiffieHellman ckaSecuritySpec

variable [DecidableEq G]

section Step2
variable [Inhabited F]
variable [Fintype G]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited F] [Fintype G] in
/-- Left/right `corruptB` relational step. For related states `R sL sR`,
matching counters, and B-state agreement at enabled corruption points, the
paired `oracleCorruptB` calls return equal outputs and leave the resulting
states related by `R`. -/
lemma relTriple_oracleCorruptB_of_state_rel
    (gp : GameParams)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_tA : sL.tA = sR.tA) (h_tB : sL.tB = sR.tB)
    (h_safeB : (allowCorrPCS gp sL || allowCorrFS gp sL .B) = true → sL.stB = sR.stB)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleCorruptB gp (CKAState F G) G G ()).run sL)
      ((oracleCorruptB gp (CKAState F G) G G ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  unfold oracleCorruptB
  have h_guard :
      (allowCorrPCS gp sR || allowCorrFS gp sR .B) =
        (allowCorrPCS gp sL || allowCorrFS gp sL .B) := by
    simp [allowCorrPCS, allowCorrFS, h_tA, h_tB]
  by_cases h : allowCorrPCS gp sL || allowCorrFS gp sL .B
  · have hR : (allowCorrPCS gp sR || allowCorrFS gp sR .B) = true := by
      rw [h_guard]
      exact h
    convert (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
      (spec₁ := unifSpec) (spec₂ := unifSpec)
      (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
      (a := (some sL.stB, sL)) (b := (some sR.stB, sR))
      ⟨by simp [h_safeB h], hrel⟩) using 1 <;>
      (change ((get : StateT _ ProbComp _) >>= fun state =>
          if (allowCorrPCS gp state || allowCorrFS gp state .B) = true then
            pure (some state.stB) else pure none).run _ = _
       rw [StateT.run_get_bind]
       first
       | rw [if_pos h]
       | rw [if_pos hR]
       rfl)
  · have hL : (allowCorrPCS gp sL || allowCorrFS gp sL .B) = false :=
      Bool.eq_false_iff.mpr h
    have hR : (allowCorrPCS gp sR || allowCorrFS gp sR .B) = false := by
      rw [h_guard]
      exact hL
    have hNotL : ¬ ((allowCorrPCS gp sL || allowCorrFS gp sL .B) = true) := by
      simp [hL]
    have hNotR : ¬ ((allowCorrPCS gp sR || allowCorrFS gp sR .B) = true) := by
      simp [hR]
    have hp : OracleComp.ProgramLogic.Relational.RelTriple
        (pure (none, sL) : ProbComp (Option (CKAState F G) × GameState (CKAState F G) G G))
        (pure (none, sR) : ProbComp (Option (CKAState F G) × GameState (CKAState F G) G G))
        (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) :=
      OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
        (a := (none, sL)) (b := (none, sR))
        ⟨rfl, hrel⟩
    convert hp using 1 <;>
      (change ((get : StateT _ ProbComp _) >>= fun state =>
          if (allowCorrPCS gp state || allowCorrFS gp state .B) = true then
            pure (some state.stB) else pure none).run _ = _
       rw [StateT.run_get_bind]
       first
       | rw [if_neg hNotL]
       | rw [if_neg hNotR]
       rfl)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited F] [Fintype G] in
/-- Left/right `corruptA` relational step. For related states `R sL sR`,
matching counters, and A-state agreement at enabled corruption points, the
paired `oracleCorruptA` calls return equal outputs and leave the resulting
states related by `R`. -/
lemma relTriple_oracleCorruptA_of_state_rel
    (gp : GameParams)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_tA : sL.tA = sR.tA) (h_tB : sL.tB = sR.tB)
    (h_safeA : (allowCorrPCS gp sL || allowCorrFS gp sL .A) = true → sL.stA = sR.stA)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleCorruptA gp (CKAState F G) G G ()).run sL)
      ((oracleCorruptA gp (CKAState F G) G G ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  unfold oracleCorruptA
  have h_guard :
      (allowCorrPCS gp sR || allowCorrFS gp sR .A) =
        (allowCorrPCS gp sL || allowCorrFS gp sL .A) := by
    simp [allowCorrPCS, allowCorrFS, h_tA, h_tB]
  by_cases h : allowCorrPCS gp sL || allowCorrFS gp sL .A
  · have hR : (allowCorrPCS gp sR || allowCorrFS gp sR .A) = true := by
      rw [h_guard]
      exact h
    convert (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
      (spec₁ := unifSpec) (spec₂ := unifSpec)
      (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
      (a := (some sL.stA, sL)) (b := (some sR.stA, sR))
      ⟨by simp [h_safeA h], hrel⟩) using 1 <;>
      (change ((get : StateT _ ProbComp _) >>= fun state =>
          if (allowCorrPCS gp state || allowCorrFS gp state .A) = true then
            pure (some state.stA) else pure none).run _ = _
       rw [StateT.run_get_bind]
       first
       | rw [if_pos h]
       | rw [if_pos hR]
       rfl)
  · have hL : (allowCorrPCS gp sL || allowCorrFS gp sL .A) = false :=
      Bool.eq_false_iff.mpr h
    have hR : (allowCorrPCS gp sR || allowCorrFS gp sR .A) = false := by
      rw [h_guard]
      exact hL
    have hNotL : ¬ ((allowCorrPCS gp sL || allowCorrFS gp sL .A) = true) := by
      simp [hL]
    have hNotR : ¬ ((allowCorrPCS gp sR || allowCorrFS gp sR .A) = true) := by
      simp [hR]
    have hp : OracleComp.ProgramLogic.Relational.RelTriple
        (pure (none, sL) : ProbComp (Option (CKAState F G) × GameState (CKAState F G) G G))
        (pure (none, sR) : ProbComp (Option (CKAState F G) × GameState (CKAState F G) G G))
        (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) :=
      OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
        (a := (none, sL)) (b := (none, sR))
        ⟨rfl, hrel⟩
    convert hp using 1 <;>
      (change ((get : StateT _ ProbComp _) >>= fun state =>
          if (allowCorrPCS gp state || allowCorrFS gp state .A) = true then
            pure (some state.stA) else pure none).run _ = _
       rw [StateT.run_get_bind]
       first
       | rw [if_neg hNotL]
       | rw [if_neg hNotR]
       rfl)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited F] [Fintype G] in
/-- Left/right uniform-query relational step. For related states
`R sL sR`, the paired `oracleUnif n` calls are coupled on the same uniform
answer; their visible results agree and the resulting states remain related by
`R`. -/
lemma relTriple_oracleUnif_of_state_rel
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (n : unifSpec.Domain)
    (sL sR : GameState (CKAState F G) G G)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleUnif (CKAState F G) G G n).run sL)
      ((oracleUnif (CKAState F G) G G n).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  unfold oracleUnif QueryImpl.liftTarget QueryImpl.ofLift
  change OracleComp.ProgramLogic.Relational.RelTriple
    ((query n : ProbComp ((unifSpec).Range n)) >>= fun u => pure (u, sL))
    ((query n : ProbComp ((unifSpec).Range n)) >>= fun u => pure (u, sR))
    (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_refl
      (spec₁ := unifSpec) (oa := (query n : ProbComp ((unifSpec).Range n)))) ?_
  intro uL uR hu
  subst hu
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure
    (spec₁ := unifSpec) (spec₂ := unifSpec)
    ⟨rfl, hrel⟩

omit [Inhabited F] [Fintype G] in
/-- Left/right disabled-action `recvB` relational step. For `R sL sR`,
equal last actions, and a disabled `recvB` transition at `sL`, the paired
`oracleRecvB` calls both return `()` and establish
`pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_oracleRecvB_invalid_of_state_rel
    (gen : G)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_last : sL.lastAction = sR.lastAction)
    (h_v : ¬ validStep sL.lastAction CKAAction.recvB = true)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleRecvB (ddhCKA F G gen) ()).run sL)
      ((oracleRecvB (ddhCKA F G gen) ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_vL : validStep sL.lastAction CKAAction.recvB = false :=
    Bool.eq_false_iff.mpr h_v
  have h_vR : validStep sR.lastAction CKAAction.recvB = false := by
    rw [← h_last]
    exact h_vL
  have h_runL :
      (oracleRecvB (ddhCKA F G gen) ()).run sL =
        (pure ((), sL) : ProbComp (Unit × GameState (CKAState F G) G G)) := by
    unfold oracleRecvB
    rw [StateT.run_get_bind]
    simp [h_vL]
  have h_runR :
      (oracleRecvB (ddhCKA F G gen) ()).run sR =
        (pure ((), sR) : ProbComp (Unit × GameState (CKAState F G) G G)) := by
    unfold oracleRecvB
    rw [StateT.run_get_bind]
    simp [h_vR]
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := ((), sL)) (b := ((), sR)) h_runL h_runR ⟨rfl, hrel⟩

omit [Inhabited F] [Fintype G] in
/-- Left/right disabled-action `recvA` relational step. For `R sL sR`,
equal last actions, and a disabled `recvA` transition at `sL`, the paired
`oracleRecvA` calls both return `()` and establish
`pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_oracleRecvA_invalid_of_state_rel
    (gen : G)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_last : sL.lastAction = sR.lastAction)
    (h_v : ¬ validStep sL.lastAction CKAAction.recvA = true)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleRecvA (ddhCKA F G gen) ()).run sL)
      ((oracleRecvA (ddhCKA F G gen) ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_vL : validStep sL.lastAction CKAAction.recvA = false :=
    Bool.eq_false_iff.mpr h_v
  have h_vR : validStep sR.lastAction CKAAction.recvA = false := by
    rw [← h_last]
    exact h_vL
  have h_runL :
      (oracleRecvA (ddhCKA F G gen) ()).run sL =
        (pure ((), sL) : ProbComp (Unit × GameState (CKAState F G) G G)) := by
    unfold oracleRecvA
    rw [StateT.run_get_bind]
    simp [h_vL]
  have h_runR :
      (oracleRecvA (ddhCKA F G gen) ()).run sR =
        (pure ((), sR) : ProbComp (Unit × GameState (CKAState F G) G G)) := by
    unfold oracleRecvA
    rw [StateT.run_get_bind]
    simp [h_vR]
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := ((), sL)) (b := ((), sR)) h_runL h_runR ⟨rfl, hrel⟩

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Left/right disabled-action `sendA` relational step. For `R sL sR`,
equal last actions, and a disabled `sendA` transition at `sL`, the paired
left/right `sendA` calls both return `none` and establish
`pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_reductionSendA_invalid_of_state_rel
    (gp : GameParams) (gen : G) (a : F)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_last : sL.lastAction = sR.lastAction)
    (h_v : ¬ validStep sL.lastAction CKAAction.sendA = true)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionSendA (F := F) gp gen (a • gen) ()).run sL)
      ((honestSendA_param (F := F) gp gen a ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_vL : validStep sL.lastAction CKAAction.sendA = false :=
    Bool.eq_false_iff.mpr h_v
  have h_vR : validStep sR.lastAction CKAAction.sendA = false := by
    rw [← h_last]
    exact h_vL
  have h_runL :
      (reductionSendA (F := F) gp gen (a • gen) ()).run sL =
        (pure (none, sL) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    unfold reductionSendA
    rw [StateT.run_get_bind]
    simp [h_vL]
  have h_predR :
      (validStep sR.lastAction CKAAction.sendA &&
        (gp.challengedParty == CKAParty.B) &&
        isOtherSendBeforeChall gp { sR with tA := sR.tA + 1 }) = false := by
    rw [h_vR]
    simp
  have h_runR :
      (honestSendA_param (F := F) gp gen a ()).run sR =
        (pure (none, sR) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    rw [honestSendA_param_run_eq_when_pred_false (gen := gen) gp a sR h_predR]
    unfold oracleSendA
    rw [StateT.run_get_bind]
    simp [h_vR]
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := (none, sL)) (b := (none, sR)) h_runL h_runR ⟨rfl, hrel⟩

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Left/right disabled-action `sendB` relational step. For `R sL sR`,
equal last actions, and a disabled `sendB` transition at `sL`, the paired
left/right `sendB` calls both return `none` and establish
`pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_reductionSendB_invalid_of_state_rel
    (gp : GameParams) (gen : G) (a : F)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_last : sL.lastAction = sR.lastAction)
    (h_v : ¬ validStep sL.lastAction CKAAction.sendB = true)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionSendB (F := F) gp gen (a • gen) ()).run sL)
      ((honestSendB_param (F := F) gp gen a ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_vL : validStep sL.lastAction CKAAction.sendB = false :=
    Bool.eq_false_iff.mpr h_v
  have h_vR : validStep sR.lastAction CKAAction.sendB = false := by
    rw [← h_last]
    exact h_vL
  have h_runL :
      (reductionSendB (F := F) gp gen (a • gen) ()).run sL =
        (pure (none, sL) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    unfold reductionSendB
    rw [StateT.run_get_bind]
    simp [h_vL]
  have h_predR :
      (validStep sR.lastAction CKAAction.sendB &&
        (gp.challengedParty == CKAParty.A) &&
        isOtherSendBeforeChall gp { sR with tB := sR.tB + 1 }) = false := by
    rw [h_vR]
    simp
  have h_runR :
      (honestSendB_param (F := F) gp gen a ()).run sR =
        (pure (none, sR) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    rw [honestSendB_param_run_eq_when_pred_false (gen := gen) gp a sR h_predR]
    unfold oracleSendB
    rw [StateT.run_get_bind]
    simp [h_vR]
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := (none, sL)) (b := (none, sR)) h_runL h_runR ⟨rfl, hrel⟩

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Left/right inactive `challA` relational step. For `R sL sR` and
inactive left/right challenge predicates, the paired left/right `challA` calls
both return `none` and establish `pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_reductionChallA_pred_false_of_state_rel
    (mode : HonestChallengeMode)
    (gp : GameParams) (gen : G) (b : F) (gB gT gTH : G)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_predL : ((gp.challengedParty == CKAParty.A &&
          validStep sL.lastAction CKAAction.challA) &&
        isChallengeEpoch gp { sL with tA := sL.tA + 1 }) = false)
    (h_predR : ((validStep sR.lastAction CKAAction.challA &&
          (gp.challengedParty == CKAParty.A)) &&
        isChallengeEpoch gp { sR with tA := sR.tA + 1 }) = false)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionChallA (F := F) gp gB gT ()).run sL)
      ((honestChallA_param_mode (F := F) mode gp gen b gTH ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_runL :
      (reductionChallA (F := F) gp gB gT ()).run sL =
        (pure (none, sL) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    unfold reductionChallA
    rw [StateT.run_get_bind]
    by_cases h_guard :
        (gp.challengedParty == CKAParty.A &&
          validStep sL.lastAction CKAAction.challA) = true
    · have h_epochL :
          isChallengeEpoch gp { sL with tA := sL.tA + 1 } = false := by
        simpa [h_guard] using h_predL
      simp [h_guard, h_epochL]
    · have h_guardL :
        (gp.challengedParty == CKAParty.A &&
          validStep sL.lastAction CKAAction.challA) = false :=
        Bool.eq_false_iff.mpr h_guard
      simp [h_guardL]
  have h_runR :
      (honestChallA_param_mode (F := F) mode gp gen b gTH ()).run sR =
        (pure (none, sR) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    have h_param_false :
        ¬ (((validStep sR.lastAction CKAAction.challA &&
              (gp.challengedParty == CKAParty.A)) &&
            isChallengeEpoch gp { sR with tA := sR.tA + 1 }) = true) := by
      simp [h_predR]
    unfold honestChallA_param_mode
    rw [StateT.run_get_bind]
    rw [if_neg h_param_false]
    unfold oracleChallA
    rw [StateT.run_get_bind]
    by_cases h_valid : validStep sR.lastAction CKAAction.challA = true
    · have h_tail :
          ((gp.challengedParty == CKAParty.A) &&
            isChallengeEpoch gp { sR with tA := sR.tA + 1 }) = false := by
        simpa [h_valid] using h_predR
      have h_tail_not :
          ¬ (((gp.challengedParty == CKAParty.A) &&
            isChallengeEpoch gp { sR with tA := sR.tA + 1 }) = true) := by
        simp [h_tail]
      rw [if_pos h_valid]
      rw [if_neg h_tail_not]
      rfl
    · rw [if_neg h_valid]
      rfl
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := (none, sL)) (b := (none, sR)) h_runL h_runR ⟨rfl, hrel⟩

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Left/right inactive `challB` relational step. For `R sL sR` and
inactive left/right challenge predicates, the paired left/right `challB` calls
both return `none` and establish `pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_reductionChallB_pred_false_of_state_rel
    (mode : HonestChallengeMode)
    (gp : GameParams) (gen : G) (b : F) (gB gT gTH : G)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_predL : ((gp.challengedParty == CKAParty.B &&
          validStep sL.lastAction CKAAction.challB) &&
        isChallengeEpoch gp { sL with tB := sL.tB + 1 }) = false)
    (h_predR : ((validStep sR.lastAction CKAAction.challB &&
          (gp.challengedParty == CKAParty.B)) &&
        isChallengeEpoch gp { sR with tB := sR.tB + 1 }) = false)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionChallB (F := F) gp gB gT ()).run sL)
      ((honestChallB_param_mode (F := F) mode gp gen b gTH ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_runL :
      (reductionChallB (F := F) gp gB gT ()).run sL =
        (pure (none, sL) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    unfold reductionChallB
    rw [StateT.run_get_bind]
    by_cases h_guard :
        (gp.challengedParty == CKAParty.B &&
          validStep sL.lastAction CKAAction.challB) = true
    · have h_epochL :
          isChallengeEpoch gp { sL with tB := sL.tB + 1 } = false := by
        simpa [h_guard] using h_predL
      simp [h_guard, h_epochL]
    · have h_guardL :
        (gp.challengedParty == CKAParty.B &&
          validStep sL.lastAction CKAAction.challB) = false :=
        Bool.eq_false_iff.mpr h_guard
      simp [h_guardL]
  have h_runR :
      (honestChallB_param_mode (F := F) mode gp gen b gTH ()).run sR =
        (pure (none, sR) : ProbComp (Option (G × G) × GameState (CKAState F G) G G)) := by
    have h_param_false :
        ¬ (((validStep sR.lastAction CKAAction.challB &&
              (gp.challengedParty == CKAParty.B)) &&
            isChallengeEpoch gp { sR with tB := sR.tB + 1 }) = true) := by
      simp [h_predR]
    unfold honestChallB_param_mode
    rw [StateT.run_get_bind]
    rw [if_neg h_param_false]
    unfold oracleChallB
    rw [StateT.run_get_bind]
    by_cases h_valid : validStep sR.lastAction CKAAction.challB = true
    · have h_tail :
          ((gp.challengedParty == CKAParty.B) &&
            isChallengeEpoch gp { sR with tB := sR.tB + 1 }) = false := by
        simpa [h_valid] using h_predR
      have h_tail_not :
          ¬ (((gp.challengedParty == CKAParty.B) &&
            isChallengeEpoch gp { sR with tB := sR.tB + 1 }) = true) := by
        simp [h_tail]
      rw [if_pos h_valid]
      rw [if_neg h_tail_not]
      rfl
    · rw [if_neg h_valid]
      rfl
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := (none, sL)) (b := (none, sR)) h_runL h_runR ⟨rfl, hrel⟩

omit [DecidableEq G] [Inhabited F] [Fintype G] in
/-- Left/right disabled-action `sendA_rleak` relational step. For
`R sL sR`, equal last actions, and a disabled `sendA` transition at `sL`, the
paired leak-oracle calls both return `none` and establish
`pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_oracleSendA_rleak_invalid_of_state_rel
    (gp : GameParams) (gen : G)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_last : sL.lastAction = sR.lastAction)
    (h_v : ¬ validStep sL.lastAction CKAAction.sendA = true)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleSendA_rleak gp (ddhCKA F G gen) ()).run sL)
      ((oracleSendA_rleak gp (ddhCKA F G gen) ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_vL : validStep sL.lastAction CKAAction.sendA = false :=
    Bool.eq_false_iff.mpr h_v
  have h_vR : validStep sR.lastAction CKAAction.sendA = false := by
    rw [← h_last]
    exact h_vL
  have h_runL :
      (oracleSendA_rleak gp (ddhCKA F G gen) ()).run sL =
        (pure (none, sL) :
          ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
    unfold oracleSendA_rleak
    rw [StateT.run_get_bind]
    simp [h_vL]
  have h_runR :
      (oracleSendA_rleak gp (ddhCKA F G gen) ()).run sR =
        (pure (none, sR) :
          ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
    unfold oracleSendA_rleak
    rw [StateT.run_get_bind]
    simp [h_vR]
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := (none, sL)) (b := (none, sR)) h_runL h_runR ⟨rfl, hrel⟩

omit [DecidableEq G] [Inhabited F] [Fintype G] in
/-- Left/right disabled-action `sendB_rleak` relational step. For
`R sL sR`, equal last actions, and a disabled `sendB` transition at `sL`, the
paired leak-oracle calls both return `none` and establish
`pL.1 = pR.1 ∧ R pL.2 pR.2`. -/
lemma relTriple_oracleSendB_rleak_invalid_of_state_rel
    (gp : GameParams) (gen : G)
    (R : GameState (CKAState F G) G G → GameState (CKAState F G) G G → Prop)
    (sL sR : GameState (CKAState F G) G G)
    (h_last : sL.lastAction = sR.lastAction)
    (h_v : ¬ validStep sL.lastAction CKAAction.sendB = true)
    (hrel : R sL sR) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleSendB_rleak gp (ddhCKA F G gen) ()).run sL)
      ((oracleSendB_rleak gp (ddhCKA F G gen) ()).run sR)
      (fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2) := by
  have h_vL : validStep sL.lastAction CKAAction.sendB = false :=
    Bool.eq_false_iff.mpr h_v
  have h_vR : validStep sR.lastAction CKAAction.sendB = false := by
    rw [← h_last]
    exact h_vL
  have h_runL :
      (oracleSendB_rleak gp (ddhCKA F G gen) ()).run sL =
        (pure (none, sL) :
          ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
    unfold oracleSendB_rleak
    rw [StateT.run_get_bind]
    simp [h_vL]
  have h_runR :
      (oracleSendB_rleak gp (ddhCKA F G gen) ()).run sR =
        (pure (none, sR) :
          ProbComp (Option (G × G × F) × GameState (CKAState F G) G G)) := by
    unfold oracleSendB_rleak
    rw [StateT.run_get_bind]
    simp [h_vR]
  refine relTriple_of_eq_pure_pure
    (R := fun pL pR => pL.1 = pR.1 ∧ R pL.2 pR.2)
    (a := (none, sL)) (b := (none, sR)) h_runL h_runR ⟨rfl, hrel⟩

end Step2

end ddhCKA
