/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromDDH.Security.ReductionRand.EagerHonestBridge

/-!
# CKA from DDH — Reduction (rand) — Endpoint Bridge

This file proves that `securityReductionRandGame` and `securityExpRandGame`
with `isRandom = true` have the same probability of returning `false`.

The reduction samples a scalar `c` and uses `c • gen` as the challenge key. The
bijection hypothesis `hg` replaces this with a direct group sample `gT`. The
proof then compares the reduction game with the parameterized honest random
game, and compares that game with the ordinary random CKA game.

There are two cases for the initial state. In the general case, both games start
from `(.sendReady (x₀ • gen), .recvReady x₀)`. In the initial-challenge case,
`gp.challengeEpoch = 1 ∧ gp.challengedParty = .A`, the reduction starts from
`(.sendReady (a • gen), .recvReady 0)` and the ordinary CKA game starts from
`(.sendReady (x₀ • gen), .recvReady x₀)`.

The final lemma is `probOutput_securityReductionRandGame_eq_honestTrue`.
-/

open ToVCVio OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

namespace ddhCKA

open DDH

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme DiffieHellman ckaSecuritySpec

variable [DecidableEq G]

section Step2
variable [Inhabited F]
variable [Fintype G]

omit [Inhabited F] [Fintype G] in
/-- General-case rand-branch per-fixed-`x₀` claim. With `a, b, c ← $ᵗ F`,
the reduction output from `(.sendReady (x₀•gen), .recvReady x₀)` matches the `true`-branch
honest output from the same initial state. Couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
lemma probOutput_general_per_x₀_rand
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
  (h_general_case : ¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (CKAState F G) G G F) (x₀ : F) :
    Pr{let x ← (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G)))}[x = false] =
    Pr{let x ← ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G)))}[x = false] := by
  let s₀R : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)
  let s₀H : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)
  calc
    Pr{let x ← (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
          s₀R)}[x = false]
      = Pr{let x ← (do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) gT) adversary).run'
            s₀R)}[x = false] := by
              refine prEvent_bind_congr _ _ _ _ _ fun a => ?_
              refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
              have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective hg).bind_left
                fun gT =>
                  (simulateQ
                      (reductionOracleImpl gp gen (a • gen) (b • gen) gT) adversary).run'
                    s₀R
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply] at h
              exact h.prEvent_eq _
    _ = Pr{let x ← (do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ (honestImplParamRand gp gen a b gT) adversary).run' s₀H)}[x = false] := by
              -- Per-fixed-(a, b, gT) state-relation bridge: reduction → honest_param_rand.
              refine prEvent_bind_congr _ _ _ _ _ fun a => ?_
              refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
              refine prEvent_bind_congr _ _ _ _ _ fun gT => ?_
              exact (evalDistEq_reduction_honest_param_rand
                (gen := gen) gp hΔFS hΔPCS h_general_case x₀ a b gT adversary).prEvent_eq _
    _ = Pr{let x ← ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
          s₀H)}[x = false] := by
          -- Rand game-oracle bridge: honest_param_rand outer samples to eager random CKA.
              exact (evalDistEq_eager_honest_rand (gen := gen) gp s₀H adversary).prEvent_eq _

omit [Inhabited F] [Fintype G] in
/-- General-case (`¬ (challengeEpoch = 1 ∧ challengedParty = A)`) rand-branch game-level bridge.
Analogue of `probOutput_general_pointwise` with the extra `c ← $ᵗ F`
sampled internally; challenge couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
lemma probOutput_general_pointwise_rand
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (h_general_case : ¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr{let x ← (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G)))}[x = false] =
    Pr{let x ← (do
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G)))}[x = false] := by
  -- 4-way swap: move x₀ past c, then past b, then past a.
  calc Pr{let x ← (do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        let x₀ ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
          (initGameState
            (CKAState.sendReady (x₀ • gen) : CKAState F G)
            (CKAState.recvReady x₀ : CKAState F G)))}[x = false]
      _ = Pr{let x ← (do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G)))}[x = false] := by
        refine prEvent_bind_congr _ _ _ _ _ fun a => ?_
        refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
        exact (EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _
      _ = Pr{let x ← (do
          let a ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G)))}[x = false] := by
        refine prEvent_bind_congr _ _ _ _ _ fun a => ?_
        exact (EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _
      _ = Pr{let x ← (do
          let x₀ ← ($ᵗ F : ProbComp F)
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G)))}[x = false] :=
          (EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _
      _ = _ := by
        refine prEvent_bind_congr _ _ _ _ _ fun x₀ => ?_
        exact probOutput_general_per_x₀_rand gp hΔFS hΔPCS hg h_general_case adversary x₀

omit [Inhabited F] [Fintype G] in
/-- Special-case fixed-parameter rand bridge.

When `challengeEpoch = 1` and `challengedParty = A`, the reduction starts with
B's scalar cell dead (`.recvReady 0`) while the honest stack starts with the
cached scalar `x₀`. For fixed `x₀`, `b`, and external key `gT`, the relation
`reductionHonestRelRand` shows that the two stacks have the same output
distribution. -/
lemma evalDistEq_reduction_honest_param_rand_special
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (x₀ b : F) (gT : G)
    (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool) :
    ((simulateQ
        (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        ((CKAState.recvReady 0) : CKAState F G))) =ᵈ
    ((simulateQ (honestImplParamRand gp gen x₀ b gT) adversary).run'
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        (CKAState.recvReady x₀ : CKAState F G))) := by
  refine OracleComp.ProgramLogic.Relational.evalDistEq_of_relTriple_eqRel
    (OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run' _ _
      (reductionHonestRelRand gp gen x₀ b gT) _ ?_ _ _ ?_)
  · intro t sR sH hrel
    exact reduction_honest_param_rand_step_rel
      (gen := gen) gp hΔFS hΔPCS x₀ b gT t sR sH hrel
  · rcases h_special_case with ⟨h_challengeEpoch, h_cp⟩
    simp [reductionHonestRelRand, initGameState, reachableShape, epochCounterInv,
      stateShapeInv, allowCorrPCS, allowCorrFS, h_challengeEpoch, h_cp,
      hΔFS, hΔPCS]

omit [Inhabited F] [Fintype G] in
/-- Special-case honest rand bridge with the embedding scalar fixed.

When `challengeEpoch = 1` and `challengedParty = A`, the parameterized honest
random game with `a = x₀` fixed, `b ← $ᵗ F` sampled, and `gT ← $ᵗ G` sampled is
equal in distribution to the ordinary random CKA game from the same state. -/
lemma evalDistEq_special_honest_fixed_a_rand_eager
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (x₀ : F)
    (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) :
    (do
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImplParamRand gp gen x₀ b gT) adversary).run' s) =ᵈ
    ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run' s) := by
  have h_bind_fixed : ∀ b gT,
      (do
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImplParamRand gp gen a b gT) adversary).run' s) =ᵈ
      ((simulateQ (honestImplParamRand gp gen x₀ b gT) adversary).run' s) :=
    fun b gT => evalDistEq_sample_simulateQ_run'_of_param_indep
      (fun a => honestImplParamRand gp gen a b gT) adversary s x₀ fun a t s' => by
        rw [honestImpl_param_rand_a_indep_special (gen := gen) gp h_special_case b gT t s' a x₀]
  -- Insert the dead `a` sample, then move it in front of `b` and `gT`.
  exact (EvalDistEq.bind_right _ fun b => EvalDistEq.bind_right _ fun gT =>
      (h_bind_fixed b gT).symm).trans <|
    (EvalDistEq.bind_right _ fun b => EvalDistEq.bind_bind_swap _ _ _).trans <|
    (EvalDistEq.bind_bind_swap _ _ _).trans
      (evalDistEq_eager_honest_rand (gen := gen) gp s adversary)

omit [Inhabited F] [Fintype G] in
/-- Special-case rand-branch per-fixed-`x₀` claim: after renaming `a ↔ x₀`,
reduction's init `(.sendReady (x₀•gen), .recvReady 0)` with remaining `b, c ← $ᵗ F`
matches the `true`-branch honest init `(.sendReady (x₀•gen), .recvReady x₀)`. Couples
`c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
lemma probOutput_special_per_x₀_rand
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (CKAState F G) G G F) (x₀ : F) :
    Pr{let x ← (do
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (x₀ • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          ((CKAState.recvReady 0) : CKAState F G)))}[x = false] =
    Pr{let x ← ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G)))}[x = false] := by
  let s₀R : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      ((CKAState.recvReady 0) : CKAState F G)
  let s₀H : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)
  calc
    Pr{let x ← (do
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (x₀ • gen) (b • gen) (c • gen)) adversary).run'
          s₀R)}[x = false]
      = Pr{let x ← (do
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ
              (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
            s₀R)}[x = false] := by
              refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
              have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective hg).bind_left
                fun gT =>
                  (simulateQ
                      (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
                    s₀R
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply] at h
              exact h.prEvent_eq _
    _ = Pr{let x ← ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
          s₀H)}[x = false] := by
            calc
              Pr{let x ← (do
                  let b ← ($ᵗ F : ProbComp F)
                  let gT ← ($ᵗ G : ProbComp G)
                  (simulateQ
                      (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
                    s₀R)}[x = false]
                = Pr{let x ← (do
                    let b ← ($ᵗ F : ProbComp F)
                    let gT ← ($ᵗ G : ProbComp G)
                    (simulateQ (honestImplParamRand gp gen x₀ b gT) adversary).run'
                      s₀H)}[x = false] := by
                    refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
                    refine prEvent_bind_congr _ _ _ _ _ fun gT => ?_
                    exact (evalDistEq_reduction_honest_param_rand_special
                      (gen := gen) gp hΔFS hΔPCS h_special_case x₀ b gT adversary).prEvent_eq _
              _ = Pr{let x ← ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
                      s₀H)}[x = false] := by
                    exact (evalDistEq_special_honest_fixed_a_rand_eager
                      (gen := gen) gp h_special_case x₀ adversary s₀H).prEvent_eq _

omit [Inhabited F] [Fintype G] in
/-- Special-case (`gp = ⟨1, _, _, .A⟩`) rand-branch bridge. Analogue of
`probOutput_special_pointwise`; reduction's init is `(.sendReady (a•gen), .recvReady 0)`
with `c` replacing `a*b` in `gT`; rename `a ↔ x₀`, couple
`c•gen ↔ outKey ← $ᵗ G` via `hg` at the challenge. -/
lemma probOutput_special_pointwise_rand
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr{let x ← (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (a • gen) : CKAState F G)
          ((CKAState.recvReady 0) : CKAState F G)))}[x = false] =
    Pr{let x ← (do
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G)))}[x = false] := by
  refine prEvent_bind_congr _ _ _ _ _ fun x₀ => ?_
  exact probOutput_special_per_x₀_rand gp hΔFS hΔPCS hg h_special_case adversary x₀

omit [Inhabited F] [Fintype G] in
/-- **Step (2) of the random branch.** Game-level bridge:
`Pr{let x ← securityReductionRandGame}[x = false] = Pr{let x ← CKA^{isRandom = true}}[x = false]`.
Parallel to `probOutput_securityReductionRealGame_eq_honestFalse`. -/
lemma probOutput_securityReductionRandGame_eq_honestTrue
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr{let x ← securityReductionRandGame (gen := gen) gp adversary}[x = false] =
    Pr{let x ← securityExpRandGame (gen := gen) gp adversary}[x = false] := by
  unfold securityReductionRandGame securityExpRandGame
  by_cases h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A
  · simp only [reductionInitState, ite_eq_left h_special_case, pure_bind]
    exact probOutput_special_pointwise_rand (gen := gen) gp hΔFS hΔPCS hg h_special_case adversary
  · simp only [reductionInitState, ite_eq_right h_special_case, bind_assoc, pure_bind]
    exact probOutput_general_pointwise_rand (gen := gen) gp hΔFS hΔPCS hg h_special_case adversary



end Step2

end ddhCKA
