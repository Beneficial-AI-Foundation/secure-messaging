/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
/-- General-case rand-branch per-fixed-`x₀` claim. With `a, b, c ← $ᵗ F`,
the reduction output from `(.sendReady (x₀•gen), .recvReady x₀)` matches the `true`-branch
honest output from the same initial state. Couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
lemma probOutput_general_per_x₀_rand
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
  (h_general_case : ¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (CKAState F G) G G F) (x₀ : F) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] =
    Pr[= false |
      (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  let s₀R : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)
  let s₀H : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)
  calc
    Pr[= false | do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
          s₀R]
      = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) gT) adversary).run'
            s₀R] := by
              refine probOutput_bind_congr' _ false fun a => ?_
              refine probOutput_bind_congr' _ false fun b => ?_
              exact probOutput_reduction_rand_sample_gT (gen := gen) hg
                (m := fun gT =>
                  (simulateQ
                      (reductionOracleImpl gp gen (a • gen) (b • gen) gT) adversary).run'
                    s₀R)
                false
    _ = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s₀H] := by
              -- Per-fixed-(a, b, gT) state-relation bridge: reduction → honest_param_rand.
              refine probOutput_bind_congr' _ false fun a => ?_
              refine probOutput_bind_congr' _ false fun b => ?_
              refine probOutput_bind_congr' _ false fun gT => ?_
              exact probOutput_eq_of_evalDist_eq
                (evalDist_reduction_honest_param_rand_eq
                  (gen := gen) gp hΔFS hΔPCS h_general_case x₀ a b gT adversary)
                false
    _ = Pr[= false |
          (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run' s₀H] := by
          -- Rand game-oracle bridge: honest_param_rand outer samples to eager random CKA.
              exact probOutput_eq_of_evalDist_eq
                (evalDist_eager_honest_rand_eq (gen := gen) gp s₀H adversary)
                false

omit [Inhabited F] [Fintype G] in
/-- General-case (`¬ (challengeEpoch = 1 ∧ challengedParty = A)`) rand-branch game-level bridge.
Analogue of `probOutput_general_pointwise` with the extra `c ← $ᵗ F`
sampled internally; challenge couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
lemma probOutput_general_pointwise_rand
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (h_general_case : ¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  -- 4-way swap: move x₀ past c, then past b, then past a.
  calc Pr[= false | do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        let x₀ ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
          (initGameState
            (CKAState.sendReady (x₀ • gen) : CKAState F G)
            (CKAState.recvReady x₀ : CKAState F G))]
      _ = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G))] := by
        refine probOutput_bind_congr' _ false fun a => ?_2
        refine probOutput_bind_congr' _ false fun b => ?_
        exact probOutput_bind_bind_swap _ _ _ _
      _ = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G))] := by
        refine probOutput_bind_congr' _ false fun a => ?_
        exact probOutput_bind_bind_swap _ _ _ _
      _ = Pr[= false | do
          let x₀ ← ($ᵗ F : ProbComp F)
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G))] :=
          probOutput_bind_bind_swap _ _ _ _
      _ = _ := by
        refine probOutput_bind_congr' _ false fun x₀ => ?_
        exact probOutput_general_per_x₀_rand gp hΔFS hΔPCS hg h_general_case adversary x₀

omit [Inhabited F] [Fintype G] in
/-- Special-case fixed-parameter rand bridge.

When `challengeEpoch = 1` and `challengedParty = A`, the reduction starts with
B's scalar cell dead (`.recvReady 0`) while the honest stack starts with the
cached scalar `x₀`. For fixed `x₀`, `b`, and external key `gT`, the relation
`reductionHonestRel_rand` shows that the two stacks have the same output
distribution. -/
lemma evalDist_reduction_honest_param_rand_special_eq
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (x₀ b : F) (gT : G)
    (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool) :
    evalDist ((simulateQ
        (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        ((CKAState.recvReady 0) : CKAState F G))) =
    evalDist ((simulateQ (honestImpl_param_rand gp gen x₀ b gT) adversary).run'
      (initGameState
        (CKAState.sendReady (x₀ • gen) : CKAState F G)
        (CKAState.recvReady x₀ : CKAState F G))) := by
  apply OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run'_eq_of_state_rel
    (R := reductionHonestRel_rand gp gen x₀ b gT)
  · intro t sR sH hrel
    exact reduction_honest_param_rand_step_rel
      (gen := gen) gp hΔFS hΔPCS x₀ b gT t sR sH hrel
  · rcases h_special_case with ⟨h_challengeEpoch, h_cp⟩
    simp [reductionHonestRel_rand, initGameState, reachableShape, epochCounterInv,
      stateShapeInv, allowCorrPCS, allowCorrFS, h_challengeEpoch, h_cp,
      hΔFS, hΔPCS]

omit [Inhabited F] [Fintype G] in
/-- Special-case honest rand bridge with the embedding scalar fixed.

When `challengeEpoch = 1` and `challengedParty = A`, the parameterized honest
random game with `a = x₀` fixed, `b ← $ᵗ F` sampled, and `gT ← $ᵗ G` sampled has
the same output distribution as the ordinary random CKA game from the same
state. -/
lemma evalDist_special_honest_fixed_a_rand_eq_eager
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (x₀ : F)
    (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
    (s : GameState (CKAState F G) G G) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let gT ← ($ᵗ G : ProbComp G)
      (simulateQ (honestImpl_param_rand gp gen x₀ b gT) adversary).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run' s) := by
  have h_fixed_vs_a : ∀ b gT a,
      evalDist ((simulateQ (honestImpl_param_rand gp gen x₀ b gT) adversary).run' s) =
      evalDist ((simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s) := by
    intro b gT a
    exact evalDist_simulateQ_run'_eq_of_impl_evalDist_eq
      (impl₁ := honestImpl_param_rand gp gen x₀ b gT)
      (impl₂ := honestImpl_param_rand gp gen a b gT)
      (oa := adversary)
      (himpl := fun t s' => by
        exact congrArg evalDist
          (honestImpl_param_rand_a_indep_special (gen := gen)
            gp h_special_case b gT t s' x₀ a))
      s s rfl
  have h_bind_fixed : ∀ b gT,
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s) =
      evalDist ((simulateQ (honestImpl_param_rand gp gen x₀ b gT) adversary).run' s) := by
    intro b gT
    exact evalDist_sample_bind_eq_of_forall_evalDist_eq
      (f := fun a => (simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s)
      (p := (simulateQ (honestImpl_param_rand gp gen x₀ b gT) adversary).run' s)
      (fun a => (h_fixed_vs_a b gT a).symm)
  apply evalDist_ext
  intro y
  calc
    Pr[= y | do
        let b ← ($ᵗ F : ProbComp F)
        let gT ← ($ᵗ G : ProbComp G)
        (simulateQ (honestImpl_param_rand gp gen x₀ b gT) adversary).run' s]
      = Pr[= y | do
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          let a ← ($ᵗ F : ProbComp F)
          (simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s] := by
          refine probOutput_bind_congr' _ y fun b => ?_
          refine probOutput_bind_congr' _ y fun gT => ?_
          exact probOutput_eq_of_evalDist_eq (h_bind_fixed b gT).symm y
    _ = Pr[= y | do
          let b ← ($ᵗ F : ProbComp F)
          let a ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s] := by
          refine probOutput_bind_congr' _ y fun b => ?_
          exact probOutput_bind_bind_swap _ _ _ _
    _ = Pr[= y | do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ (honestImpl_param_rand gp gen a b gT) adversary).run' s] := by
          exact probOutput_bind_bind_swap _ _ _ _
    _ = Pr[= y | (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run' s] := by
          exact probOutput_eq_of_evalDist_eq
            (evalDist_eager_honest_rand_eq (gen := gen) gp s adversary)
            y

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
    Pr[= false | do
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (x₀ • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          ((CKAState.recvReady 0) : CKAState F G))] =
    Pr[= false |
      (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  let s₀R : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      ((CKAState.recvReady 0) : CKAState F G)
  let s₀H : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)
  calc
    Pr[= false | do
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (x₀ • gen) (b • gen) (c • gen)) adversary).run'
          s₀R]
      = Pr[= false | do
          let b ← ($ᵗ F : ProbComp F)
          let gT ← ($ᵗ G : ProbComp G)
          (simulateQ
              (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
            s₀R] := by
              refine probOutput_bind_congr' _ false fun b => ?_
              exact probOutput_reduction_rand_sample_gT (gen := gen) hg
                (m := fun gT =>
                  (simulateQ
                      (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
                    s₀R)
                false
    _ = Pr[= false |
          (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run' s₀H] := by
            calc
              Pr[= false | do
                  let b ← ($ᵗ F : ProbComp F)
                  let gT ← ($ᵗ G : ProbComp G)
                  (simulateQ
                      (reductionOracleImpl gp gen (x₀ • gen) (b • gen) gT) adversary).run'
                    s₀R]
                = Pr[= false | do
                    let b ← ($ᵗ F : ProbComp F)
                    let gT ← ($ᵗ G : ProbComp G)
                    (simulateQ (honestImpl_param_rand gp gen x₀ b gT) adversary).run'
                      s₀H] := by
                    refine probOutput_bind_congr' _ false fun b => ?_
                    refine probOutput_bind_congr' _ false fun gT => ?_
                    exact probOutput_eq_of_evalDist_eq
                      (evalDist_reduction_honest_param_rand_special_eq
                        (gen := gen) gp hΔFS hΔPCS h_special_case x₀ b gT adversary)
                      false
              _ = Pr[= false |
                    (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
                      s₀H] := by
                    exact probOutput_eq_of_evalDist_eq
                      (evalDist_special_honest_fixed_a_rand_eq_eager
                        (gen := gen) gp h_special_case x₀ adversary s₀H)
                      false

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
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (a • gen) : CKAState F G)
          ((CKAState.recvReady 0) : CKAState F G))] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  refine probOutput_bind_congr' _ false fun x₀ => ?_
  exact probOutput_special_per_x₀_rand gp hΔFS hΔPCS hg h_special_case adversary x₀

omit [Inhabited F] [Fintype G] in
/-- **Step (2) of the random branch.** Game-level bridge:
`Pr[= false | securityReductionRandGame] = Pr[= false | CKA^{isRandom = true}]`.
Parallel to `probOutput_securityReductionRealGame_eq_honestFalse`. -/
lemma probOutput_securityReductionRandGame_eq_honestTrue
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= false | securityReductionRandGame (gen := gen) gp adversary] =
    Pr[= false | securityExpRandGame (gen := gen) gp adversary] := by
  unfold securityReductionRandGame securityExpRandGame
  by_cases h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A
  · simp only [reductionInitState, if_pos h_special_case, pure_bind]
    exact probOutput_special_pointwise_rand (gen := gen) gp hΔFS hΔPCS hg h_special_case adversary
  · simp only [reductionInitState, if_neg h_special_case, bind_assoc, pure_bind]
    exact probOutput_general_pointwise_rand (gen := gen) gp hΔFS hΔPCS hg h_special_case adversary



end Step2

end ddhCKA
