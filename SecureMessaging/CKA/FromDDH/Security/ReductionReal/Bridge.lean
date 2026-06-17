/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.ReductionReal.RelStep

/-!
# CKA from DDH — Reduction (real) — Endpoint Bridge

This file proves that `securityReductionRealGame` and `securityExpRealGame`
with `isRandom = false` have the same probability of returning `false`.

The proof first compares the reduction game with the parameterized honest real
game, then compares the parameterized honest real game with the ordinary real
CKA game.

There are two cases for the initial state. In the general case, both games start
from `(.sendReady (x₀ • gen), .recvReady x₀)`. In the initial-challenge case,
`gp.challengeEpoch = 1 ∧ gp.challengedParty = .A`, the reduction starts from
`(.sendReady (a • gen), .recvReady 0)` and the ordinary CKA game starts from
`(.sendReady (x₀ • gen), .recvReady x₀)`.

The final lemma is `probOutput_securityReductionRealGame_eq_honestFalse`.
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
/-- Special-case honest bridge with the embedding scalar fixed.

When `challengeEpoch = 1` and `challengedParty = A`, the parameterized honest
real game with `a = x₀` fixed and `b ← $ᵗ F` sampled has the same output
distribution as the ordinary real CKA game from the same state. -/
lemma evalDist_special_honest_fixed_a_eq_eager
    (gp : GameParams) (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (x₀ : F)
  (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool)
  (s : GameState (CKAState F G) G G) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen x₀ b) adversary).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run' s) := by
  have h_fixed_vs_a : ∀ b a,
      evalDist ((simulateQ (honestImpl_param_real gp gen x₀ b) adversary).run' s) =
      evalDist ((simulateQ (honestImpl_param_real gp gen a b) adversary).run' s) := by
    intro b a
    exact evalDist_simulateQ_run'_eq_of_impl_evalDist_eq
      (impl₁ := honestImpl_param_real gp gen x₀ b)
      (impl₂ := honestImpl_param_real gp gen a b)
      (oa := adversary)
      (himpl := fun t s' => by
        exact congrArg evalDist
          (honestImpl_param_real_a_indep_special (gen := gen)
            gp h_special_case b t s' x₀ a))
      s s rfl
  have h_bind_fixed : ∀ b,
      evalDist (do
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen a b) adversary).run' s) =
      evalDist ((simulateQ (honestImpl_param_real gp gen x₀ b) adversary).run' s) := by
    intro b
    exact evalDist_sample_bind_eq_of_forall_evalDist_eq
      (f := fun a => (simulateQ (honestImpl_param_real gp gen a b) adversary).run' s)
      (p := (simulateQ (honestImpl_param_real gp gen x₀ b) adversary).run' s)
      (fun a => (h_fixed_vs_a b a).symm)
  calc
    evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_param_real gp gen x₀ b) adversary).run' s)
      =
        evalDist (do
          let b ← ($ᵗ F : ProbComp F)
          let a ← ($ᵗ F : ProbComp F)
          (simulateQ (honestImpl_param_real gp gen a b) adversary).run' s) := by
          exact evalDist_sample_bind_congr_of_forall_evalDist_eq
            (f := fun b => (simulateQ (honestImpl_param_real gp gen x₀ b) adversary).run' s)
            (g := fun b => do
              let a ← ($ᵗ F : ProbComp F)
              (simulateQ (honestImpl_param_real gp gen a b) adversary).run' s)
            (fun b => (h_bind_fixed b).symm)
    _ =
        evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run' s) := by
          exact evalDist_eager_honest_lazy_eq (gen := gen) gp s adversary

omit [Inhabited F] [Fintype G] in
/-- General-case real-branch endpoint for a fixed initial secret `x₀`.

Assuming `¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)`, the reduction
game with real DDH key `(a * b) • gen` has the same `false` output probability
as the regular false-branch CKA game from the same initial state. -/
lemma probOutput_general_per_x₀
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
  (h_general_case : ¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (CKAState F G) G G F) (x₀ : F) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] =
    Pr[= false |
      (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  exact probOutput_eq_of_evalDist_eq
    (evalDist_eager_reduction_lazy_eq
      (gen := gen) gp hΔFS hΔPCS h_general_case x₀ adversary)
    false

omit [Inhabited F] [Fintype G] in
/-- General-case (`¬ (challengeEpoch = 1 ∧ challengedParty = A)`) game-level bridge.

Stated with `x₀ ← $ᵗ F` sampled *inside* on both sides (matching the shape
Step (2)'s dispatch produces in the non-initial-challenge case). -/
lemma probOutput_general_pointwise
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
  (h_general_case : ¬ (gp.challengeEpoch = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  -- Move x₀ outermost on LHS: first swap (b, x₀) under the outer a, then
  -- swap (a, x₀) at the top. Then apply the per-fixed-x₀ claim.
  calc Pr[= false | do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let x₀ ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run'
          (initGameState
            (CKAState.sendReady (x₀ • gen) : CKAState F G)
            (CKAState.recvReady x₀ : CKAState F G))]
      _ = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen))
              adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G))] := by
        refine probOutput_bind_congr' _ false fun a => ?_
        exact probOutput_bind_bind_swap _ _ _ _
      _ = Pr[= false | do
          let x₀ ← ($ᵗ F : ProbComp F)
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run'
            (initGameState
              (CKAState.sendReady (x₀ • gen) : CKAState F G)
              (CKAState.recvReady x₀ : CKAState F G))] :=
          probOutput_bind_bind_swap _ _ _ _
      _ = _ := by
        refine probOutput_bind_congr' _ false fun x₀ => ?_
        exact probOutput_general_per_x₀ gp hΔFS hΔPCS h_general_case adversary x₀

omit [Inhabited F] [Fintype G] in
/-- Special-case per-fixed-`x₀` claim: with the rename `a ↔ x₀`, reduction's
init `(.sendReady (x₀•gen), .recvReady 0)` (stB dead) and honest's
`(.sendReady (x₀•gen), .recvReady x₀)`
produce the same output distribution after the remaining `b ← $ᵗ F` peel. -/
lemma probOutput_special_per_x₀
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (CKAState F G) G G F) (x₀ : F) :
    Pr[= false | do
      let b ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (x₀ • gen) (b • gen) ((x₀ * b) • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          ((.recvReady 0) : CKAState F G))] =
    Pr[= false |
      (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  let s₀R : GameState (CKAState F G) G G :=
    initGameState (CKAState.sendReady (x₀ • gen) : CKAState F G) ((.recvReady 0) : CKAState F G)
  let s₀H : GameState (CKAState F G) G G :=
    initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)
  calc
    Pr[= false | do
        let b ← ($ᵗ F : ProbComp F)
        (simulateQ
            (reductionOracleImpl gp gen (x₀ • gen) (b • gen) ((x₀ * b) • gen)) adversary).run'
          s₀R]
      = Pr[= false | do
          let b ← ($ᵗ F : ProbComp F)
          (simulateQ (honestImpl_param_real gp gen x₀ b) adversary).run' s₀H] := by
            refine probOutput_bind_congr' _ false fun b => ?_
            exact probOutput_eq_of_evalDist_eq
              (OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run'_eq_of_state_rel
                (impl₁ := reductionOracleImpl gp gen (x₀ • gen) (b • gen) ((x₀ * b) • gen))
                (impl₂ := honestImpl_param_real gp gen x₀ b)
                (R := reductionHonestRel gp gen x₀ b)
                (oa := adversary)
                (s₁ := s₀R) (s₂ := s₀H)
                (by
                  intro t sR sH hrel
                  exact reduction_honest_param_real_step_rel
                    (gen := gen) gp hΔFS hΔPCS x₀ b t sR sH hrel)
                (by
                  rcases h_special_case with ⟨h_challengeEpoch, h_cp⟩
                  simp [reductionHonestRel, s₀R, s₀H, initGameState, reachableShape,
                    epochCounterInv, stateShapeInv, allowCorrPCS, allowCorrFS,
                    h_challengeEpoch, h_cp, hΔFS, hΔPCS]))
              false
    _ = Pr[= false |
          (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run' s₀H] := by
            exact probOutput_eq_of_evalDist_eq
              (evalDist_special_honest_fixed_a_eq_eager (gen := gen)
                gp h_special_case x₀ adversary s₀H)
              false

omit [Inhabited F] [Fintype G] in
/-- Special-case (`gp = ⟨1, _, _, .A⟩`) bridge: reduction init `(.sendReady (a•gen), .recvReady 0)`
with outer `a ←$ F` equals honest init `(.sendReady (x₀•gen), .recvReady x₀)` with
outer `x₀ ←$ F` (renaming `a ↔ x₀`), averaged over the remaining `b ←$ F`. -/
lemma probOutput_special_pointwise
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (a • gen) : CKAState F G)
          ((.recvReady 0) : CKAState F G))] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run'
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))] := by
  refine probOutput_bind_congr' _ false fun x₀ => ?_
  exact probOutput_special_per_x₀ gp hΔFS hΔPCS h_special_case adversary x₀

omit [Inhabited F] [Fintype G] in
/-- **Step (2) of the real branch.** Game-level bridge:
`Pr[= false | securityReductionRealGame] = Pr[= false | CKA^{isRandom = false}]`.

Unfolds both games, case-splits on `reductionInitState`'s `if`, and reduces
each branch to one of the named inner bridges above. -/
lemma probOutput_securityReductionRealGame_eq_honestFalse
  (gp : GameParams) (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] =
    Pr[= false | securityExpRealGame (gen := gen) gp adversary] := by
  unfold securityReductionRealGame securityExpRealGame
  by_cases h_special_case : gp.challengeEpoch = 1 ∧ gp.challengedParty = .A
  · -- Special: `reductionInitState` = `pure (init .sendReady gA .recvReady 0)` (no x₀ sample).
    simp only [reductionInitState, if_pos h_special_case, pure_bind]
    exact probOutput_special_pointwise (gen := gen) gp hΔFS hΔPCS h_special_case adversary
  · -- General: `reductionInitState` = `do x₀ ← $F; pure (init .sendReady (x₀•gen) .recvReady x₀)`.
    simp only [reductionInitState, if_neg h_special_case, bind_assoc, pure_bind]
    exact probOutput_general_pointwise (gen := gen) gp hΔFS hΔPCS h_special_case adversary



end Step2

end ddhCKA
