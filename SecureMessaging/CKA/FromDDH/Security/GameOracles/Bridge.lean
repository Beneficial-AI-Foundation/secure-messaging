/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.GameOracles.Step

/-!
# CKA from DDH — Game Oracles — Bridge

Distribution-level equivalence between two presentations of the honest CKA
game that differ only in where the two DDH-programmed scalars are sampled.

The regular CKA game samples them lazily, inside the oracle stack:

  `𝒟[simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) 𝒜]`.

The parameterized game samples them eagerly, before the adversary runs:

  `𝒟[do b a ← $ᵗ F; simulateQ (honestImpl_param_real gp gen a b) 𝒜]`.

Here `a` is the scalar consumed at the embedding epoch, and `b` is the scalar
consumed at the challenge epoch. The bridge proves that moving these samples
from the oracle body to the top-level `ProbComp` does not change the output
distribution.

The connection is made by the generic `consumeLazy` operator from
`ToVCVio.OracleComp.QueryTracking.LazySampling.lean`. Given:
* a family `implFam : τ → QueryImpl spec (StateT σ ProbComp)`, and
* a predicate `hit : spec.Domain → Bool` marking the oracle queries that
  actually consume the external parameter (here, queries that use the
  embedding/challenge scalar),

the call `consumeLazy implFam hit` produces a single oracle stack that defers
sampling the parameter `θ : τ` until it is first needed:

  eager: `do θ ←$ τ; simulateQ (implFam θ) 𝒜`
  lazy:  `simulateQ (consumeLazy implFam hit) 𝒜`.

At the first query `t` with `hit t = true`, the lazy stack samples `θ ←$ τ`
and caches it; later hits reuse the cache. At queries with `hit t = false`, it
runs `implFam` without sampling. The non-hit case is sound under the
parameter-independence hypothesis (the `hindep` lemmas), which says that
`implFam`'s output does not depend on `θ` at non-hit queries.

Main results in this file:

* `evalDist_eager_honest_lazy_eq` — the whole-adversary bridge: for every
  adversary `𝒜`,

      `𝒟[do b a ← $ᵗ F; simulateQ (honestImpl_param_real gp gen a b) 𝒜] =`
      `𝒟[simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) 𝒜]`.

  Proved by induction on `𝒜` using the per-query step lemmas in `Step.lean`.

* `probOutput_lazy_honest_eq` — the probability-level corollary of the
  bridge above, for an adversary `𝒜` simulated from the initial state
  `initGameState (.sendReady (x₀•gen)) (.recvReady x₀)`:

      `Pr[= false | simulateQ (ckaSecurityImpl_lazy_real gp gen) 𝒜 …] =`
      `Pr[= false | simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) 𝒜 …]`.

  The LHS uses the `consumeLazy`-wrapped lazy stack `ckaSecurityImpl_lazy_real`
  (from `GameOracles/Defs.lean`); the RHS uses the regular CKA game
  `ckaSecurityImpl gp false (ddhCKA F G gen)`. The proof composes two steps:
  - `evalDist_ckaSecurityImpl_lazy_eq_eager` (from `GameOracles/Defs.lean`)
    rewrites the lazy `consumeLazy` presentation as the eager
    `do b a ← $ᵗ F; …` form;
  - `evalDist_eager_honest_lazy_eq` (the bridge above) connects that eager
    form with the regular CKA game.

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

set_option maxHeartbeats 2000000 in
-- The adversary induction expands `simulateQ` through every oracle case; the
-- default heartbeat limit times out while checking the bridge theorem.
omit [Inhabited F] [Fintype G] in
/-- **Honest eager–lazy bridge.** For every adversary `𝒜` and initial
state `s`, the eager parameterized presentation matches the regular CKA game
at the `evalDist` level:

  `𝒟[do b a ← $ᵗ F; (simulateQ (honestImpl_param_real gp gen a b) 𝒜).run' s] =`
  `𝒟[(simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) 𝒜).run' s]`. -/
lemma evalDist_eager_honest_lazy_eq
    (gp : GameParams) (s : GameState (CKAState F G) G G)
    (adversary : OracleComp (ckaSecuritySpec (CKAState F G) G G F) Bool) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b) adversary).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run' s) := by
  induction adversary using OracleComp.inductionOn generalizing s with
  | pure x =>
    -- Both sides reduce to `pure x` after `simulateQ_pure` + `StateT.run'_pure`;
    -- on LHS the external samples `b, a` become a constant bind which collapses
    -- to `pure x` since `$ᵗ F` has zero failure probability.
    simp only [simulateQ_pure, StateT.run'_pure']
    exact evalDist_sample_bind₂_eq_of_forall_eq
      (f := fun _b _a => (pure x : ProbComp Bool))
      (p := pure x)
      (fun _ _ => rfl)
  | query_bind t k ih =>
    let pass := evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s
    -- Decompose: `simulateQ impl (query t >>= k) = (impl t).run >>= fun (u, s') =>
    --   simulateQ impl (k u) .run' s'`. Case on `t : ckaSecuritySpec.Domain`.
    -- The 9 oracle cases split into:
    --   * 5 non-divergence (impl_param = impl_reg pointwise): unifSpec, recvA,
    --     recvB, corruptA, corruptB. Bind-swap + IH.
    --   * 4 conditional-divergence (party-split): sendA, sendB, challA, challB.
    --     Off-party: same as non-divergence. On-party with embedding/challenge:
    --     bijection `a ↔ x'` or `b ↔ x` via `probOutput_bind_bijective_uniform_cross`.
    match t with
    | OUnif _ =>
      exact pass _ k (fun _ _ => rfl) ih
    | ORecvA =>
      exact pass _ k (fun _ _ => rfl) ih
    | ORecvB =>
      exact pass _ k (fun _ _ => rfl) ih
    | OCorruptA =>
      exact pass _ k (fun _ _ => rfl) ih
    | OCorruptB =>
      exact pass _ k (fun _ _ => rfl) ih
    | OSendA_rleak =>
      exact evalDist_eager_honest_lazy_eq_step_passthrough
        (gen := gen) gp s OSendA_rleak k (fun _ _ => rfl) ih
    | OSendB_rleak =>
      exact evalDist_eager_honest_lazy_eq_step_passthrough
        (gen := gen) gp s OSendB_rleak k (fun _ _ => rfl) ih
    | OSendA =>  -- sendA
      -- Case-split on `gp.challengedParty`:
      -- • challengedParty=A (off-party): impl_eq via
      --   `honestSendA_param_run_eq_at_chal_A`, then passthrough.
      -- • challengedParty=B (on-party): embedding event; bijection coupling needed
      --   (see `On-party bijection roadmap` doc-comment above the bridge lemma).
      cases h_cp : gp.challengedParty with
      | A =>
        refine pass _ k (fun a _ => ?_) ih
        exact honestSendA_param_run_eq_at_chal_A (gen := gen) gp h_cp a s
      | B =>
        exact evalDist_eager_honest_lazy_eq_step_at_sendA_chal_B
          (gen := gen) gp h_cp s k ih
    | OSendB =>  -- sendB
      cases h_cp : gp.challengedParty with
      | A =>
        exact evalDist_eager_honest_lazy_eq_step_at_sendB_chal_A
          (gen := gen) gp h_cp s k ih
      | B =>
        refine pass _ k (fun a _ => ?_) ih
        exact honestSendB_param_run_eq_at_chal_B (gen := gen) gp h_cp a s
    | OChallA =>  -- challA
      cases h_cp : gp.challengedParty with
      | A =>
        exact evalDist_eager_honest_lazy_eq_step_at_challA_chal_A
          (gen := gen) gp h_cp s k ih
      | B =>
        refine pass _ k (fun _ b => ?_) ih
        exact honestChallA_param_run_eq_at_chal_B (gen := gen) gp h_cp b s
    | OChallB =>  -- challB
      cases h_cp : gp.challengedParty with
      | A =>
        refine pass _ k (fun _ b => ?_) ih
        exact honestChallB_param_run_eq_at_chal_A (gen := gen) gp h_cp b s
      | B =>
        exact evalDist_eager_honest_lazy_eq_step_at_challB_chal_B
          (gen := gen) gp h_cp s k ih

omit [Fintype G] in
/-- **Lazy-vs-regular honest endpoint.** From the initial state
`initGameState (.sendReady (x₀ • gen)) (.recvReady x₀)`, the adversary has the
same probability of outputting `false` under two presentations of the honest
real-branch CKA game: the `consumeLazy`-wrapped oracle stack
`ckaSecurityImpl_lazy_real gp gen`, and the regular false-branch oracle stack
`ckaSecurityImpl gp false (ddhCKA F G gen)`. -/
lemma probOutput_lazy_honest_eq [Finite G] (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) (x₀ : F) :
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl_lazy_real gp gen) adversary).run
        ((initGameState
            (CKAState.sendReady (x₀ • gen) : CKAState F G)
            (CKAState.recvReady x₀ : CKAState F G), none), none)
      return b'] =
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run
        (initGameState
          (CKAState.sendReady (x₀ • gen) : CKAState F G)
          (CKAState.recvReady x₀ : CKAState F G))
      return b'] := by
  letI : Fintype G := Fintype.ofFinite G
  -- Compose Step 1 (consumeLazy commutation × 2) and Step 2 (adversary
  -- induction via bijection at hits + bind-swap at non-hits).
  have h₁ := evalDist_ckaSecurityImpl_lazy_eq_eager (gen := gen) gp adversary
    (initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G))
  have h₂ := evalDist_eager_honest_lazy_eq (gen := gen) gp
    (initGameState
      (CKAState.sendReady (x₀ • gen) : CKAState F G)
      (CKAState.recvReady x₀ : CKAState F G)) adversary
  exact probOutput_eq_of_evalDist_eq (h₁.trans h₂) false

end Step2

end ddhCKA
