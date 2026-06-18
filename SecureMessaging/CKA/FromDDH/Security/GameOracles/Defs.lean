/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.ReductionGames
import ToVCVio.EvalDist.Monad.Basic

/-!
# CKA from DDH — Game Oracles — Definitions

Building blocks used in the security reduction of the Continuous Key
Agreement (CKA) construction from the Decisional Diffie-Hellman (DDH)
assumption:

* cache-aware honest oracle handlers;
* the parameterized oracle implementation sets built from them;
* the lazy↔eager bridge that exposes the external samples consumed at
  the embedding and challenge events at the top of the security game.
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

omit [Field F] [SampleableType F] [SampleableType G] [DecidableEq G] [Inhabited F] in
/-- The CKA security spec has finitely many oracle indices. Required by
VCVio's probability-of-output lemmas that quantify over queries. -/
instance ckaSecuritySpec_Fintype :
    (ckaSecuritySpec (CKAState F G) G G F).Fintype := by
  unfold ckaSecuritySpec ckaCorrectnessSpec
  infer_instance

omit [Field F] [SampleableType F] [SampleableType G] [DecidableEq G] [Inhabited F]
[Fintype G] [Fintype F] in
/-- The CKA security spec has at least one oracle index. Required by
VCVio's existence lemmas that pick a sample query. -/
instance ckaSecuritySpec_Inhabited :
    (ckaSecuritySpec (CKAState F G) G G F).Inhabited := by
  unfold ckaSecuritySpec ckaCorrectnessSpec
  infer_instance

open OracleComp.ProgramLogic.Relational in
/-- Predicate defining which oracle calls may require embedding of scalar `a` -/
def hitA (gp : GameParams) :
    (ckaSecuritySpec (CKAState F G) G G F).Domain → Bool
  | OChallA => gp.challengedParty = .A
  | OChallB => gp.challengedParty = .B
  | OSendB  => gp.challengedParty = .A
  | OSendA  => gp.challengedParty = .B
  | _ => false

/-- Predicate defining which oracle calls may require embedding of scalar `b` -/
def hitB (gp : GameParams) :
    (ckaSecuritySpec (CKAState F G) G G F).Domain → Bool
  | OChallA => gp.challengedParty = .A
  | OChallB => gp.challengedParty = .B
  | _ => false

/-! ### Cache-aware honest oracles

The DDH experiment samples its scalars at the top of the game:

```text
a ←$ F       (used as `gA = a•gen`, the embedding image)
b ←$ F       (used as `gB = b•gen`, the challenge image)
```

The CKA game samples a fresh scalar inside each call to `send`:

```text
y_a ←$ F     sendA or sendB at challengeEpoch − 1 (the embedding event)
y_b ←$ F     challA or challB at challengeEpoch   (the challenge event)
```

This section defines four parameterized variants of the CKA
game oracles that accept the DDH scalars `a, b : F` as external inputs
instead of sampling `y_a, y_b` internally:

* `honestSendA_param gp gen a`, `honestSendB_param gp gen a` — variants of
  the CKA `oracleSendA` / `oracleSendB` that use `a` at the embedding
  event in place of the internal `y_a`.
* `honestChallA_param gp gen b`, `honestChallB_param gp gen b` — variants
  of the CKA `oracleChallA` / `oracleChallB` that use `b` at the
  challenge event in place of the internal `y_b`.

Together with the unchanged CKA oracles `oracleUnif`, `oracleRecv{A,B}`, `oracleCorrupt{A,B}`,
they bundle into the first parameterized family `honestImpl_param_real gp gen a b`.

The reduction side has an analogous family `reductionOracleImpl gp gen gA gB gT`
(defined in `ReductionGames.lean`), with the same oracle indices but
`reductionSend{A,B}` / `reductionChall{A,B}` at the hit (embedding, challenge) events.

`consumeLazy hit implFam` (from `ToVCVio/OracleComp/QueryTracking/LazySampling.lean`)
samples `←$ τ` at the first query with `hit t = true`, caches it, and reuses
the cache afterwards; off-hit queries use the cache (or a default) without
sampling. Valid when off-hit oracles are parameter-independent — proved here
as `hindepA` / `hindepB`.

Applied twice, this turns each parameterized family into lazy oracle implementations where
we sample values at first use:

* `honestImpl_param_real` ↦ `ckaSecurityImpl_lazy_real gp gen :=
   consumeLazy hitB (fun b => consumeLazy hitA (fun a =>
     honestImpl_param_real gp gen a b))`
* `reductionOracleImpl` ↦ `reductionImpl_lazy_real gp gen :=
   consumeLazy hitB (fun b => consumeLazy hitA (fun a =>
     reductionOracleImpl gp gen (a•gen) (b•gen) ((a·b)•gen)))`

A series of lemmas prove that each lazy implementation is distributionally equal to the
regular CKA implementation or the DDH-real branch of the reduction `ℬ`:

* `evalDist_ckaSecurityImpl_lazy_eq_eager` (this file): the lazy CKA implementation
  equals the eager one — sample `b, a ←$ F` in `ProbComp`, then run
  `honestImpl_param_real gp gen a b`.

* `evalDist_eager_honest_lazy_eq` (`Bridge.lean`, per-query steps in `Step.lean`):
  the eager CKA implementation equals the regular honest CKA game.

* `evalDist_eager_reduction_lazy_eq` (`ReductionReal/Step.lean`): the same
  lazy/eager pattern for `reductionOracleImpl`, bridging to the DDH-real
  branch of `ℬ`. -/

/-- Variant of `oracleSendB (ddhCKA F G gen)` taking `a : F` as a parameter.
At the **embedding event** (`sendB` at `challengeEpoch − 1`,
`challengedParty = .A`) it uses `a` instead of the internal `x ←$ F`,
producing `ρ = a • gen`, `key = a • h`. Off-event: identical to
`oracleSendB`. -/
noncomputable def honestSendB_param (gp : GameParams) (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tB := state.tB + 1 }
    -- embedding event: challengedParty = A, last sendB before challenge
    if validStep state.lastAction .sendB && gp.challengedParty == .A &&
        isOtherSendBeforeChall gp state' then
      match state'.stB with
      | .sendReady h =>
        let key := a • h          -- use parameter `a` in place of fresh `x ←$ F`
        let ρ := a • gen
        set { state' with
          stB := (.recvReady a : CKAState F G), rhoB := some ρ, keyB := some key,
          lastAction := some .sendB }
        return some (ρ, key)
      | .recvReady _ => pure none
    else
      oracleSendB (ddhCKA F G gen) ()  -- off-event: regular oracle

/-- Variant of `oracleSendA (ddhCKA F G gen)` taking `a : F` as a parameter.
At the **embedding event** (`sendA` at `challengeEpoch − 1`,
`challengedParty = .B`) it uses `a` instead of the internal `x ←$ F`,
producing `ρ = a • gen`, `key = a • h`. Off-event: identical to
`oracleSendA`. -/
noncomputable def honestSendA_param (gp : GameParams) (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tA := state.tA + 1 }
    -- embedding event: challengedParty = B, last sendA before challenge
    if validStep state.lastAction .sendA && gp.challengedParty == .B &&
        isOtherSendBeforeChall gp state' then
      match state'.stA with
      | .sendReady h =>
        let key := a • h          -- use parameter `a` in place of fresh `x ←$ F`
        let ρ := a • gen
        set { state' with
          stA := (.recvReady a : CKAState F G), rhoA := some ρ, keyA := some key,
          lastAction := some .sendA }
        return some (ρ, key)
      | .recvReady _ => pure none
    else
      oracleSendA (ddhCKA F G gen) ()  -- off-event: regular oracle

/-- Challenge-output mode for the honest parameterized challenge handlers. -/
inductive HonestChallengeMode where
  | real
  | rand

/-- `true` for `rand` mode, `false` for `real` mode. -/
@[simp] def HonestChallengeMode.isRandom : HonestChallengeMode → Bool
  | .real => false
  | .rand => true

/-- Select the key exposed to the adversary at the challenge event. In `real`
mode the exposed key is the honest Diffie-Hellman key `b • h`; in `rand` mode
it is the external random key `gT`. -/
@[simp] def HonestChallengeMode.outputKey
    (mode : HonestChallengeMode) (b : F) (h gT : G) : G :=
  match mode with
  | .real => b • h
  | .rand => gT

/-- Challenge oracle for `challengedParty = A`, parameterized by `b : F` and
by `mode : HonestChallengeMode` selecting which DDH branch is simulated:
at the challenge event, `.real` returns the honest key `b • h`; `.rand`
returns the external key `gT`.
The state update (`stA := .recvReady b`, `ρ := b • gen`) is the same in both
modes; only the key returned to the adversary differs. Off-event: identical
to `oracleChallA`. -/
noncomputable abbrev honestChallA_param_mode
    (mode : HonestChallengeMode) (gp : GameParams) (gen : G) (b : F) (gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tA := state.tA + 1 }
    -- challenge event: challengedParty = A, challA at `challengeEpoch`
    if validStep state.lastAction .challA && gp.challengedParty == .A &&
        isChallengeEpoch gp state' then
      match state'.stA with
      | .sendReady h =>
        let key := b • h          -- use parameter `b` in place of fresh `x ←$ F`
        let ρ := b • gen
        set { state' with
          stA := (.recvReady b : CKAState F G), rhoA := some ρ, keyA := some key,
          lastAction := some .challA }
        return some (ρ, mode.outputKey b h gT)
      | .recvReady _ => pure none
    else
      oracleChallA gp mode.isRandom (ddhCKA F G gen) ()

/-- Challenge oracle for `challengedParty = B`, parameterized by `b : F` and
by `mode : HonestChallengeMode` selecting which DDH branch is simulated:
at the challenge event, `.real` returns the honest key `b • h`; `.rand`
returns the external key `gT`.
The state update (`stB := .recvReady b`, `ρ := b • gen`) is the same in both
modes; only the key returned to the adversary differs. Off-event: identical
to `oracleChallB`. -/
noncomputable abbrev honestChallB_param_mode
    (mode : HonestChallengeMode) (gp : GameParams) (gen : G) (b : F) (gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tB := state.tB + 1 }
    -- challenge event: challengedParty = B, challB at `challengeEpoch`
    if validStep state.lastAction .challB && gp.challengedParty == .B &&
        isChallengeEpoch gp state' then
      match state'.stB with
      | .sendReady h =>
        let key := b • h          -- use parameter `b` in place of fresh `x ←$ F`
        let ρ := b • gen
        set { state' with
          stB := (.recvReady b : CKAState F G), rhoB := some ρ, keyB := some key,
          lastAction := some .challB }
        return some (ρ, mode.outputKey b h gT)
      | .recvReady _ => pure none
    else
      oracleChallB gp mode.isRandom (ddhCKA F G gen) ()

/-- `oracleChallA gp (ddhCKA F G gen)` with parameter `b` substituted for the
internal sample at the challenge event (challengedParty=A, challA at `challengeEpoch`). Off-event:
identical. -/
noncomputable abbrev honestChallA_param (gp : GameParams) (gen : G) (b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  honestChallA_param_mode (F := F) .real gp gen b gen

/-- Symmetric mirror of `honestChallA_param` for `challengedParty = B`. -/
noncomputable abbrev honestChallB_param (gp : GameParams) (gen : G) (b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  honestChallB_param_mode (F := F) .real gp gen b gen

/-- Rand-branch challenge oracle for `challengedParty = A`: reuse the honest state update,
by `mode : HonestChallengeMode` selecting which DDH branch is simulated:
at the challenge event, `.real` returns the honest key `b • h`; `.rand`
returns the external key `gT`.
Off-event: identical to `oracleChallA`. -/
noncomputable abbrev honestChallA_param_rand
    (gp : GameParams) (gen : G) (b : F) (gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  honestChallA_param_mode (F := F) .rand gp gen b gT

/-- Symmetric rand-branch challenge oracle for `challengedParty = B`. -/
noncomputable abbrev honestChallB_param_rand
    (gp : GameParams) (gen : G) (b : F) (gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  honestChallB_param_mode (F := F) .rand gp gen b gT

/-- **DDH-real branch** honest oracle set with embedding scalar `a` and
challenge scalar `b` exposed as parameters. At the challenge event, the key
returned to the adversary is the honest Diffie-Hellman key `b • h` — i.e.
the value that `ℬ` would expose when its DDH challenger gives it
`gT = (a·b)•gen`. Built from the same seven shared oracles as
`reductionOracleImpl` (`oracleUnif`, `oracleRecv{A,B}`, `oracleCorrupt{A,B}`,
`oracleSend{A,B}_rleak`) and the four parameterized handlers above
(`honestSend{A,B}_param`, `honestChall{A,B}_param`). Under the substitution
`gA = a•gen`, `gB = b•gen`, `gT = (a·b)•gen`, each parameterized handler
matches the corresponding one in
`reductionOracleImpl gp gen (a•gen) (b•gen) ((a·b)•gen)` (per-step lemmas
of `evalDist_eager_reduction_lazy_eq`). -/
noncomputable def honestImpl_param_real (gp : GameParams) (gen : G) (a b : F) :
    QueryImpl (ckaSecuritySpec (CKAState F G) G G F)
      (StateT (GameState (CKAState F G) G G) ProbComp) :=
  (oracleUnif (CKAState F G) G G
    + honestSendA_param (F := F) gp gen a
    + oracleRecvA (ddhCKA F G gen)
    + honestSendB_param (F := F) gp gen a
    + oracleRecvB (ddhCKA F G gen))
  + honestChallA_param (F := F) gp gen b
  + honestChallB_param (F := F) gp gen b
  + oracleCorruptA gp (CKAState F G) G G
  + oracleCorruptB gp (CKAState F G) G G
  + oracleSendA_rleak gp (ddhCKA F G gen)
  + oracleSendB_rleak gp (ddhCKA F G gen)

/-- Rand-branch variant of `honestImpl_param_real`. Same seven shared oracles
and same `honestSend{A,B}_param` handlers; the challenge handlers
`honestChall{A,B}_param` (key = `b • h`) are swapped for
`honestChall{A,B}_param_rand` (key = external `gT : G`), so the state update
at the challenge event is identical but the exposed key is `gT`. Under the
substitution `gA = a•gen`, `gB = b•gen`, this matches
`reductionOracleImpl gp gen (a•gen) (b•gen) gT` — the DDH-rand branch of `ℬ`. -/
noncomputable def honestImpl_param_rand
    (gp : GameParams) (gen : G) (a b : F) (gT : G) :
    QueryImpl (ckaSecuritySpec (CKAState F G) G G F)
      (StateT (GameState (CKAState F G) G G) ProbComp) :=
  (oracleUnif (CKAState F G) G G
    + honestSendA_param (F := F) gp gen a
    + oracleRecvA (ddhCKA F G gen)
    + honestSendB_param (F := F) gp gen a
    + oracleRecvB (ddhCKA F G gen))
  + honestChallA_param_rand (F := F) gp gen b gT
  + honestChallB_param_rand (F := F) gp gen b gT
  + oracleCorruptA gp (CKAState F G) G G
  + oracleCorruptB gp (CKAState F G) G G
  + oracleSendA_rleak gp (ddhCKA F G gen)
  + oracleSendB_rleak gp (ddhCKA F G gen)

open OracleComp.ProgramLogic.Relational in
/-- Lazy reduction oracle set (real branch): wraps `reductionOracleImpl`
with `consumeLazy ∘ consumeLazy` so the `a, b` samples are deferred to
the first query that consumes them (`hitA`, `hitB`). -/
noncomputable def reductionImpl_lazy_real (gp : GameParams) (gen : G) :
    QueryImpl (ckaSecuritySpec (CKAState F G) G G F)
      (StateT ((GameState (CKAState F G) G G × Option F) × Option F) ProbComp) :=
  consumeLazy (hit := hitB gp) (implFam := fun b =>
    consumeLazy (hit := hitA gp) (implFam := fun a =>
      reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)))

open OracleComp.ProgramLogic.Relational in
/-- Cache-aware honest oracle set wrapping `honestImpl_param_real` with the
same `consumeLazy ∘ consumeLazy` shape as `reductionImpl_lazy_real`. Bridge
to the regular `ckaSecurityImpl`: `probOutput_lazy_honest_eq`. -/
noncomputable def ckaSecurityImpl_lazy_real (gp : GameParams) (gen : G) :
    QueryImpl (ckaSecuritySpec (CKAState F G) G G F)
      (StateT ((GameState (CKAState F G) G G × Option F) × Option F) ProbComp) :=
  consumeLazy (hit := hitB gp) (implFam := fun b =>
    consumeLazy (hit := hitA gp) (implFam := fun a =>
      honestImpl_param_real gp gen a b))


omit [Inhabited F] [Fintype G] in
/-- At non-`hitA` queries, `honestImpl_param_real gp gen a b` doesn't read `a` . -/
lemma hindepA_param_honest (gp : GameParams) (b : F)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G) (a₁ a₂ : F)
    (h : hitA gp t = false) :
    (honestImpl_param_real gp gen a₁ b t).run s =
    (honestImpl_param_real gp gen a₂ b t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>  -- challB: gated by challengedParty = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp only [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallB_param]
    | B =>
      exfalso; simp [hitA, h_cp] at h
  | OChallA =>  -- challA: gated by challengedParty = .A; impl uses b not a
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso; simp [hitA, h_cp] at h
    | B =>
      simp only [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallA_param]
  | ORecvB => rfl  -- recvB
  | OSendB =>  -- sendB: gated by challengedParty = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso; simp [hitA, h_cp] at h
    | B =>
      simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestSendB_param, h_cp]
  | ORecvA => rfl  -- recvA
  | OSendA =>  -- sendA: gated by challengedParty = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestSendA_param, h_cp]
    | B =>
      exfalso; simp [hitA, h_cp] at h
  | OUnif _ => rfl  -- oracleUnif

omit [Fintype G] in
/-- Lazy honest impl wrapped in inner `consumeLazy hitA` is `b`-independent
at non-`hitB` queries. -/
lemma hindepB_param_honest (gp : GameParams)
    (t : (ckaSecuritySpec (CKAState F G) G G F).Domain)
    (s : GameState (CKAState F G) G G × Option F) (b₁ b₂ : F)
    (h : hitB gp t = false) :
    (OracleComp.ProgramLogic.Relational.consumeLazy (hit := hitA gp)
        (implFam := fun a => honestImpl_param_real gp gen a b₁) t).run s =
    (OracleComp.ProgramLogic.Relational.consumeLazy (hit := hitA gp)
        (implFam := fun a => honestImpl_param_real gp gen a b₂) t).run s := by
  match t with
  | OSendB_rleak => rfl
  | OSendA_rleak => rfl
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>  -- challB: gated by challengedParty = .B
    cases h_cp : gp.challengedParty with
    | A =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallB_param, honestChallB_param_mode, hitA, h_cp]
    | B =>
      exfalso; simp [hitB, h_cp] at h
  | OChallA =>  -- challA: gated by challengedParty = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso; simp [hitB, h_cp] at h
    | B =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp [honestImpl_param_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallA_param, honestChallA_param_mode, hitA, h_cp]
  | ORecvB => rfl  -- recvB
  | OSendB => rfl  -- sendB
  | ORecvA => rfl  -- recvA
  | OSendA => rfl  -- sendA
  | OUnif _ => rfl  -- oracleUnif


/-! ### Lazy `QueryImpl` set ↔ eager `ProbComp` sampling

`evalDist_ckaSecurityImpl_lazy_eq_eager` proves the `evalDist` equality between
- running an adversary under the lazy `QueryImpl` set `ckaSecurityImpl_lazy_real`, and
- sampling `b, a ←$ F` in `ProbComp` then running it under `honestImpl_param_real`.
-/

omit [Fintype G] in
/-- Proves the `evalDist` equality between
- running an adversary under the lazy `QueryImpl` set `ckaSecurityImpl_lazy_real`, and
- sampling `b, a ←$ F` in `ProbComp` then running it under
  the parameterized `QueryImpl` set `honestImpl_param_real gp gen a b`.
This is the lazy/eager endpoint for the two cache samples used by
`ckaSecurityImpl_lazy_real`. -/
-- `Finite G` is unused in the proof but kept for uniformity with the
-- surrounding lazy/eager bridge lemmas.
@[nolint unusedArguments]
lemma evalDist_ckaSecurityImpl_lazy_eq_eager
    [Finite G]
    (gp : GameParams) (adversary : CKAAdversary (CKAState F G) G G F)
    (s : GameState (CKAState F G) G G) :
    evalDist ((simulateQ (ckaSecurityImpl_lazy_real gp gen) adversary).run' ((s, none), none)) =
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b) adversary).run' s) := by
  letI : Fintype G := Fintype.ofFinite G
  unfold ckaSecurityImpl_lazy_real
  rw [← OracleComp.ProgramLogic.Relational.probOutput_simulateQ_consumeLazy_run'_eq
        (spec := ckaSecuritySpec (CKAState F G) G G F) (τ := F)
        (implFam := fun b => OracleComp.ProgramLogic.Relational.consumeLazy
          (hit := hitA gp)
          (implFam := fun a => honestImpl_param_real gp gen a b))
        (hit := hitB gp)
        (h_indep := fun t s' b₁ b₂ h => hindepB_param_honest gp t s' b₁ b₂ h)
        adversary (s, none)]
  exact evalDist_sample_bind_congr_of_forall_evalDist_eq
    (f := fun b =>
      (simulateQ (OracleComp.ProgramLogic.Relational.consumeLazy
        (hit := hitA gp)
        (implFam := fun a => honestImpl_param_real gp gen a b)) adversary).run' (s, none))
    (g := fun b => do
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_param_real gp gen a b) adversary).run' s)
    (fun b => by
      exact (OracleComp.ProgramLogic.Relational.probOutput_simulateQ_consumeLazy_run'_eq
        (spec := ckaSecuritySpec (CKAState F G) G G F) (τ := F)
        (implFam := fun a => honestImpl_param_real gp gen a b)
        (hit := hitA gp)
        (h_indep := fun t s'' a₁ a₂ h => hindepA_param_honest gp b t s'' a₁ a₂ h)
        adversary s).symm)

end Step2

end ddhCKA
