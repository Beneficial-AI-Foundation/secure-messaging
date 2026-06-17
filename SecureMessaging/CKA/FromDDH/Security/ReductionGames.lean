/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Common
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Tactics.Relational
import ToVCVio.OracleComp.QueryTracking.LazySampling

/-!
# CKA from DDH — Reduction Games

This file defines the reduction from a CKA security adversary to a DDH
adversary. Given a DDH challenge tuple `(gen, gA, gB, gT)` and a CKA adversary
`𝒜`, the reduction `ℬ = securityReduction gp 𝒜` simulates an honest CKA game for
`𝒜` with the following modifications:
  - At the embedding epoch (`tX = challengeEpoch - 1`), the reduction injects
    `gA` into the honest CKA oracle's output.
  - At the challenge epoch (`tX = challengeEpoch`), the reduction injects
    `(gB, gT)` into the honest CKA oracle's output.
All other epochs run honest CKA.
The reduction outputs `!b'`, where `b'` is `𝒜`'s challenge guess to the simulated
CKA game.
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

/-! ### DDH reduction

Input: DDH tuple `(gen, gA, gB, gT)` with `a, b ←$ F`, `gA = a•gen`,
`gB = b•gen`, and `gT = (a·b)•gen` (real) or `gT = c•gen`, `c ←$ F` (random).

Embedding epoch (`O-Send-X` at `tX = challengeEpoch - 1`) injects `gA` into
the output. Challenge epoch (`O-Chall-X` at `tX = challengeEpoch`) injects
`(gB, gT)`. Both write `stX := .recvReady 0` placeholder to state. All other
epochs run honest CKA.

The diagram below shows the case `gp.challengedParty = .A` and challenge epoch `tA = t*`.

```text
 DDH Challenger                 DDH Adversary ℬ = securityReduction gp 𝒜
┌──────────────┐               ┌──────────────────────────────────────────────────┐
│              │ (gen,gA,gB,gT)│ sample x₀ ←$ F                                   │
│  gA = a•gen  │──────────────▶│ init A with g₀ := x₀ • gen, init B with x₀       │
│  gB = b•gen  │               │                                                  │
│  gT = c•gen  │               │ simulate CKA oracles for 𝒜 (honest except below) │
│              │               │                                                  │
│  c = a·b     │               │          Honest CKA        │ Reduction           │
│  or random   │               │ ─────────────────────────────────────────────────│
│              │               │ O-Send-B, tB = t* - 1, stA = xA ∈ F, stB = xA•gen│
│              │               │   y ←$ F                   │                     │
│              │               │   ρ   = y • gen            │ ρ   = gA            │
│              │               │   key = y • xA • gen       │ key = xA • gA       │
│              │               │   stB := y (live)          │ stB := 0 (dead)     │
│              │               │ ─────────────────────────────────────────────────│
│              │               │ recvA delivers ρ from above:                     │
│              │               │   stA := y • gen           │ stA := gA           │
│              │               │ ─────────────────────────────────────────────────│
│              │               │ O-Chall-A, tA = t*, (stA, stB) as updated above: │
│              │               │   x ←$ F                   │                     │
│              │               │   ρ   = x • gen            │ ρ   = gB            │
│              │               │   key = x • stA            │ key = gT            │
│              │               │   stA := x (live)          │ stA := 0 (dead)     │
│              │               │ · · · · · · · · · · · · · · · · · · · · · · · · ·│
│              │               │  real: gT = b • gA            random: gT ←$ G    │
│              │               │ ─────────────────────────────────────────────────│
│              │               │ all later queries: honest in both columns        │
│              │               │                                                  │
│              │     !b'       │ output !b', where b' is 𝒜's challenge guess      │
│              │◀──────────────│                                                  │
└──────────────┘               └──────────────────────────────────────────────────┘
```

See `SecureMessaging.CKA.FromDDH.Security` for the full proof overview. -/

/-- `R-Send-B = O-Send-B` (= `oracleSendB`) at every step except the
embedding epoch (`tB = t*−1`, `challengedParty = .A`), where:

  O-Send-B:  `y ←$ F`;  `(ρ, keyB) := (y•gen, y•stB)`,  `stB := y`
  R-Send-B:              `(ρ, keyB) := (gA,    xA•gA)`,  `stB := 0`

At this point `stB = xA•gen` (with `xA` from `stA`) and `gA = a•gen`,
so identifying `y ≡ a`:
  `y•gen  = a•gen = gA`,
  `y•stB  = a•(xA•gen) = xA•(a•gen) = xA•gA`.
Since `a ←$ F` in the DDH game matches `y ←$ F` in the honest one, the
reduction's output can be shown to perfectly simulate `O-Send-B`. -/
noncomputable def reductionSendB (gp : GameParams) (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      let state := { state with tB := state.tB + 1 }
      if gp.challengedParty == .A && isOtherSendBeforeChall gp state then
        -- embed: stB := .recvReady 0 (dead), rhoB := gA, keyB := xA • gA
        let xA := match state.stA with | .recvReady x => x | .sendReady _ => 0
        set { state with
          stB := (.recvReady 0 : CKAState F G), rhoB := some gA, keyB := some (xA • gA),
          lastAction := some .sendB }
        return some (gA, xA • gA)
      else
        -- honest = `send gen state.stB`: requires stB = .sendReady h, then
        --   x ←$ F; stB := .recvReady x, rhoB := x • gen, keyB := x • h
        match ← liftM (send gen state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          set { state with
            stB := stB', rhoB := some ρ, keyB := some key,
            lastAction := some .sendB }
          return some (ρ, key)
    else pure none

/-- `R-Send-A = O-Send-A` (= `oracleSendA`) at every step except the
embedding epoch (`tA = t*−1`, `challengedParty = .B`), where:

  O-Send-A:  `y ←$ F`;  `(ρ, keyA) := (y•gen, y•stA)`,  `stA := y`
  R-Send-A:              `(ρ, keyA) := (gA,    xB•gA)`,  `stA := 0`

At this point `stA = xB•gen` (with `xB` from `stB`) and `gA = a•gen`,
so identifying `y ≡ a`:
  `y•gen  = a•gen = gA`,
  `y•stA  = a•(xB•gen) = xB•(a•gen) = xB•gA`.
Since `a ←$ F` in the DDH game matches `y ←$ F` in the honest one, the
reduction's output can be shown to perfectly simulate `O-Send-A`. -/
noncomputable def reductionSendA (gp : GameParams) (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      let state := { state with tA := state.tA + 1 }
      if gp.challengedParty == .B && isOtherSendBeforeChall gp state then
        -- embed: stA := .recvReady 0 (dead), rhoA := gA, keyA := xB • gA
        let xB := match state.stB with | .recvReady x => x | .sendReady _ => 0
        set { state with
          stA := (.recvReady 0 : CKAState F G), rhoA := some gA, keyA := some (xB • gA),
          lastAction := some .sendA }
        return some (gA, xB • gA)
      else
        -- honest = `send gen state.stA`: requires stA = .sendReady h, then
        --   x ←$ F; stA := .recvReady x, rhoA := x • gen, keyA := x • h
        match ← liftM (send gen state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          set { state with
            stA := stA', rhoA := some ρ, keyA := some key,
            lastAction := some .sendA }
          return some (ρ, key)
    else pure none

/-- `R-Chall-A` ≡ `O-Chall-A` (= `oracleChallA`): fires only at
`tA = t*` with `challengedParty = .A`, where:

  O-Chall-A:  `x ←$ F`;  `(ρ, keyA) := (x•gen, x•stA)` or `(x•gen, $ᵗ G)`
  R-Chall-A:              `(ρ, keyA) := (gB,    gT)`,  `stA := 0`

At this point `stA = gA = a•gen` and `gB = b•gen`, so identifying
`x ≡ b`:
  real DDH (`gT = (a·b)•gen`): `gT = b•gA` = honest key for `x = b`.
  rand DDH (`gT ←$ G`):        `gT` uniform = honest random key. -/
noncomputable def reductionChallA (gp : GameParams) (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .A && validStep state.lastAction .challA then
      let state := { state with tA := state.tA + 1 }
      if isChallengeEpoch gp state then
        -- challenge: stA := .recvReady 0 (dead), rhoA := gB, keyA := gT
        set { state with
          stA := (.recvReady 0 : CKAState F G),
          rhoA := some gB, keyA := some gT,
          lastAction := some .challA }
        return some (gB, gT)
      else pure none
    else pure none

/-- `R-Chall-B` ≡ `O-Chall-B` (= `oracleChallB`): fires only at
`tB = t*` with `challengedParty = .B`, where:

  O-Chall-B:  `x ←$ F`;  `(ρ, keyB) := (x•gen, x•stB)` or `(x•gen, $ᵗ G)`
  R-Chall-B:              `(ρ, keyB) := (gB,    gT)`,  `stB := 0`

At this point `stB = gA = a•gen` and `gB = b•gen`, so identifying
`x ≡ b`:
  real DDH (`gT = (a·b)•gen`): `gT = b•gA` = honest key for `x = b`.
  rand DDH (`gT ←$ G`):        `gT` uniform = honest random key. -/
noncomputable def reductionChallB (gp : GameParams) (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (CKAState F G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .B && validStep state.lastAction .challB then
      let state := { state with tB := state.tB + 1 }
      if isChallengeEpoch gp state then
        -- challenge: stB := .recvReady 0 (dead), rhoB := gB, keyB := gT
        set { state with
          stB := (.recvReady 0 : CKAState F G),
          rhoB := some gB, keyB := some gT,
          lastAction := some .challB }
        return some (gB, gT)
      else pure none
    else pure none

/-- Oracle set for the reduction: the four DDH-embedding components
(`reductionSend{A,B}` and `reductionChall{A,B}`) combined with honest
`oracleUnif`, `oracleRecv{A,B}`, and `oracleCorrupt{A,B}`. -/
noncomputable def reductionOracleImpl (gp : GameParams) (gen gA gB gT : G) :
    QueryImpl (ckaSecuritySpec (CKAState F G) G G F)
      (StateT (GameState (CKAState F G) G G) ProbComp) :=
  (oracleUnif (CKAState F G) G G
    + reductionSendA (F := F) gp gen gA
    + oracleRecvA (ddhCKA F G gen)
    + reductionSendB (F := F) gp gen gA
    + oracleRecvB (ddhCKA F G gen))
  + reductionChallA (F := F) gp gB gT
  + reductionChallB (F := F) gp gB gT
  + oracleCorruptA gp (CKAState F G) G G
  + oracleCorruptB gp (CKAState F G) G G
  + oracleSendA_rleak gp (ddhCKA F G gen)
  + oracleSendB_rleak gp (ddhCKA F G gen)

/-- Initial CKA game state used by the reduction, case-split on game
parameters `gp`:

* **General case**: `x₀ ←$ F`; `stA := .sendReady (x₀•gen)`, `stB := .recvReady x₀`
  (same as for CKA initialization). `gA` is embedded later, at `tB = t*−1`
  (`challengedParty = .A`) or `tA = t*−1` (`challengedParty = .B`).

* **Special case** (`challengeEpoch = 1`, `challengedParty = .A`):
  `challA` fires as the first action, so no pre-challenge send exists.
  The reduction identifies `x₀ ≡ a` and sets `stA := .sendReady gA`,
  `stB := .recvReady 0` directly. -/
noncomputable def reductionInitState (gp : GameParams) (gen gA : G) :
    ProbComp (GameState (CKAState F G) G G) :=
  -- special case
  if gp.challengeEpoch = 1 ∧ gp.challengedParty = .A then
    return initGameState (.sendReady gA) ((.recvReady 0) : CKAState F G)
  -- general case
  else do
    let x₀ ← $ᵗ F
    return initGameState (.sendReady (x₀ • gen)) (.recvReady x₀)

/-- DDH adversary obtained by reduction from a CKA security adversary
[ACD19, Theorem 3], parameterized by `gp : GameParams`.

Given a DDH triple `(gen, gA, gB, gT)` and a CKA adversary, the reduction:
1. Builds the initial CKA game state via `reductionInitState` (case-split on `gp`).
2. Runs the CKA adversary against `reductionOracleImpl`, which embeds `gA` into
   the other party's send and `(gB, gT)` into `gp.challengedParty`'s challenge.
3. Outputs `!b'` as DDH guess (negated CKA guess, to align bit conventions). -/
noncomputable def securityReduction (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) : DDHAdversary F G :=
  fun gen gA gB gT => do
    let s₀ ← reductionInitState gp gen gA
    let b' ← (simulateQ (reductionOracleImpl gp gen gA gB gT) adversary).run' s₀
    return !b'

/-! ### Simulation: each DDH branch maps to the corresponding CKA branch

Goal: the reduction `ℬ = securityReduction gp 𝒜` (which returns `¬b'`)
satisfies the top-level branch identities

    Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA^{isRandom = false}]   (**real branch**)
    Pr[ℬ = true | DDH_rand] = Pr[𝒜 = false | CKA^{isRandom = true}]   (**random branch**)

Each branch is proved by a 3-step chain:

```text
Pr[ℬ = true | DDH_real]
    = Pr[= false | securityReductionRealGame]             -- (1) peel `¬b'`
    = Pr[= false | securityExpRealGame]          -- (2) game-level bridge
    = Pr[= false | securityExpFixedBit ... false gp]      -- (3) def. fold

Pr[ℬ = true | DDH_rand]
    = Pr[= false | securityReductionRandGame]             -- (1) peel `¬b'`
    = Pr[= false | securityExpRandGame]           -- (2) game-level bridge
    = Pr[= false | securityExpFixedBit ... true gp]       -- (3) def. fold
```

Steps (1) and (3) on each branch are simple mechanical unfolding.
Steps (2) on each branch contain the main proof arguments.
They are proved in `ReductionReal/` (real branch) and `ReductionRand/` (random branch). -/

/-- Real DDH branch reduction game. Samples DDH exponents `a, b`, initializes
the reduction with `gA = a • gen`, and runs the reduction oracle stack with
`gB = b • gen` and `gT = (a * b) • gen`. The returned bit is the adversary's
bit before the reduction's final negation. -/
noncomputable def securityReductionRealGame (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let s₀ ← reductionInitState gp gen (a • gen)
  -- we use a*b in the real game, corresponding to DDH_real
  (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run' s₀

/-- **Step (1) of the real branch.** Peel `ℬ`'s final `¬`:

  `Pr[ℬ = true | DDH_real]  =  Pr[securityReductionRealGame = false]`

`ddhExpReal gen ℬ` and `securityReductionRealGame gp 𝒜` run the same sampling
and simulation; they differ only in their (negated bit) return. -/
lemma probOutput_ddhExpReal_securityReduction (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpReal securityReduction
  simpa [securityReductionRealGame, monad_norm] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRealGame (gen := gen) gp adversary))

/-- **Game `CKA^{isRandom = false}`**
`x₀ ←$ F`, run `𝒜` against `ckaSecurityImpl gp (ddhCKA F G gen)` with challenge bit `false`.
-/
noncomputable def securityExpRealGame (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  (simulateQ (ckaSecurityImpl gp false (ddhCKA F G gen)) adversary).run'
    (initGameState (.sendReady (x₀ • gen)) (.recvReady x₀))

/-- **Step (3) of the real branch.**
  `Pr[𝒜 = false ∣ securityExpFixedBit … false gp] = Pr[𝒜 = false | CKA^{isRandom = false}]`

Pure definitional unfolding of `securityExpFixedBit` at `ddhCKA F G gen` -/
lemma probOutput_securityExpFixedBit_false (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] =
    Pr[= false | securityExpRealGame (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpRealGame ddhCKA
  simp [initGameState]

/-- Random DDH branch reduction game. Samples `a, b, c ←$ F`, initializes the
reduction with `gA = a • gen`, and runs the reduction oracle stack with
`gB = b • gen` and independent `gT = c • gen`. The returned bit is the
adversary's bit before the reduction's final negation. -/
noncomputable def securityReductionRandGame (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let c ← $ᵗ F
  let s₀ ← reductionInitState gp gen (a • gen)
  (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run' s₀

/-- **Step (1) of the random branch.** Peel `ℬ`'s final `¬`:

  `Pr[ℬ = true | DDH_rand]  =  Pr[= false | securityReductionRandGame]`

`ddhExpRand gen ℬ` returns `!b'` where `b'` is the output of
`securityReductionRandGame`, so the probability of `true` on the left
equals the probability of `false` on the right by `probOutput_not_map`. -/
lemma probOutput_ddhExpRand_securityReduction (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= true | ddhExpRand gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRandGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpRand securityReduction
  simpa [securityReductionRandGame, monad_norm] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRandGame (gen := gen) gp adversary))

/-- **Game `CKA^{isRandom = true}`**
 `x₀ ←$ F`, run `𝒜` against `ckaSecurityImpl gp (ddhCKA F G gen)` with challenge bit
`true`. Same per-epoch sampling pattern as `CKA^{isRandom = false}`, but `challX`
outputs a uniform `outKey ←$ᵗ G` instead of the real key. -/
noncomputable def securityExpRandGame (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  (simulateQ (ckaSecurityImpl gp true (ddhCKA F G gen)) adversary).run'
    (initGameState (.sendReady (x₀ • gen)) (.recvReady x₀))

/-- **Step (3) of the random branch.** Fold the named endpoint game
back into the generic fixed-bit notation at `isRandom = true`:

  `Pr[= false | securityExpFixedBit ... true gp]
    = Pr[= false | securityExpRandGame gp 𝒜]`

Holds by unfolding both sides; the two games coincide definitionally
once `ddhCKA`'s `initKeyGen`/`initA`/`initB` are inlined. -/
lemma probOutput_securityExpFixedBit_true (gp : GameParams)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true gp] =
    Pr[= false | securityExpRandGame (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpRandGame ddhCKA
  simp [initGameState]

end ddhCKA
