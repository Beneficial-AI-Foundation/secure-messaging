/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Security.ReductionRand.Bridge

/-!
# CKA from DDH — Security Proof

Security reduction from the Decisional Diffie-Hellman (DDH) assumption to
key-indistinguishability of the Continuous Key Agreement (CKA) construction,
following [ACD19, Theorem 3].
https://eprint.iacr.org/2018/1037.pdf

## Main result

**Theorem** (`ddhCKA.security`). *Let `F` be a finite field, let `G` be an
additive commutative group with an `F`-module structure, and let `gen : G` be
such that the scalar-multiplication map `fun x : F => x • gen` is bijective.
For every CKA adversary `𝒜` and
every choice of game parameters
`gp = ⟨challengeEpoch, ΔFS, ΔPCS, challengedParty⟩`
with `ΔFS = 1` and `ΔPCS = 2`, there is an explicit DDH adversary
`ℬ := securityReduction gp 𝒜` such that:*

  `ckaGuessAdvantage(ddhCKA F G gen, 𝒜, gp) ≤ ddhGuessAdvantage(gen, ℬ)`

*where `ckaGuessAdvantage(cka, 𝒜, gp) = | Pr[securityExp(cka, 𝒜, gp) = 1] − 1/2 |`
and `ddhGuessAdvantage(gen, ℬ) = | Pr[ddhExp(gen, ℬ) = 1] − 1/2 |`.*

*Note (cyclic group).* A particular instance of `(F, G)` satisfying the theorem
is the prime-field case: `(F, +)` and `(G, +)` are cyclic groups of order `p`
admitting an isomorphism `(F, +) ≅ (G, +)`.
Example: for `F = Zₚ` and prime `p`, both additive groups are cyclic of prime order `p`.

*Note (reduction efficiency - informal).* The adversary `ℬ := securityReduction gp 𝒜`
uses the CKA adversary `𝒜` as a subroutine and answers its CKA oracle queries using
the given DDH challenge `(gen, gA, gB, gT)`.
The complexity of the setup is `O(1)` and each of `𝒜`'s oracle queries
is answered making `O(1)` group operations.
Therefore,
- `time(ℬ) = time(𝒜) + O(q_𝒜)`, where `q_𝒜` is the number of CKA oracle queries made by `𝒜`.
- a negligible DDH advantage over a given adversary class translates to a negligible CKA advantage.

In the diagrams below, write `t* := challengeEpoch`.

### `ΔFS = 1`

`ΔFS = 1` in the main theorem means the adversary is allowed to corrupt
party `Q` only if `tQ ≥ t* + ΔFS`: one more action after the challenge epoch.

Illustration with `challengedParty = A` challenged at `tA = t*`:

```text
         A (challenged)                              B
         ──────────────                              ──
              │                                       │
              │                                       │ sendB: ...
              │                                       │ B stores y
              │◀──────── ρ = y•gen ────────────────── │
              │                                       │
 tA = t*  challA:                                     |
          z ←$ F                                      |
          A stores z                                  │
          key_A = z•ρ                                 │
          ρ' = z•gen                                  │
              │──────── ρ' ─────────────────────────▶ │
              │                                  tB++ │ recvB: ...
              │                                       │ B stores ρ' ∈ G
              │                                       │
              │                             tB = t*   │ sendB: x' ←$ F
              │                                       │ key_B = x'•ρ'
              │                                       │ B stores x'
              │◀──────── ρ'' = x'•gen ──────────────  │
 tA++     recvA                                       │
          key_A' = z•ρ'' = z•x'•gen                   │
          A stores ρ'' ∈ G                            │
          (z overwritten)                             │
              │                                       │
         ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
         allowCorrFS .A (tA ≥ t*+1)    allowCorrFS .B (tB ≥ t*+1)
         corruptA → ρ'' ∈ G      corruptB → x' ∈ F
```

With `ΔFS = 1`, corruption is delayed until the challenge scalars have been
overwritten: A no longer stores `z`, and B no longer stores `y`. The remaining
challenge transcript is `(gen, y•gen, z•gen)`, so hiding `z•y•gen` is the DDH
problem.

## Proof overview — reduction diagram (the constructed DDH adversary `ℬ`)

Assume given a CKA adversary `𝒜` that challenges exactly one party at epoch `t*`.
We show how to construct a DDH adversary `ℬ = securityReduction gp 𝒜`
that answers `𝒜`'s CKA oracle queries using the DDH challenge.

In the diagram below, we show the case where `𝒜` calls `O-Chall-A` at `tA = t*`.

The reduction `ℬ` is given as input: a DDH triple `(gen, gA, gB, gT)`
with `gA = a•gen`, `gB = b•gen`, and `gT = c•gen` where `c = a·b` (real) or `c` is uniform (rand).

`ℬ` maintains a CKA `GameState` and answers `𝒜`'s queries honestly except at two epochs:

* **Embedding epoch** (`O-Send-B` at `tB = t*−1`): instead of sampling `y ←$ F`,
  the reduction outputs `ρ = gA` and `keyB = xA•gA`, where `xA` is read
  from `state.stA` (A's scalar from its honest `O-Send-A` at `tA = t*−2`).
  Writes `stB := 0`, since the honest `y = a` is unknown to the reduction.

* **Challenge epoch** (`O-Chall-A` at `tA = t*`): instead of sampling `x ←$ F`,
  the reduction outputs `(gB, gT)`. Writes `stA := 0`, since the honest
  `x = b` is unknown to the reduction.

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

**Goal.** Show that the reduction perfectly simulates the honest CKA game on
each DDH branch, and assemble the two branch equivalences into the final
advantage bound:

```text
  (real)  Pr[ℬ=⊤ | DDH_real] = Pr[𝒜=⊥ | CKA_real]      -- securityReduction_real
  (rand)  Pr[ℬ=⊤ | DDH_rand] = Pr[𝒜=⊥ | CKA_rand]      -- securityReduction_rand
                     │
                     ▼   average over the `isRandom` bit + Pr[⊥] ≡ 0
                     │
  ckaGuessAdvantage(ddhCKA, 𝒜, gp)  ≤  ddhGuessAdvantage(gen, ℬ)
```
where
`CKA_real := securityExpFixedBit (ddhCKA F G gen) 𝒜 false gp` and
`CKA_rand := securityExpFixedBit (ddhCKA F G gen) 𝒜 true gp`
are the two endpoint games at fixed `isRandom` bit.

## Proof modules

```text
Mathematical statement                         Lean proof modules / lemmas
──────────────────────                         ───────────────────────────
Define ℬ = securityReduction gp 𝒜              ReductionGames
Define fixed real/rand branch games            securityReduction{Real,Rand}Game
                                               securityExpFixedBit

Move samples in/out of CKA oracles             GameOracles/Defs
honest_param_{real,rand} ≡ ckaSecurityImpl     GameOracles/PerQuery
                                               GameOracles/SimulateQ
                                               GameOracles/Step
                                               GameOracles/Bridge

DDH branch-independent query lemmas            ReductionCommon

DDH real branch simulates CKA_real             ReductionReal/RelStep
Pr[ℬ = true | DDH_real]                        ReductionReal/Bridge
  = Pr[𝒜 = false | CKA_real]                   securityReduction_real

DDH random branch simulates CKA_rand           ReductionRand/RelStep
Pr[ℬ = true | DDH_rand]                        ReductionRand/EagerHonestBridge
  = Pr[𝒜 = false | CKA_rand]                   ReductionRand/Bridge
                                               securityReduction_rand

Combine real/rand branch identities            security_le_ddh_plus_failGap
and discharge the fixed-bit failure gap        security
```

For each branch, we have:

```text
DDH branch game for ℬ
  │  ReductionCommon + Reduction{Real,Rand}/RelStep + Bridge
  ▼
parameterized honest CKA oracle stack
  │  GameOracles/Step + Bridge
  ▼
ordinary fixed-bit CKA experiment
```

The `ToVCVio` helper lemmas provide the generic probability and `simulateQ`
facts used across these modules.
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

section BranchLemmas
variable [Inhabited F]
variable [Fintype G]

omit [Inhabited F] [Fintype G] in
/-- **Real-branch lemma.** Proves that the reduction `ℬ = securityReduction gp 𝒜`
satisfies the real DDH branch identity:
`Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA_real]`. -/
lemma securityReduction_real (gp : GameParams)
  (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  rw [probOutput_ddhExpReal_securityReduction, probOutput_securityExpFixedBit_false]
  exact probOutput_securityReductionRealGame_eq_honestFalse
    (gen := gen) gp hΔFS hΔPCS adversary

omit [Inhabited F] [Fintype G] in
/-- **Random-branch lemma.** Proves that the reduction `ℬ = securityReduction gp 𝒜`
satisfies the random DDH branch identity:
`Pr[ℬ = true | DDH_rand] = Pr[𝒜 = false | CKA_rand]`. -/
lemma securityReduction_rand (gp : GameParams)
  (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[= true | ddhExpRand gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true gp] := by
  rw [probOutput_ddhExpRand_securityReduction, probOutput_securityExpFixedBit_true]
  exact probOutput_securityReductionRandGame_eq_honestTrue
    (gen := gen) gp hΔFS hΔPCS hg adversary

/-! ### Main security theorems

Averaging the branch lemmas over `isRandom` yields

  `Adv_secCKA(𝒜) ≤ Adv_DDH(ℬ) + ΔFail/2`        (`security_le_ddh_plus_failGap`),

where `ΔFail := |Pr[⊥ | CKA_real] − Pr[⊥ | CKA_rand]|`. The two fixed-bit games
never fail, so `ΔFail = 0` (`probFailure_securityExpFixedBit_eq`), tightening
this to

  `Adv_secCKA(𝒜) ≤ Adv_DDH(ℬ)`        (`security`, `ddhCKA_security`).
-/

/-- `ΔFail := |Pr[⊥ | CKA_real] − Pr[⊥ | CKA_rand]|`. -/
private noncomputable def securityFailGap
    (gp : GameParams) (adversary : CKAAdversary (CKAState F G) G G F) : ℝ :=
  |(Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
    (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal|

omit [Inhabited F] [Fintype G] in
/-- **Unconditional DDH-CKA security bound.**

For every CKA adversary, the CKA guess-advantage is bounded by the DDH guess-advantage
of the reduction plus half the failure-probability gap between the two fixed-bit games:

  `ckaGuessAdvantage(ddhCKA, 𝒜, gp) ≤ ddhGuessAdvantage(gen, securityReduction gp 𝒜) + ΔFail / 2`

where `ΔFail := |Pr[⊥ | CKA_real] - Pr[⊥ | CKA_rand]|`. -/
lemma security_le_ddh_plus_failGap (gp : GameParams)
  (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    ckaGuessAdvantage (ddhCKA F G gen) adversary gp ≤
      ddhGuessAdvantage gen (securityReduction gp adversary) +
      securityFailGap (gen := gen) gp adversary / 2 := by
  -- Branch lemmas (ℬ's guess distribution on each DDH branch ↔ 𝒜's `=false` output)
  have hReal := securityReduction_real (gen := gen) gp hΔFS hΔPCS adversary
  have hRand := securityReduction_rand (gen := gen) gp hΔFS hΔPCS hg adversary
  -- Advantage decomposition identities on each side
  have hDdh := ddhExp_probOutput_sub_half (F := F) gen
    (securityReduction (F := F) (G := G) gp adversary)
  have hSec := securityExp_toReal_sub_half (ddhCKA F G gen) adversary gp
  have hRealR := congrArg ENNReal.toReal hReal
  have hRandR := congrArg ENNReal.toReal hRand
  -- `Pr[=true] + Pr[=false] + Pr[⊥] = 1` for each fixed-bit game
  have hSum (b : Bool) :
      (Pr[= true | securityExpFixedBit (ddhCKA F G gen) adversary b gp]).toReal +
      (Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary b gp]).toReal +
      (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary b gp]).toReal = 1 := by
    have h := probOutput_false_add_true
      (mx := securityExpFixedBit (ddhCKA F G gen) adversary b gp)
    have hT := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (by simp) (by simp),
        ENNReal.toReal_sub_of_le (by simp) (by simp), ENNReal.toReal_one] at hT
    linarith
  -- Key algebraic identity: sec = ddh + ΔFail/2
  have hKeyEq :
      (Pr[= true | securityExp (ddhCKA F G gen) adversary gp]).toReal - 1 / 2 =
      ((Pr[= true | ddhExp gen
        (securityReduction (F := F) (G := G) gp adversary)]).toReal - 1 / 2) +
      ((Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
       (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal) / 2 := by
    rw [hDdh, hSec, hRealR, hRandR]
    linarith [hSum true, hSum false]
  -- Local triangle inequality: |x + y| ≤ |x| + |y|
  have htri : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := fun x y =>
    abs_le.mpr ⟨by linarith [neg_le_abs x, neg_le_abs y],
                 by linarith [le_abs_self x, le_abs_self y]⟩
  -- Align the `/2` inside the absolute value with `failGap / 2`
  have habs' :
      |((Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
        (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal) / 2| =
      securityFailGap (gen := gen) gp adversary / 2 := by
    unfold securityFailGap
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have habs :
      |(Pr[= true | securityExp (ddhCKA F G gen) adversary gp]).toReal - 1 / 2| ≤
      |(Pr[= true | ddhExp gen
        (securityReduction (F := F) (G := G) gp adversary)]).toReal - 1 / 2| +
      securityFailGap (gen := gen) gp adversary / 2 := by
    rw [hKeyEq]
    calc |((Pr[= true | ddhExp gen
            (securityReduction (F := F) (G := G) gp adversary)]).toReal - 1 / 2) +
            ((Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
             (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal) / 2|
        ≤ _ + _ := htri _ _
      _ = _ := by rw [habs']
  unfold ckaGuessAdvantage ddhGuessAdvantage
  exact habs

omit [Inhabited F] [Fintype G] in
/-- The failure probability of `securityExpFixedBit` does not depend on the challenge bit. -/
private lemma probFailure_securityExpFixedBit_eq
    (gp : GameParams) (adversary : CKAAdversary (CKAState F G) G G F) :
    Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp] =
    Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  simp

omit [Inhabited F] [Fintype G] in
/-- **Main theorem: security of CKA-from-DDH reduced to the DDH security assumption**

For any CKA adversary `𝒜`, the CKA advantage of `𝒜` is bounded by the DDH
advantage of the reduction `ℬ = securityReduction gp 𝒜`:

  `ckaGuessAdvantage(ddhCKA, 𝒜, gp) ≤ ddhGuessAdvantage(gen, ℬ)`
-/
-- ANCHOR: security
theorem security (gp : GameParams)
  (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    ckaGuessAdvantage (ddhCKA F G gen) adversary gp ≤
      ddhGuessAdvantage gen (securityReduction gp adversary)
-- ANCHOR_END: security
    := by
  have hBound := security_le_ddh_plus_failGap (gen := gen) gp hΔFS hΔPCS hg adversary
  have hFail := probFailure_securityExpFixedBit_eq (F := F) (G := G) (gen := gen) gp adversary
  have hGap : securityFailGap (gen := gen) gp adversary = 0 := by
    unfold securityFailGap
    have : (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal =
        (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal :=
      (congrArg ENNReal.toReal hFail).symm
    rw [this]; simp
  linarith [hBound, hGap]

end BranchLemmas

end ddhCKA
