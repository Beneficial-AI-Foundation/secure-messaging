---
phase: 07a-ghash-polynomial-form
plan: 04
subsystem: crypto
tags: [gcm, gfmul, adjoinroot, reflect, bitvec, fold-invariant, multiplicativity, lean]

# Dependency graph
requires:
  - phase: 07a-ghash-polynomial-form (plan 03)
    provides: reflectN / reflectN_apply / reflectN_xor / reflect_gfmulStep / vStep
  - phase: 07a-ghash-polynomial-form (plan 02)
    provides: boolToZMod2
  - phase: 07a-ghash-polynomial-form (plan 01)
    provides: nistPoly_natDegree
provides:
  - "GCM.gfmulStep : the named gfmul foldl body (z-update + vStep), definitionally gfmul's body"
  - "GCM.reflectN_zero : reflectN (0 : BitVec 128) = 0 (additive identity preserved)"
  - "GCM.gfmul_eq_foldl : gfmul x y = ((List.range 128).foldl (gfmulStep x) (0, y)).1 (rfl)"
  - "GCM.reflect_gfmul_aux : the dual fold invariant over List.range k (v- and z-accumulators)"
  - "GCM.reflect_gfmul : reflectN (gfmul x y) = reflectN x * reflectN y (criterion 1)"
  - "GCM.gfmul_eq_reflect_symm : gfmul x y = reflectN.symm (reflectN x * reflectN y)"
affects: [07a-05-ghash-eval, 07b]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "fold invariant peeled from the tail with List.range_succ + List.foldl_append (not head recursion): the last step applies the single-step lemma to the accumulator produced by the IH prefix"
    - "dual (conjunction) invariant so the z-accumulator can read the v-accumulator's value at the peeled step (the ⊕v term needs reflectN p.2 = reflectN y * root^k)"
    - "gfmulStep defined with its second component literally vStep p.2, so gfmul_eq_foldl closes by rfl and the succ step's .2 is defeq to vStep p.2 (change, not rw)"
    - "reflectN_zero via reflectN_apply + Finset.sum_eq_zero (each getMsbD 0 bit is false), avoiding the OfNat/0#w normalization mismatch that self-cancellation and BitVec.xor_zero tripped on"

key-files:
  created: []
  modified:
    - SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean

key-decisions:
  - "reflect_gfmul_aux stated WITHOUT the plan's k ≤ 128 hypothesis: the invariant holds unconditionally because reflect_gfmulStep is bit-index agnostic, so no bound is threaded through the induction (and an unused hypothesis would draw a linter warning)"
  - "reflectN_zero proved from reflectN_apply/Finset.sum_eq_zero, not the self-cancellation trick: reflectN_xor 0 0 leaves reflectN (0 ^^^ 0) whose 0#128 does not match BitVec.xor_zero's 0#w pattern under rw"
  - "base case done by change (not simp): simp normalized the foldl-nil .1 to reflectN 0#128, which reflectN_zero (stated over (0 : BitVec 128)) would not rewrite; an explicit change onto the (0 : BitVec 128) pair projection aligns the syntactic form"
  - "z-invariant kept as (coefficient-sum) * reflectN y with reflectN y on the RIGHT, matching reflect_apply's convention and reflect_gfmul's reflectN x * reflectN y target — no mul_comm detour at the k=128 specialization"

patterns-established:
  - "Pattern: lift a single-step reflect lemma across a List.range foldl by a dual invariant peeled with range_succ/foldl_append; the char-2 v-step and the coefficient-accumulating z-step share one induction"

# Metrics
duration: 3min
completed: 2026-09-08
---

# Phase 07a Plan 04: reflect_gfmul (criterion 1) Summary

**Closes Phase 7a criterion 1: `gfmul` is multiplication in `AdjoinRoot nistPoly` transported through `reflectN` — `reflectN (gfmul x y) = reflectN x * reflectN y` — proven by lifting plan 07a-03's single-step lemma across `gfmul`'s 128-step `List.range` fold with a dual loop invariant. CommRing-only, sorry-free, standard axioms only.**

## Performance

- **Duration:** 3 min
- **Started:** 2026-09-08T18:32:11Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments

- `gfmulStep x` names `gfmul`'s exact `foldl` body — `z ↦ z ⊕ v` gated on the multiplier bit `xᵢ`, `v ↦ vStep v` — so `gfmul_eq_foldl` (`gfmul x y = ((List.range 128).foldl (gfmulStep x) (0, y)).1`) holds by `rfl`.
- `reflectN_zero`: `reflectN` sends the XOR-identity to the ring `0` (the fold invariant's base case).
- `reflect_gfmul_aux`: the dual invariant over `List.range k` — after `k` steps the `v`-accumulator is `reflectN y * root^k` and the `z`-accumulator is `(∑_{i<k} boolToZMod2 xᵢ • root^i) * reflectN y`. Peeled from the tail with `List.range_succ` + `List.foldl_append`: the `v`-half advances one `reflect_gfmulStep` (`· root`), the `z`-half either extends the coefficient sum by the `i = k` term (bit set: `reflectN_xor` + `Finset.sum_range_succ`, and it reads the `v`-half's `reflectN y * root^k` for the `⊕ v` summand) or is unchanged (bit clear: new coefficient `0`).
- `reflect_gfmul` (criterion 1): the invariant at `k = 128`, where `∑_{i<128} boolToZMod2 xᵢ • root^i = reflectN x` via `reflectN_apply` (`nistPoly.natDegree = 128`) and `Fin.sum_univ_eq_sum_range`.
- `gfmul_eq_reflect_symm`: the multiplication-through-the-bijection form `gfmul x y = reflectN.symm (reflectN x * reflectN y)`, from `reflect_gfmul` + `Equiv.symm_apply_apply` — the rewrite plan 07a-05 and Phase 7b consume.

## Task Commits

1. **Task 1: gfmulStep, reflectN_zero, gfmul_eq_foldl, reflect_gfmul_aux** — `bdc48d9` (feat)
2. **Task 2: reflect_gfmul (criterion 1), gfmul_eq_reflect_symm** — `88b7f59` (feat)

## Files Modified

- `SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean` — appended the `gfmul` fold invariant and criterion-1 multiplicativity (now 357 lines).

## Decisions Made

- **No `k ≤ 128` hypothesis on `reflect_gfmul_aux`.** The plan's signature carried `hk : k ≤ 128`, but the invariant holds for every `k` (the single-step lemma is bit-index agnostic), so threading a bound is unnecessary and an unused binder would draw a linter warning. Specialization at `k = 128` needs no proof obligation.
- **`reflectN_zero` via the coordinate sum, not self-cancellation.** `reflectN_xor 0 0` gives `reflectN (0 ^^^ 0) = reflectN 0 + reflectN 0`, but `0 ^^^ 0`'s `0#128` did not match `BitVec.xor_zero`'s `0#w` pattern under `rw`. Proved instead by `reflectN_apply` + `Finset.sum_eq_zero` (every `getMsbD` bit of `0` is `false`).
- **Base case by `change`, not `simp`.** `simp` normalized the `foldl`-nil `.1` to `reflectN 0#128`, which `reflectN_zero` (stated over `(0 : BitVec 128)`) would not rewrite (`OfNat` vs `BitVec.ofNat` head). An explicit `change` onto the `(0 : BitVec 128)` pair projection aligns the syntactic form; the style linter also mandates `change` over goal-changing `show`.

## Deviations from Plan

Both criterion-1 artifacts (`reflect_gfmul`, `gfmul_eq_reflect_symm`) exist in `namespace GCM`, sorry-free and CommRing-only, with the fold peeled by `List.range_succ` + `List.foldl_append` as specified. Refinements within the plan's stated latitude:

- **[Plan latitude] Dropped the `k ≤ 128` hypothesis** (see Decisions) — the invariant is unconditional.
- **[Rule 1 - Bug] `reflectN_zero` proof method** switched from the plan's suggested self-cancellation to a coordinate-sum vanishing argument, because the `0 ^^^ 0` form does not match `BitVec.xor_zero` (`0#w` vs `OfNat` mismatch). Same statement, working proof.
- **[Plan latitude] Base case discharged by `change` + explicit `rw`** rather than `simp`, to sidestep the `0#128` / `(0 : BitVec 128)` normalization mismatch that blocked `reflectN_zero` from firing.

No auto-fixes beyond the above; no architectural changes; no authentication gates.

## Verification

- `lake build` (full workspace) exits 0; no warnings referencing `Polynomial.lean` (the two pre-existing `SecureMessaging/PRP/Defs.lean` `sorry` warnings are out of scope, untouched).
- `grep -rn "sorry\|native_decide\|Irreducible\|IsDomain\|instField\|GaloisField\|maxHeartbeats" …/Polynomial.lean`: only one hit, docstring prose ("`GaloisField`) is used or needed"), no code usage.
- `#print axioms` for `reflect_gfmul`, `gfmul_eq_reflect_symm`, `reflect_gfmul_aux`: `[propext, Classical.choice, Quot.sound]` — standard only, no `sorryAx`.
- `reflect_gfmul` is stated as `reflectN (gfmul x y) = reflectN x * reflectN y` — the exact criterion-1 identity.
- Fold induction uses `List.range_succ` + `List.foldl_append` (canonical tail peel), invoking `reflect_gfmulStep` at each step.

## Next Phase Readiness

- Plan 07a-05 (`reflect_ghash`, criterion 2) can rewrite each of `ghash`'s `foldl` steps with `reflect_gfmul` / `gfmul_eq_reflect_symm`: `ghash h blocks = blocks.foldl (fun y x => gfmul (y ^^^ x) h) 0`, so criterion 2 is another `foldl` argument over the polynomial evaluation, closed by the same `reflectN_xor` + `reflect_gfmul` combination.
- No blockers.

## Self-Check: PASSED

- FOUND: SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean
- FOUND commit bdc48d9 (Task 1)
- FOUND commit 88b7f59 (Task 2)
- FOUND: gfmulStep, reflectN_zero, gfmul_eq_foldl, reflect_gfmul_aux, reflect_gfmul, gfmul_eq_reflect_symm in namespace GCM

---
*Phase: 07a-ghash-polynomial-form*
*Completed: 2026-09-08*
