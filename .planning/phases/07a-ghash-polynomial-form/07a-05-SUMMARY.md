---
phase: 07a-ghash-polynomial-form
plan: 05
subsystem: crypto
tags: [gcm, ghash, adjoinroot, reflect, polynomial, horner, reversed-block, lean]

# Dependency graph
requires:
  - phase: 07a-ghash-polynomial-form (plan 04)
    provides: reflect_gfmul / gfmul_eq_reflect_symm / reflectN_zero
  - phase: 07a-ghash-polynomial-form (plan 02)
    provides: reflectN_xor
  - phase: 07a-ghash-polynomial-form (plan 03)
    provides: reflectN / reflectN_apply
  - phase: 01-structural-foundations
    provides: gcmEncode_tail_distinct (reversed-block index convention)
provides:
  - "GCM.reflect_ghash_foldl_gen : ghash's fold reflects to the Horner fold in AdjoinRoot nistPoly (any seed)"
  - "GCM.reflect_ghash_foldl : the Horner fold at seed 0"
  - "GCM.horner_foldl_eq_sum : Horner fold = sum reflectN(reverse[i]) * H^(i+1)"
  - "GCM.reflect_ghash : criterion 2 (sum form), reversed-block indexed, zero constant term"
  - "GCM.ghashPoly : the block-coefficient polynomial in (AdjoinRoot nistPoly)[X]"
  - "GCM.reflect_ghash_eval : reflectN (ghash h blocks) = (ghashPoly blocks).eval (reflectN h)"
  - "GCM.ghashPoly_coeff_zero : (ghashPoly blocks).coeff 0 = 0 (zero constant term)"
  - "GCM.ghashPoly_natDegree_le : natDegree (ghashPoly blocks) <= blocks.length (maxBlocks bound)"
affects: [07b]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "seed-generalized foldl induction (generalizing y) so the accumulator can vary at each step; specialize seed 0 via reflectN_zero"
    - "List.reverseRecOn (append-at-end induction) to align the foldl's left-to-right accumulation with reversed-block indexing: appending b multiplies by H and prepends b at reverse index 0"
    - "Horner-to-sum via Finset.sum_range_succ' (peel i=0) + Finset.sum_mul + mul_assoc + pow_succ"
    - "Polynomial packaging via eval_finsetSum / finsetSum_coeff / coeff_C_mul / coeff_X_pow (renamed from eval_finset_sum / finset_sum_coeff)"

key-files:
  created: []
  modified:
    - SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean

key-decisions:
  - "reversed-block indexing (locked design note): coefficient of h^(i+1) is blocks.reverse[i], matching Encoding.lean's gcmEncode_tail_distinct docstring verbatim, so Phase 7b transport is index-for-index"
  - "horner_foldl_eq_sum proven by List.reverseRecOn (append-singleton) rather than head induction: appending a block at the end multiplies the whole accumulator by H (raising every power) and adds reflectN b * H^1 — the reverse list gaining b at index 0 — so the reindex is a single Finset.sum_range_succ' peel plus sum_mul/mul_assoc/pow_succ"
  - "seed generalized in reflect_ghash_foldl_gen (generalizing y): the foldl accumulator changes every step, so the induction needs an arbitrary seed reflecting pointwise; the actual seed 0 is discharged once via reflectN_zero"
  - "ghashPoly natDegree bound proven (not just noted): (natDegree_C_mul_le).trans (natDegree_X_pow_le).trans omega, giving the maxBlocks degree Phase 7b's root count consumes"

patterns-established:
  - "Pattern: lift a per-step reflect identity across ghash's foldl by a seed-generalized induction, then reassociate the Horner accumulation into a reversed-index sum with reverseRecOn"

# Metrics
duration: 4min
completed: 2026-09-08
---

# Phase 07a Plan 05: reflect_ghash (criterion 2) Summary

**Closes Phase 7a criterion 2: `ghash h blocks` is evaluation of the reversed-block-coefficient polynomial at `reflectN h` with zero constant term — `ghash h [X₁,…,X_m] = X₁·hᵐ ⊕ ⋯ ⊕ X_m·h` — transported through `reflectN` and built on plan 07a-04's `reflect_gfmul`. Reversed-block indexed to match `Encoding.lean`'s `gcmEncode_tail_distinct` for Phase 7b. CommRing-only, sorry-free, standard axioms only. With criterion 1 (07a-04) this lands both Phase 7a deliverables (criterion 3 gate: `lake build` green).**

## Performance

- **Duration:** 4 min
- **Started:** 2026-09-08T18:41:56Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments

- `reflect_ghash_foldl_gen` / `reflect_ghash_foldl`: `ghash`'s `foldl (fun y x => gfmul (y ^^^ x) h) 0` reflects to the Horner fold `foldl (fun acc x => (acc + reflectN x) * reflectN h) 0` in `AdjoinRoot nistPoly`. Seed-generalized induction, each step `reflect_gfmul` (07a-04) + `reflectN_xor` (07a-02); the seed `0` closed by `reflectN_zero` (07a-04).
- `horner_foldl_eq_sum`: the Horner fold unrolls to `∑_{i<m} reflectN (blocks.reverse[i]) * H^(i+1)`, proven by `List.reverseRecOn` — appending a block `b` multiplies the accumulator by `H` (raising every power) and adds `reflectN b · H¹`, matching the reversed list gaining `b` at index `0`. Reindex: `Finset.sum_range_succ'` + `Finset.sum_mul` + `mul_assoc` + `pow_succ`.
- `reflect_ghash` (criterion 2, sum form): `reflectN (ghash h blocks) = ∑_{i<m} reflectN (blocks.reverse[i]) * (reflectN h)^(i+1)`. Lowest power `h¹`, so the constant term is zero; coefficient of `h^(i+1)` is `blocks.reverse[i]`.
- `ghashPoly` + `reflect_ghash_eval`: the explicit `Polynomial (AdjoinRoot nistPoly)` `∑ C (reflectN (reverse[i])) * X^(i+1)`, with `reflectN (ghash h blocks) = (ghashPoly blocks).eval (reflectN h)` via `eval_finsetSum`/`eval_mul`/`eval_pow`/`eval_C`/`eval_X`.
- `ghashPoly_coeff_zero`: `(ghashPoly blocks).coeff 0 = 0` (every summand `C c · X^(i+1)`, `i+1 ≥ 1`) — the explicit zero-constant-term record.
- `ghashPoly_natDegree_le`: `natDegree (ghashPoly blocks) ≤ blocks.length` — the `maxBlocks` degree bound Phase 7b's root count consumes.

## Task Commits

1. **Task 1: reflect_ghash_foldl_gen, reflect_ghash_foldl** — `9f6db24` (feat)
2. **Task 2: horner_foldl_eq_sum, reflect_ghash, ghashPoly, reflect_ghash_eval, ghashPoly_coeff_zero, ghashPoly_natDegree_le** — `fa2981d` (feat)

## Files Modified

- `SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean` — appended criterion 2 (`ghash` as polynomial evaluation) after criterion 1 (now 477 lines).

## Decisions Made

- **Reversed-block indexing (locked design note).** The sum is stated over `blocks.reverse` so the coefficient of `h^(i+1)` is `blocks.reverse[i]`, matching `Encoding.lean`'s `gcmEncode_tail_distinct` docstring verbatim — Phase 7b's transport of the tail-distinctness is then index-for-index, with no re-derivation.
- **`List.reverseRecOn`, not head induction.** Appending a block at the end multiplies the whole accumulator by `H` and adds `reflectN b · H¹`, which lines up cleanly with the reversed list gaining `b` at index `0`. Head induction would fight the power bookkeeping (every existing coefficient's power rises). The reindex is a single `Finset.sum_range_succ'` peel.
- **Seed generalized in `reflect_ghash_foldl_gen`.** `ghash`'s `foldl` accumulator changes at every step, so the induction needs an arbitrary seed that reflects pointwise; the actual seed `0` is discharged once via `reflectN_zero`.
- **`ghashPoly_natDegree_le` proven, not just noted.** The plan mentioned the `natDegree ≤ blocks.length` bound as a "note"; it is delivered as a lemma (`natDegree_C_mul_le` ∘ `natDegree_X_pow_le` ∘ `omega`) since Phase 7b's root count consumes exactly this `maxBlocks` degree.

## Deviations from Plan

Both criterion-2 deliverables and all four required artifacts (`reflect_ghash`, `ghashPoly`, `reflect_ghash_eval`, `ghashPoly_coeff_zero`) exist in `namespace GCM`, sorry-free and CommRing-only. Refinements within the plan's stated latitude:

- **[Plan latitude] Added `reflect_ghash_foldl_gen`** (seed-generalized helper) so the Task 1 induction goes through; `reflect_ghash_foldl` (the plan's named lemma, seed 0) follows immediately. The plan explicitly allowed "a `foldl` invariant".
- **[Plan latitude] Added `horner_foldl_eq_sum`** as a standalone Horner-to-sum lemma over an abstract `H`, keeping `reflect_ghash` a three-rewrite composition (`unfold ghash` + `reflect_ghash_foldl` + `horner_foldl_eq_sum`).
- **[Rule 3 - Blocking] Renamed lemmas.** `eval_finset_sum` → `Polynomial.eval_finsetSum` and `finset_sum_coeff` → `Polynomial.finsetSum_coeff` (both deprecated aliases as of 2026-04-08 in the pinned Mathlib); using the new names avoids deprecation warnings ("no new warnings" gate).
- **[Plan latitude] Added `ghashPoly_natDegree_le`** — the `maxBlocks` degree bound stated as a "note" is delivered as a proven lemma for Phase 7b.

No architectural changes; no authentication gates.

## Verification

- `lake build` (full workspace, 3120 jobs) exits 0; no warning references `Polynomial.lean` (the two pre-existing `SecureMessaging/PRP/Defs.lean` `sorry` warnings and the `SCKA/OppUniKEM/…/RecvB.lean` flexible-linter info are out of scope, untouched).
- `grep -rn "sorry\|axiom\|native_decide\|Irreducible\|IsDomain\|instField\|GaloisField" …/Polynomial.lean`: only docstring prose hits (lines 28, 29, 75, 339 — "no irreducibility / `Field` / `IsDomain`"), no code usage.
- `#print axioms` for `reflect_ghash`, `reflect_ghash_eval`, `ghashPoly_coeff_zero`, `ghashPoly_natDegree_le`, `reflect_ghash_foldl`: `[propext, Classical.choice, Quot.sound]` — standard only, no `sorryAx`.
- `reflect_ghash` is built from `reflect_gfmul` (07a-04) + `reflectN_xor` (07a-02), not by re-deriving multiplication.
- Evaluation form's lowest power is `h¹` (zero constant term via `ghashPoly_coeff_zero`); coefficient of `h^(i+1)` is `blocks.reverse[i]`, matching `Encoding.lean`'s reversed-index docstring for Phase 7b.

## Next Phase Readiness

- Phase 7a is complete: criterion 1 (`reflect_gfmul`, 07a-04) and criterion 2 (`reflect_ghash` / `ghashPoly`, this plan) both landed, `lake build` green with no `sorry` (criterion 3 gate).
- Phase 7b transports Phase 1's `gcmEncode_tail_distinct` through `ghashPoly`: a differing reversed position gives a nonzero difference polynomial of degree `≤ blocks.length` (`ghashPoly_natDegree_le`) with zero constant term (`ghashPoly_coeff_zero`), immune to any constant offset `Δ`. Irreducibility enters there (for the root count over the field), not here.
- No blockers.

## Self-Check: PASSED

- FOUND: SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean
- FOUND commit 9f6db24 (Task 1)
- FOUND commit fa2981d (Task 2)
- FOUND: reflect_ghash_foldl_gen, reflect_ghash_foldl, horner_foldl_eq_sum, reflect_ghash, ghashPoly, reflect_ghash_eval, ghashPoly_coeff_zero, ghashPoly_natDegree_le in namespace GCM

---
*Phase: 07a-ghash-polynomial-form*
*Completed: 2026-09-08*
</content>
</invoke>
