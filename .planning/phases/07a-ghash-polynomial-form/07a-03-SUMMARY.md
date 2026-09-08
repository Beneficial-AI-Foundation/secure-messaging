---
phase: 07a-ghash-polynomial-form
plan: 03
subsystem: crypto
tags: [gcm, ghash, gfmul, adjoinroot, reflect, bitvec, multiplicativity, lean]

# Dependency graph
requires:
  - phase: 07a-ghash-polynomial-form (plan 01)
    provides: nistPoly_monic, nistPoly_natDegree, nistPoly_root_pow
  - phase: 07a-ghash-polynomial-form (plan 02)
    provides: AdjoinRootReflect.reflect / reflect_apply / reflect_xor / boolToZMod2
provides:
  - "GCM.reflectN : BitVec 128 ≃ AdjoinRoot nistPoly (reflect nistPoly_monic + BitVec.cast bridge)"
  - "GCM.reflectN_apply : coordinate=coefficient over Fin 128 (transport discharged once)"
  - "GCM.reflectN_xor : XOR additivity specialized to BitVec 128"
  - "GCM.reflect_gcmReductionConst : reflectN R = root^7 + root^2 + root + 1"
  - "GCM.getLsbD0_eq_getMsbD127 : the reduction bit is the x^127 coefficient"
  - "GCM.reflectN_mul_root : reflectN v * root = reflectN (v>>>1) + v₁₂₇ • root^128"
  - "GCM.vStep : the exact v-update of gfmul's foldl body"
  - "GCM.reflect_gfmulStep : reflectN (vStep v) = reflectN v * root (the phase crux)"
affects: [07a-04-gfmul-fold, 07a-05-ghash-eval, 07b]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "reflectN via structure literal (toFun = reflect ∘ BitVec.cast) so ⇑reflectN x is defeq to reflect _ (x.cast _); the natDegree=128 transport is discharged once in reflectN_apply and never fought again"
    - "coordinate sum peeling: Fin.sum_univ_castSucc (top term) vs Fin.sum_univ_succ (index 0) on the two sides of the shift/multiply identity — both collapse to a shared ∑ Fin 127"
    - "single per-index getMsbD decides for the reduction constant (allowed); no full-128-bit decide, bit reasoning is a general getMsbD i argument"
    - "heavy coordinate lemmas kept top-level (reflectN_mul_root_left / reflectN_ushiftRight_eq) to fit the default heartbeat budget — never bump maxHeartbeats (repo convention)"

key-files:
  created: []
  modified:
    - SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean

key-decisions:
  - "reflectN defined as an Equiv structure literal using BitVec.cast on both sides (not `▸`/`_root_.cast`), so getMsbD_cast/xor_cast reduce cleanly and ⇑reflectN unfolds by defeq"
  - "reflectN_apply stated over Fin 128 with x.getMsbD (transport to nistPoly.natDegree done via Fintype.sum_equiv (finCongr nistPoly_natDegree)) — the single primitive all downstream bit reasoning reads off"
  - "reduction bit handled by branching on v.getMsbD 127 (= v.getLsbD 0 via getLsbD0_eq_getMsbD127); avoids rewriting inside the if-condition's Decidable instance"
  - "reflect_gfmulStep proved from reflectN_mul_root + reflect_gcmReductionConst + nistPoly_root_pow only: the ⊕R branch supplies root^128, which the shift's escaped-coefficient term duplicates, and 2•root^128 = 0 in char 2 closes both branches"

patterns-established:
  - "Pattern: prove the shift-vs-multiply identity generically (reflectN_mul_root) and finish the step lemma by a two-case boolean split, not per-bit"

# Metrics
duration: 19min
completed: 2026-09-08
---

# Phase 07a Plan 03: reflect_gfmulStep Summary

**Proves the phase's crux: one iteration of `gfmul`'s `v`-update (`vStep`) equals multiplication by `root` in `AdjoinRoot nistPoly` — `reflectN (vStep v) = reflectN v * root` — after instantiating the reflected equivalence at `nistPoly` (`reflectN`) and reflecting the reduction constant `R` to `root⁷+root²+root+1`. CommRing-only, sorry-free, standard axioms only.**

## Performance

- **Duration:** 19 min
- **Started:** 2026-09-08T18:05:50Z
- **Completed:** 2026-09-08T18:25:44Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments

- `reflectN : BitVec 128 ≃ AdjoinRoot nistPoly` instantiates the general `reflect nistPoly_monic`, bridging the `nistPoly.natDegree = 128` gap with `BitVec.cast` on both `Equiv` legs.
- `reflectN_apply` expresses `reflectN` as the `Fin 128` coordinate sum with `getMsbD` on the concrete `BitVec 128`; the `natDegree`-transport is discharged once via `Fintype.sum_equiv (finCongr nistPoly_natDegree)`, so every downstream lemma reads bits off `getMsbD` and never fights the cast.
- `reflectN_xor` (XOR additivity, from `BitVec.xor_cast` + `reflect_xor`).
- `reflect_gcmReductionConst`: `R = 0xE1 <<< 120` reflects (MSB ↔ x⁰) to `root⁷+root²+root+1` — proven by cutting the 128-term coordinate sum to `range 8` (generic vanishing above) and evaluating the 8 top-byte bits with single per-index `decide`s. No full-width `decide`.
- `getLsbD0_eq_getMsbD127`: the arithmetic LSB `getLsbD 0` equals the `x¹²⁷` coefficient `getMsbD 127`.
- `reflectN_mul_root`: `reflectN v * root = reflectN (v>>>1) + v₁₂₇ • root¹²⁸` — the shift and the multiply share the same reindex `xⁱ ↦ xⁱ⁺¹`; multiplying peels the top term into `root¹²⁸`, the shift drops it.
- `reflect_gfmulStep` (the crux): a two-case boolean split on `v.getMsbD 127`. In the reduce branch the `⊕R` contributes `root¹²⁸` (via `reflect_gcmReductionConst` + `nistPoly_root_pow`) which exactly duplicates the escaped-coefficient term; `2•root¹²⁸ = 0` in char 2 makes both branches equal `reflectN v * root`.

## Task Commits

1. **Task 1: reflectN, reflectN_apply, reflectN_xor, reflect_gcmReductionConst** — `004866b` (feat)
2. **Task 2: getLsbD0_eq_getMsbD127, reflectN_mul_root, vStep, reflect_gfmulStep** — `ebcfbf8` (feat)

## Files Modified

- `SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean` — appended the reflected-equivalence instantiation and the single-step multiplicativity crux (now 255 lines).

## Decisions Made

- **`reflectN` as an `Equiv` structure literal** (`toFun := fun x => reflect nistPoly_monic (x.cast nistPoly_natDegree.symm)`), not `nistPoly_natDegree ▸ reflect nistPoly_monic`. The `▸`/`_root_.cast` form leaves an opaque `Eq.rec` at use sites; the `BitVec.cast` form reduces through `getMsbD_cast`/`xor_cast` and `⇑reflectN x` is defeq to `reflect _ (x.cast _)`, so `reflectN_apply`/`reflectN_xor` open with a `change` and then use the general lemmas directly.
- **Coordinate-sum peeling with two different Fin lemmas.** `reflectN v * root` peels its top term with `Fin.sum_univ_castSucc` (giving `+ v₁₂₇•root¹²⁸`); `reflectN (v>>>1)` peels its index-0 term with `Fin.sum_univ_succ` (which vanishes). Both land on the shared `∑ i : Fin 127, vᵢ • root^(i+1)`, so `reflectN_mul_root` is `rw [left, right]`.
- **Branch on `getMsbD 127`, not on the if-condition.** `getLsbD0_eq_getMsbD127` converts the `if v.getLsbD 0` guard to the reduction-coefficient view without rewriting inside the `if`'s `Decidable` instance (which trips the motive check).

## Deviations from Plan

None functionally — all three required artifacts (`reflectN`, `reflect_gcmReductionConst`, `reflect_gfmulStep`) exist in `namespace GCM`, sorry-free and CommRing-only. Implementation refinements within the plan's stated latitude:

- **[Plan latitude] `reflectN` exposed with `reflectN_apply` characterization** rather than the raw `▸` cast, exactly as the plan offered ("instead expose the `natDegree`-indexed form plus a `reflectN_apply`/`getMsbD` characterization lemma so downstream proofs never fight the transport").
- **[Plan latitude] `reflect_gcmReductionConst` sum-collapse** done via `Fin.sum_univ_eq_sum_range` → `Finset.sum_subset` (to `range 8`) → `Finset.sum_range_succ`, with per-index `decide` only on the 8 top-byte bits — matching the plan's "establish a clean `getMsbD` characterization … `decide` on individual small-index bits is fine, the full 128-bit `decide` is NOT".
- **[Rule 3 - Blocking] Two coordinate lemmas pulled to top level.** Inline `have`s for the shift/multiply coordinate forms overran the default heartbeat budget; per repo convention (never bump `maxHeartbeats`) they became the top-level `reflectN_mul_root_left` / `reflectN_ushiftRight_eq`. `set_option maxRecDepth 4000` (allowed, as in 07a-01) is used for the `root^128` normalization.

## Verification

- `lake build` (full workspace, 3120 jobs) exits 0; module `SecureMessaging.AEAD.FromGCM.Security.Polynomial` builds with no warnings referencing it.
- `grep -n "sorry\|native_decide\|maxHeartbeats\|instField\|GaloisField"` on the file: empty (matches for `Irreducible`/`IsDomain` are docstring prose only, no code usage).
- No full-128-bit `decide`; bit reasoning is a general `getMsbD i` argument. The reduction-constant bits use 8 single-index `decide`s.
- `#print axioms GCM.reflect_gfmulStep` and `GCM.reflect_gcmReductionConst`: `[propext, Classical.choice, Quot.sound]` — standard only, no `sorryAx`.
- Dependencies consumed as required: `reflect_apply`/`reflect_xor` (07a-02) via `reflectN_apply`/`reflectN_xor`; `nistPoly_root_pow` (07a-01) in `reflect_gfmulStep`.

## Issues Encountered

- Inline `have` coordinate lemmas hit the 200000-heartbeat limit (timeout at `congr 1` / whole-lemma execution); resolved by splitting into top-level lemmas and replacing `congr 1` with `simp only [smul_mul_assoc, ← pow_succ]` + one `Fin.sum_univ_castSucc` rewrite (no structural congruence whnf).
- `simp` left `if (false = true) then 1 else 0` unreduced after rewriting bits to `false`; closed by decided `boolToZMod2 true = 1` / `boolToZMod2 false = 0` haves.
- `Fin.coe_castSucc` is deprecated → `Fin.val_castSucc`.

## Next Phase Readiness

- Plan 07a-04 (`gfmul` fold invariant → criterion 1) can consume `reflect_gfmulStep` (v-component step) and `reflectN_xor` (z-component accumulation) inside a `List.range_succ` / `List.foldl_append` induction over `gfmul`'s 128-step fold. `vStep` is stated to match the foldl body's second component verbatim.
- No blockers.

## Self-Check: PASSED

- FOUND: SecureMessaging/AEAD/FromGCM/Security/Polynomial.lean
- FOUND commit 004866b (Task 1)
- FOUND commit ebcfbf8 (Task 2)
- FOUND: reflectN, reflectN_apply, reflect_gcmReductionConst, reflect_gfmulStep in namespace GCM

---
*Phase: 07a-ghash-polynomial-form*
*Completed: 2026-09-08*
