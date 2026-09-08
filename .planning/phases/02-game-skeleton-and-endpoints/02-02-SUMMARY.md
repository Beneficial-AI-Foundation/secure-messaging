---
phase: 02-game-skeleton-and-endpoints
plan: 02
subsystem: crypto-proofs
tags: [lean4, vcvio, gcm, lazy-sampling, greedyLazy, consumeLazy, ind-cca]

# Dependency graph
requires:
  - phase: 02-game-skeleton-and-endpoints (02-01)
    provides: gcmGameSkeleton (QueryImpl builder), gcmTupleImpl/gcmTupleImplReject, game0/game1
  - phase: 01-structural-foundations
    provides: gcmEncode, ghash, ValidMsgLength, SampleableType instances
provides:
  - "game2: game1's tuple moved inside the oracles via greedyLazy gcmTupleImpl, run' (none, none)"
  - "game3: consumeLazy gcmTupleImplReject at hit = (fun t => t matches OEncrypt _), run' (none, none)"
  - "gcmTupleImplReject_indep: criterion-3 h_indep obligation, both non-hit branches close by rfl; passes DIRECTLY into probOutput_simulateQ_consumeLazy_run'_eq (verified by elaboration)"
  - "gcmRandRejectImpl: uniform-cipher + always-reject family, ignores its tuple argument everywhere"
  - "game4: consumeLazy gcmRandRejectImpl at the same hit/cache as game3 (Phase 5's shared sample site)"
affects: [02-03, 02-04, phase-3-greedy-hop, phase-4-forgery-bound, phase-5-otp-coupling]

# Tech tracking
tech-stack:
  added: []
  patterns: ["hit predicate spelled (fun t => t matches OEncrypt _) — `matches` already yields Bool, no decide wrapper; reuse verbatim at every consumeLazy site"]

key-files:
  created: []
  modified:
    - SecureMessaging/AEAD/FromGCM/Security/Games.lean

key-decisions:
  - "hit predicate spelled (fun t => t matches OEncrypt _) without a decide wrapper (matches elaborates to Bool directly); same term used verbatim in gcmTupleImplReject_indep, game3, game4"
  - "gcmTupleImplReject_indep non-hit branches close by plain rfl — 02-01 skeleton factoring confirmed sound, no escalation"
  - "unused binders underscore-prefixed (_prp/_hL/_a) + nolint unusedArguments, matching game1's EtM-encReduction pattern, to keep the no-new-warnings gate"

patterns-established:
  - "Lazy games take augmented state (Option C × Option τ) with empty cache (none, none); direct-passability of h_indep lemmas verified by a throwaway lake env lean elaboration before commit"

# Metrics
duration: 4min
completed: 2026-09-08
---

# Phase 02 Plan 02: Lazily-Sampled Games Summary

**game2 (greedyLazy), game3/game4 (consumeLazy at the encryption hit) plus the criterion-3 independence lemma gcmTupleImplReject_indep, whose non-hit branches close by rfl and which slots verbatim into probOutput_simulateQ_consumeLazy_run'_eq**

## Performance

- **Duration:** 4 min
- **Started:** 2026-09-08T19:19:13Z
- **Completed:** 2026-09-08T19:23:14Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments

- `game2`: game1's top-level tuple deferred to the first query via `greedyLazy gcmTupleImpl` (no side condition, live decrypt survives), state `(none, none)`.
- `gcmTupleImplReject_indep`: τ-independence of the reject family at every non-hit query, in the exact `h_indep` shape `probOutput_simulateQ_consumeLazy_run'_eq` demands. Both non-hit branches (`OUnif` = lifted unif handler, `ODecrypt` = `pure none` behind the challenge guard) closed by plain `rfl` — the design signal the plan watched for did not fire.
- `game3`: `consumeLazy gcmTupleImplReject` at `hit = (fun t => t matches OEncrypt _)`, empty cache.
- `gcmRandRejectImpl` + `game4`: uniform challenge ciphertext in the same `consumeLazy` shape at the same hit and cache, so Phase 5's per-query coupling lands at a shared sample site; the family ignores its tuple argument everywhere (its own h_indep is immediate).
- Direct passability verified by elaboration: `probOutput_simulateQ_consumeLazy_run'_eq gcmTupleImplReject (fun t => t matches OEncrypt _) gcmTupleImplReject_indep adv s` typechecks as-is (throwaway file, not committed).

## Task Commits

Each task was committed atomically:

1. **Task 1: game2 (greedyLazy) and game3 (consumeLazy) + h_indep** - `7e52506` (feat)
2. **Task 2: game4 (uniform challenge ciphertext)** - `e78a04c` (feat)

## Files Created/Modified

- `SecureMessaging/AEAD/FromGCM/Security/Games.lean` - added `game2`, `gcmTupleImplReject_indep`, `game3`, `gcmRandRejectImpl`, `game4` in `namespace GCM`; opened `OracleComp.ProgramLogic.Relational`; 253 lines, sorry-free, no warnings referencing the file.

## Decisions Made

- Hit predicate spelled `(fun t => t matches OEncrypt _)` — `matches` already elaborates to `Bool`, so the plan's optional `decide` wrapper is redundant; the identical term is used in the lemma, `game3`, and `game4` so downstream phases can pass `gcmTupleImplReject_indep` without any predicate conversion.
- Unused signature binders written `_prp`/`_hL`/`_a` with `@[nolint unusedArguments]` (the plan's "nolint if needed" allowance, matching `game1`'s established pattern) to keep the full build warning-clean.

## Deviations from Plan

None - plan executed exactly as written. (Binder underscore-prefixing and the hit-predicate spelling were choices the plan explicitly delegated, not deviations; no immutable or pinned statement was altered.)

## Issues Encountered

None. The statement-discipline tripwire (`rfl` failure on the non-hit branches) did not trigger — both closed definitionally on the first attempt, confirming the 02-01 skeleton factoring.

Pre-existing, out-of-scope build noise logged to `deferred-items.md`: flexible-simp linter warnings in `SCKA/OppUniKEM/Correctness/Invariant/RecvB.lean` and the known deliberate `sorry`s in `PRP/Defs.lean`.

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- 02-03 (bad-flag variants game2♭/game3♭) and 02-04 (endpoint lemmas incl. `game4_eq_rand`) can consume `game2`/`game3`/`game4` and `gcmTupleImplReject_indep` as-is.
- Phase 3's `game1 = game2` hop is a direct `probOutput_simulateQ_greedyLazy_run'_eq gcmTupleImpl` application; Phase 4's `consumeLazy` hop passes `gcmTupleImplReject_indep` verbatim (elaboration-verified).
- `uniformSample_prod_eq_bind` remains available for 02-04's dead-sample elimination in `game4_eq_rand`.

---
*Phase: 02-game-skeleton-and-endpoints*
*Completed: 2026-09-08*

## Self-Check: PASSED

- Games.lean, 02-02-SUMMARY.md: found
- Commits 7e52506, e78a04c: found
- Declarations game2, game3, game4, gcmRandRejectImpl, gcmTupleImplReject_indep: found
