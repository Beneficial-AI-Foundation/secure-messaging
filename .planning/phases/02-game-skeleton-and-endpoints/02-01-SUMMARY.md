---
phase: 02-game-skeleton-and-endpoints
plan: 01
subsystem: crypto
tags: [gcm, aead, ind-cca, game-hopping, queryimpl, vcvio, lean]

# Dependency graph
requires:
  - phase: 01-structural-foundations
    provides: gcmEncode, gcmEncryptSpec/gcmDecryptSpec, gcmOneTimeAEAD, keystream/OTP bricks
  - phase: none (existing EtM machinery)
    provides: etmGameSkeleton shape, oracleUnif, aeadOneTimeCCASpec, LazySampling impl-family API
provides:
  - "GCM.gcmGameSkeleton : OracleSpec-polymorphic QueryImpl builder (unifImpl + encImpl + decImpl) over StateT (Option (BitVec L x BitVec 128)) (OracleComp spec)"
  - "GCM.gcmTupleImpl : LIVE per-tuple impl family, tuple (H, mask, ks) with ks : BitVec L"
  - "GCM.gcmTupleImplReject : REJECT per-tuple impl family (decryptResp = pure none)"
  - "GCM.game0 : real cipher, key sampled outside skeleton, state Option C"
  - "GCM.game1 : top-level uniform tuple + gcmTupleImpl (eager form for greedyLazy)"
  - "criterion-7 instance pins as CI examples (SampleableType/DecidableEq/Fintype)"
affects: [02-02, 02-03, 02-04, phase-3, phase-4, phase-5]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "skeleton returns a QueryImpl (not simulateQ...run'): lazy-sampling lemmas take implFam : tau -> QueryImpl spec (StateT sigma ProbComp), so games do the simulateQ/run' themselves"
    - "per-tuple families share the encrypt/decrypt cipher expressions verbatim (gcmEncode + XOR form) so 02-02's h_indep and Phase 5's coupling see one shared cipher form"
    - "unused signature binders pinned with underscore prefix + @[nolint unusedArguments] (EtM encReduction pattern)"

key-files:
  created:
    - SecureMessaging/AEAD/FromGCM/Security/Games.lean
  modified:
    - SecureMessaging.lean

key-decisions:
  - "gcmGameSkeleton returns the assembled QueryImpl; simulateQ ... .run' none lives in game0/game1 bodies only"
  - "tuple fixed as (H, mask, ks) with ks : BitVec L (single flat keystream, NOT a block list); profile-to-tuple bridge deferred to Phase 3"
  - "game0 uses gcmOneTimeAEAD.encrypt/decrypt directly (not the spec/profile form) so game0_eq_real is an id-projection against aeadSecurityImpl ... false k"
  - "game1 keeps prp/hL in the signature (underscore-prefixed + nolint) to pin K/L and align with the other games"
  - "DecidableEq SupportedAAD deliberately not pinned: the challenge guard compares the ciphertext only"

patterns-established:
  - "Pattern: GCM game = gcmGameSkeleton instance; only encStar/decryptResp/unifImpl vary across the chain"

# Metrics
duration: 8min
completed: 2026-09-08
---

# Phase 02 Plan 01: Game Skeleton, Tuple Families, game0/game1 Summary

**Phase 2's foundation: the OracleSpec-polymorphic `gcmGameSkeleton` QueryImpl builder (one-shot encrypt oracle + ACD19 ciphertext-only challenge guard, state `Option (BitVec L × BitVec 128)`), the two per-tuple impl families `gcmTupleImpl`/`gcmTupleImplReject` over `(H, mask, ks)` with `ks : BitVec L`, the endpoint game `game0` (real cipher, key sampled outside), and the top-level-tuple game `game1` — sorry-free, warning-clean, imported from the root.**

## Performance

- **Duration:** 8 min
- **Started:** 2026-09-08T19:11:02Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments

- `Games.lean` created in `namespace GCM` with the BAIF/Apache-2.0 header, a module docstring naming the full game chain (game0–game4 + game2♭/game3♭), and the plan's import set (GCM construction/profile/encoding/OTP + LazySampling/IdenticalUntilBad/StateProjection/NeverFails for 02-02..02-04).
- `gcmGameSkeleton`: returns `unifImpl + encImpl + decImpl` as a `QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)) (StateT (Option (BitVec L × BitVec 128)) (OracleComp spec))` — NOT a baked-in `simulateQ … |>.run'`. Encrypt oracle is one-shot Option-returning (`some _ => pure none`, else set-and-return); decrypt oracle implements the ACD19 ciphertext-only guard `if (← get) == some e then pure none else …`, AAD ignored, matching `oracleDecrypt`. At `spec := unifSpec` the base is definitionally `ProbComp`, so `oracleUnif (BitVec L × BitVec 128)` fits the `unifImpl` slot (confirmed at build).
- Five criterion-7 instance pins as `example … := inferInstance` (product `SampleableType` incl. the game1 triple, `DecidableEq` on C, `Fintype`/`DecidableEq` on `BitVec 128`), with a comment recording that `DecidableEq SupportedAAD` is deliberately absent.
- `gcmTupleImpl a` (LIVE, game1/game2) and `gcmTupleImplReject a` (REJECT, game3): τ-parameterised families over `StateT (Option C) ProbComp`, cipher bodies expressed via `gcmEncode` (`c = m ^^^ ks`, `t = ghash h (gcmEncode ad c) ^^^ mask`) and shared verbatim between the two families; they differ only in `decryptResp` (live verify+decrypt vs `pure none`).
- `game0`: samples `k ← prp.keygen` outside the skeleton, oracles call `(gcmOneTimeAEAD prp L hL).encrypt/decrypt` directly, state plain `Option C` — the `id`-projection shape 02-04's `game0_eq_real` needs.
- `game1`: samples `a ← $ᵗ (BitVec 128 × BitVec 128 × BitVec L)` at the top level, runs `simulateQ (gcmTupleImpl a) adv |>.run' none` — the eager form `probOutput_simulateQ_greedyLazy_run'_eq` consumes in 02-02.

## Task Commits

1. **Task 1: Scaffold Games.lean, pin instances, define gcmGameSkeleton** — `81636fc` (feat)
2. **Task 2: Tuple impl families, game0 (real), game1 (top-level tuple)** — `308aeab` (feat)

## Files Created/Modified

- `SecureMessaging/AEAD/FromGCM/Security/Games.lean` (created, 186 lines) — skeleton + tuple families + game0/game1 + instance pins.
- `SecureMessaging.lean` — root import added alphabetically (between `…Security.Encoding` and `…Security.OneTimePad`).

## Decisions Made

- **Skeleton factoring (research Open Question 1):** `gcmGameSkeleton` returns the `QueryImpl`; the `simulateQ … .run' none` lives in the game definitions. This is what lets 02-02/02-03 apply the lazy-sampling lemmas, whose interface is `implFam : τ → QueryImpl spec (StateT σ ProbComp)`.
- **Namespace `GCM`** (research Open Question 3), consistent with `gcmOneTimeAEAD`'s file and the Phase-6 blueprint anchor.
- **`ks : BitVec L`, not a block list:** the tuple form uses the flat keystream per the roadmap game-chain table; the `gcmEncryptSpec`/`gcmDecryptSpec` (block-list) bridge is Phase 3's job.
- **`game0` state plain `Option C`** (research Pitfall 4): matches `aeadSecurityImpl`'s state, avoiding EtM's `Prod.fst` projection obligation.
- **`game1` binders `_prp`/`_hL` + `@[nolint unusedArguments]`:** the plan pre-authorized the nolint "matching EtM `encReduction`"; that same EtM precedent underscore-prefixes the unused binder to satisfy the core unused-variables linter. Call sites are unaffected (positional).

## Deviations from Plan

- **[Plan latitude] `game1` unused binders underscore-prefixed** (`_prp`/`_hL` instead of `prp`/`hL`) alongside the plan's own `@[nolint unusedArguments]` instruction, exactly matching the cited EtM `encReduction` precedent (`_se`). Signature (types, order, explicitness) unchanged.

Otherwise: none — plan executed as written. No architectural changes; no authentication gates.

## Verification

- `lake build` (full workspace, 3120+ jobs) exits 0; no warning references `Games.lean`. The 15 pre-existing warnings (PRP/Defs + PRFPRNG/Defs `sorry`s, RKEM longLine, SCKA flexible-simp) are untouched and out of scope.
- `grep -rn "sorry\|axiom" …/Games.lean`: empty.
- `gcmGameSkeleton` body contains no `simulateQ` (grep: only docstrings and the game0/game1 bodies at lines 167/182).
- Decrypt guard is `(← get) == some e`, ciphertext-only, matching `oracleDecrypt`.
- All five defs (`gcmGameSkeleton`, `gcmTupleImpl`, `gcmTupleImplReject`, `game0`, `game1`) elaborate in `namespace GCM`; five instance-pin examples elaborate; `grep -c "FromGCM.Security.Games" SecureMessaging.lean` = 1.

## Next Phase Readiness

- 02-02 (game2 + `game1 = game2` via `greedyLazy`) and 02-03 (game3/game2♭/game3♭ via `consumeLazy` + IdenticalUntilBad) can consume `gcmTupleImpl`/`gcmTupleImplReject` directly as impl families.
- 02-04's `game0_eq_real` gets the `id`-projection shape from `game0`'s plain `Option C` state and direct `encrypt`/`decrypt` calls.
- No blockers.

## Self-Check: PASSED

- FOUND: SecureMessaging/AEAD/FromGCM/Security/Games.lean
- FOUND commit 81636fc (Task 1)
- FOUND commit 308aeab (Task 2)
- FOUND: gcmGameSkeleton, gcmTupleImpl, gcmTupleImplReject, game0, game1 in namespace GCM

---
*Phase: 02-game-skeleton-and-endpoints*
*Completed: 2026-09-08*
