---
phase: 04-wegman-carter-authenticity-hop
plan: 01
subsystem: crypto-proofs
tags: [lean4, vcvio, wegman-carter, axu, ghash, gcm, identical-until-bad, sorry-skeleton]

# Dependency graph
requires:
  - phase: 01-structural-foundations
    provides: IsAlmostXorUniversal / card_inv_le (UniversalHash.lean), GhashIsAXU + ghashAXU_eps_lower (Axu.lean), gcmEncode
  - phase: 02-game-skeleton-and-endpoints
    provides: gcmInstImpl, game2Flat/game3Flat and their projections, game2/game3 (Games.lean, FROZEN)
  - phase: 03-prf-hop
    provides: PrfHop.lean house layout for the GCM Security/ hop files
provides:
  - "ToVCVio/CryptoFoundations/WegmanCarter.lean — wcSpec, wcInstImpl, wcInstImpl_decrypt_run (PROVED), WCLogState, wcLogImpl, wcAccepts, wcFlag, wcProj, and the sorried WC1/WC2/WC3/WC3b/WC7/WC8"
  - "ToVCVio/CryptoFoundations/WegmanCarterBound.lean — the sorried abstract probability core WC4/WC5/WC6"
  - "SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean — the wcSpec = aeadOneTimeCCASpec rfl pin, gcmInstImpl_eq_wcInstImpl (PROVED), and the sorried WC9/WC-IUB0/WC-IUB/WC10"
  - "The whole Phase-4 statement surface in-tree, typed and elaborating: 13 named obligations / 14 sorry bodies"
affects: [04-02, 04-03, 04-04, 04-05, 04-06, 06-assembly, 07b-ghash-axu]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Generic brick whose spec IS the consumer's spec (wcSpec = aeadOneTimeCCASpec spelled inline), collapsing EtM's 696-line transport to a 6-line funext/cases bridge"
    - "In-tree typed sorry skeleton as the phase's anti-drift device: later plans read statements from the tree, never re-derive them from plan prose"

key-files:
  created:
    - ToVCVio/CryptoFoundations/WegmanCarter.lean
    - ToVCVio/CryptoFoundations/WegmanCarterBound.lean
    - SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean
  modified:
    - ToVCVio.lean
    - SecureMessaging.lean

key-decisions:
  - "wcInstImpl/wcLogImpl summand ascriptions spell the target monad explicitly instead of the pin's `_`: with `_` the StateT state type stays a metavariable when `let (challenge, forged) ← get` elaborates, and the `match challenge with` pattern variable is then ill-typed. Same spelling Games.lean's gcmInstImpl uses; term unchanged, and the pinned 6-line bridge proof still closes."
  - "WC7's `fun z => ((H, mask), z.2)` needs an explicit binder type `α × WCLogState A Cb` (elaboration order leaves z's type unknown under `<$>`)."
  - "In WegmanCarterBound.lean the pins' `μ.support` is spelled `support μ`: ProbComp reduces to `unifSpec.toPFunctor.FreeM`, so generalized field notation resolves `.support` against PFunctor.FreeM and fails."
  - "WC-IUB0 landed UNSPLIT (one declaration, the three-way conjunction) — its packaging latitude was not exercised, so the plan's 14-declaration count holds, not 16."
  - "Section-variable layout: only WC0, WC1, WC2, wcLogImpl_log_length_le and WC3b sit under `variable {K A M Cb D : Type}`; every declaration whose pin carries its own type binders is placed outside those sections, so no pinned binder shadows a section variable (the project sets autoImplicit = false)."

patterns-established:
  - "Pattern: pinned generic-vs-concrete handler equalities are stated at QueryImpl level but PROVED by descending to `(impl t).run s` and case-splitting the Option challenge slot — two matcher auxiliaries are not isDefEq at a stuck discriminant"
  - "Pattern: sorry ledger reconciled BY NAME against a pre-touch `rg -n '\\bsorry\\b'` baseline, never by an anchored line count (three baseline sorries are inline and invisible to `^\\s*sorry\\s*$`)"

# Metrics
duration: 24min
completed: 2026-09-09
---

# Phase 4 Plan 01: Wegman–Carter Statement Skeleton Summary

**The entire Phase-4 statement surface landed in-tree, typed and elaborating: the generic Wegman–Carter handler `wcInstImpl`, its decrypt normal form and the 6-line bridge identifying `gcmInstImpl (h, mask, ks) b` with it (both PROVED, axioms standard-only), plus 13 named `sorry`-bodied obligations across three new files.**

## Performance

- **Duration:** 24 min
- **Started:** 2026-09-09T00:00:00Z (approx.)
- **Completed:** 2026-09-09
- **Tasks:** 3
- **Files modified:** 5 (3 created, 2 registration files)

## Accomplishments

- `wcInstImpl` — the generic Wegman–Carter flag-instrumented handler over `wcSpec A M Cb`, a verbatim generic copy of Phase 2's `gcmInstImpl`, with `[DecidableEq Cb]` (not `[BEq Cb]`) so the challenge guard's instance path matches the GCM one syntactically.
- `wcInstImpl_decrypt_run` (WC0) — PROVED. The `§A.1` decrypt normal form every later per-query obligation rewrites through.
- `gcmInstImpl_eq_wcInstImpl` (WC-BRIDGE) — PROVED by the pinned 6-line `funext`/`rcases`/`cases` proof, at `enc := id`, `hash := fun H p => ghash H (gcmEncode p.1 p.2)`, `D := SupportedAAD × BitVec L`, `padMsg = unpad = (· ^^^ ks)`. `Games.lean` untouched.
- The `wcSpec = aeadOneTimeCCASpec` identification pinned by `example … := rfl` on the SecureMessaging side, resolving the layering constraint (ToVCVio may not import SecureMessaging).
- The log-refined surface `WCLogState`/`wcLogImpl`/`wcAccepts`/`wcFlag`/`wcProj`: the challenge slot carries its AAD and every log entry carries a pre/post tag, so the mandatory pre/post split is expressible; the log handler's decrypt oracle reads neither `H` nor `mask`.
- 13 named obligations / 14 sorry bodies staged with docstrings naming their owning plan and their intended proof route.

## Task Commits

1. **Task 1: WegmanCarter.lean — handler, log refinement surface, sorried WC1/WC2/WC3/WC3b/WC7/WC8** — `72165c0` (feat)
2. **Task 2: WegmanCarterBound.lean — the three abstract probability statements; register both files** — `cdb0b7f` (feat)
3. **Task 3: AuthHop.lean — bridging lemma, spec pin, sorried WC9/WC-IUB0/WC-IUB/WC10; gates** — `c306026` (feat)

## Files Created/Modified

- `ToVCVio/CryptoFoundations/WegmanCarter.lean` (389 lines, new) — the generic brick: spec, handler, decrypt normal form, log-refined surface, and the six staged obligations that live in ToVCVio.
- `ToVCVio/CryptoFoundations/WegmanCarterBound.lean` (114 lines, new) — the three abstract probability statements (post-AXU half, pre-fresh half, shared-count combination), with the docstring recording why the unified pre/post treatment is unsound.
- `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean` (218 lines, new) — the GCM side: spec pin, bridge, and the four staged GCM-level obligations.
- `ToVCVio.lean` — two import lines, alphabetical after `UniversalHash`.
- `SecureMessaging.lean` — one import line, first of the `FromGCM.Security.*` block.

## Sorry Ledger

Reconciled BY NAME against `allowed_sorries`. Line numbers are the `sorry` body's line; the declaration line is given in parentheses.

| Obligation | Declaration | File:line (body) | Owner |
| --- | --- | --- | --- |
| WC1 | `OracleComp.WegmanCarter.map_run_simulateQ_wcLogImpl_eq` | `ToVCVio/CryptoFoundations/WegmanCarter.lean:247` (decl :239) | 04-03 |
| WC2 | `OracleComp.WegmanCarter.probEvent_bad_wcInst_eq_wcLog` | `ToVCVio/CryptoFoundations/WegmanCarter.lean:261` (decl :254) | 04-03 |
| WC3 (1/2) | `OracleComp.WegmanCarter.support_state_measure_le_of_isQueryBoundP` | `ToVCVio/CryptoFoundations/WegmanCarter.lean:282` (decl :274) | 04-03 |
| WC3 (2/2) | `OracleComp.WegmanCarter.wcLogImpl_log_length_le` | `ToVCVio/CryptoFoundations/WegmanCarter.lean:300` (decl :294) | 04-03 |
| WC3b | `OracleComp.WegmanCarter.wcLogImpl_post_ne_challenge` | `ToVCVio/CryptoFoundations/WegmanCarter.lean:318` (decl :313) | 04-03 |
| WC4 | `OracleComp.WegmanCarter.probEvent_post_axu_le` | `ToVCVio/CryptoFoundations/WegmanCarterBound.lean:76` (decl :68) | 04-04 |
| WC5 | `OracleComp.WegmanCarter.probEvent_pre_fresh_le` | `ToVCVio/CryptoFoundations/WegmanCarterBound.lean:93` (decl :87) | 04-04 |
| WC6 | `OracleComp.WegmanCarter.combine_pre_post_le` | `ToVCVio/CryptoFoundations/WegmanCarterBound.lean:112` (decl :105) | 04-04 |
| WC7 | `OracleComp.WegmanCarter.probEvent_bad_wcLog_le` | `ToVCVio/CryptoFoundations/WegmanCarter.lean:353` (decl :340) | 04-05 |
| WC8 | `OracleComp.WegmanCarter.probEvent_wcInst_forge_le` | `ToVCVio/CryptoFoundations/WegmanCarter.lean:387` (decl :373) | 04-05 |
| WC9 | `GCM.probEvent_forge_gcmInst_le` | `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:127` (decl :119) | 04-06 |
| WC-IUB0 | `GCM.gcmInstImpl_identicalUntilBad` | `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:173` (decl :155) | 04-06 |
| WC-IUB | `GCM.gcmInst_tvDist_le_probEvent_forge` | `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:192` (decl :185) | 04-06 |
| WC10 | `GCM.game2_game3_le_auth` | `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:216` (decl :209) | 04-06 |

**13 named obligations, 14 sorry bodies.** WC-IUB0 landed UNSPLIT (one declaration), so the 14-declaration count holds and the 16-declaration variant did not arise.

**PROVED here, not sorried:**

- WC0 `OracleComp.WegmanCarter.wcInstImpl_decrypt_run` — `ToVCVio/CryptoFoundations/WegmanCarter.lean:147`.
- WC-BRIDGE `GCM.gcmInstImpl_eq_wcInstImpl` — `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:88`.

### Baseline

Snapshotted before any edit (`rg -n '\bsorry\b' SecureMessaging/ ToVCVio/ -g '*.lean'`), 13 lines = 12 sorry TERMS + 1 prose line:

```
SecureMessaging/PRFPRNG/Defs.lean:16:this module are still `sorry`-stubbed and under development.   <- prose
SecureMessaging/PRFPRNG/Defs.lean:83:  sorry
SecureMessaging/PRFPRNG/Defs.lean:88:  sorry
SecureMessaging/PRFPRNG/Defs.lean:94:  sorry
SecureMessaging/PRFPRNG/Defs.lean:100:  sorry
SecureMessaging/PRFPRNG/Defs.lean:105:  sorry
SecureMessaging/PRFPRNG/Defs.lean:142:    sorry
SecureMessaging/PRFPRNG/Defs.lean:163:  init := sorry        <- inline
SecureMessaging/PRFPRNG/Defs.lean:164:  up := sorry          <- inline
SecureMessaging/PRFPRNG/Defs.lean:171:    (sorry : Prop) :=  <- inline
SecureMessaging/PRFPRNG/Defs.lean:172:  sorry
SecureMessaging/PRP/Defs.lean:75:    sorry
SecureMessaging/PRP/Defs.lean:87:    sorry
```

### Diff against the baseline (purely additive, nothing removed)

```
> ToVCVio/CryptoFoundations/WegmanCarterBound.lean:49:  ... typed `sorry`-bodied lemmas ...   (prose)
> ToVCVio/CryptoFoundations/WegmanCarterBound.lean:76:  sorry                                  WC4
> ToVCVio/CryptoFoundations/WegmanCarterBound.lean:93:  sorry                                  WC5
> ToVCVio/CryptoFoundations/WegmanCarterBound.lean:112:  sorry                                 WC6
> ToVCVio/CryptoFoundations/WegmanCarter.lean:43:  ... `sorry`-bodied lemma** ...              (prose)
> ToVCVio/CryptoFoundations/WegmanCarter.lean:75:  ... typed `sorry`-bodied lemmas ...         (prose)
> ToVCVio/CryptoFoundations/WegmanCarter.lean:247:  sorry                                      WC1
> ToVCVio/CryptoFoundations/WegmanCarter.lean:261:  sorry                                      WC2
> ToVCVio/CryptoFoundations/WegmanCarter.lean:282:  sorry                                      WC3 (1/2)
> ToVCVio/CryptoFoundations/WegmanCarter.lean:300:  sorry                                      WC3 (2/2)
> ToVCVio/CryptoFoundations/WegmanCarter.lean:318:  sorry                                      WC3b
> ToVCVio/CryptoFoundations/WegmanCarter.lean:353:  sorry                                      WC7
> ToVCVio/CryptoFoundations/WegmanCarter.lean:387:  sorry                                      WC8
> SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:127:  sorry                               WC9
> SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:136:  ... `sorry`-bodied lemma ...         (prose)
> SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:173:  sorry                               WC-IUB0
> SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:192:  sorry                               WC-IUB
> SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:216:  sorry                               WC10
```

14 new bodies + 4 new prose lines. Every body reconciles by name against `allowed_sorries`; nothing else changed.

## Gate Outputs

**Full `lake build`:** `Build completed successfully (3127 jobs).`

**Warnings on the three new files** — `declaration uses 'sorry'` only, one per sorried declaration, 14 in total, nothing else:

```
warning: ToVCVio/CryptoFoundations/WegmanCarter.lean:239:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarter.lean:254:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarter.lean:274:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarter.lean:294:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarter.lean:313:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarter.lean:340:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarter.lean:373:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarterBound.lean:68:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarterBound.lean:87:8: declaration uses `sorry`
warning: ToVCVio/CryptoFoundations/WegmanCarterBound.lean:105:8: declaration uses `sorry`
warning: SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:119:8: declaration uses `sorry`
warning: SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:155:8: declaration uses `sorry`
warning: SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:185:8: declaration uses `sorry`
warning: SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean:209:8: declaration uses `sorry`
```

**`#print axioms` on the two proved declarations:**

```
'GCM.gcmInstImpl_eq_wcInstImpl' depends on axioms: [propext, Quot.sound]
'OracleComp.WegmanCarter.wcInstImpl_decrypt_run' depends on axioms: [propext, Quot.sound]
```

Standard-only; `sorryAx` absent.

**Scope audit, over THIS PLAN'S OWN COMMITS** (04-02's `fbfef5a` lands `LazySampling.lean` on the same branch in the same wave and is correctly excluded):

```
--- 72165c0
 ToVCVio/CryptoFoundations/WegmanCarter.lean | 389 ++++++++++++++++++++++++++++
--- cdb0b7f
 ToVCVio.lean                                     |   2 +
 ToVCVio/CryptoFoundations/WegmanCarterBound.lean | 114 +++++++++++++++++++++++
--- c306026
 SecureMessaging.lean                               |   1 +
 SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean | 218 +++++++++++++++++++++
```

Union = exactly the five `files_modified`. `git status --short` over the five owned paths is empty.

**`Games.lean` untouched:** `git diff 1e1c3e0..HEAD -- SecureMessaging/AEAD/FromGCM/Security/Games.lean` is EMPTY.

**AXU-domain check:** `gcmEncode` appears in `AuthHop.lean` only inside the `hash` argument (`AuthHop.lean:94`, `(fun H p => ghash H (gcmEncode p.1 p.2)) id h mask …`) and in docstrings — never as `enc`, which is `id`.

**Log shape check:** `WCLogState A Cb = Option (A × (Cb × BitVec 128)) × List (A × (Cb × BitVec 128) × Bool)` — the challenge slot carries its AAD, and log entries carry a `Bool` pre/post tag.

## Decisions Made

- **Explicit target monad in the two handler definitions.** The pins wrote `QueryImpl (A × M →ₒ …) _`. With `_`, the `StateT` state type is still a metavariable when `let (challenge, forged) ← get` elaborates, so the subsequent `match challenge with` has a pattern variable of metavariable type and fails. Spelled the monad out — exactly as `Games.lean`'s `gcmInstImpl` does. The elaborated term is unchanged, which the pinned 6-line bridge proof confirms (it closes verbatim).
- **WC-IUB0 landed unsplit.** The three-way conjunction elaborated first try with the pinned binder spellings (`.Domain`, `.Range t`, unqualified `aeadOneTimeCCASpec` under `open AEADScheme`), so its split latitude was not exercised. Ledger count for 04-06: 14 declarations, not 16.
- **`support μ` rather than `μ.support`.** Not a statement change: generalized field notation cannot see `OracleComp.support` through `ProbComp`'s reduction to `unifSpec.toPFunctor.FreeM`.
- **Section-variable discipline.** Only the five pins that carry no type binders of their own sit under `variable {K A M Cb D : Type}`; the rest are outside, so no pinned `{K A Cb D : Type}` or `{α K A M Cb D : Type}` shadows a section variable. `α` is never a section variable.

## Deviations from Plan

Statement content: **none**. The statement-discipline tripwire stayed silent — every pinned statement landed with its pinned content, including the restored `henc_inj` and the added `hfloor` on WC7/WC8, WC7's `(K × BitVec 128) × WCLogState A Cb` carrier, and WC10's `|Pr[game3] − Pr[game2]|` orientation.

Three elaboration-level spellings were adjusted (none weakens, strengthens, or reshapes a statement; all three are notation, not content):

**1. [Rule 3 - Blocking] Explicit target monad on the four `QueryImpl` summand ascriptions**
- **Found during:** Task 1 (`wcInstImpl`, then `wcLogImpl`)
- **Issue:** `Invalid match expression: The type of pattern variable 'val✝' contains metavariables` — with the pin's `_` for the summand's target monad, `get`'s state type is undetermined when the `match challenge with` elaborates.
- **Fix:** Replaced `_` with `(StateT (Option (Cb × BitVec 128) × Bool) ProbComp)` resp. `(StateT (WCLogState A Cb) ProbComp)`, matching `Games.lean`'s own spelling.
- **Files modified:** `ToVCVio/CryptoFoundations/WegmanCarter.lean`
- **Verification:** `lake build` green; `gcmInstImpl_eq_wcInstImpl` closes by the pinned 6-line proof, which would fail if the term had changed.
- **Committed in:** `72165c0`

**2. [Rule 3 - Blocking] Binder type annotation on WC7's mapping function**
- **Found during:** Task 1 (WC7 `probEvent_bad_wcLog_le`)
- **Issue:** `Invalid projection: Type of z is not known` on `(fun z => ((H, mask), z.2)) <$> …`.
- **Fix:** `fun z : α × WCLogState A Cb => ((H, mask), z.2)`.
- **Files modified:** `ToVCVio/CryptoFoundations/WegmanCarter.lean`
- **Verification:** `lake build` green; statement type is the pinned one.
- **Committed in:** `72165c0`

**3. [Rule 3 - Blocking] `support μ` in place of `μ.support`**
- **Found during:** Task 2 (WC4, WC5, WC6)
- **Issue:** `Invalid field 'support': the environment does not contain PFunctor.FreeM.support` — `ProbComp Z` reduces to `unifSpec.toPFunctor.FreeM Z`, so dot-notation resolves against the wrong namespace.
- **Fix:** Prefix form `support μ` / `support (k w m)` (`OracleComp.support`, already opened).
- **Files modified:** `ToVCVio/CryptoFoundations/WegmanCarterBound.lean`
- **Verification:** `lake build` green; same term.
- **Committed in:** `cdb0b7f`

---

**Total deviations:** 3 auto-fixed (all Rule 3 - blocking elaboration issues, all notation-level)
**Impact on plan:** No statement changed. No scope creep — the five `files_modified` are exactly what was touched.

## Issues Encountered

- The research probe (`04-RESEARCH §C.3`) reported `wcInstImpl` green with `_` summand ascriptions; against the tree, inside the target file's namespace and imports, it is not. Diagnosed and fixed in-place (deviation 1). Worth carrying: **always spell the `StateT … ProbComp` target monad in a `QueryImpl` summand ascription** — the `do`-block's `get` cannot postpone.
- No heartbeat pressure: every per-query obligation is its own named lemma, as the pitfall list requires. The bridge's `funext s; cases ch <;> rfl` shape kept the kernel work per branch small.

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- **Wave-2 gate:** the Codex interface review runs next, on this plan alone. Both things it checks are visible in-tree: the AXU-domain instantiation in `AuthHop.lean:88-96` (`enc := id`, `hash := ghash ∘ gcmEncode`, `D := SupportedAAD × BitVec L`) and the pre/post log shape in `WegmanCarter.lean:176-182`.
- **04-03** can start from WC1/WC2/WC3/WC3b as written; note WC1 must use the `.run` (joint) projection lemma `map_run_simulateQ_eq_of_query_map_eq` (`StateProjection.lean:53`), not the `run'` sibling.
- **04-04** owns WC4/WC5/WC6 and has packaging latitude on all three (bound and hypothesis content pinned); it must record the final signatures verbatim in its SUMMARY as a pin update for 04-05.
- **04-05** owns WC7/WC8 and may re-package WC7's carrier, provided WC8 is unchanged.
- **04-06** owns WC9/WC-IUB0/WC-IUB/WC10 and its `allowed_sorries` is `none`; the 14-declaration warning allowance expires there. WC-IUB0 landed unsplit, so 04-06 discharges 4 declarations, not 6.
- No blockers. Ledger draw-down remains 14 → (04-03: −5) → (04-04: −3) → (04-05: −2) → (04-06: −4) → 0.

---
*Phase: 04-wegman-carter-authenticity-hop*
*Completed: 2026-09-09*

## Self-Check: PASSED

All three created source files exist on disk (389 / 114 / 218 lines, all above their
`min_lines` floors of 180 / 60 / 80), both registration files exist and carry their new
import lines, and all three task commits (`72165c0`, `cdb0b7f`, `c306026`) are present in
`git log`.
