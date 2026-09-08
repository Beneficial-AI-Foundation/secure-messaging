# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-09-08)

**Core value:** A machine-checked, concrete-bound security theorem for GCM in the same `AEADScheme.distAdvantage` framework as the completed Encrypt-then-MAC proof.
**Current focus:** Phase 2 — Game Skeleton and Endpoints

## Current Position

Phase: 02 of 10 (Game Skeleton and Endpoints)
Plan: 2 of 4 complete in phase 02 (02-01, 02-02 done; next 02-03)
Status: 02-02 complete — lazy games landed in Games.lean: game2 (greedyLazy gcmTupleImpl, live decrypt), game3 (consumeLazy gcmTupleImplReject at hit = (fun t => t matches OEncrypt _)), game4 (consumeLazy gcmRandRejectImpl, uniform challenge cipher, same hit/cache), gcmTupleImplReject_indep (criterion 3, non-hit branches by rfl, passes verbatim into probOutput_simulateQ_consumeLazy_run'_eq — elaboration-verified). lake build green, sorry-free, no new warnings
Last activity: 2026-09-08 — Executed 02-02 (hit predicate spelled without decide since `matches` yields Bool; statement-discipline rfl tripwire did not fire, 02-01 skeleton factoring confirmed)

Progress: [██░░░░░░░░] 19% (phase 1 complete: 9/9; phase 07a complete: 5/5; phase 02: 2/4)

## Performance Metrics

**Velocity:**
- Total plans completed: 1
- Average duration: 4 min
- Total execution time: 4 min

**By Phase:**

| Phase | Plans | Total | Avg/Plan |
|-------|-------|-------|----------|
| 01 | 1 | 4 min | 4 min |

**Recent Trend:**
- Last 5 plans: 01-01 (4 min)
- Trend: -

*Updated after each plan completion*
| Phase 01 P05 | 6 min | 2 tasks | 1 files |
| Phase 01-structural-foundations P06 | 6 min | 2 tasks | 1 files |
| Phase 01 P02 | 6 min | 3 tasks | 1 files |
| Phase 01-structural-foundations P04 | 9 min | 2 tasks | 1 files |
| Phase 01 P03 | 9 min | 3 tasks | 1 files |
| Phase 01-structural-foundations P07 | 3 min | 2 tasks | 1 files |
| Phase 01 P08 | 5 min | 2 tasks | 1 files |
| Phase 01-structural-foundations P09 | 3 min | 2 tasks | 1 files |
| Phase 07a P01 | 4 min | 2 tasks | 2 files |
| Phase 07a P02 | 10 min | 2 tasks | 2 files |
| Phase 07a P03 | 19 min | 2 tasks | 1 files |
| Phase 07a P04 | 3 min | 2 tasks | 1 files |
| Phase 07a P05 | 4 min | 2 tasks | 1 files |
| Phase 07a P05 | 4 min | 2 tasks | 1 files |
| Phase 02 P01 | 8 min | 2 tasks | 2 files |
| Phase 02 P02 | 4 min | 2 tasks | 1 files |

## Accumulated Context

### Decisions

Decisions are logged in PROJECT.md Key Decisions table.
Recent decisions affecting current work:

- Phase 1 (01-01, executed): `keystream` de-privatized in GCM.lean per research Open Question 1 — privacy would force keystream-unfolding lemmas into the NIST spec file, violating REQ-07 placement
- Phase 1: AXU predicate stated via `probOutput` over `ProbComp` (matches Phase 4/7b consumers)
- Phase 1: generic AXU predicate + floor in `ToVCVio/CryptoFoundations/UniversalHash.lean`; GCM instantiation in `SecureMessaging/AEAD/FromGCM/Security/Axu.lean`
- [Phase 01]: 01-08: unequal-lenA distinctness proven entirely at reversed position 0 (length block) per roadmap lock — no leading-coefficient or list-length comparison; sigma trap avoided by substituting the lenA equality before touching payloads; gcmEncode_injective derived as contrapositive of gcmEncode_tail_distinct so the equal-lenA append_inj argument lives in one place
- [Phase 01]: 01-07: single-sample OTP form kept as GCM-named entry point with m on the XOR left (Phase 5's argument order, no xor_comm detour at use sites); block form by 3-step calc (Functor.map_map, probOutput_xor_map, 01-04 brick) so the proof stays visibly counting-free; keystream bridge closed by rfl as 01-04 engineered
- [Phase 01]: 01-05: lenBlock_ne_of_ne stated at general bound a,b < 2^64 so 01-08 applies it without re-deriving the AAD bound; gcmEncrypt connection lemma is a full rfl unfolding for one-step game rewriting
- [Phase 01]: 01-02: profile theorems packaged via explicit spec defs (gcmEncryptSpec/gcmDecryptSpec) with h/mask/ksBlocks as leading explicit parameters — Phase 2 games substitute sampled values positionally; specializations stated with prp.toBlockCipher.perm (Construction.lean's exact term)
- [Phase 01]: 01-06: AXU predicate uses [XorOp T] (Lean v4.32 core renamed the ^^^ typeclass; Xor is now Prop-level); floor lemma card_inv_le needs no Nonempty T (card T != 0 by contradiction from 1 <= card T * eps); sums-to-one via sum_probOutput_eq_one, no tsum sublemma needed
- [Phase 01]: 01-04: uniformity via split bijection (blocksSplit) chained through evalDist_map_bijective_uniform_cross + evalDist_map_fst_uniformSample_prod, not fiber counting; block width kept at 128 so blocksToBitVec matches GCM.keystream verbatim for 01-07's rfl bridge; evalDist-level theorem provided alongside the probOutput shape
- [Phase 01]: 01-03: counterChain_ofNat non-wrap hypothesis stated as c + m <= 2^32 (plan's 2^32 - 1 bound cannot reach the ValidMsgLength boundary n = 2^32 - 2); inc32 non-wrap packaged at toNat level (x.toNat % 2^32 < 2^32 - 1); distinctness delivered as Pairwise (ne) on the concrete list 0 :: 1 :: counterChain 2 n
- [Phase 01]: 01-09: floor shipped in both normal forms (card-form direct from generic lemma, 2^128-form via FinEnum.card_eq_fintypeCard bridge) so Phase 4 consumes either without conversion; witness distinctness via congrArg on a.1.1 (0 vs 8), no Subtype.ext_iff/HEq; GhashIsAXU kept a def with a rfl example pinning the unfolding in CI
- [Phase 07a]: 01: nistPoly grouped as X^128 + (X^7+X^2+X+1) so monic_X_pow_add applies with the tail as p; monic + natDegree=128 both via compute_degree!; root annihilation stated with modulus written literally as nistPoly (only the reduced element spelled out) so mk_X yields root nistPoly and avoids an atom mismatch under ring; char 2 taken as (2 : AdjoinRoot nistPoly)=0 via map_ofNat on AdjoinRoot.of (no CharP/CharTwo instance exists for AdjoinRoot), reduction closed by linear_combination; set_option maxRecDepth 4000 needed for ring over root^128, and it must precede the docstring
- [Phase 07a]: 07a-02: BitVec half is a plain Equiv + separate reflect_xor (Mathlib BitVec + is arithmetic not XOR); cross PowerBasis.dim=natDegree defeq with change not rw; Basis renamed to Module.Basis
- [Phase 07a]: 07a-05: reversed-block indexing locked (coefficient of h^(i+1) is blocks.reverse[i], verbatim match to Encoding.lean gcmEncode_tail_distinct — Phase 7b transport index-for-index); horner_foldl_eq_sum by List.reverseRecOn (append-singleton multiplies acc by H and prepends b at reverse index 0), reindex via one Finset.sum_range_succ' + sum_mul + mul_assoc + pow_succ; reflect_ghash_foldl_gen seed-generalized (foldl accumulator varies; seed 0 via reflectN_zero); ghashPoly packaging uses renamed eval_finsetSum/finsetSum_coeff (old eval_finset_sum/finset_sum_coeff deprecated 2026-04-08); ghashPoly_natDegree_le ≤ blocks.length proven (natDegree_C_mul_le∘natDegree_X_pow_le∘omega) as the maxBlocks bound for 7b
- [Phase 07a]: 07a-04: reflect_gfmul_aux dropped the plan's k ≤ 128 hypothesis (invariant is unconditional since reflect_gfmulStep is bit-index agnostic — unused binder avoided); stated as a DUAL conjunction so the z-step's ⊕v term can read the v-step's reflectN y·root^k; gfmulStep's 2nd component IS vStep p.2 so gfmul_eq_foldl is rfl and the succ .2 is defeq (change, not rw); reflectN_zero via reflectN_apply + Finset.sum_eq_zero (not self-cancellation — 0^^^0's 0#128 misses BitVec.xor_zero's 0#w); base case by `change` onto (0 : BitVec 128) (simp normalizes to 0#128 which reflectN_zero won't rewrite); reflect_gfmul = invariant at k=128 with coefficient-sum = reflectN x via Fin.sum_univ_eq_sum_range
- [Phase 07a]: 07a-03: reflectN defined as an Equiv structure literal using BitVec.cast on both legs (not `▸`/_root_.cast) so ⇑reflectN unfolds by defeq and getMsbD_cast/xor_cast reduce; the natDegree=128 transport is discharged once in reflectN_apply (Fintype.sum_equiv (finCongr nistPoly_natDegree)) and never fought again; reflect_gcmReductionConst collapses the 128-term sum to range 8 (generic vanishing above) + 8 single-index decides (no full-128 decide); reflect_gfmulStep = two-case boolean split on getMsbD 127 (= getLsbD 0), the ⊕R branch supplies root^128 that duplicates the shift's escaped term and cancels via 2•root^128=0; heavy coordinate lemmas (reflectN_mul_root_left/reflectN_ushiftRight_eq) pulled top-level for heartbeat budget — congr 1 on the AdjoinRoot sum equation times out, replaced by simp only [smul_mul_assoc, ← pow_succ] + one Fin.sum_univ_castSucc
- [Phase 02]: 02-02: hit predicate spelled (fun t => t matches OEncrypt _) with NO decide wrapper (`matches` elaborates to Bool directly) — identical term in gcmTupleImplReject_indep/game3/game4 so Phases 3/4/5 pass the lemma with zero predicate conversion (direct passability into probOutput_simulateQ_consumeLazy_run'_eq verified by throwaway elaboration); gcmTupleImplReject_indep non-hit branches closed by plain rfl (statement-discipline tripwire silent — 02-01 factoring sound); gcmRandRejectImpl ignores its tuple binder (_a + nolint) so its own h_indep is immediate and the dead hit-sample falls to uniform losslessness in 02-04's game4_eq_rand
- [Phase 02]: 02-01: gcmGameSkeleton returns a QueryImpl (unifImpl + encImpl + decImpl) over StateT (Option C) (OracleComp spec) — simulateQ/run' lives in the game defs so LazySampling's implFam interface composes; tuple locked as (H, mask, ks) with ks : BitVec L (flat keystream, profile-to-tuple bridge deferred to Phase 3); game0 uses gcmOneTimeAEAD.encrypt/decrypt directly at a key sampled outside the skeleton with plain Option C state (id-projection for game0_eq_real); game1 pins K/L via underscore-prefixed _prp/_hL + nolint (EtM encReduction pattern); DecidableEq SupportedAAD deliberately not pinned (ciphertext-only guard)

### Pending Todos

1 pending todo (.planning/todos/pending/):
- Run crypto-eval adversarial review after Phase 2 execution (2026-09-08, area: planning) — build .claude/agents/crypto-eval.md (FVS eval mode: ACCEPT/FOLLOWUP/HUMAN_RULING/BLOCKED) and run it cross-engine after /gsd:execute-phase 2, persisting 02-EVAL.md

### Blockers

None.

## Session Continuity

Last session: 2026-09-08
Stopped at: Completed 02-02-PLAN.md (Games.lean: game2/game3/game4 + gcmTupleImplReject_indep; sorry-free, warning-clean). Next: execute 02-03
Resume file: None
