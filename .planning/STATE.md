# Project State

## Project Reference

See: .planning/PROJECT.md (updated 2026-09-08)

**Core value:** A machine-checked, concrete-bound security theorem for GCM in the same `AEADScheme.distAdvantage` framework as the completed Encrypt-then-MAC proof.
**Current focus:** Phase 1 — Structural Foundations

## Current Position

Phase: 07a of 10 (GHASH Polynomial Form) — parallel phase, depends on Phase 1
Plan: 3 of 5 complete in phase 07a (07a-01, 07a-02, 07a-03 done; 07a-04, 07a-05 remain)
Status: 07a-03 complete — the phase crux: reflectN : BitVec 128 ≃ AdjoinRoot nistPoly + reflect_gfmulStep (one gfmul v-update = ·root), reflect_gcmReductionConst, CommRing-only, sorry-free, standard axioms only
Last activity: 2026-09-08 — Executed 07a-03 (reflectN via reflect nistPoly_monic + BitVec.cast bridge; reflectN_apply coordinate=coeff over Fin 128; reflectN_xor; reflect_gcmReductionConst = root^7+root^2+root+1 via range-8 cut + per-bit decide; reflectN_mul_root shift-vs-multiply; vStep; reflect_gfmulStep two-case char-2 argument)

Progress: [██░░░░░░░░] 14% (phase 1 complete: 9/9; phase 07a: 3/5)

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
- [Phase 07a]: 07a-03: reflectN defined as an Equiv structure literal using BitVec.cast on both legs (not `▸`/_root_.cast) so ⇑reflectN unfolds by defeq and getMsbD_cast/xor_cast reduce; the natDegree=128 transport is discharged once in reflectN_apply (Fintype.sum_equiv (finCongr nistPoly_natDegree)) and never fought again; reflect_gcmReductionConst collapses the 128-term sum to range 8 (generic vanishing above) + 8 single-index decides (no full-128 decide); reflect_gfmulStep = two-case boolean split on getMsbD 127 (= getLsbD 0), the ⊕R branch supplies root^128 that duplicates the shift's escaped term and cancels via 2•root^128=0; heavy coordinate lemmas (reflectN_mul_root_left/reflectN_ushiftRight_eq) pulled top-level for heartbeat budget — congr 1 on the AdjoinRoot sum equation times out, replaced by simp only [smul_mul_assoc, ← pow_succ] + one Fin.sum_univ_castSucc

### Pending Todos

None.

### Blockers

None.

## Session Continuity

Last session: 2026-09-08
Stopped at: Completed 07a-03-PLAN.md (reflectN + reflect_gfmulStep crux, sorry-free, standard axioms)
Resume file: None
