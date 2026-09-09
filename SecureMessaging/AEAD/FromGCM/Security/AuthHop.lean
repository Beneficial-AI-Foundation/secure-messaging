/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Axu
import SecureMessaging.AEAD.FromGCM.Security.Games
import ToVCVio.CryptoFoundations.WegmanCarter
import ToVCVio.CryptoFoundations.WegmanCarterBound

/-!
# GCM — the Wegman–Carter authenticity hop (`game2` → `game3`)

Suppress live decryption: replace the live-verification game `game2` by the
always-reject game `game3`, at the cost of the one-time Wegman–Carter forgery
probability `q_d · ε`, where `ε` bounds the almost-XOR-universality of
`ghash ∘ gcmEncode` on `SupportedAAD × BitVec L`.

`SecureMessaging/AEAD/FromGCM/Security/Games.lean` is FROZEN (Phase 2, completed,
verified and crypto-eval-ACCEPTed). The connection to the Phase-2 games is made by
transport in this file — `gcmInstImpl_eq_wcInstImpl` and the two landed projections
`game2Flat_eq_game2` / `game3Flat_eq_game3` — never by an edit there.

Contents:
- the `wcSpec = aeadOneTimeCCASpec` identification, pinned as an `example … := rfl`
  (the generic brick lives in `ToVCVio`, which may not import `SecureMessaging`, so the
  spec is spelled inline there and identified here);
- `gcmInstImpl_eq_wcInstImpl` — the bridging lemma (PROVED), identifying the Phase-2
  instrumented handler with the generic Wegman–Carter handler at `enc := id`,
  `hash := fun H p => ghash H (gcmEncode p.1 p.2)`;
- `probEvent_forge_gcmInst_le` — the per-`ks` forgery bound (staged, plan 04-06);
- `gcmInstImpl_identicalUntilBad` and `gcmInst_tvDist_le_probEvent_forge` — the
  identical-until-bad state relation and the distance bound it feeds (staged, plan 04-06);
- `game2_game3_le_auth` — the phase theorem (staged, plan 04-06).

## AXU domain

The AXU hypothesis is `GhashIsAXU L ε` (`Axu.lean`), i.e. almost-XOR-universality of
`fun H p => ghash H (gcmEncode p.1 p.2)` on `SupportedAAD × BitVec L`. The brick is
therefore instantiated at `D := SupportedAAD × BitVec L` and `enc := id`, with `gcmEncode`
appearing INSIDE the `hash` argument and never as `enc`. AXU of raw `ghash` on block lists
is false (`Axu.lean`), so the encoding must not be moved into `enc`.

## ROADMAP criterion 8 — the pad-leakage note

A successful decryption in the LIVE branch (`b = true`, i.e. `game2`) returns `C' ^^^ ks`:
it leaks the keystream pad. This authenticity hop therefore carries the confidentiality
consequence of live decryption, and the privacy hop is well-posed only between the
suppressed-decryption games.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational
open OracleComp.WegmanCarter

/-! ## Spec identification

`ToVCVio` may not import `SecureMessaging` (`AEAD/Defs.lean` already imports
`ToVCVio.OracleComp.SimSemantics.UnifLift`), so the brick spells the one-time AEAD CCA
spec inline as `wcSpec`. Since `aeadOneTimeCCASpec` is an `abbrev`, the two are the same
term; this `example` pins that in CI. -/
example (A M Cb : Type) :
    OracleComp.WegmanCarter.wcSpec A M Cb =
      AEADScheme.aeadOneTimeCCASpec A M (Cb × BitVec 128) := rfl

/-! ## The bridging lemma -/

/-- **Obligation WC-BRIDGE** (proved here). The Phase-2 instrumented handler
`gcmInstImpl (h, mask, ks) b` IS the generic Wegman–Carter handler `wcInstImpl`, at
`K := BitVec 128`, `D := SupportedAAD × BitVec L`, `enc := id`,
`hash := fun H p => ghash H (gcmEncode p.1 p.2)`, and `padMsg = unpad = (· ^^^ ks)`.

Two facts a fresh reader would otherwise re-discover the hard way:

* **Plain `rfl` FAILS**, and so does `simp only [...] ; rfl`. The only residual difference
  between the two `pp.explicit` terms is the matcher constant — `gcmGameSkeleton.match_1`
  versus `wcInstImpl.match_1` — and `isDefEq` will not identify two matcher auxiliaries at
  a stuck discriminant (here `__x.1`, a projection of a bound variable). Descending to the
  state with `funext s` and case-splitting the challenge slot makes the discriminant a
  constructor, so both matchers iota-reduce and each branch closes by `rfl`.
* **The tuple must be destructured in the statement.** `let (h, mask, ks) := a` does not
  reduce for a variable `a`. At use sites the outer bind is `a ← $ᵗ …`, so apply this
  lemma after `obtain ⟨h, mask, ks⟩ := a` under `bind_congr`. -/
theorem gcmInstImpl_eq_wcInstImpl (L : ℕ) (h mask : BitVec 128) (ks : BitVec L)
    (b : Bool) :
    gcmInstImpl (L := L) (h, mask, ks) b =
      OracleComp.WegmanCarter.wcInstImpl
        (A := SupportedAAD) (M := BitVec L) (Cb := BitVec L)
        (K := BitVec 128) (D := SupportedAAD × BitVec L)
        (fun H p => ghash H (gcmEncode p.1 p.2)) id h mask
        (fun m => m ^^^ ks) (fun c => c ^^^ ks) b := by
  funext t
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
  · rfl
  · funext s; obtain ⟨ch, fg⟩ := s; cases ch <;> rfl
  · funext s; obtain ⟨ch, fg⟩ := s; cases ch <;> rfl

/-! ## Staged obligations -/

/-- **Obligation WC9** (PROVED by plan 04-06). The per-`ks` forgery bound
on the GCM instrumented handler: with the GHASH key and the tag mask sampled at the top and
the keystream held fixed, the always-reject execution raises its `forged` flag with
probability at most `q_d · ε`.

Route: rewrite with `gcmInstImpl_eq_wcInstImpl` and apply
`OracleComp.WegmanCarter.probEvent_wcInst_forge_le`, supplying

* `haxu := haxu` — `GhashIsAXU L ε` unfolds to `IsAlmostXorUniversal` at exactly the
  brick's `hash` (`Axu.lean`, `GhashIsAXU` is a `def` with an `rfl` pin);
* `hfloor := ghashAXU_eps_lower haxu` (`Axu.lean`) — free, so no floor hypothesis leaks
  into this statement's hypothesis set;
* `henc_inj := Function.injective_id`;
* `hq` — **NOT directly**, contrary to what this docstring claimed before the phase's
  Codex interface review (finding F2, confirmed by a WC8→WC9 composition probe).
  `AEADScheme.decryptQueryBound` is indeed a `def` for
  `IsQueryBoundP (· matches Sum.inr _)`, but the two `matches` predicates elaborate to
  DIFFERENT matcher auxiliaries — `AEADScheme.decryptQueryBound.match_1` versus the one
  shared by the generic bound's declarations — and a direct application fails with a type
  mismatch. The transport is `isQueryBoundP_congr_pred` (VCVio
  `OracleComp/QueryTracking/QueryBound.lean`) at the pointwise `Iff`, which is `rfl` after
  a `cases` on the query index. Same predicate extensionally, same budget,
  `decryptQueryBound` still the sole counting hypothesis. -/
theorem probEvent_forge_gcmInst_le (L : ℕ) {ε : ℝ≥0∞} (haxu : GhashIsAXU L ε)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) (ks : BitVec L) :
    Pr[fun z : Bool × (Option (BitVec L × BitVec 128) × Bool) => z.2.2 = true |
        (do let h ← ($ᵗ (BitVec 128) : ProbComp _)
            let mask ← ($ᵗ (BitVec 128) : ProbComp _)
            (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false))]
      ≤ (q_d : ℝ≥0∞) * ε := by
  have hrw :
      (do let h ← ($ᵗ (BitVec 128) : ProbComp _)
          let mask ← ($ᵗ (BitVec 128) : ProbComp _)
          (simulateQ (gcmInstImpl (L := L) (h, mask, ks) false) adv).run (none, false)) =
        (do let H ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
            let mask ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
            (simulateQ (OracleComp.WegmanCarter.wcInstImpl
                (A := SupportedAAD) (M := BitVec L) (Cb := BitVec L)
                (K := BitVec 128) (D := SupportedAAD × BitVec L)
                (fun H p => ghash H (gcmEncode p.1 p.2)) id H mask
                (fun m => m ^^^ ks) (fun c => c ^^^ ks) false) adv).run (none, false)) :=
    bind_congr fun h => bind_congr fun mask => by
      rw [gcmInstImpl_eq_wcInstImpl]
  rw [hrw]
  exact probEvent_wcInst_forge_le haxu (ghashAXU_eps_lower haxu) Function.injective_id
    (fun m => m ^^^ ks) (fun c => c ^^^ ks) adv q_d
    ((isQueryBoundP_congr_pred (fun queryIndex => by cases queryIndex <;> rfl)).mp hq)

/-! ### The flag-monotonicity helper

WC-IUB0's second and third conjuncts are the SAME statement at `b = false` and `b = true`,
so they are proved once here, generically in `b`. -/

/-- The `forged` flag is monotone in every oracle of `gcmInstImpl a b`, at either `b`:
started from a state whose flag is already set, every reachable state has it set. The unif
and encrypt oracles thread the flag unchanged; the decrypt oracle either returns under the
challenge guard (flag unchanged) or writes `forged || ok = true || ok = true`. -/
private theorem gcmInstImpl_flag_mono (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L) (b : Bool)
    (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)).Domain)
    (p : Option (BitVec L × BitVec 128) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support (((gcmInstImpl a b) t).run p), z.2.2 = true := by
  obtain ⟨ch, fg⟩ := p
  obtain rfl : fg = true := hp
  intro z hz
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
  · -- OUnif: the lifted uniform oracle threads both state slots unchanged.
    simp only [add_apply_inl, gcmInstImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, beq_iff_eq, decide_eq_true_eq, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, QueryImpl.id'_apply, StateT.run_monadLift,
      monadLift_self, support_map, support_liftM, OracleQuery.input_query,
      OracleQuery.cont_query, Set.range_id, Set.image_univ] at hz
    obtain ⟨w, hw⟩ := hz
    exact hw ▸ rfl
  · -- OEncrypt: one-shot; the flag is written back unchanged in both branches.
    obtain ⟨h, mask, ks⟩ := a
    cases ch
    · simp only [add_apply_inl, add_apply_inr, gcmInstImpl, bind_pure_comp, beq_iff_eq,
        decide_eq_true_eq, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_map, StateT.run_set,
        map_pure, support_pure] at hz
      exact Set.eq_of_mem_singleton hz ▸ rfl
    · simp only [add_apply_inl, add_apply_inr, gcmInstImpl, bind_pure_comp, beq_iff_eq,
        decide_eq_true_eq, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, support_pure] at hz
      exact Set.eq_of_mem_singleton hz ▸ rfl
  · -- ODecrypt: guard split, then `ok` split; `true || ok = true` in every branch.
    obtain ⟨h, mask, ks⟩ := a
    by_cases hguard : ch = some e
    · simp only [add_apply_inr, gcmInstImpl, bind_pure_comp, beq_iff_eq,
        decide_eq_true_eq, QueryImpl.add_apply_inr, hguard, StateT.run_bind,
        StateT.run_get, pure_bind, ↓reduceIte, StateT.run_pure, support_pure] at hz
      exact Set.eq_of_mem_singleton hz ▸ rfl
    · by_cases hok : (e.2 = ghash h (gcmEncode ad e.1) ^^^ mask)
      · cases b
        · simp only [add_apply_inr, gcmInstImpl, bind_pure_comp, beq_iff_eq,
            decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte, ite_self,
            QueryImpl.add_apply_inr, hok, decide_true, Bool.or_true, StateT.run_bind,
            StateT.run_get, pure_bind, hguard, StateT.run_map, StateT.run_set, map_pure,
            support_pure] at hz
          exact Set.eq_of_mem_singleton hz ▸ rfl
        · simp only [add_apply_inr, gcmInstImpl, bind_pure_comp, beq_iff_eq,
            decide_eq_true_eq, ↓reduceIte, QueryImpl.add_apply_inr, hok, decide_true,
            Bool.or_true, StateT.run_bind, StateT.run_get, pure_bind, hguard,
            StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
          exact Set.eq_of_mem_singleton hz ▸ rfl
      · cases b
        · simp only [add_apply_inr, gcmInstImpl, bind_pure_comp, beq_iff_eq,
            decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte, ite_self,
            QueryImpl.add_apply_inr, hok, decide_false, Bool.or_false, Prod.mk.eta,
            StateT.run_bind, StateT.run_get, pure_bind, hguard, StateT.run_map,
            StateT.run_set, map_pure, support_pure] at hz
          exact Set.eq_of_mem_singleton hz ▸ rfl
        · simp only [add_apply_inr, gcmInstImpl, bind_pure_comp, beq_iff_eq,
            decide_eq_true_eq, ↓reduceIte, QueryImpl.add_apply_inr, hok, decide_false,
            Bool.or_false, Prod.mk.eta, StateT.run_bind, StateT.run_get, pure_bind,
            hguard, StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
          exact Set.eq_of_mem_singleton hz ▸ rfl

/-- **Obligation WC-IUB0** (PROVED by plan 04-06). THE
IDENTICAL-UNTIL-BAD STATE RELATION: the three per-oracle conditions of
`tvDist_simulateQ_le_probEvent_output_bad_base` (`IdenticalUntilBad.lean`), at the GCM
state and query types, bundled as one lemma.

This — not the distance bound `gcmInst_tvDist_le_probEvent_forge` below — is what ROADMAP
Phase 4 criterion 1 means by staging "the identical-until-bad state relation" as a typed
`sorry`-bodied lemma: an output-distance inequality is strictly weaker, since two handlers
can return equal responses with equal bad flags while writing different hidden base states,
making the distance bound read `0 ≤ 0` where good-transition equality reads `1 = 0`.

The three conjuncts are `h_agree_good`, `h_mono₁`, `h_mono₂`, instantiated at
`spec := aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)`,
`spec₂ := unifSpec` (`ProbComp` IS `OracleComp unifSpec`, so the brick's
`[IsUniformSpec spec₂]` is satisfied) and `σ := Option (BitVec L × BitVec 128)`.

Why they hold: the `forged` flag is write-only in BOTH branches (the update is
`forged || ok`, identical at `b = false` and `b = true`, and never cleared), and the two
branches differ ONLY in the decrypt oracle's returned response on `ok = true` — which is
exactly a transition the first conjunct excludes, since on that transition the resulting
flag is `true`, not `false`.

Route: read the three conditions off the decrypt normal form
(`OracleComp.WegmanCarter.wcInstImpl_decrypt_run` gives the shape via
`gcmInstImpl_eq_wcInstImpl`); `Games.lean`'s own flag-erasure proofs are the model for the
per-oracle case discipline. -/
theorem gcmInstImpl_identicalUntilBad (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L) :
    (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
               (BitVec L × BitVec 128)).Domain)
        (s : Option (BitVec L × BitVec 128))
        (u : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
               (BitVec L × BitVec 128)).Range t)
        (s' : Option (BitVec L × BitVec 128)),
      Pr[= (u, (s', false)) | ((gcmInstImpl a false) t).run (s, false)] =
        Pr[= (u, (s', false)) | ((gcmInstImpl a true) t).run (s, false)])
    ∧ (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
                 (BitVec L × BitVec 128)).Domain)
          (p : Option (BitVec L × BitVec 128) × Bool), p.2 = true →
        ∀ z ∈ support (((gcmInstImpl a false) t).run p), z.2.2 = true)
    ∧ (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
                 (BitVec L × BitVec 128)).Domain)
          (p : Option (BitVec L × BitVec 128) × Bool), p.2 = true →
        ∀ z ∈ support (((gcmInstImpl a true) t).run p), z.2.2 = true) := by
  refine ⟨?_, fun t p hp => gcmInstImpl_flag_mono L a false t p hp,
    fun t p hp => gcmInstImpl_flag_mono L a true t p hp⟩
  rintro ((n | ⟨ad, m⟩) | ⟨ad, e⟩) s u s'
  · -- OUnif: `b` does not occur in this summand.
    rfl
  · -- OEncrypt: `b` does not occur in this summand.
    rfl
  · -- ODecrypt: under the guard both branches are `pure none` at an unchanged state; off
    -- the guard, `ok = false` makes both `pure none` at flag `false`, and `ok = true`
    -- makes BOTH sides write flag `true`, so the observed `false`-flag transition has
    -- probability `0` on each side (this is the transition the two handlers differ on).
    obtain ⟨h, mask, ks⟩ := a
    by_cases hguard : s = some e
    · simp [gcmInstImpl, StateT.run_bind, StateT.run_get,
        StateT.run_pure, beq_iff_eq, hguard]
    · by_cases hok : (e.2 = ghash h (gcmEncode ad e.1) ^^^ mask) <;>
        simp [gcmInstImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
          beq_iff_eq, hguard, hok]

/-- **Obligation WC-IUB** (PROVED by plan 04-06). The identical-until-bad
DISTANCE BOUND at a fixed tuple: `gcmInstImpl_identicalUntilBad` (WC-IUB0) fed through
`tvDist_simulateQ_le_probEvent_output_bad_base` (`IdenticalUntilBad.lean`) at
`impl₁ := gcmInstImpl a false`, `impl₂ := gcmInstImpl a true`.

Staged alongside WC-IUB0 because it is the shape the assembly in `game2_game3_le_auth`
consumes. Note `game3Flat`'s handler (`b = false`) sits in the FIRST slot, so the charged
bad event is the ALWAYS-REJECT execution's — ROADMAP criterion 6. Plan 04-06 Task 2 step 1
closes BOTH WC-IUB0 and WC-IUB: the three conditions are no longer anonymous private
helpers, they are WC-IUB0's conjuncts. -/
theorem gcmInst_tvDist_le_probEvent_forge (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    tvDist ((simulateQ (gcmInstImpl a false) adv).run' (none, false))
        ((simulateQ (gcmInstImpl a true) adv).run' (none, false))
      ≤ Pr[fun z : Bool × (Option (BitVec L × BitVec 128) × Bool) => z.2.2 = true |
          (simulateQ (gcmInstImpl a false) adv).run (none, false)].toReal := by
  obtain ⟨h_agree_good, h_mono₁, h_mono₂⟩ := gcmInstImpl_identicalUntilBad L a
  exact tvDist_simulateQ_le_probEvent_output_bad_base (gcmInstImpl a false)
    (gcmInstImpl a true) adv none h_agree_good h_mono₁ h_mono₂

/-- **Obligation WC10 — THE PHASE THEOREM** (staged here, discharged by plan 04-06).

`|Pr[game3] − Pr[game2]| ≤ q_d · ε`: suppressing live decryption costs at most the
one-time Wegman–Carter forgery probability. The argument order matches EtM's landed
`game1_game2_le_auth` (`FromEtM/Security/Auth/Hop.lean`); Phase 6's triangle inequality
consumes this exact orientation.

Route: `tvDist_bind_left_le` (VCVio `EvalDist/TVDist.lean` — NOT
`tvDist_bind_left_le_const'`, unusable here since at a fixed tuple the forgery probability
is 0 or 1, ROADMAP criterion 6) over the outer tuple sample, with the per-tuple distance
supplied by `gcmInst_tvDist_le_probEvent_forge` and the per-tuple bad probability by
`probEvent_forge_gcmInst_le`; then the two Phase-2 projections `game3Flat_eq_game3` and
`game2Flat_eq_game2` (`Games.lean`) to move from the instrumented games to `game3`/`game2`;
then `abs_probOutput_toReal_sub_le_tvDist` (`TVDist.lean`) to leave `ℝ≥0∞` for `ℝ`, which
is where `hε : ε ≠ ⊤` is consumed. -/
theorem game2_game3_le_auth {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    {ε : ℝ≥0∞} (hε : ε ≠ ⊤) (haxu : GhashIsAXU L ε) :
    |(Pr[= true | game3 prp L hL adv]).toReal -
      (Pr[= true | game2 prp L hL adv]).toReal| ≤ (q_d : ℝ) * ε.toReal :=
  sorry

end GCM
