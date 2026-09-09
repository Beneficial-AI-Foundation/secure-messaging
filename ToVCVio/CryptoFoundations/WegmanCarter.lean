/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.UniversalHash
import ToVCVio.CryptoFoundations.WegmanCarterBound
import ToVCVio.OracleComp.QueryTracking.LazySampling
import ToVCVio.OracleComp.SimSemantics.UnifLift
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Wegman–Carter one-time authenticity: the generic forgery brick

The generic (GCM-free) Wegman–Carter authenticity brick: a one-time AEAD whose tag is
`hash H (enc (ad, c)) ^^^ mask`, with `H` a uniformly random hash key and `mask` a
uniformly random one-time pad on the tag, admits at most `q · ε` forgery probability
against an adversary making at most `q` decryption queries, where `ε` bounds the
almost-XOR-universality of the hash family. The public deliverable is
`probEvent_wcInst_forge_le`.

## Layering

This file lives in `ToVCVio` and therefore may NOT import `SecureMessaging`
(`SecureMessaging/AEAD/Defs.lean` already imports `ToVCVio.OracleComp.SimSemantics.UnifLift`,
so the reverse import would invert the library layering). `wcSpec` below is a verbatim
inline spelling of `AEADScheme.aeadOneTimeCCASpec A M (Cb × BitVec 128)`, which is an
`abbrev`; the identification with it is pinned by an `example … := rfl` on the
`SecureMessaging` side, in `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean`.

## AXU domain warning

Almost-XOR-universality must be assumed of the composite `hash` on the ENCODED domain
`D`, never of a raw pre-encoding hash on block lists. For GCM this means
`hash := fun H p => ghash H (gcmEncode p.1 p.2)` at `D := SupportedAAD × BitVec L` and
`enc := id` — raw-block-list AXU for `ghash` is FALSE
(`ghash h [0, X] = ghash h [X]`; see `SecureMessaging/AEAD/FromGCM/Security/Axu.lean`).

## Structural facts, recorded rather than hypothesized

* **`X*`-independence is structural, and is deliberately NOT stated as a typed
  `sorry`-bodied lemma** (a deliberate deviation from ROADMAP Phase 4 criterion 1's
  staging requirement). The challenge digest `X* = enc (ad*, padMsg m*)` is built from
  `padMsg` and `enc`, whose binder types — `M → Cb` and `A × Cb → D` — cannot mention
  `(H, mask)`. There is nothing to state.
* **Hidden verification results do not influence adversary-visible behavior.** The
  decrypt oracle of `wcInstImpl … false` returns `none` in EVERY branch (guard, accept,
  reject alike), so the `forged` flag is genuinely write-only. Note the collapse is not
  `rfl`: at `b = false` the body is literally `if ok then pure none else pure none`,
  which needs `ite_self` or a case split on `ok`. `wcInstImpl_decrypt_run` is the named
  normal form that does this once and for all.

## ROADMAP criterion 8 — the pad-leakage note

A successful decryption in the LIVE branch (`b = true`) returns `unpad e.1`, which at
the GCM instantiation is `C' ^^^ ks`: it leaks the keystream pad. This authenticity hop
therefore carries the confidentiality consequence of live decryption, and the privacy
hop is well-posed only between the suppressed-decryption games.

## Main definitions

- `wcSpec` — the one-time AEAD CCA spec, spelled inline.
- `wcInstImpl` — the flag-instrumented generic Wegman–Carter handler.
- `WCLogState`, `wcLogImpl` — the log-refined state and handler, whose decrypt oracle
  reads NEITHER `H` NOR `mask`.
- `wcAccepts`, `wcFlag`, `wcProj` — the fold recovering the flag, and the state
  projection from the log-refined state onto `wcInstImpl`'s.

## Main statements

- `wcInstImpl_decrypt_run` — the decrypt normal form (PROVED here).
- `probEvent_wcInst_forge_le` — the public `q · ε` forgery bound.

The remaining declarations below are typed `sorry`-bodied lemmas staged by plan 04-01 and
discharged by later plans of the phase; each docstring names its owning plan.
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace OracleComp.WegmanCarter

/-! ## The spec -/

/-- The one-time AEAD CCA spec, spelled inline. Definitionally and syntactically the
unfolding of `AEADScheme.aeadOneTimeCCASpec A M (Cb × BitVec 128)`; the identification is
pinned by an `example … := rfl` in `SecureMessaging/AEAD/FromGCM/Security/AuthHop.lean`
(this file may not import `SecureMessaging`). -/
abbrev wcSpec (A M Cb : Type) :=
  unifSpec + (A × M →ₒ Option (Cb × BitVec 128)) + (A × (Cb × BitVec 128) →ₒ Option M)

/-! ## The flag-instrumented handler -/

/-- The generic flag-instrumented Wegman–Carter handler: a verbatim generic copy of the
GCM handler `GCM.gcmInstImpl`.

State is `Option (Cb × BitVec 128) × Bool`, the challenge ciphertext slot and the
monotone `forged` flag (RIGHTMOST, as the identical-until-bad brick requires). Encryption
is one-shot and produces `(padMsg m, hash H (enc (ad, padMsg m)) ^^^ mask)`. Decryption
implements the ciphertext-only challenge guard, sets the flag whenever verification would
accept (`forged || ok`, identical in both `b` branches, never cleared), and returns
`unpad e.1` on acceptance only when `b = true`.

Both `b` and `unpad` are kept so the SAME handler and the SAME bridging lemma serve the
always-reject execution (`b = false`) and the live-decrypt execution (`b = true`).
`[DecidableEq Cb]`, not `[BEq Cb]`: the resulting `BEq` instance path then matches the GCM
guard's syntactically after instantiation. -/
noncomputable def wcInstImpl {K A M Cb D : Type} [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M) (b : Bool) :
    QueryImpl (wcSpec A M Cb)
      (StateT (Option (Cb × BitVec 128) × Bool) ProbComp) :=
  (unifLiftStateT (Option (Cb × BitVec 128) × Bool) unifSpec)
  + ((fun (ad, m) => do
      let (challenge, forged) ← get
      match challenge with
      | some _ => pure none
      | none => do
        let c := padMsg m
        let e := (c, hash H (enc (ad, c)) ^^^ mask)
        set ((some e, forged) : Option (Cb × BitVec 128) × Bool)
        return some e) : QueryImpl (A × M →ₒ Option (Cb × BitVec 128))
      (StateT (Option (Cb × BitVec 128) × Bool) ProbComp))
  + ((fun (ad, e) => do
      let (challenge, forged) ← get
      if challenge == some e then pure none
      else do
        let ok : Bool := decide (e.2 = hash H (enc (ad, e.1)) ^^^ mask)
        set ((challenge, forged || ok) : Option (Cb × BitVec 128) × Bool)
        if ok then (if b then pure (some (unpad e.1)) else pure none) else pure none) :
    QueryImpl (A × (Cb × BitVec 128) →ₒ Option M)
      (StateT (Option (Cb × BitVec 128) × Bool) ProbComp))

section DecryptNormalForm

variable {K A M Cb D : Type}

/-- **Obligation WC0** (proved here). The decrypt normal form of the ALWAYS-REJECT
instrumented handler: the response is `none` unconditionally, and the state transition is
a pure flag update — untouched under the challenge guard, `forged || ok` otherwise.

Every later per-query obligation of this phase rewrites through this lemma. Note the
collapse is NOT `rfl`: at `b = false` the returned computation is literally
`if ok then pure none else pure none`, which is not definitionally `pure none` for a
stuck `ok`; it needs `ite_self` (here supplied by `simp` after the guard case split). -/
theorem wcInstImpl_decrypt_run [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M)
    (ad : A) (e : Cb × BitVec 128)
    (ch : Option (Cb × BitVec 128)) (fg : Bool) :
    ((wcInstImpl hash enc H mask padMsg unpad false) (Sum.inr (ad, e))).run (ch, fg) =
      (pure (none, (ch, if ch = some e then fg
        else fg || decide (e.2 = hash H (enc (ad, e.1)) ^^^ mask))) : ProbComp _) := by
  by_cases hg : ch = some e <;>
    simp [wcInstImpl, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      beq_iff_eq, hg]

end DecryptNormalForm

/-! ## The log-refined handler

Step 1 of the phase's five-step chain. The `Bool` flag is replaced by a LOG of the
guard-passing decrypt queries, which removes `(H, mask)` from the decrypt oracle
entirely; the flag is recovered as a pure fold (`wcFlag`) over the log. The challenge
slot additionally carries its AAD, because the AXU application needs the full digest
point `X* = enc (ad*, c*)` and the uninstrumented game state records the ciphertext only.
Each log entry carries a `Bool` tag: `false` = logged BEFORE the challenge was set,
`true` = logged after. The pre/post split of the probability core is charged to two
disjoint index sets (pre-challenge entries to the fresh `mask`, post-challenge entries to
AXU over `H`), which is what keeps the bound at `q · ε` rather than `2 · q · ε`. -/

/-- The log-refined state: the challenge ciphertext WITH its AAD, and the list of raw
guard-passing decrypt queries, each tagged `false` (pre-challenge) or `true`
(post-challenge). -/
abbrev WCLogState (A Cb : Type) :=
  Option (A × (Cb × BitVec 128)) × List (A × (Cb × BitVec 128) × Bool)

/-- The log-refined handler. Its decrypt oracle reads NEITHER `H` NOR `mask` — it merely
appends the raw query to the log with its pre/post tag — which is the whole point of step
1 of the chain. The observable behaviour is unchanged: the guard compares
`challenge.map Prod.snd` against the queried ciphertext, exactly as `wcInstImpl` compares
its challenge slot, and every decrypt response is `none`. -/
noncomputable def wcLogImpl {K A M Cb D : Type} [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128) (padMsg : M → Cb) :
    QueryImpl (wcSpec A M Cb) (StateT (WCLogState A Cb) ProbComp) :=
  (unifLiftStateT (WCLogState A Cb) unifSpec)
  + ((fun (ad, m) => do
      let (challenge, log) ← get
      match challenge with
      | some _ => pure none
      | none => do
        let c := padMsg m
        let e := (c, hash H (enc (ad, c)) ^^^ mask)
        set ((some (ad, e), log) : WCLogState A Cb)
        return some e) : QueryImpl (A × M →ₒ Option (Cb × BitVec 128))
      (StateT (WCLogState A Cb) ProbComp))
  + ((fun (ad, e) => do
      let (challenge, log) ← get
      if challenge.map Prod.snd == some e then pure none
      else do
        set ((challenge, log ++ [(ad, e, challenge.isSome)]) : WCLogState A Cb)
        pure none) : QueryImpl (A × (Cb × BitVec 128) →ₒ Option M)
      (StateT (WCLogState A Cb) ProbComp))

/-- Acceptance of a single logged decrypt query: the tag matches the Wegman–Carter tag of
the query's own digest point. This is the per-entry predicate the flag folds. -/
def wcAccepts {K A Cb D : Type} (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128) (q : A × (Cb × BitVec 128) × Bool) : Bool :=
  decide (q.2.1.2 = hash H (enc (q.1, q.2.1.1)) ^^^ mask)

/-- The `forged` flag, recovered as a pure fold over the log. -/
def wcFlag {K A Cb D : Type} (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128) (s : WCLogState A Cb) : Bool :=
  s.2.any (wcAccepts hash enc H mask)

/-- The state projection from the log-refined state onto `wcInstImpl`'s: forget the
challenge AAD, and collapse the log to the flag. -/
def wcProj {K A Cb D : Type} (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128) (s : WCLogState A Cb) :
    Option (Cb × BitVec 128) × Bool :=
  (s.1.map Prod.snd, wcFlag hash enc H mask s)

/-! ## Staged obligations -/

section StagedRefinement

variable {K A M Cb D : Type}

/-! ### The three per-oracle projection steps

WC1's single obligation is a per-query identity, discharged one oracle at a time. Splitting
it is not cosmetic: a single monolithic `rfl`/`simp` over the three handler summands makes
the kernel unfold all of them at once, which has already timed out once in this phase. -/

/-- Per-oracle projection step at the uniform oracle: both handlers forward the query
through `unifLiftStateT`, threading the state unchanged, so `wcProj` commutes trivially. -/
private lemma hproj_unif [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M)
    (n : ℕ) (s : WCLogState A Cb) :
    Prod.map id (wcProj hash enc H mask) <$>
        ((wcLogImpl hash enc H mask padMsg) (Sum.inl (Sum.inl n))).run s =
      ((wcInstImpl hash enc H mask padMsg unpad false) (Sum.inl (Sum.inl n))).run
        (wcProj hash enc H mask s) := by
  simp [wcLogImpl, wcInstImpl, unifLiftStateT,
    QueryImpl.liftTarget_apply, StateT.run_monadLift, Prod.map, Functor.map_map]

/-- Per-oracle projection step at the one-shot encrypt oracle. The challenge slot is cased
FIRST: at a stuck `Option` discriminant the two `match` auxiliaries are not `isDefEq`, and
making it a constructor lets both iota-reduce. In the `none` branch the log-refined handler
writes `some (ad, e)` while the instrumented one writes `some e`; `wcProj`'s
`Option.map Prod.snd` bridges them, and the log is untouched so `wcFlag` is unchanged. -/
private lemma hproj_encrypt [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M)
    (ad : A) (m : M) (s : WCLogState A Cb) :
    Prod.map id (wcProj hash enc H mask) <$>
        ((wcLogImpl hash enc H mask padMsg) (Sum.inl (Sum.inr (ad, m)))).run s =
      ((wcInstImpl hash enc H mask padMsg unpad false) (Sum.inl (Sum.inr (ad, m)))).run
        (wcProj hash enc H mask s) := by
  obtain ⟨ch, log⟩ := s
  cases ch <;>
    simp [wcLogImpl, wcInstImpl, wcProj, wcFlag, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, Prod.map]

/-- Per-oracle projection step at the decrypt oracle, the only one with content. The
instrumented side is rewritten through the normal form `wcInstImpl_decrypt_run` rather than
unfolded again. Under the guard both sides leave their state alone, and the two guards are
the SAME test because `wcProj`'s challenge component is `Option.map Prod.snd`. Off the guard
the log grows by one entry and `List.any_append` turns the fold into
`wcFlag log || wcAccepts (ad, e, _)`, which is exactly the `forged || ok` of the normal form:
`wcAccepts` ignores the entry's pre/post tag. -/
private lemma hproj_decrypt [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M)
    (ad : A) (e : Cb × BitVec 128) (s : WCLogState A Cb) :
    Prod.map id (wcProj hash enc H mask) <$>
        ((wcLogImpl hash enc H mask padMsg) (Sum.inr (ad, e))).run s =
      ((wcInstImpl hash enc H mask padMsg unpad false) (Sum.inr (ad, e))).run
        (wcProj hash enc H mask s) := by
  obtain ⟨ch, log⟩ := s
  rw [show (wcProj hash enc H mask (ch, log)) =
        (ch.map Prod.snd, wcFlag hash enc H mask (ch, log)) from rfl,
    wcInstImpl_decrypt_run hash enc H mask padMsg unpad ad e]
  by_cases hg : ch.map Prod.snd = some e
  · simp [wcLogImpl, wcProj, StateT.run_bind, StateT.run_get, Prod.map, hg]
  · simp [wcLogImpl, wcProj, wcFlag, wcAccepts, StateT.run_bind, StateT.run_get,
      StateT.run_set, Prod.map, hg, List.any_append]

/-- **Obligation WC1** (staged here, discharged by plan 04-03). Log refinement, JOINT
(output AND state): projecting the log-refined run with `wcProj` recovers the
instrumented run.

Route: `map_run_simulateQ_eq_of_query_map_eq`
(VCVio `SimSemantics/StateT/StateProjection.lean:53`) at `proj := wcProj hash enc H mask`
— the `.run` version, NOT the `run'` one at `:75`, because the bad event reads the final
state. -/
theorem map_run_simulateQ_wcLogImpl_eq {α : Type} [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M)
    (oa : OracleComp (wcSpec A M Cb) α) (s : WCLogState A Cb) :
    Prod.map id (wcProj hash enc H mask) <$>
        (simulateQ (wcLogImpl hash enc H mask padMsg) oa).run s =
      (simulateQ (wcInstImpl hash enc H mask padMsg unpad false) oa).run
        (wcProj hash enc H mask s) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ (wcProj hash enc H mask) ?_ oa s
  rintro ((n | ⟨ad, m⟩) | ⟨ad, e⟩) s
  · exact hproj_unif hash enc H mask padMsg unpad n s
  · exact hproj_encrypt hash enc H mask padMsg unpad ad m s
  · exact hproj_decrypt hash enc H mask padMsg unpad ad e s

/-- **Obligation WC2** (staged here, discharged by plan 04-03). Transport of the bad event
across the log refinement WC1.

Route: `probEvent_map` (VCVio `EvalDist/Monad/Map.lean:125`) applied to WC1, using
`wcProj`'s second component being `wcFlag` by definition. -/
theorem probEvent_bad_wcInst_eq_wcLog {α : Type} [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M) (oa : OracleComp (wcSpec A M Cb) α) :
    Pr[fun z : α × (Option (Cb × BitVec 128) × Bool) => z.2.2 = true |
        (simulateQ (wcInstImpl hash enc H mask padMsg unpad false) oa).run (none, false)] =
      Pr[fun z : α × WCLogState A Cb => wcFlag hash enc H mask z.2 = true |
        (simulateQ (wcLogImpl hash enc H mask padMsg) oa).run (none, [])] := by
  have hs : wcProj hash enc H mask ((none, []) : WCLogState A Cb) = (none, false) := rfl
  have h1 := map_run_simulateQ_wcLogImpl_eq hash enc H mask padMsg unpad oa (none, [])
  rw [hs] at h1
  rw [← h1, probEvent_map]
  rfl

end StagedRefinement

/-- **Obligation WC3, first declaration** (staged here, discharged by plan 04-03). Generic
support-level transfer of a predicate-targeted query bound to a STATE MEASURE: if a state
functional `f` grows by at most one at every `p`-query and never grows at a `¬ p`-query,
then along every run in the support it grows by at most the `p`-query budget.

Route: an induction modelled on `IsQueryBoundP.simulateQ_run_of_step`
(VCVio `QueryTracking/QueryBound.lean:1331-1357`), which itself CANNOT deliver this: its
conclusion bounds the number of TARGET-spec queries made by the simulated run, not a
functional of the simulated state. Only its PROOF SHAPE carries over — induction on `oa`
generalizing the budget and the state, `isQueryBoundP_query_bind_iff` to peel one query,
then a `support`-of-bind membership step feeding the induction hypothesis with the residual
budget, split on `p t` to spend `1` or `0`.

This bound is deliberately SUPPORT-LEVEL and deliberately decoupled from the probability
argument. An interleaved induction (the Encrypt-then-MAC analogue, `probForge_run_le`) charges
`ε` per query as it goes, which is incompatible with hoisting the hash key `H` past the whole
run to the end; here the count is established once, on the support, and consumed later as a
pure cardinality fact. No counter is threaded through the handler state. -/
theorem support_state_measure_le_of_isQueryBoundP
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (f : σ → ℕ)
    (p : ι → Prop) [DecidablePred p]
    (hstep_p : ∀ t, p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s + 1)
    (hstep_np : ∀ t, ¬ p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP p n) (s : σ) :
    ∀ z ∈ support ((simulateQ impl oa).run s), f z.2 ≤ f s + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp
  | query_bind t oa ih =>
      intro z hz
      rw [isQueryBoundP_query_bind_iff] at hq
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      have hrec := ih x.1 (if p t then n - 1 else n) (hq.2 x.1) x.2 z hzx
      by_cases hpt : p t
      · have h1 := hstep_p t hpt s x hx
        have h2 : 0 < n := hq.1.resolve_left (not_not_intro hpt)
        simp only [if_pos hpt] at hrec
        omega
      · have h1 := hstep_np t hpt s x hx
        simp only [if_neg hpt] at hrec
        omega

section StagedCounting

variable {K A M Cb D : Type}

/-- **Obligation WC3, second declaration** (staged here, discharged by plan 04-03). The
log never exceeds the adversary's decrypt-query budget, at the support level.

Route: `support_state_measure_le_of_isQueryBoundP` at `f := fun s => s.2.length`,
`p := (· matches Sum.inr _)` — the encrypt and unif oracles never append, and the decrypt
oracle appends at most one entry (exactly one off the challenge guard, none under it).

As with the generic lemma, this is a support-level fact established independently of the
probability charge, and the handler carries no query counter: the budget lives entirely in
`decryptQueryBound` (`IsQueryBoundP`) on the adversary. -/
theorem wcLogImpl_log_length_le {α : Type} [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (oa : OracleComp (wcSpec A M Cb) α) (q : ℕ)
    (hq : oa.IsQueryBoundP (· matches Sum.inr _) q) :
    ∀ z ∈ support ((simulateQ (wcLogImpl hash enc H mask padMsg) oa).run (none, [])),
      z.2.2.length ≤ q := by
  have hp : ∀ t : (wcSpec A M Cb).Domain, (t matches Sum.inr _) →
      ∀ s : WCLogState A Cb, ∀ z ∈ support ((wcLogImpl hash enc H mask padMsg t).run s),
        z.2.2.length ≤ s.2.length + 1 := by
    rintro ((n | ⟨ad, m⟩) | ⟨ad, e⟩) ht ⟨ch, log⟩ z hz
    · simp at ht
    · simp at ht
    · by_cases hg : (Option.map Prod.snd ch : Option (Cb × BitVec 128)) = some e
      · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
          Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, pure_bind, hg, BEq.rfl, ↓reduceIte,
          StateT.run_pure, support_pure] at hz
        subst hz
        simp
      · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
          Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_map,
          StateT.run_set, map_pure, support_pure] at hz
        subst hz
        simp
  have hnp : ∀ t : (wcSpec A M Cb).Domain, ¬ (t matches Sum.inr _) →
      ∀ s : WCLogState A Cb, ∀ z ∈ support ((wcLogImpl hash enc H mask padMsg t).run s),
        z.2.2.length ≤ s.2.length := by
    rintro ((n | ⟨ad, m⟩) | ⟨ad, e⟩) ht ⟨ch, log⟩ z hz
    · simp only [add_apply_inl, wcLogImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
        bind_pure_comp, beq_iff_eq, Option.map_eq_some_iff, Prod.exists, exists_eq_right,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
        StateT.run_monadLift, monadLift_self, support_map, support_liftM,
        OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hz
      obtain ⟨u, hu⟩ := hz
      simp [← hu]
    · cases ch with
      | none =>
        simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
          Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inl,
          QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
        subst hz
        simp
      | some c0 =>
        simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
          Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inl,
          QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_pure, support_pure] at hz
        subst hz
        simp
    · simp at ht
  intro z hz
  simpa using support_state_measure_le_of_isQueryBoundP
    (wcLogImpl hash enc H mask padMsg) (fun s : WCLogState A Cb => s.2.length)
    (· matches Sum.inr _) hp hnp oa q hq (none, []) z hz

/-! ### The post-challenge guard invariant

WC3b is proved as a support-level invariant of the run, carried by
`simulateQ_run_preserves_inv_of_query` (VCVio `SimSemantics/StateT/StateProjection.lean`),
which is already in scope here. VCVio's `QueryImpl.PreservesInv` packaging would serve
equally well but lives behind an import this file does not otherwise need. -/

/-- The two-clause state invariant behind `wcLogImpl_post_ne_challenge`.

The FIRST clause is load-bearing: the second alone is not inductive at the encrypt step.
From `s = (none, [(ad, e, true)])`, which satisfies the second clause vacuously, an encrypt
query emitting exactly `e` sets the challenge to `some (ad, e)` and leaves the log alone, so
the post-tagged entry now equals the challenge. The first clause rules that initial state
out, and it is what supplies "every existing entry is PRE-tagged" at the encrypt step, where
no appeal to the entry's history is available under the generalised induction. -/
private def PostInv (s : WCLogState A Cb) : Prop :=
  (s.1 = none → ∀ q ∈ s.2, q.2.2 = false) ∧
    (∀ q ∈ s.2, q.2.2 = true → ∀ c ∈ s.1, q.2.1 ≠ c.2)

/-- The initial state of the run satisfies both clauses vacuously. -/
private lemma postInv_nil : PostInv ((none, []) : WCLogState A Cb) :=
  ⟨fun _ q hq => absurd hq (by simp), fun q hq => absurd hq (by simp)⟩

/-- Every oracle step of `wcLogImpl` preserves `PostInv` on the support.

Unif leaves the state alone. Encrypt at `some _` does not write; at `none` the challenge
becomes `some (ad, e)` while the log is unchanged, and the first clause makes the second
clause's `q.2.2 = true` premise vacuous for every existing entry (the successor's first
clause is then vacuous because its challenge is `some`). Decrypt under the guard does not
write; off the guard the appended entry is tagged `challenge.isSome`, and when that is
`true` the failed guard `challenge.map Prod.snd ≠ some e` says exactly `e ≠ c.2` for the
challenge's `c`. -/
private lemma postInv_step [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) :
    ∀ (t : (wcSpec A M Cb).Domain) (s : WCLogState A Cb), PostInv s →
      ∀ y ∈ support ((wcLogImpl hash enc H mask padMsg t).run s), PostInv y.2 := by
  rintro ((n | ⟨ad, m⟩) | ⟨ad, e⟩) ⟨ch, log⟩ hinv y hy
  · -- OUnif: the state is threaded unchanged.
    simp only [add_apply_inl, wcLogImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, beq_iff_eq, Option.map_eq_some_iff, Prod.exists, exists_eq_right,
      QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
      StateT.run_monadLift, monadLift_self, support_map, support_liftM,
      OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hy
    obtain ⟨u, hu⟩ := hy
    simpa [← hu] using hinv
  · -- OEncrypt: one-shot; only the `none` branch writes, and only the challenge slot.
    cases ch with
    | none =>
      simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_map, StateT.run_set, map_pure, support_pure] at hy
      subst hy
      refine ⟨by simp, ?_⟩
      intro q hq hqt c hc
      exact absurd (hinv.1 rfl q hq) (by simp [hqt])
    | some c0 =>
      simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_pure, support_pure] at hy
      subst hy
      exact hinv
  · -- ODecrypt: the guard branch does not write; otherwise one tagged entry is appended.
    by_cases hg : (Option.map Prod.snd ch : Option (Cb × BitVec 128)) = some e
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hg, BEq.rfl, ↓reduceIte,
        StateT.run_pure, support_pure] at hy
      subst hy
      exact hinv
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_map,
        StateT.run_set, map_pure, support_pure] at hy
      subst hy
      constructor
      · rintro (h1 : ch = none) q hq
        subst h1
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hinv.1 rfl q hq
        · simp
      · intro q hq hqt c hc
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hinv.2 q hq hqt c hc
        · simp only at hqt hc ⊢
          cases ch with
          | none => simp at hc
          | some c1 =>
            simp only [Option.mem_def, Option.some.injEq] at hc
            subst hc
            intro hcontra
            exact hg (by simp [hcontra])

/-- **Obligation WC3b** (staged here, discharged by plan 04-03). The guard invariant the
post-challenge half of the bound consumes: a POST-tagged log entry is never the challenge
ciphertext, because the guard branch returns before appending.

Only post-tagged entries carry this guarantee: a pre-tagged entry may coincide with a
LATER challenge ciphertext by chance, and that case is charged to the pre-challenge half
of the bound (a blind guess against the fresh mask), not to AXU.

Route: a two-clause support invariant carried through the run — (i) the challenge slot is
monotone (once `some`, never changed), (ii) every post-tagged entry differs from the
challenge slot's ciphertext at the moment it was appended. -/
theorem wcLogImpl_post_ne_challenge {α : Type} [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (oa : OracleComp (wcSpec A M Cb) α) :
    ∀ z ∈ support ((simulateQ (wcLogImpl hash enc H mask padMsg) oa).run (none, [])),
      ∀ e ∈ z.2.2, e.2.2 = true → ∀ c ∈ z.2.1, e.2.1 ≠ c.2 := by
  intro z hz
  exact (simulateQ_run_preserves_inv_of_query (wcLogImpl hash enc H mask padMsg) PostInv
    (postInv_step hash enc H mask padMsg) oa (none, []) postInv_nil z hz).2

end StagedCounting

/-! ## The probability core and the public brick

The chain from the log-refined run to the `q · ε` bound. The five-step chain of
`04-CONTEXT` is realised here as an induction over the adversary that conditions on the
prefix SYNTACTICALLY, which is what makes the frozen pre-challenge log a fixed list at the
point where the mask is charged:

* while the challenge slot is `none` the handler is `(H, mask)`-free, so the two top-level
  draws commute past every step (`hoist_step`) and the induction walks to the encrypt query
  charging one log entry per decrypt query (`pre_phase`);
* at the encrypt query the pre-challenge log `L` is a FIXED list, the mask is still fresh,
  and the pre-half is a blind guess: `probEvent_pre_fresh_le` at `ν := $ᵗ K`
  (`pre_half_le`);
* from the encrypt query on, the challenge slot is `some`, so the handler no longer reads
  `(H, mask)` at all (`run_challenge_some_indep`); reparameterizing the mask draw by the
  XOR-by-constant bijection `mask ↦ hash H X* ^^^ mask` makes the run emit the TAG
  uniformly and become `H`-free (`reparam_bind`), after which `H` hoists past the whole run
  (`hoist_H`) and the post-half is `probEvent_post_axu_le` (`post_half_le`);
* the two halves are combined at the SHARED count `L.length + n` by `combine_pre_post_le`
  (`post_phase`), never bounded by the budget separately.
-/

section ProbabilityCore

variable {K A M Cb D : Type}

/-! ### `BitVec` rearrangements

The tag is pinned to `BitVec 128` precisely so the Wegman–Carter acceptance test can be
solved for the mask (and for the offset) by XOR cancellation alone. -/

/-- Solving the acceptance test `T' = hash H X' ^^^ mask` for the mask. -/
private lemma tag_eq_iff_mask_eq (a h m : BitVec 128) :
    a = h ^^^ m ↔ m = a ^^^ h := by
  constructor
  · rintro rfl
    simp [BitVec.xor_comm]
  · rintro rfl
    rw [BitVec.xor_comm a h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- XOR by a constant is a bijection on `BitVec 128`. This is the local reparameterization
at the encrypt query: sampling the mask and deriving the tag has the same law as sampling
the tag and deriving the mask. -/
private lemma xor_bijective (a : BitVec 128) :
    Function.Bijective (fun x : BitVec 128 => a ^^^ x) := by
  refine ⟨fun x y h => ?_, fun y => ⟨a ^^^ y, ?_⟩⟩
  · simpa using congrArg (a ^^^ ·) h
  · simp

/-- The involution law behind `xor_bijective`: the reparameterized tag is `T` itself. -/
private lemma xor_cancel (a T : BitVec 128) : a ^^^ (a ^^^ T) = T := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The post-challenge acceptance test, with the mask eliminated in favour of the challenge
tag: `T' = hash H X' ^^^ (hash H X* ^^^ T*)` is exactly the AXU-shaped
`hash H X' ^^^ hash H X* = T' ^^^ T*` that `probEvent_post_axu_le` charges. -/
private lemma post_event_iff (u v a T : BitVec 128) :
    a = u ^^^ (v ^^^ T) ↔ u ^^^ v = a ^^^ T := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm (u ^^^ v) T]
  exact tag_eq_iff_mask_eq a T (u ^^^ v)

/-- `SampleableType` types are nonempty: their uniform sample is a `ProbComp`, which never
fails, so its support cannot be empty. Used to name a key at which the challenge-set run is
evaluated once `run_challenge_some_indep` has shown the run does not depend on it. -/
private lemma nonempty_of_sampleable (K : Type) [SampleableType K] : Nonempty K := by
  by_contra hcon
  have hns : ¬ (support ($ᵗ K : ProbComp K)).Nonempty := by
    rintro ⟨x, -⟩
    exact hcon ⟨x⟩
  have h1 := (probFailure_eq_one_iff_not_nonempty ($ᵗ K : ProbComp K)).2 hns
  rw [probFailure_of_liftM_PMF] at h1
  exact zero_ne_one h1

/-- `probEvent_congr'` at a fixed `ProbComp`: equal evaluation distributions give equal
event probabilities. Specialised so the ambient spec is not a metavariable. -/
private lemma probEvent_of_evalDist_eq {α : Type} {p : α → Prop} {oa oa' : ProbComp α}
    (h : 𝒟[oa] = 𝒟[oa']) : Pr[ p | oa] = Pr[ p | oa'] :=
  probEvent_congr' (fun _ _ => Iff.rfl) h

/-- Two-sided bind congruence: the shared prefix may be followed by continuations of
different types carrying different events, as long as they agree pointwise. -/
private lemma probEvent_bind_congr₂ {α β γ : Type} (mx : ProbComp α)
    {ob₁ : α → ProbComp β} {ob₂ : α → ProbComp γ} {p : β → Prop} {q : γ → Prop}
    (h : ∀ x, Pr[ p | ob₁ x] = Pr[ q | ob₂ x]) :
    Pr[ p | mx >>= ob₁] = Pr[ q | mx >>= ob₂] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact tsum_congr fun x => by rw [h x]

/-! ### The pre-challenge half

At the point where the mask is drawn the pre-challenge log is a FIXED list `L`, and the
observed key/mask pair is reported faithfully by the continuation. That is exactly the
shape of `probEvent_pre_fresh_le` at `ν := $ᵗ K`: the hash key is the prefix, the mask is
the fresh draw, and the locus is `L`'s targets `T'ᵢ ^^^ hash H X'ᵢ`. -/

/-- **Pre-challenge half.** Over a uniform key and a fresh uniform mask, the probability
that some entry of the FIXED pre-challenge log `L` accepts is at most `|L| · 2⁻¹²⁸`, under
an arbitrary continuation `k` that reports the drawn pair (`hk`).

Route: `probEvent_pre_fresh_le` (WC5) at `ν := $ᵗ K` and
`pre H := L.map (fun r => T'ᵣ ^^^ hash H X'ᵣ)`; the acceptance test is solved for the mask
by `tag_eq_iff_mask_eq`. -/
private lemma pre_half_le [SampleableType K]
    (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (L : List (A × (Cb × BitVec 128) × Bool))
    {β : Type} (k : K → BitVec 128 → ProbComp β) (obs : β → K × BitVec 128)
    (hk : ∀ H m, ∀ y ∈ support (k H m), obs y = (H, m)) :
    Pr[fun y => L.any (wcAccepts hash enc (obs y).1 (obs y).2) = true
       | ($ᵗ K : ProbComp K) >>= fun H =>
           ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m => k H m]
      ≤ (L.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := by
  refine le_trans (probEvent_pre_fresh_le ($ᵗ K)
      (fun H => L.map (fun r => r.2.1.2 ^^^ hash H (enc (r.1, r.2.1.1)))) k _ ?_) ?_
  · intro H m y hy
    rw [hk H m y hy]
    simp only [List.any_eq_true, wcAccepts, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, ((tag_eq_iff_mask_eq _ _ _).1 he).symm⟩
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, (tag_eq_iff_mask_eq _ _ _).2 he.symm⟩
  · simp only [List.length_map]
    calc ∑' H : K, Pr[= H | ($ᵗ K : ProbComp K)] * (L.length : ℝ≥0∞)
            * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹
        = (∑' H : K, Pr[= H | ($ᵗ K : ProbComp K)])
            * ((L.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹) := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun H => mul_assoc _ _ _
      _ ≤ 1 * ((L.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹) := by
          gcongr
          exact tsum_probOutput_le_one
      _ = (L.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := one_mul _

/-! ### The challenge-set run is key- and mask-free

Once the challenge slot is `some`, the encrypt oracle returns `none` without touching
`(H, mask)` and the log-refined decrypt oracle never read them in the first place. So the
whole remaining run is a computation in which neither appears — which is what licenses
hoisting `H` past it. -/

/-- One handler step from a challenge-set state does not read `(H, mask)`. -/
private lemma step_eq [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H H' : K) (m m' : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128) × Bool)) (t : (wcSpec A M Cb).Domain) :
    (wcLogImpl hash enc H m padMsg t).run (some c, L) =
      (wcLogImpl hash enc H' m' padMsg t).run (some c, L) := by
  rcases t with (j | ⟨ad, mm⟩) | ⟨ad, e⟩ <;>
    simp [wcLogImpl, StateT.run_bind, StateT.run_get]

/-- The challenge slot is monotone: from a challenge-set state every step lands in a
challenge-set state, with the SAME challenge. -/
private lemma step_state [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128) × Bool)) (t : (wcSpec A M Cb).Domain) :
    ∀ p ∈ support ((wcLogImpl hash enc H m padMsg t).run (some c, L)),
      ∃ L', p.2 = (some c, L') := by
  rcases t with (j | ⟨ad, mm⟩) | ⟨ad, e⟩ <;> intro p hp
  · simp only [add_apply_inl, wcLogImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, support_map, support_liftM,
      OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hp
    obtain ⟨u, hu⟩ := hp
    exact ⟨L, by simp [← hu]⟩
  · simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_pure, support_pure] at hp
    exact ⟨L, by rw [Set.eq_of_mem_singleton hp]⟩
  · by_cases hg : c.2 = e
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_some, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_pure, support_pure] at hp
      exact ⟨L, by rw [Set.eq_of_mem_singleton hp]⟩
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_some, Option.some.injEq, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure,
        support_pure, Option.isSome_some] at hp
      exact ⟨L ++ [(ad, e, true)], by rw [Set.eq_of_mem_singleton hp]⟩

/-- **Step 3's structural half.** From a challenge-set state the whole log-refined run is
literally the same `ProbComp` for every `(H, mask)`: the one-shot encrypt oracle is spent,
and neither the unif nor the log-refined decrypt oracle reads the key or the mask. This is
what makes the reparameterized run `H`-free, hence hoistable past the key draw. -/
private lemma run_challenge_some_indep [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H H' : K) (m m' : BitVec 128) (c : A × (Cb × BitVec 128))
    (oa : OracleComp (wcSpec A M Cb) α) (L : List (A × (Cb × BitVec 128) × Bool)) :
    (simulateQ (wcLogImpl hash enc H m padMsg) oa).run (some c, L) =
      (simulateQ (wcLogImpl hash enc H' m' padMsg) oa).run (some c, L) := by
  induction oa using OracleComp.inductionOn generalizing L with
  | pure x => rfl
  | query_bind t ob ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [step_eq hash enc padMsg H H' m m' c L t]
      refine bind_congr_of_forall_mem_support _ fun p hp => ?_
      obtain ⟨L', hL'⟩ := step_state hash enc padMsg H' m' c L t p hp
      rw [hL']
      exact ih p.1 L'

/-! ### The post-challenge log extends the frozen prefix

`ExtInv` is the support invariant of the run that starts at the moment the challenge is
set. It records both halves of the pre/post split at once: the frozen prefix `L` is an
initial segment of the final log, and every entry appended afterwards differs from the
challenge ciphertext (the guard returns before appending). The second clause is
ROADMAP criterion 5's structural input to `probEvent_post_axu_le`'s `hne`. -/

/-- The support invariant of the post-challenge run: the challenge slot is fixed, the log
extends the frozen prefix `L`, and every appended entry differs from the challenge
ciphertext. -/
private def ExtInv (c : A × (Cb × BitVec 128)) (L : List (A × (Cb × BitVec 128) × Bool))
    (s : WCLogState A Cb) : Prop :=
  s.1 = some c ∧ ∃ rest, s.2 = L ++ rest ∧ ∀ r ∈ rest, r.2.1 ≠ c.2

/-- `ExtInv` holds at the state the encrypt query leaves behind, with an empty extension. -/
private lemma extInv_init (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128) × Bool)) :
    ExtInv c L ((some c, L) : WCLogState A Cb) :=
  ⟨rfl, [], by simp, by simp⟩

/-- Every oracle step preserves `ExtInv`. Unif does not write; encrypt at a set challenge
does not write; decrypt under the guard does not write, and off the guard the appended
entry's ciphertext is exactly what the failed guard says differs from the challenge. -/
private lemma extInv_step [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128) × Bool)) :
    ∀ (t : (wcSpec A M Cb).Domain) (s : WCLogState A Cb), ExtInv c L s →
      ∀ y ∈ support ((wcLogImpl hash enc H m padMsg t).run s), ExtInv c L y.2 := by
  rintro t ⟨ch, log⟩ ⟨hs1, rest, hrest, hnec⟩ y hy
  simp only at hs1 hrest
  subst hs1
  subst hrest
  rcases t with (j | ⟨ad, mm⟩) | ⟨ad, e⟩
  · simp only [add_apply_inl, wcLogImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, support_map, support_liftM,
      OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hy
    obtain ⟨u, hu⟩ := hy
    rw [← hu]
    exact ⟨rfl, rest, rfl, hnec⟩
  · simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_pure, support_pure] at hy
    rw [Set.eq_of_mem_singleton hy]
    exact ⟨rfl, rest, rfl, hnec⟩
  · by_cases hg : c.2 = e
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_some, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
        pure_bind, hg, ↓reduceIte, StateT.run_pure, support_pure] at hy
      rw [Set.eq_of_mem_singleton hy]
      exact ⟨rfl, rest, rfl, hnec⟩
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_some, Option.some.injEq, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_map,
        StateT.run_set, map_pure, support_pure, Option.isSome_some] at hy
      rw [Set.eq_of_mem_singleton hy]
      refine ⟨rfl, rest ++ [(ad, e, true)], by simp, ?_⟩
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hnec r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact fun hcontra => hg hcontra.symm

/-- `ExtInv` along the whole post-challenge run, by
`simulateQ_run_preserves_inv_of_query`. -/
private lemma wcLogImpl_extends [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128) × Bool)) (oa : OracleComp (wcSpec A M Cb) α) :
    ∀ z ∈ support ((simulateQ (wcLogImpl hash enc H m padMsg) oa).run ((some c, L))),
      ExtInv c L z.2 :=
  fun z hz => simulateQ_run_preserves_inv_of_query (wcLogImpl hash enc H m padMsg)
    (ExtInv c L) (extInv_step hash enc padMsg H m c L) oa (some c, L) (extInv_init c L) z hz

/-! ### Counting from an arbitrary start state

`wcLogImpl_log_length_le` counts from the initial state only; the post-challenge half needs
the same count from the state the encrypt query leaves behind, so the two per-step
obligations of `support_state_measure_le_of_isQueryBoundP` are recorded separately here. -/

/-- Every step appends at most one log entry. -/
private lemma log_step_le_one [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (t : (wcSpec A M Cb).Domain) (s : WCLogState A Cb) :
    ∀ z ∈ support ((wcLogImpl hash enc H mask padMsg t).run s),
      z.2.2.length ≤ s.2.length + 1 := by
  obtain ⟨ch, log⟩ := s
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩ <;> intro z hz
  · simp only [add_apply_inl, wcLogImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, support_map, support_liftM,
      OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hz
    obtain ⟨u, hu⟩ := hz
    simp [← hu]
  · cases ch with
    | none =>
      simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
        pure_bind, StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
      rw [Set.eq_of_mem_singleton hz]
      simp
    | some c0 =>
      simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
        pure_bind, StateT.run_pure, support_pure] at hz
      rw [Set.eq_of_mem_singleton hz]
      simp
  · by_cases hg : (Option.map Prod.snd ch : Option (Cb × BitVec 128)) = some e
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hg, BEq.rfl, ↓reduceIte,
        StateT.run_pure, support_pure] at hz
      rw [Set.eq_of_mem_singleton hz]
      simp
    · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
        Option.map_eq_some_iff, Prod.exists, exists_eq_right, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_map,
        StateT.run_set, map_pure, support_pure] at hz
      rw [Set.eq_of_mem_singleton hz]
      simp

/-- Only the decrypt oracle ever appends. -/
private lemma log_step_le_zero [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (t : (wcSpec A M Cb).Domain)
    (ht : ∀ y : A × (Cb × BitVec 128), t ≠ Sum.inr y) (s : WCLogState A Cb) :
    ∀ z ∈ support ((wcLogImpl hash enc H mask padMsg t).run s),
      z.2.2.length ≤ s.2.length := by
  obtain ⟨ch, log⟩ := s
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩ <;> intro z hz
  · simp only [add_apply_inl, wcLogImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, support_map, support_liftM,
      OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hz
    obtain ⟨u, hu⟩ := hz
    simp [← hu]
  · cases ch with
    | none =>
      simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
        pure_bind, StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
      rw [Set.eq_of_mem_singleton hz]
    | some c0 =>
      simp only [add_apply_inl, add_apply_inr, wcLogImpl, bind_pure_comp,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
        pure_bind, StateT.run_pure, support_pure] at hz
      rw [Set.eq_of_mem_singleton hz]
  · exact absurd rfl (ht (ad, e))

/-- The log-length bound from an ARBITRARY start state: the support-level instance of
`support_state_measure_le_of_isQueryBoundP` the post-challenge half consumes. -/
private lemma log_length_le_from [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (oa : OracleComp (wcSpec A M Cb) α) (q : ℕ)
    (hq : oa.IsQueryBoundP (· matches Sum.inr _) q) (s : WCLogState A Cb) :
    ∀ z ∈ support ((simulateQ (wcLogImpl hash enc H mask padMsg) oa).run s),
      z.2.2.length ≤ s.2.length + q :=
  support_state_measure_le_of_isQueryBoundP (wcLogImpl hash enc H mask padMsg)
    (fun s : WCLogState A Cb => s.2.length) (· matches Sum.inr _)
    (fun t _ => log_step_le_one hash enc H mask padMsg t)
    (fun t ht => log_step_le_zero hash enc H mask padMsg t (fun y hy => ht (by rw [hy])))
    oa q hq s

/-! ### Steps 3 and 4: the local bijection and the hoisted key -/

/-- **Step 3.** At the (single) encrypt query, reparameterize the mask draw along the
XOR-by-constant bijection `mask ↦ hash H X* ^^^ mask`. On the right the encrypt oracle
emits the TAG `T` drawn uniformly and the run no longer mentions `H` or the mask at all
(`run_challenge_some_indep` replaces them by the dummies `H0`, `0`); the mask survives only
in the observed value, as `hash H X* ^^^ T`.

Route: `probOutput_bind_bijective_uniform_cross` at `f := (hash H X* ^^^ ·)`, which is the
free pushforward form; the `Equiv`/`relTriple` coupling route is not needed because the
run is already a `ProbComp` bind of a single uniform draw. -/
private lemma reparam_bind [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128) × Bool))
    (H H0 : K) :
    𝒟[($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
        (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
          (simulateQ (wcLogImpl hash enc H m padMsg)
              (ob (some (c0, hash H (enc (ad, c0)) ^^^ m)))).run
            (some (ad, (c0, hash H (enc (ad, c0)) ^^^ m)), L)]
      = 𝒟[($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun T =>
            (fun z : α × WCLogState A Cb => ((H, hash H (enc (ad, c0)) ^^^ T), z.2)) <$>
              (simulateQ (wcLogImpl hash enc H0 0 padMsg) (ob (some (c0, T)))).run
                (some (ad, (c0, T)), L)] := by
  have key : ∀ T : BitVec 128,
      ((fun z : α × WCLogState A Cb => ((H, hash H (enc (ad, c0)) ^^^ T), z.2)) <$>
        (simulateQ (wcLogImpl hash enc H0 0 padMsg) (ob (some (c0, T)))).run
          (some (ad, (c0, T)), L))
      = ((fun z : α × WCLogState A Cb =>
            ((H, hash H (enc (ad, c0)) ^^^ T), z.2)) <$>
          (simulateQ (wcLogImpl hash enc H (hash H (enc (ad, c0)) ^^^ T) padMsg)
              (ob (some (c0, hash H (enc (ad, c0)) ^^^ (hash H (enc (ad, c0)) ^^^ T))))).run
            (some (ad, (c0, hash H (enc (ad, c0)) ^^^ (hash H (enc (ad, c0)) ^^^ T))), L)) := by
    intro T
    rw [xor_cancel]
    rw [run_challenge_some_indep hash enc padMsg H0 H 0
      (hash H (enc (ad, c0)) ^^^ T) (ad, (c0, T)) (ob (some (c0, T))) L]
  simp only [key]
  refine evalDist_ext fun z => ?_
  exact (probOutput_bind_bijective_uniform_cross (BitVec 128)
    (fun x : BitVec 128 => hash H (enc (ad, c0)) ^^^ x) (xor_bijective _)
    (fun m => (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
      (simulateQ (wcLogImpl hash enc H m padMsg)
          (ob (some (c0, hash H (enc (ad, c0)) ^^^ m)))).run
        (some (ad, (c0, hash H (enc (ad, c0)) ^^^ m)), L)) z).symm

/-- **Step 4.** With the run `H`-free, the key draw commutes past the whole run and lands
at the end, which is exactly `probEvent_post_axu_le`'s shape `do z ← μ; H ← $ᵗ K`.

Route: two applications of `OracleComp.DeferredSampling.evalDist_bind_comm` — a plain
two-independent-draw swap, not a `simulateQ` commutation. -/
private lemma hoist_H [SampleableType K] {α : Type}
    (hash : K → D → BitVec 128) (X : D)
    (R : BitVec 128 → ProbComp (α × WCLogState A Cb)) :
    𝒟[($ᵗ K : ProbComp K) >>= fun H =>
        ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun T =>
          (fun z : α × WCLogState A Cb => ((H, hash H X ^^^ T), z.2)) <$> R T]
      = 𝒟[(fun p : (BitVec 128 × (α × WCLogState A Cb)) × K =>
             ((p.2, hash p.2 X ^^^ p.1.1), p.1.2.2)) <$>
          ((($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun T => R T >>= fun z => pure (T, z))
             >>= fun w => ($ᵗ K : ProbComp K) >>= fun H => pure (w, H))] := by
  have h0 : ∀ (H : K) (T : BitVec 128),
      ((fun z : α × WCLogState A Cb => ((H, hash H X ^^^ T), z.2)) <$> R T)
        = R T >>= fun z => pure ((H, hash H X ^^^ T), z.2) := fun H T => by
    rw [map_eq_bind_pure_comp]
    rfl
  simp only [h0]
  rw [DeferredSampling.evalDist_bind_comm ($ᵗ K) ($ᵗ (BitVec 128))
    (fun H T => R T >>= fun z => pure ((H, hash H X ^^^ T), z.2))]
  refine Eq.trans (evalDist_bind_congr' _ fun T =>
    DeferredSampling.evalDist_bind_comm ($ᵗ K) (R T)
      (fun H z => pure ((H, hash H X ^^^ T), z.2))) ?_
  congr 1
  simp [bind_assoc, map_eq_bind_pure_comp]

/-- Steps 3 and 4 composed: the post-challenge distribution in
`probEvent_post_axu_le`'s shape. -/
private lemma post_half_reshape [SampleableType K] [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128) × Bool)) (H0 : K) :
    𝒟[($ᵗ K : ProbComp K) >>= fun H =>
        ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
          (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
            (simulateQ (wcLogImpl hash enc H m padMsg)
                (ob (some (c0, hash H (enc (ad, c0)) ^^^ m)))).run
              (some (ad, (c0, hash H (enc (ad, c0)) ^^^ m)), L)]
      = 𝒟[(fun p : (BitVec 128 × (α × WCLogState A Cb)) × K =>
             ((p.2, hash p.2 (enc (ad, c0)) ^^^ p.1.1), p.1.2.2)) <$>
          ((($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun T =>
              (simulateQ (wcLogImpl hash enc H0 0 padMsg) (ob (some (c0, T)))).run
                  (some (ad, (c0, T)), L) >>= fun z => pure (T, z))
             >>= fun w => ($ᵗ K : ProbComp K) >>= fun H => pure (w, H))] :=
  Eq.trans (evalDist_bind_congr' _ fun H => reparam_bind hash enc padMsg ob ad c0 L H H0)
    (hoist_H hash (enc (ad, c0)) _)

/-- An expected count bounded on the support collapses to the constant bound. -/
private lemma tsum_count_le {Z : Type} (μ : ProbComp Z) (cnt : Z → ℕ) (n : ℕ) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support μ, cnt z ≤ n) :
    ∑' z, Pr[= z | μ] * (cnt z : ℝ≥0∞) * ε ≤ (n : ℝ≥0∞) * ε := by
  calc ∑' z, Pr[= z | μ] * (cnt z : ℝ≥0∞) * ε
      ≤ ∑' _z : Z, Pr[= _z | μ] * ((n : ℝ≥0∞) * ε) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        rcases Classical.em (z ∈ support μ) with hz | hz
        · rw [mul_assoc]
          gcongr
          exact Nat.cast_le.2 (h z hz)
        · rw [probOutput_eq_zero_of_not_mem_support hz]
          simp
    _ = (∑' z : Z, Pr[= z | μ]) * ((n : ℝ≥0∞) * ε) := ENNReal.tsum_mul_right
    _ ≤ 1 * ((n : ℝ≥0∞) * ε) := by
        gcongr
        exact tsum_probOutput_le_one
    _ = (n : ℝ≥0∞) * ε := one_mul _

/-- **Post-challenge half.** The entries appended AFTER the challenge was set accept with
probability at most `n · ε`, where `n` bounds the adversary's remaining decrypt budget.

Route: `post_half_reshape` puts the run in `probEvent_post_axu_le`'s shape, `post_event_iff`
turns the acceptance test into the AXU form, `wcLogImpl_extends` supplies the PAIR
inequality `hne` (through `henc_inj`: equal encodings force equal `(ad, C)`, and an equal
tag then makes the entry the challenge ciphertext, which the guard excluded), and
`log_length_le_from` bounds the number of post-challenge entries. -/
private lemma post_half_le [SampleableType K] [DecidableEq Cb] {α : Type}
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α) (n : ℕ)
    (hn : ∀ y, (ob y).IsQueryBoundP (· matches Sum.inr _) n)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128) × Bool)) :
    Pr[fun z : (K × BitVec 128) × WCLogState A Cb =>
         (z.2.2.drop L.length).any (wcAccepts hash enc z.1.1 z.1.2) = true
       | ($ᵗ K : ProbComp K) >>= fun H =>
           ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
             (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
               (simulateQ (wcLogImpl hash enc H m padMsg)
                   (ob (some (c0, hash H (enc (ad, c0)) ^^^ m)))).run
                 (some (ad, (c0, hash H (enc (ad, c0)) ^^^ m)), L)]
      ≤ (n : ℝ≥0∞) * ε := by
  obtain ⟨H0⟩ := nonempty_of_sampleable K
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (post_half_reshape hash enc padMsg ob ad c0 L H0), probEvent_map]
  simp only [Function.comp_def]
  have hiff : ∀ p : (BitVec 128 × (α × WCLogState A Cb)) × K,
      ((p.1.2.2.2.drop L.length).any
          (wcAccepts hash enc p.2 (hash p.2 (enc (ad, c0)) ^^^ p.1.1)) = true)
        ↔ (∃ x ∈ (p.1.2.2.2.drop L.length).map
              (fun r : A × (Cb × BitVec 128) × Bool => (enc (r.1, r.2.1.1), r.2.1.2)),
            hash p.2 x.1 ^^^ hash p.2 (enc (ad, c0), p.1.1).1
              = x.2 ^^^ (enc (ad, c0), p.1.1).2) := by
    intro p
    simp only [List.any_eq_true, wcAccepts, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨r, hr, he⟩
      exact ⟨_, ⟨r, hr, rfl⟩, (post_event_iff _ _ _ _).1 he⟩
    · rintro ⟨x, ⟨r, hr, rfl⟩, he⟩
      exact ⟨r, hr, (post_event_iff _ _ _ _).2 he⟩
  rw [probEvent_ext (fun p _ => hiff p)]
  refine le_trans (probEvent_post_axu_le haxu _
    (fun w : BitVec 128 × (α × WCLogState A Cb) => (enc (ad, c0), w.1))
    (fun w : BitVec 128 × (α × WCLogState A Cb) => (w.2.2.2.drop L.length).map
      (fun r : A × (Cb × BitVec 128) × Bool => (enc (r.1, r.2.1.1), r.2.1.2))) ?_) ?_
  · rintro w hw x hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨T, -, z, hz, rfl⟩ := hw
    obtain ⟨-, rest, hrest, hnec⟩ :=
      wcLogImpl_extends hash enc padMsg H0 0 (ad, (c0, T)) L (ob (some (c0, T))) z hz
    simp only [hrest, List.drop_left, List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    intro hcontra
    rw [Prod.ext_iff] at hcontra
    obtain ⟨h1, h2⟩ := hcontra
    have h3 : (r.1, r.2.1.1) = (ad, c0) := henc_inj h1
    exact hnec r hr (by rw [Prod.ext_iff]; exact ⟨(Prod.ext_iff.1 h3).2, h2⟩)
  · refine tsum_count_le _ _ n ε ?_
    rintro w hw
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨T, -, z, hz, rfl⟩ := hw
    have hlen := log_length_le_from hash enc H0 0 padMsg (ob (some (c0, T))) n (hn _)
      (some (ad, (c0, T)), L) z hz
    dsimp only at hlen
    simp only [List.length_map, List.length_drop]
    omega

/-! ### Assembling the two halves -/

/-- Two independent draws in front of a `(H, mask)`-free step commute past it. -/
private lemma hoist_step [SampleableType K] {α β : Type}
    (Q : ProbComp β) (F : K → BitVec 128 → β → ProbComp α) :
    𝒟[($ᵗ K : ProbComp K) >>= fun H =>
        ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m => Q >>= fun p => F H m p]
      = 𝒟[Q >>= fun p => ($ᵗ K : ProbComp K) >>= fun H =>
            ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m => F H m p] :=
  Eq.trans (evalDist_bind_congr' _ fun H =>
      DeferredSampling.evalDist_bind_comm ($ᵗ (BitVec 128)) Q (fun m p => F H m p))
    (DeferredSampling.evalDist_bind_comm ($ᵗ K) Q (fun H p =>
      ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m => F H m p))

/-- **The challenge case of the criterion-4 split.** At the moment the challenge is set the
pre-challenge log is the FIXED list `L` and the remaining decrypt budget is `n`; the bad
event splits along `L ++ rest`, the two halves are charged to disjoint randomness sources,
and they are combined at the SHARED count `L.length + n` by `combine_pre_post_le` — never
bounded by the budget separately. -/
private lemma post_phase [SampleableType K] [DecidableEq Cb] {α : Type}
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α) (n : ℕ)
    (hn : ∀ y, (ob y).IsQueryBoundP (· matches Sum.inr _) n)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128) × Bool)) :
    Pr[fun z : (K × BitVec 128) × WCLogState A Cb => wcFlag hash enc z.1.1 z.1.2 z.2 = true
       | ($ᵗ K : ProbComp K) >>= fun H =>
           ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
             (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
               (simulateQ (wcLogImpl hash enc H m padMsg)
                   (ob (some (c0, hash H (enc (ad, c0)) ^^^ m)))).run
                 (some (ad, (c0, hash H (enc (ad, c0)) ^^^ m)), L)]
      ≤ ((L.length + n : ℕ) : ℝ≥0∞) * ε := by
  refine le_trans (probEvent_mono (q := fun z : (K × BitVec 128) × WCLogState A Cb =>
    L.any (wcAccepts hash enc z.1.1 z.1.2) = true
      ∨ (z.2.2.drop L.length).any (wcAccepts hash enc z.1.1 z.1.2) = true) ?_) ?_
  · rintro z hz hflag
    simp only [mem_support_bind_iff, support_map, Set.mem_image] at hz
    obtain ⟨H, -, m, -, zz, hzz, rfl⟩ := hz
    obtain ⟨-, rest, hrest, -⟩ := wcLogImpl_extends hash enc padMsg H m
      (ad, (c0, hash H (enc (ad, c0)) ^^^ m)) L _ zz hzz
    rw [wcFlag] at hflag
    dsimp only at hflag ⊢
    rw [hrest] at hflag ⊢
    rw [List.drop_left]
    rw [List.any_append, Bool.or_eq_true] at hflag
    exact hflag
  · refine le_trans (probEvent_or_le _ _ _) ?_
    refine combine_pre_post_le (pure () : ProbComp Unit) (L.length + n) ε
      (fun _ => L.length) (fun _ => n) _ _ ?_ ?_ (fun _ _ => le_rfl) hfloor
    · refine le_trans (pre_half_le hash enc L _ Prod.fst ?_) ?_
      · intro H m y hy
        simp only [support_map, Set.mem_image] at hy
        obtain ⟨z, -, rfl⟩ := hy
        rfl
      · simp [tsum_fintype]
    · refine le_trans (post_half_le haxu henc_inj padMsg ob n hn ad c0 L) ?_
      simp [tsum_fintype]

/-! ### The pre-challenge phase -/

/-- One `(H, mask)`-free step in front of the induction hypothesis. -/
private lemma pre_phase_bind_le [SampleableType K] [DecidableEq Cb] {α β : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (Q : ProbComp (β × WCLogState A Cb))
    (F : β → OracleComp (wcSpec A M Cb) α) (bnd : ℝ≥0∞)
    (hstate : ∀ p ∈ support Q, p.2.1 = none)
    (hIH : ∀ p ∈ support Q,
      Pr[ fun z : (K × BitVec 128) × WCLogState A Cb => wcFlag hash enc z.1.1 z.1.2 z.2 = true
         | ($ᵗ K : ProbComp K) >>= fun H =>
             ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
               (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
                 (simulateQ (wcLogImpl hash enc H m padMsg) (F p.1)).run
                   ((none, p.2.2) : WCLogState A Cb)] ≤ bnd) :
    Pr[fun z : (K × BitVec 128) × WCLogState A Cb => wcFlag hash enc z.1.1 z.1.2 z.2 = true
       | Q >>= fun p => ($ᵗ K : ProbComp K) >>= fun H =>
           ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
             (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
               (simulateQ (wcLogImpl hash enc H m padMsg) (F p.1)).run p.2] ≤ bnd := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' p : β × WCLogState A Cb, Pr[= p | Q] * Pr[fun z : (K × BitVec 128) × WCLogState A Cb =>
          wcFlag hash enc z.1.1 z.1.2 z.2 = true
        | ($ᵗ K : ProbComp K) >>= fun H =>
            ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
              (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
                (simulateQ (wcLogImpl hash enc H m padMsg) (F p.1)).run p.2]
      ≤ ∑' _p : β × WCLogState A Cb, Pr[= _p | Q] * bnd := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        rcases Classical.em (p ∈ support Q) with hp | hp
        · gcongr
          have hp2 : p.2 = ((none, p.2.2) : WCLogState A Cb) := by
            rw [← hstate p hp]
          rw [hp2]
          exact hIH p hp
        · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ = (∑' p : β × WCLogState A Cb, Pr[= p | Q]) * bnd := ENNReal.tsum_mul_right
    _ ≤ 1 * bnd := by
        gcongr
        exact tsum_probOutput_le_one
    _ = bnd := one_mul _

/-- Peeling one query off the simulated run. -/
private lemma run_query_step [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (t : (wcSpec A M Cb).Domain)
    (ob : (wcSpec A M Cb).Range t → OracleComp (wcSpec A M Cb) α) (s : WCLogState A Cb) :
    (simulateQ (wcLogImpl hash enc H m padMsg)
        ((liftM (OracleSpec.query t) : OracleComp (wcSpec A M Cb) ((wcSpec A M Cb).Range t))
          >>= ob)).run s
      = (wcLogImpl hash enc H m padMsg t).run s >>= fun p =>
          (simulateQ (wcLogImpl hash enc H m padMsg) (ob p.1)).run p.2 := by
  simp [simulateQ_bind, StateT.run_bind]

/-- Neither the unif nor the log-refined decrypt oracle reads `(H, mask)` from a state
whose challenge slot is still `none`. -/
private lemma nonEncrypt_step_eq [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H H' : K) (m m' : BitVec 128) (L : List (A × (Cb × BitVec 128) × Bool))
    (t : (wcSpec A M Cb).Domain) (ht : ∀ (ad : A) (mm : M), t ≠ Sum.inl (Sum.inr (ad, mm))) :
    (wcLogImpl hash enc H m padMsg t).run ((none, L) : WCLogState A Cb)
      = (wcLogImpl hash enc H' m' padMsg t).run ((none, L) : WCLogState A Cb) := by
  rcases t with (j | ⟨ad, mm⟩) | ⟨ad, e⟩
  · simp [wcLogImpl]
  · exact absurd rfl (ht ad mm)
  · simp [wcLogImpl, StateT.run_bind, StateT.run_get]

/-- Only the encrypt oracle sets the challenge slot. -/
private lemma nonEncrypt_step_state [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (L : List (A × (Cb × BitVec 128) × Bool))
    (t : (wcSpec A M Cb).Domain) (ht : ∀ (ad : A) (mm : M), t ≠ Sum.inl (Sum.inr (ad, mm))) :
    ∀ p ∈ support ((wcLogImpl hash enc H m padMsg t).run ((none, L) : WCLogState A Cb)),
      p.2.1 = none := by
  rcases t with (j | ⟨ad, mm⟩) | ⟨ad, e⟩ <;> intro p hp
  · simp only [add_apply_inl, wcLogImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, support_map, support_liftM,
      OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hp
    obtain ⟨u, hu⟩ := hp
    simp [← hu]
  · exact absurd rfl (ht ad mm)
  · simp only [add_apply_inr, wcLogImpl, bind_pure_comp, beq_iff_eq,
      Option.map_none, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
      pure_bind, reduceCtorEq, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure,
      support_pure] at hp
    rw [Set.eq_of_mem_singleton hp]

/-- The encrypt query fires the one-shot branch: the challenge is set to
`(ad, (padMsg m*, hash H X* ^^^ mask))` and the run continues from there. -/
private lemma encrypt_step_run [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (L : List (A × (Cb × BitVec 128) × Bool))
    (ad : A) (mm : M)
    (ob : (wcSpec A M Cb).Range (Sum.inl (Sum.inr (ad, mm))) → OracleComp (wcSpec A M Cb) α) :
    (simulateQ (wcLogImpl hash enc H m padMsg)
        ((liftM (OracleSpec.query (Sum.inl (Sum.inr (ad, mm)))) :
            OracleComp (wcSpec A M Cb) ((wcSpec A M Cb).Range (Sum.inl (Sum.inr (ad, mm)))))
          >>= ob)).run ((none, L) : WCLogState A Cb)
      = (simulateQ (wcLogImpl hash enc H m padMsg)
          (ob (some (padMsg mm, hash H (enc (ad, padMsg mm)) ^^^ m)))).run
            ((some (ad, (padMsg mm, hash H (enc (ad, padMsg mm)) ^^^ m)), L) :
              WCLogState A Cb) := by
  simp [simulateQ_bind, simulateQ_query, wcLogImpl, StateT.run_bind, StateT.run_get,
    StateT.run_set]

/-- **The pre-challenge phase, by induction on the adversary.** While the challenge slot is
`none` the run is `(H, mask)`-free, so the two top-level draws hoist past every step and the
induction charges one log entry per decrypt query. The `pure` leaf is
ROADMAP criterion 4's second case (the encrypt oracle was never queried): every entry is
pre-tagged, the post half is empty and contributes `0`, and the mask can be sampled at
termination. The encrypt query hands over to `post_phase`. -/
private lemma pre_phase [SampleableType K] [DecidableEq Cb] {α : Type}
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb) (oa : OracleComp (wcSpec A M Cb) α) :
    ∀ (n : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) n →
      ∀ L : List (A × (Cb × BitVec 128) × Bool),
        Pr[fun z : (K × BitVec 128) × WCLogState A Cb =>
             wcFlag hash enc z.1.1 z.1.2 z.2 = true
           | ($ᵗ K : ProbComp K) >>= fun H =>
               ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
                 (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
                   (simulateQ (wcLogImpl hash enc H m padMsg) oa).run
                     ((none, L) : WCLogState A Cb)]
          ≤ ((L.length + n : ℕ) : ℝ≥0∞) * ε := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro n _ L
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      refine le_trans (le_of_eq (probEvent_ext
        (q := fun y : (K × BitVec 128) × WCLogState A Cb =>
          L.any (wcAccepts hash enc (Prod.fst y).1 (Prod.fst y).2) = true)
        (fun z hz => ?_))) ?_
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨H, -, m, -, rfl⟩ := hz
        exact Iff.rfl
      refine le_trans (pre_half_le hash enc L _ Prod.fst (fun H m y hy => ?_)) ?_
      · simp only [support_pure, Set.mem_singleton_iff] at hy
        rw [hy]
      · exact mul_le_mul' (Nat.cast_le.2 (Nat.le_add_right _ _)) hfloor
  | query_bind t ob ih =>
      intro n hq L
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hq1, hq2⟩ := hq
      obtain ⟨H0⟩ := nonempty_of_sampleable K
      by_cases ht : ∀ (ad : A) (mm : M), t ≠ Sum.inl (Sum.inr (ad, mm))
      · have hrun : ∀ (H : K) (m : BitVec 128),
            ((fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
              (simulateQ (wcLogImpl hash enc H m padMsg)
                ((liftM (OracleSpec.query t) :
                    OracleComp (wcSpec A M Cb) ((wcSpec A M Cb).Range t))
                  >>= ob)).run ((none, L) : WCLogState A Cb))
              = (wcLogImpl hash enc H0 0 padMsg t).run ((none, L) : WCLogState A Cb) >>=
                  fun p => (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
                    (simulateQ (wcLogImpl hash enc H m padMsg) (ob p.1)).run p.2 := by
          intro H m
          rw [run_query_step hash enc padMsg H m t ob (none, L),
            nonEncrypt_step_eq hash enc padMsg H H0 m 0 L t ht, map_bind]
        simp only [hrun]
        rw [probEvent_of_evalDist_eq (p := fun z : (K × BitVec 128) × WCLogState A Cb =>
          wcFlag hash enc z.1.1 z.1.2 z.2 = true)
          (hoist_step ((wcLogImpl hash enc H0 0 padMsg t).run ((none, L) : WCLogState A Cb))
            (fun H m p => (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
              (simulateQ (wcLogImpl hash enc H m padMsg) (ob p.1)).run p.2))]
        refine pre_phase_bind_le hash enc padMsg _ ob _
          (nonEncrypt_step_state hash enc padMsg H0 0 L t ht) (fun p hp => ?_)
        refine le_trans (ih p.1 _ (hq2 p.1) p.2.2) ?_
        refine mul_le_mul' (Nat.cast_le.2 ?_) le_rfl
        split_ifs with hpt
        · have hlen := log_step_le_one hash enc H0 0 padMsg t (none, L) p hp
          have hn1 : 0 < n := hq1.resolve_left (not_not_intro hpt)
          dsimp only at hlen
          omega
        · have hlen := log_step_le_zero hash enc H0 0 padMsg t
            (fun y hy => hpt (by rw [hy])) (none, L) p hp
          dsimp only at hlen
          omega
      · have ht' : ∃ (ad : A) (mm : M), t = Sum.inl (Sum.inr (ad, mm)) := by
          by_contra hc
          exact ht fun ad mm h => hc ⟨ad, mm, h⟩
        obtain ⟨ad, mm, rfl⟩ := ht'
        have hrunE : ∀ (H : K) (m : BitVec 128),
            ((fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
              (simulateQ (wcLogImpl hash enc H m padMsg)
                ((liftM (OracleSpec.query (Sum.inl (Sum.inr (ad, mm)))) :
                    OracleComp (wcSpec A M Cb)
                      ((wcSpec A M Cb).Range (Sum.inl (Sum.inr (ad, mm)))))
                  >>= ob)).run ((none, L) : WCLogState A Cb))
              = ((fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
                  (simulateQ (wcLogImpl hash enc H m padMsg)
                    (ob (some (padMsg mm, hash H (enc (ad, padMsg mm)) ^^^ m)))).run
                      ((some (ad, (padMsg mm, hash H (enc (ad, padMsg mm)) ^^^ m)), L) :
                        WCLogState A Cb)) := by
          intro H m
          rw [encrypt_step_run hash enc padMsg H m L ad mm ob]
        simp only [hrunE]
        exact post_phase haxu hfloor henc_inj padMsg _ n
          (fun y => by simpa using hq2 y) ad (padMsg mm) L

end ProbabilityCore

/-- **Obligation WC7** (staged here, discharged by plan 04-05). The brick's probability
core, at the LOG-REFINED handler, with `(H, mask)` sampled at the top and carried into the
observed value (the bad event reads both, so the observed carrier is
`(K × BitVec 128) × WCLogState A Cb`; the adversary's output `α` is discarded).

Route: the phase's five-step chain — sink `mask` to the one-shot encrypt query, the local
XOR bijection `mask ↦ T*` there, hoist `H` past the (now `H`-free) run, then the pure
bound: the post-tagged entries by union bound + AXU over `H` (`probEvent_post_axu_le`),
the pre-tagged entries by a blind guess against the fresh 128-bit draw
(`probEvent_pre_fresh_le`), combined at the SHARED support count
(`combine_pre_post_le`) with `wcLogImpl_log_length_le`.

`hfloor` is load-bearing and may not be dropped: `IsAlmostXorUniversal` quantifies only
over pairs `x ≠ y`, so on a subsingleton domain `D` it is vacuous and `ε = 0` is
admissible, while a pre-challenge blind tag guess still succeeds with probability
`2⁻¹²⁸`. At the GCM call site it is discharged at zero cost by `GCM.ghashAXU_eps_lower`. -/
theorem probEvent_bad_wcLog_le {α K A M Cb D : Type} [SampleableType K] [DecidableEq Cb]
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb) (oa : OracleComp (wcSpec A M Cb) α) (q : ℕ)
    (hq : oa.IsQueryBoundP (· matches Sum.inr _) q) :
    Pr[fun z : (K × BitVec 128) × WCLogState A Cb =>
         wcFlag hash enc z.1.1 z.1.2 z.2 = true |
       (do let H ← ($ᵗ K : ProbComp K)
           let mask ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
           (fun z : α × WCLogState A Cb => ((H, mask), z.2)) <$>
             (simulateQ (wcLogImpl hash enc H mask padMsg) oa).run (none, []))]
      ≤ (q : ℝ≥0∞) * ε := by
  simpa using pre_phase haxu hfloor henc_inj padMsg oa q hq []

/-- **Obligation WC8 — THE PUBLIC BRICK** (staged here, discharged by plan 04-05).

One-time Wegman–Carter authenticity: against an adversary making at most `q` decryption
queries, the always-reject instrumented execution raises its `forged` flag with
probability at most `q · ε`, where `ε` bounds the almost-XOR-universality of `hash` on the
ENCODED domain.

This is the phase's `ToVCVio` deliverable and the only declaration the GCM side consumes
from this file. Route: `probEvent_bad_wcLog_le` (WC7) transported back across the log
refinement by `probEvent_bad_wcInst_eq_wcLog` (WC2), which itself rests on
`map_run_simulateQ_wcLogImpl_eq` (WC1).

Both side hypotheses are load-bearing for the GENERIC statement and are discharged for
free at the GCM instantiation: `henc_inj` by `Function.injective_id` (at a non-injective
`enc`, a query with `enc (ad', C') = enc (ad*, C*)`, `C' ≠ C*`, `T' = T*` clears the
ciphertext-only guard and then accepts with probability 1), and `hfloor` by
`GCM.ghashAXU_eps_lower` (without it a subsingleton domain admits `ε = 0` while a blind
pre-challenge tag guess still wins with probability `2⁻¹²⁸`). -/
theorem probEvent_wcInst_forge_le {α K A M Cb D : Type}
    [SampleableType K] [DecidableEq Cb]
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb) (unpad : Cb → M)
    (oa : OracleComp (wcSpec A M Cb) α) (q : ℕ)
    (hq : oa.IsQueryBoundP (· matches Sum.inr _) q) :
    Pr[fun z : α × (Option (Cb × BitVec 128) × Bool) => z.2.2 = true |
        (do let H ← ($ᵗ K : ProbComp K)
            let mask ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
            (simulateQ (wcInstImpl hash enc H mask padMsg unpad false) oa).run
              (none, false))]
      ≤ (q : ℝ≥0∞) * ε := by
  refine le_trans (le_of_eq ?_)
    (probEvent_bad_wcLog_le haxu hfloor henc_inj padMsg oa q hq)
  refine probEvent_bind_congr₂ ($ᵗ K : ProbComp K) fun H =>
    probEvent_bind_congr₂ ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) fun mask => ?_
  rw [probEvent_bad_wcInst_eq_wcLog hash enc H mask padMsg unpad oa, probEvent_map]
  rfl

end OracleComp.WegmanCarter
