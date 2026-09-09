/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.UniversalHash
import ToVCVio.OracleComp.QueryTracking.LazySampling
import ToVCVio.OracleComp.SimSemantics.UnifLift
import VCVio.OracleComp.QueryTracking.QueryBound
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

/-! ## The probability core and the public brick -/

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
      ≤ (q : ℝ≥0∞) * ε :=
  sorry

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
      ≤ (q : ℝ≥0∞) * ε :=
  sorry

end OracleComp.WegmanCarter
