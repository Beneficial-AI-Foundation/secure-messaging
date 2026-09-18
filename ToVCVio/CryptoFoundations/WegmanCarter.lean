/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.UniversalHash
import ToVCVio.CryptoFoundations.WegmanCarterBound
import ToVCVio.OracleComp.Constructions.BitVec
import ToVCVio.OracleComp.SimSemantics.UnifLift
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Wegman-Carter one-time authenticity

A one-time authenticated encryption scheme whose tag is `hash H X ^^^ mask`, with `H` a
uniformly random key of an almost-XOR-universal (AXU) hash family and `mask` a uniformly
random one-time pad, admits forgery probability at most `q · ε` against an adversary making at
most `q` decryption queries, `ε` being the AXU bound. The public result is
`probEvent_wcInst_forge_le`. GCM is the motivating instance, but nothing here depends on it.

Two points a consumer must get right:

* AXU is assumed of `hash` on the *encoded* domain `D`. A polynomial hash on raw block lists
  is not AXU: `[0, X]` and `[X]` are distinct inputs with the same hash under every key. The
  AEAD's length encoding separates such pairs. Instantiate `hash := hash ∘ encode` and
  `enc := id`.
* The live-decrypt handler (`b = true`) returns `unpad e.1`, which for a stream cipher is
  `C' ^^^ keystream`: a successful decryption leaks the pad. A privacy argument built on this
  file must be made between the always-reject executions.

## Main declarations

* `wcSpec`, `wcInstImpl`: the one-time AEAD chosen-ciphertext oracle spec and the
  flag-instrumented handler, whose `forged` flag records whether any decryption query would
  have verified.
* `WCLogState`, `wcLogImpl`, `wcProj`: a log-refined handler whose decrypt oracle does not
  read `(H, mask)`, and the projection back onto `wcInstImpl`'s state.
* `probEvent_wcInst_forge_le`: the `q · ε` bound.
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace OracleComp.WegmanCarter

/-! ## The spec -/

/-- The one-time AEAD chosen-ciphertext oracle spec: uniform sampling, a one-shot encrypt
oracle and a decrypt oracle. The same spec as `aeadOneTimeCCASpec` in
`SecureMessaging/AEAD/Defs.lean`, restated so that `ToVCVio` does not import `SecureMessaging`. -/
abbrev wcSpec (A M Cb : Type) :=
  unifSpec + (A × M →ₒ Option (Cb × BitVec 128)) + (A × (Cb × BitVec 128) →ₒ Option M)

/-! ## The flag-instrumented handler -/

/-- The flag-instrumented Wegman-Carter handler. The state is the challenge ciphertext slot
and a `forged` flag, in that order as the identical-until-bad lemmas expect. Decryption rejects
the challenge ciphertext, raises the flag whenever the tag verifies and never lowers it, and
returns the plaintext only when `b = true`; `b = false` is the always-reject execution. -/
def wcInstImpl {K A M Cb D : Type} [DecidableEq Cb]
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

/-- Normal form of the always-reject decrypt step, a pure flag update returning `none`.
`hproj_decrypt` rewrites the instrumented side with it instead of unfolding `wcInstImpl`. -/
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

The `forged` flag is replaced by a log of the guard-passing decrypt queries, so that the
decrypt oracle no longer reads `(H, mask)`; the flag is recovered by the fold `wcFlag`. The
challenge slot also keeps its AAD, which the AXU step needs for the digest point
`enc (ad*, c*)`. -/

/-- The challenge ciphertext with its AAD, and the log of guard-passing decrypt queries. -/
abbrev WCLogState (A Cb : Type) :=
  Option (A × (Cb × BitVec 128)) × List (A × (Cb × BitVec 128))

/-- The log-refined handler: observably the same as `wcInstImpl … false`, but its decrypt
oracle only appends the query to the log and never reads `H` or `mask`. -/
def wcLogImpl {K A M Cb D : Type} [DecidableEq Cb]
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
        set ((challenge, log ++ [(ad, e)]) : WCLogState A Cb)
        pure none) : QueryImpl (A × (Cb × BitVec 128) →ₒ Option M)
      (StateT (WCLogState A Cb) ProbComp))

/-- Whether a logged decrypt query carries the correct tag for its digest point. -/
def wcAccepts {K A Cb D : Type} (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128) (q : A × (Cb × BitVec 128)) : Bool :=
  decide (q.2.2 = hash H (enc (q.1, q.2.1)) ^^^ mask)

/-- The `forged` flag, recovered as a pure fold over the log. -/
def wcFlag {K A Cb D : Type} (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128) (s : WCLogState A Cb) : Bool :=
  s.2.any (wcAccepts hash enc H mask)

/-- Projection from the log-refined state onto `wcInstImpl`'s: drop the challenge AAD and
collapse the log to the flag. -/
def wcProj {K A Cb D : Type} (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (H : K) (mask : BitVec 128) (s : WCLogState A Cb) :
    Option (Cb × BitVec 128) × Bool :=
  (s.1.map Prod.snd, wcFlag hash enc H mask s)

/-! ## Transport across the log refinement -/

section LogRefinement

variable {K A M Cb D : Type}

/-! ### Per-oracle projection steps

One lemma per oracle: a single `simp` over all three handler summands times out. -/

private lemma hproj_unif [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (H : K) (mask : BitVec 128)
    (padMsg : M → Cb) (unpad : Cb → M)
    (n : ℕ) (s : WCLogState A Cb) :
    Prod.map id (wcProj hash enc H mask) <$>
        ((wcLogImpl hash enc H mask padMsg) (Sum.inl (Sum.inl n))).run s =
      ((wcInstImpl hash enc H mask padMsg unpad false) (Sum.inl (Sum.inl n))).run
        (wcProj hash enc H mask s) := by
  simp [wcLogImpl, wcInstImpl, unifLiftStateT,
    StateT.run_monadLift, Prod.map, Functor.map_map]

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

/-- The decrypt step, the only one with content: appending an entry to the log corresponds to
`forged || ok` on the flag. -/
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

/-- Projecting the log-refined run through `wcProj` gives the instrumented always-reject run,
outputs and final states jointly. -/
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

/-- The instrumented always-reject run raises `forged` with exactly the probability that the
log-refined run raises `wcFlag`. `probEvent_wcInst_forge_le` uses it to move the forgery event
to `wcLogImpl`, where `probEvent_bad_wcLog_le` bounds it. -/
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

end LogRefinement

/-- If a state functional `f` grows by at most one at every `p`-query and not at all at other
queries, then along any run in the support it grows by at most the `p`-query budget `n`. -/
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


/-! ## The probability core

An induction over the adversary that conditions on the run so far:

* while no challenge is set the handler does not read `(H, mask)`, so both draws commute
  past each step (`hoist_step`, `pre_phase`);
* at the encrypt query the pre-challenge log is a fixed list and the mask is still fresh, so
  the pre-challenge entries are a blind guess at it (`pre_half_le`);
* afterwards the handler never reads `(H, mask)` again (`run_challenge_some_indep`); the mask
  draw is reparameterised by `mask ↦ hash H X* ^^^ mask`, making the challenge tag uniform
  and the run `H`-free (`reparam_bind`), `H` moves to the end (`hoist_H`) and the
  post-challenge entries are bounded by AXU (`post_half_le`);
* the two halves are added under one budget (`post_phase`).
-/

section ProbabilityCore

variable {K A M Cb D : Type}

/-! ### `BitVec` rearrangements -/

private lemma tag_eq_iff_mask_eq (a h m : BitVec 128) :
    a = h ^^^ m ↔ m = a ^^^ h := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    rw [BitVec.xor_comm a h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The post-challenge acceptance test in the AXU shape of `probEvent_post_axu_le`. -/
private lemma post_event_iff (u v a T : BitVec 128) :
    a = u ^^^ (v ^^^ T) ↔ u ^^^ v = a ^^^ T := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm (u ^^^ v) T]
  exact tag_eq_iff_mask_eq a T (u ^^^ v)

/-- Bind congruence for continuations of different types carrying different events. -/
private lemma probEvent_bind_congr₂ {α β γ : Type} (mx : ProbComp α)
    {ob₁ : α → ProbComp β} {ob₂ : α → ProbComp γ} {p : β → Prop} {q : γ → Prop}
    (h : ∀ x, Pr[ p | ob₁ x] = Pr[ q | ob₂ x]) :
    Pr[ p | mx >>= ob₁] = Pr[ q | mx >>= ob₂] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact tsum_congr fun x => by rw [h x]

/-! ### The pre-challenge half -/

/-- Over a uniform key and a fresh uniform mask, some entry of the fixed pre-challenge log `L`
accepts with probability at most `|L| · 2⁻¹²⁸`, under any continuation `k` that reports the
drawn pair (`hk`). -/
private lemma pre_half_le [SampleableType K]
    (hash : K → D → BitVec 128) (enc : A × Cb → D)
    (L : List (A × (Cb × BitVec 128)))
    {β : Type} (k : K → BitVec 128 → ProbComp β) (obs : β → K × BitVec 128)
    (hk : ∀ H m, ∀ y ∈ support (k H m), obs y = (H, m)) :
    Pr[fun y => L.any (wcAccepts hash enc (obs y).1 (obs y).2) = true
       | ($ᵗ K : ProbComp K) >>= fun H =>
           ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m => k H m]
      ≤ (L.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := by
  refine le_trans (probEvent_pre_fresh_le ($ᵗ K)
      (fun H => L.map (fun r => r.2.2 ^^^ hash H (enc (r.1, r.2.1)))) k _ ?_) ?_
  · intro H m y hy
    rw [hk H m y hy]
    simp only [List.any_eq_true, wcAccepts, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, ((tag_eq_iff_mask_eq _ _ _).1 he).symm⟩
    · rintro ⟨r, hr, he⟩
      exact ⟨r, hr, (tag_eq_iff_mask_eq _ _ _).2 he.symm⟩
  · simp only [List.length_map]
    exact tsum_count_le ($ᵗ K) (fun _ => L.length) L.length _ fun _ _ => le_rfl

/-! ### After the challenge, the run does not read `(H, mask)` -/

/-- One handler step from a challenge-set state does not read `(H, mask)`. -/
private lemma step_eq [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H H' : K) (m m' : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128))) (t : (wcSpec A M Cb).Domain) :
    (wcLogImpl hash enc H m padMsg t).run (some c, L) =
      (wcLogImpl hash enc H' m' padMsg t).run (some c, L) := by
  rcases t with (j | ⟨ad, mm⟩) | ⟨ad, e⟩ <;>
    simp [wcLogImpl, StateT.run_bind, StateT.run_get]

/-- Once set, the challenge slot never changes. -/
private lemma step_state [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128))) (t : (wcSpec A M Cb).Domain) :
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
        support_pure] at hp
      exact ⟨L ++ [(ad, e)], by rw [Set.eq_of_mem_singleton hp]⟩

/-- From a challenge-set state the log-refined run is the same `ProbComp` for every
`(H, mask)`: the one-shot encrypt oracle is spent and the other oracles never read them. -/
private lemma run_challenge_some_indep [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H H' : K) (m m' : BitVec 128) (c : A × (Cb × BitVec 128))
    (oa : OracleComp (wcSpec A M Cb) α) (L : List (A × (Cb × BitVec 128))) :
    (simulateQ (wcLogImpl hash enc H m padMsg) oa).run (some c, L) =
      (simulateQ (wcLogImpl hash enc H' m' padMsg) oa).run (some c, L) := by
  -- `map_run_simulateQ_eq_of_query_map_eq_inv'` with the identity projection: the invariant
  -- "challenge slot is `some c`" is preserved (`step_state`) and makes the handlers agree
  -- (`step_eq`).
  have h := map_run_simulateQ_eq_of_query_map_eq_inv' (wcLogImpl hash enc H m padMsg)
    (wcLogImpl hash enc H' m' padMsg) (fun s : WCLogState A Cb => s.1 = some c) id
    (fun t s hs y hy => by
      obtain ⟨ch, L'⟩ := s
      simp only at hs
      subst hs
      obtain ⟨L'', hL''⟩ := step_state hash enc padMsg H m c L' t y hy
      rw [hL''])
    (fun t s hs => by
      obtain ⟨ch, L'⟩ := s
      simp only at hs
      subst hs
      rw [Prod.map_id, id_map]
      exact step_eq hash enc padMsg H H' m m' c L' t)
    oa (some c, L) rfl
  simpa using h

/-! ### The post-challenge log extends the fixed prefix -/

/-- Invariant of the post-challenge run: the challenge slot is fixed, the log extends the
prefix `L`, and every appended entry differs from the challenge ciphertext, since the guard
rejects the challenge before it can be logged. -/
private def ExtInv (c : A × (Cb × BitVec 128)) (L : List (A × (Cb × BitVec 128)))
    (s : WCLogState A Cb) : Prop :=
  s.1 = some c ∧ ∃ rest, s.2 = L ++ rest ∧ ∀ r ∈ rest, r.2 ≠ c.2

/-- `ExtInv` holds at the state the encrypt query leaves behind, with an empty extension. -/
private lemma extInv_init (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128))) :
    ExtInv c L ((some c, L) : WCLogState A Cb) :=
  ⟨rfl, [], by simp, by simp⟩

/-- Every oracle step preserves `ExtInv`. -/
private lemma extInv_step [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128))) :
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
        StateT.run_set, map_pure, support_pure] at hy
      rw [Set.eq_of_mem_singleton hy]
      refine ⟨rfl, rest ++ [(ad, e)], by simp, ?_⟩
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hnec r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact fun hcontra => hg hcontra.symm

private lemma wcLogImpl_extends [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (c : A × (Cb × BitVec 128))
    (L : List (A × (Cb × BitVec 128))) (oa : OracleComp (wcSpec A M Cb) α) :
    ∀ z ∈ support ((simulateQ (wcLogImpl hash enc H m padMsg) oa).run ((some c, L))),
      ExtInv c L z.2 :=
  fun z hz => simulateQ_run_preserves_inv_of_query (wcLogImpl hash enc H m padMsg)
    (ExtInv c L) (extInv_step hash enc padMsg H m c L) oa (some c, L) (extInv_init c L) z hz

/-! ### Counting the log

Only the decrypt oracle appends, at most one entry per query, so the log length is bounded by
the decrypt-query budget (`support_state_measure_le_of_isQueryBoundP`). -/

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

/-- An adversary making at most `q` decrypt queries extends the log by at most `q` entries, from
any start state. `post_half_le` applies it from the challenge-set state with prefix `L`,
bounding the extension by the remaining budget `n`. -/
lemma log_length_le_from [DecidableEq Cb] {α : Type}
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

/-! ### The local bijection and the hoisted key -/

/-- At the encrypt query, reparameterise the mask draw along the bijection
`mask ↦ hash H X* ^^^ mask`. On the right the challenge tag `T` is drawn uniformly and the
run is executed with a dummy key `H0` and mask `0`, which `run_challenge_some_indep` allows;
the real mask survives only in the observed value, as `hash H X* ^^^ T`. -/
private lemma reparam_bind [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128)))
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
    rw [BitVec.xor_self_xor]
    rw [run_challenge_some_indep hash enc padMsg H0 H 0
      (hash H (enc (ad, c0)) ^^^ T) (ad, (c0, T)) (ob (some (c0, T))) L]
  simp only [key]
  refine evalDist_ext fun z => ?_
  exact (probOutput_bind_bijective_uniform_cross (BitVec 128)
    (fun x : BitVec 128 => hash H (enc (ad, c0)) ^^^ x) (ToVCVio.bitVec_xor_left_bijective _)
    (fun m => (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
      (simulateQ (wcLogImpl hash enc H m padMsg)
          (ob (some (c0, hash H (enc (ad, c0)) ^^^ m)))).run
        (some (ad, (c0, hash H (enc (ad, c0)) ^^^ m)), L)) z).symm

/-- With the run `H`-free, the key draw moves to the end, the shape `probEvent_post_axu_le`
expects. -/
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
  rw [evalDist_bind_bind_swap ($ᵗ K) ($ᵗ (BitVec 128))
    (fun H T => R T >>= fun z => pure ((H, hash H X ^^^ T), z.2))]
  refine Eq.trans (evalDist_bind_congr' _ fun T =>
    evalDist_bind_bind_swap ($ᵗ K) (R T)
      (fun H z => pure ((H, hash H X ^^^ T), z.2))) ?_
  congr 1
  simp [bind_assoc, map_eq_bind_pure_comp]

/-- The post-challenge run in the shape `probEvent_post_axu_le` expects: challenge tag drawn
uniformly, run executed with the dummy `(H0, 0)`, key drawn last. -/
private lemma post_half_reshape [SampleableType K] [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128))) (H0 : K) :
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

/-- The entries appended after the challenge was set accept with probability at most `n · ε`,
`n` being the remaining decrypt budget. `henc_inj` is what turns "differs from the challenge
ciphertext" (`ExtInv`) into the pair inequality `probEvent_post_axu_le` needs. -/
private lemma post_half_le [SampleableType K] [DecidableEq Cb] {α : Type}
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α) (n : ℕ)
    (hn : ∀ y, (ob y).IsQueryBoundP (· matches Sum.inr _) n)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128))) :
    Pr[fun z : (K × BitVec 128) × WCLogState A Cb =>
         (z.2.2.drop L.length).any (wcAccepts hash enc z.1.1 z.1.2) = true
       | ($ᵗ K : ProbComp K) >>= fun H =>
           ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m =>
             (fun z : α × WCLogState A Cb => ((H, m), z.2)) <$>
               (simulateQ (wcLogImpl hash enc H m padMsg)
                   (ob (some (c0, hash H (enc (ad, c0)) ^^^ m)))).run
                 (some (ad, (c0, hash H (enc (ad, c0)) ^^^ m)), L)]
      ≤ (n : ℝ≥0∞) * ε := by
  obtain ⟨H0⟩ := (inferInstance : Nonempty K)
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (post_half_reshape hash enc padMsg ob ad c0 L H0), probEvent_map]
  simp only [Function.comp_def]
  have hiff : ∀ p : (BitVec 128 × (α × WCLogState A Cb)) × K,
      ((p.1.2.2.2.drop L.length).any
          (wcAccepts hash enc p.2 (hash p.2 (enc (ad, c0)) ^^^ p.1.1)) = true)
        ↔ (∃ x ∈ (p.1.2.2.2.drop L.length).map
              (fun r : A × (Cb × BitVec 128) => (enc (r.1, r.2.1), r.2.2)),
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
      (fun r : A × (Cb × BitVec 128) => (enc (r.1, r.2.1), r.2.2))) ?_) ?_
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
    have h3 : (r.1, r.2.1) = (ad, c0) := henc_inj h1
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
      evalDist_bind_bind_swap ($ᵗ (BitVec 128)) Q (fun m p => F H m p))
    (evalDist_bind_bind_swap ($ᵗ K) Q (fun H p =>
      ($ᵗ (BitVec 128) : ProbComp (BitVec 128)) >>= fun m => F H m p))

/-- From the moment the challenge is set, with pre-challenge log `L` and remaining decrypt
budget `n`: the flag is raised with probability at most `(|L| + n) · ε`, the two halves being
added under the one budget by `combine_pre_post_le`. -/
private lemma post_phase [SampleableType K] [DecidableEq Cb] {α : Type}
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb)
    (ob : Option (Cb × BitVec 128) → OracleComp (wcSpec A M Cb) α) (n : ℕ)
    (hn : ∀ y, (ob y).IsQueryBoundP (· matches Sum.inr _) n)
    (ad : A) (c0 : Cb) (L : List (A × (Cb × BitVec 128))) :
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
    refine combine_pre_post_le (L.length + n) L.length n ε _ _ ?_
      (post_half_le haxu henc_inj padMsg ob n hn ad c0 L) le_rfl hfloor
    refine pre_half_le hash enc L _ Prod.fst ?_
    intro H m y hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨z, -, rfl⟩ := hy
    rfl

/-! ### The pre-challenge phase -/

/-- Once `hoist_step` has moved a prefix `Q` in front of the draws, the induction hypothesis
applies pointwise on `Q`'s support, provided `Q` leaves the challenge unset (`hstate`). -/
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
  refine probEvent_bind_le_of_forall_le fun p hp => ?_
  have hp2 : p.2 = ((none, p.2.2) : WCLogState A Cb) := by rw [← hstate p hp]
  rw [hp2]
  exact hIH p hp

/-- A non-encrypt step from a challenge-unset state does not read `(H, mask)`. -/
private lemma nonEncrypt_step_eq [DecidableEq Cb]
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H H' : K) (m m' : BitVec 128) (L : List (A × (Cb × BitVec 128)))
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
    (H : K) (m : BitVec 128) (L : List (A × (Cb × BitVec 128)))
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

/-- The first encrypt query sets the challenge and the run continues from there. -/
private lemma encrypt_step_run [DecidableEq Cb] {α : Type}
    (hash : K → D → BitVec 128) (enc : A × Cb → D) (padMsg : M → Cb)
    (H : K) (m : BitVec 128) (L : List (A × (Cb × BitVec 128)))
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

/-- The whole bound, by induction on the adversary from a challenge-unset state with log `L`
and decrypt budget `n`. Non-encrypt steps commute past the draws and spend at most one log
entry each; the encrypt step hands over to `post_phase`; if the adversary never encrypts,
every entry is a pre-challenge guess. -/
private lemma pre_phase [SampleableType K] [DecidableEq Cb] {α : Type}
    {hash : K → D → BitVec 128} {ε : ℝ≥0∞} (haxu : IsAlmostXorUniversal hash ε)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε)
    {enc : A × Cb → D} (henc_inj : Function.Injective enc)
    (padMsg : M → Cb) (oa : OracleComp (wcSpec A M Cb) α) :
    ∀ (n : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) n →
      ∀ L : List (A × (Cb × BitVec 128)),
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
      obtain ⟨H0⟩ := (inferInstance : Nonempty K)
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
          rw [run_simulateQ_query_bind (wcLogImpl hash enc H m padMsg) t ob (none, L),
            nonEncrypt_step_eq hash enc padMsg H H0 m 0 L t ht, map_bind]
        simp only [hrun]
        rw [probEvent_congr' (p := fun z : (K × BitVec 128) × WCLogState A Cb =>
          wcFlag hash enc z.1.1 z.1.2 z.2 = true) (fun _ _ => Iff.rfl)
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

/-- The forgery bound at the log-refined handler: `wcFlag` is raised with probability at most
`q · ε`. The observed value carries `(H, mask)` because `wcFlag` reads them; the adversary's
output is discarded. -/
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

/-- One-time Wegman-Carter authenticity: against an adversary making at most `q` decryption
queries, the always-reject instrumented execution raises its `forged` flag with probability
at most `q · ε`, where `hash` is `ε`-AXU on the encoded domain.

Both side hypotheses are needed and are usually free. `henc_inj`: with a non-injective `enc`,
a query `(ad', C')` with `enc (ad', C') = enc (ad*, C*)`, `C' ≠ C*` and the challenge tag
passes the ciphertext-only guard and verifies with probability `1`; at `enc := id` it is
`Function.injective_id`. `hfloor`: on a subsingleton domain AXU is vacuous and admits `ε = 0`,
while a blind tag guess still succeeds with probability `2⁻¹²⁸`; with two distinct domain
points it follows from `IsAlmostXorUniversal.card_inv_le`. -/
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
