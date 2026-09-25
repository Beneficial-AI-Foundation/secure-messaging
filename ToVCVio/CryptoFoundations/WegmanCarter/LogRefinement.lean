/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.WegmanCarter.Defs
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Wegman-Carter one-time authenticity: the log-refined handler

A proof device for `Security.lean`. In `wcInstImpl … false` (`Defs.lean`) the decryption
oracle reads `(H, mask)` to update `forged`, which blocks moving those draws past the
adversary's queries. `wcLogImpl` instead appends each decryption query that passes the
challenge check to a log and never reads `(H, mask)`; the flag is recovered afterwards as the
fold `wcFlag` over the log. The challenge slot also keeps its associated data, which the AXU
step needs for the hash input `enc (ad*, c*)`.

`probEvent_bad_wcInst_eq_wcLog` shows that the two handlers raise the flag with the same
probability.
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace OracleComp.WegmanCarter

section DecryptNormalForm

variable {K A M Cb D : Type}

/-- In the always-reject execution a decryption query `(ad, e)` returns `none` and only updates
the flag: it is raised when `e` is not the challenge and its tag verifies. -/
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

/-! ## The log-refined handler -/

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
log-refined run raises `wcFlag`. -/
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

end OracleComp.WegmanCarter
