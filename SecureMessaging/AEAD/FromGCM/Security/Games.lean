/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Construction
import SecureMessaging.AEAD.FromGCM.Security.CipherProfile
import SecureMessaging.AEAD.FromGCM.Security.Encoding
import SecureMessaging.AEAD.FromGCM.Security.OneTimePad
import ToVCVio.OracleComp.Constructions.SampleableType
import ToVCVio.OracleComp.QueryTracking.LazySampling
import ToVCVio.ProgramLogic.Relational.IdenticalUntilBad
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.EvalDist.Defs.NeverFails

/-!
# GCM — game skeleton and games

The OracleSpec-polymorphic game skeleton for the one-time IND-CCA proof of
`gcmOneTimeAEAD`, its per-tuple oracle-implementation families, and the games.

The Phase-2 game chain:
- `game0` — real cipher (`gcmOneTimeAEAD.encrypt`/`.decrypt` at a sampled key), live decrypt.
- `game1` — one uniform tuple `(H, mask, ks)` sampled at the top level, live decrypt.
- `game2` — the same tuple sampled inside the oracles (`greedyLazy`), live decrypt.
- `game3` — tuple sampled at the encryption query (`consumeLazy`), decrypt always rejects.
- `game4` — `game3` with the challenge ciphertext drawn uniformly.
- `game2♭`/`game3♭` — bad-flag-instrumented variants for the identical-until-bad step.

Every game is an instance of `gcmGameSkeleton`, which returns a `QueryImpl` (not a
baked-in `simulateQ … |>.run'`) so the lazy-sampling lemmas — which take an impl family
`τ → QueryImpl spec (StateT σ ProbComp)` — compose directly with the tuple families
`gcmTupleImpl`/`gcmTupleImplReject` defined here.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational

/-! ## Structural instances (criterion 7)

Pinned as `example`s so CI fails if an instance regresses. `DecidableEq SupportedAAD`
is deliberately NOT pinned: the challenge guard compares the ciphertext only
(ACD19 Def 2 / Fig 1, matching `oracleDecrypt` in `AEAD/Defs.lean`), so no decidable
equality on the associated data is ever needed. -/

section InstancePins

variable {L : ℕ}

example : SampleableType (BitVec L × BitVec 128) := inferInstance
example : DecidableEq (BitVec L × BitVec 128) := inferInstance
example : Fintype (BitVec 128) := inferInstance
example : DecidableEq (BitVec 128) := inferInstance
-- The game1 tuple `(H, mask, ks)`.
example : SampleableType (BitVec 128 × BitVec 128 × BitVec L) := inferInstance

end InstancePins

/-! ## Game skeleton -/

section Skeleton

variable {L : ℕ}

/-- Parameterized GCM one-time IND-CCA game skeleton, polymorphic over the oracle spec.

Adapted from `EtM.etmGameSkeleton`, but returning the assembled `QueryImpl` rather than
running it: the lazy-sampling lemmas (`greedyLazy`/`consumeLazy`) consume impl families
`τ → QueryImpl spec (StateT σ ProbComp)`, so the `simulateQ … |>.run'` lives in the game
definitions, not here.

- `encStar ad m` produces the challenge ciphertext (real cipher, tuple form, or uniform).
- `decryptResp ad e` answers non-challenge decryption queries (live or always-reject).
- `unifImpl` forwards the adversary's `unifSpec` queries; games (`spec := unifSpec`)
  use `oracleUnif`, reductions lift through their own spec.

The encryption oracle is one-shot (second call returns `none`) and the decryption oracle
implements the ACD19 ciphertext-only challenge guard (`(← get) == some e`, AAD ignored),
matching `oracleEncrypt`/`oracleDecrypt` in `AEAD/Defs.lean`. Game state is the challenge
ciphertext `Option (BitVec L × BitVec 128)`. -/
noncomputable def gcmGameSkeleton {ι : Type} {spec : OracleSpec ι}
    (encStar : SupportedAAD → BitVec L → OracleComp spec (BitVec L × BitVec 128))
    (decryptResp : SupportedAAD → (BitVec L × BitVec 128) → OracleComp spec (Option (BitVec L)))
    (unifImpl : QueryImpl unifSpec
        (StateT (Option (BitVec L × BitVec 128)) (OracleComp spec))) :
    QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128)) (OracleComp spec)) :=
  let encImpl : QueryImpl (SupportedAAD × BitVec L →ₒ Option (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128)) (OracleComp spec)) :=
    fun (ad, m) => do
      match (← get) with
      | some _ => pure none
      | none =>
        let e ← liftM (encStar ad m)
        set (some e)
        return some e
  let decImpl : QueryImpl (SupportedAAD × (BitVec L × BitVec 128) →ₒ Option (BitVec L))
      (StateT (Option (BitVec L × BitVec 128)) (OracleComp spec)) :=
    fun (ad, e) => do
      if (← get) == some e then pure none
      else liftM (decryptResp ad e)
  unifImpl + encImpl + decImpl

end Skeleton

/-! ## Per-tuple implementation families

The tuple `a = (H, mask, ks) : BitVec 128 × BitVec 128 × BitVec L` collects the three
separated cipher outputs of one-time GCM at the all-zero IV (`CipherProfile.lean`): the
GHASH key `H`, the tag mask, and the (flattened) GCTR keystream. The encrypt/decrypt
bodies below are the SAME expressions across both families and are written via
`gcmEncode` so the AXU/`ghash` lemmas apply downstream; the bridge from
`gcmEncryptSpec`/`gcmDecryptSpec` (which take keystream *blocks*) to this `ks : BitVec L`
form is Phase 3's job. -/

section TupleFamilies

variable {L : ℕ}

/-- LIVE per-tuple implementation family (`game1`/`game2`): encryption produces the real
GCM ciphertext from the tuple `a = (H, mask, ks)` (`c = m ^^^ ks`,
`t = ghash H (gcmEncode ad c) ^^^ mask`), and decryption runs live verification and
keystream removal from the same tuple. -/
noncomputable def gcmTupleImpl (a : BitVec 128 × BitVec 128 × BitVec L) :
    QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128)) ProbComp) :=
  gcmGameSkeleton (spec := unifSpec)
    (fun ad m => pure (let (h, mask, ks) := a
      let c := m ^^^ ks
      (c, ghash h (gcmEncode ad c) ^^^ mask)))
    (fun ad e => pure (let (h, mask, ks) := a
      if e.2 = ghash h (gcmEncode ad e.1) ^^^ mask
      then some (e.1 ^^^ ks) else none))
    (oracleUnif (BitVec L × BitVec 128))

/-- REJECT per-tuple implementation family (`game3`): identical encryption to
`gcmTupleImpl`, but the decryption oracle always rejects. -/
noncomputable def gcmTupleImplReject (a : BitVec 128 × BitVec 128 × BitVec L) :
    QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128)) ProbComp) :=
  gcmGameSkeleton (spec := unifSpec)
    (fun ad m => pure (let (h, mask, ks) := a
      let c := m ^^^ ks
      (c, ghash h (gcmEncode ad c) ^^^ mask)))
    (fun _ _ => pure none)
    (oracleUnif (BitVec L × BitVec 128))

end TupleFamilies

/-! ## Games -/

section Games

variable {K : Type} {L : ℕ}

/-- Game 0: real cipher. The key is sampled OUTSIDE the skeleton and the oracles use the
scheme's `encrypt`/`decrypt` directly (not the spec/profile form), so `game0_eq_real` is
a clean `id`-projection against `aeadSecurityImpl … false k`. State is plain
`Option (BitVec L × BitVec 128)`, matching the endpoint's. -/
noncomputable def game0 (prp : PRPScheme K (BitVec 128)) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let k ← prp.keygen
  (simulateQ (gcmGameSkeleton (spec := unifSpec)
      (fun ad m => pure ((gcmOneTimeAEAD prp L hL).encrypt k ad m))
      (fun ad e => pure ((gcmOneTimeAEAD prp L hL).decrypt k ad e))
      (oracleUnif (BitVec L × BitVec 128))) adv).run' none

/-- Game 1: one uniform tuple `(H, mask, ks)` sampled at the top level, live decrypt
(`gcmTupleImpl`). This is the eager form the greedy lazy-sampling lemma consumes in the
`game1 = game2` hop. -/
-- `_prp`/`_hL` are unused in the body but kept to pin `K`/`L` and align the signature
-- with the other games (matching EtM `encReduction`).
@[nolint unusedArguments]
noncomputable def game1 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let a ← ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
  (simulateQ (gcmTupleImpl a) adv).run' none

/-- Game 2: game1's tuple moved inside the oracles via `greedyLazy` — the sample happens
at the adversary's first query instead of at the top level, live decrypt. State grows a
one-slot cache: `Option (BitVec L × BitVec 128) × Option (BitVec 128 × BitVec 128 × BitVec L)`,
starting empty at `(none, none)`. -/
@[nolint unusedArguments]
noncomputable def game2 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool :=
  (simulateQ (greedyLazy gcmTupleImpl) adv).run' (none, none)

/-- Criterion 3: the always-reject family `gcmTupleImplReject` is independent of the tuple
`a` at every non-encryption query, in the exact `h_indep` shape
`probOutput_simulateQ_consumeLazy_run'_eq` demands. At `OUnif` the handler is the lifted
uniform oracle and at `ODecrypt` the response is `pure none` (up to the challenge guard) —
neither mentions `a`, so both branches close definitionally. -/
theorem gcmTupleImplReject_indep :
    ∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)).Domain)
      (s : Option (BitVec L × BitVec 128)) (a₁ a₂ : BitVec 128 × BitVec 128 × BitVec L),
      (fun t => t matches OEncrypt _) t = false →
      (gcmTupleImplReject a₁ t).run s = (gcmTupleImplReject a₂ t).run s := by
  intro t s a₁ a₂ h
  rcases t with (n | am) | ac
  · -- OUnif: the lifted unif handler never mentions the tuple.
    rfl
  · -- OEncrypt: hit = true, contradicting `h`.
    simp at h
  · -- ODecrypt: `pure none` (behind the challenge guard) never mentions the tuple.
    rfl

/-- Game 3: tuple sampled at the encryption query via `consumeLazy` over the always-reject
family `gcmTupleImplReject`; the non-hit queries are `τ`-independent per
`gcmTupleImplReject_indep`. Same augmented state as `game2`, starting at `(none, none)`. -/
@[nolint unusedArguments]
noncomputable def game3 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool :=
  (simulateQ (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _))
    adv).run' (none, none)

/-- UNIFORM-cipher + always-reject implementation family (`game4`): the challenge
ciphertext is drawn from `$ᵗ (BitVec L × BitVec 128)` and the decryption oracle always
rejects. The family ignores its tuple argument `a` at EVERY query, so it is trivially
`τ`-independent everywhere (its own `h_indep` is immediate); the tuple sample at the hit
query is dead and gets eliminated in `game4_eq_rand` (02-04) via uniform-sample
losslessness. Kept parameterized so `game4` stays in `consumeLazy` shape at the encryption
query — Phase 5 couples `game3` and `game4` at that shared sample site. If splitting the
product draw is convenient, `uniformSample_prod_eq_bind (BitVec L) (BitVec 128)` applies. -/
@[nolint unusedArguments]
noncomputable def gcmRandRejectImpl (_a : BitVec 128 × BitVec 128 × BitVec L) :
    QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128)) ProbComp) :=
  gcmGameSkeleton (spec := unifSpec)
    (fun _ _ => liftM ($ᵗ (BitVec L × BitVec 128) : ProbComp (BitVec L × BitVec 128)))
    (fun _ _ => pure none)
    (oracleUnif (BitVec L × BitVec 128))

/-- Game 4: `game3` with the challenge ciphertext drawn uniformly instead of computed from
the tuple — `consumeLazy` over `gcmRandRejectImpl` at the same hit predicate and the same
empty cache, so Phase 5's per-query coupling lands at the same sample site. -/
@[nolint unusedArguments]
noncomputable def game4 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool :=
  (simulateQ (consumeLazy gcmRandRejectImpl (fun t => t matches OEncrypt _))
    adv).run' (none, none)

end Games

/-! ## Instrumented pair (criterion 4): `game3♭` / `game2♭`

Bad-flag-instrumented eager variants of `game3`/`game2` for the Phase-4
identical-until-bad step (`tvDist_simulateQ_le_probEvent_output_bad_base`,
`IdenticalUntilBad.lean`). The Lean identifiers `game3Flat`/`game2Flat` realize the
roadmap's `game3♭`/`game2♭`.

The tuple is sampled EAGERLY at the top level (state `Option C × Bool`, mirroring EtM
`authInstImpl`'s `EtmGameState × Bool`): the flag update at a decrypt query evaluates
"verification would accept", which reads `H`/`mask`, so no flag-carrying family is
`τ`-independent and `consumeLazy`'s `h_indep` cannot hold for it; the Phase-4 brick
consumes an eager `StateT (σ × Bool)` pair anyway. Flag erasure (`Prod.fst`) plus the
lazy commutations (`greedyLazy` for `game2`, `consumeLazy` for `game3`) recover the
uninstrumented games — the projection lemmas below. -/

section Instrumented

variable {K : Type} {L : ℕ}

/-- Flag-instrumented per-tuple handler for the identical-until-bad step. State is
`Option (BitVec L × BitVec 128) × Bool` with the monotone `forged` flag RIGHTMOST (the
brick reads `z.2.2` and `Prod.fst` erases exactly the flag). The decrypt oracle sets the
flag whenever "verification would accept" (`forged || ok`, identical in both `b`
branches, never cleared); `b` selects only the return on `ok = true`: live decryption
(`b = true`, ≈ `game2`) or rejection (`b = false`, ≈ `game3`). This shared flag update
is what makes the brick's `h_agree_good` hold in Phase 4. -/
noncomputable def gcmInstImpl (a : BitVec 128 × BitVec 128 × BitVec L) (b : Bool) :
    QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128) × Bool) ProbComp) :=
  -- unif: thread both state slots unchanged.
  (unifLiftStateT (Option (BitVec L × BitVec 128) × Bool) unifSpec)
  -- encrypt: one-shot, real GCM ciphertext from the tuple; flag threaded unchanged.
  + ((fun (ad, m) => do
      let (challenge, forged) ← get
      match challenge with
      | some _ => pure none
      | none => do
        let (h, mask, ks) := a
        let c := m ^^^ ks
        let e := (c, ghash h (gcmEncode ad c) ^^^ mask)
        set ((some e, forged) : Option (BitVec L × BitVec 128) × Bool)
        return some e) :
    QueryImpl (SupportedAAD × BitVec L →ₒ Option (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128) × Bool) ProbComp))
  -- decrypt: challenge guard; else compute "would accept", set the flag on accept,
  -- and return per `b`.
  + ((fun (ad, e) => do
      let (challenge, forged) ← get
      if challenge == some e then pure none
      else do
        let (h, mask, ks) := a
        let ok : Bool := decide (e.2 = ghash h (gcmEncode ad e.1) ^^^ mask)
        set ((challenge, forged || ok) : Option (BitVec L × BitVec 128) × Bool)
        if ok then (if b then pure (some (e.1 ^^^ ks)) else pure none) else pure none) :
    QueryImpl (SupportedAAD × (BitVec L × BitVec 128) →ₒ Option (BitVec L))
      (StateT (Option (BitVec L × BitVec 128) × Bool) ProbComp))

/-- Game 3♭: the flag-instrumented ALWAYS-REJECT execution (`b = false`), tuple sampled
eagerly at the top level. Defined BEFORE `game2Flat`: it occupies the `impl₁` slot of
Phase 4's `tvDist_simulateQ_le_probEvent_output_bad_base` (`IdenticalUntilBad.lean:35`),
which charges the bad event of its FIRST implementation argument. -/
@[nolint unusedArguments]
noncomputable def game3Flat (_prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let a ← ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
  (simulateQ (gcmInstImpl a false) adv).run' (none, false)

/-- Game 2♭: the flag-instrumented LIVE-DECRYPT execution (`b = true`), tuple sampled
eagerly at the top level. Goes in the brick's `impl₂` slot in Phase 4. -/
@[nolint unusedArguments]
noncomputable def game2Flat (_prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let a ← ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
  (simulateQ (gcmInstImpl a true) adv).run' (none, false)

/-! ### Projection lemmas (criterion 4)

Each is proved in two steps (mirroring EtM `Auth/Hop.lean`):
(i) FLAG ERASURE — the `forged` flag is write-only (it never gates the state transition
    or the output bit), so dropping it via `Prod.fst`
    (`run'_simulateQ_eq_of_query_map_eq`) recovers the eager top-level-tuple game over
    `gcmTupleImpl` (`b = true`) resp. `gcmTupleImplReject` (`b = false`);
(ii) LAZY COMMUTATION — the eager form is exactly what the lazy lemmas commute:
    `probOutput_simulateQ_greedyLazy_run'_eq` yields `game2`, and
    `probOutput_simulateQ_consumeLazy_run'_eq` (with `gcmTupleImplReject_indep` as
    `h_indep`) yields `game3`.

Both are stated as `evalDist` (full-distribution) equalities — NOT `Pr[= true | ·]` —
because Phase 4 feeds them into a `tvDist` chain
(`abs_probOutput_toReal_sub_le_tvDist`). -/

/-- Flag erasure at `b = true`: dropping the write-only `forged` flag (`Prod.fst`) from
`gcmInstImpl a true` recovers the live per-tuple family `gcmTupleImpl a`, independently
of the initial flag. -/
lemma simulateQ_gcmInstImpl_true_run'_eq_gcmTupleImpl
    (a : BitVec 128 × BitVec 128 × BitVec L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (s : Option (BitVec L × BitVec 128)) (forged : Bool) :
    (simulateQ (gcmInstImpl a true) adv).run' (s, forged) =
      (simulateQ (gcmTupleImpl a) adv).run' s := by
  refine run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst ?_ adv (s, forged)
  intro t state
  obtain ⟨challenge, flag⟩ := state
  obtain ⟨h, mask, ks⟩ := a
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
  · -- OUnif: both handlers are the lifted uniform oracle, state threaded unchanged.
    simp [gcmInstImpl, gcmTupleImpl, gcmGameSkeleton, oracleUnif, unifLiftStateT,
      QueryImpl.liftTarget_apply, StateT.run_monadLift, Prod.map, Functor.map_map]
  · -- OEncrypt: identical one-shot bodies; the flag is written back unchanged.
    cases challenge <;>
      simp [gcmInstImpl, gcmTupleImpl, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map]
  · -- ODecrypt: guard split, then `ok` split; live return matches `gcmTupleImpl`'s
    -- verification body and the flag write is erased by the projection.
    by_cases hguard : challenge = some e
    all_goals
      simp [gcmInstImpl, gcmTupleImpl, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure,
        Prod.map, ← apply_ite, beq_iff_eq, hguard]

/-- Flag erasure at `b = false`: dropping the write-only `forged` flag (`Prod.fst`) from
`gcmInstImpl a false` recovers the always-reject family `gcmTupleImplReject a`,
independently of the initial flag. -/
lemma simulateQ_gcmInstImpl_false_run'_eq_gcmTupleImplReject
    (a : BitVec 128 × BitVec 128 × BitVec L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (s : Option (BitVec L × BitVec 128)) (forged : Bool) :
    (simulateQ (gcmInstImpl a false) adv).run' (s, forged) =
      (simulateQ (gcmTupleImplReject a) adv).run' s := by
  refine run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst ?_ adv (s, forged)
  intro t state
  obtain ⟨challenge, flag⟩ := state
  obtain ⟨h, mask, ks⟩ := a
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
  · -- OUnif: both handlers are the lifted uniform oracle, state threaded unchanged.
    simp [gcmInstImpl, gcmTupleImplReject, gcmGameSkeleton, oracleUnif, unifLiftStateT,
      QueryImpl.liftTarget_apply, StateT.run_monadLift, Prod.map, Functor.map_map]
  · -- OEncrypt: identical one-shot bodies; the flag is written back unchanged.
    cases challenge <;>
      simp [gcmInstImpl, gcmTupleImplReject, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map]
  · -- ODecrypt: both `ok` branches return `none`; the flag write is erased by the
    -- projection, matching the unconditional `pure none`.
    by_cases hguard : challenge = some e
    all_goals
      simp [gcmInstImpl, gcmTupleImplReject, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure,
        Prod.map, beq_iff_eq, hguard]

/-- Criterion 4 projection, live side: `evalDist game2♭ = evalDist game2`, by flag
erasure (`Prod.fst`) followed by `greedyLazy` commutation (premise-free). -/
theorem game2Flat_eq_game2 (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    evalDist (game2Flat prp L hL adv) = evalDist (game2 prp L hL adv) := by
  unfold game2Flat game2
  rw [bind_congr fun a =>
    simulateQ_gcmInstImpl_true_run'_eq_gcmTupleImpl a adv none false]
  exact probOutput_simulateQ_greedyLazy_run'_eq gcmTupleImpl adv none

/-- Criterion 4 projection, reject side: `evalDist game3♭ = evalDist game3`, by flag
erasure (`Prod.fst`) followed by `consumeLazy` commutation at
`hit = (fun t => t matches OEncrypt _)` with `gcmTupleImplReject_indep` as `h_indep`. -/
theorem game3Flat_eq_game3 (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    evalDist (game3Flat prp L hL adv) = evalDist (game3 prp L hL adv) := by
  unfold game3Flat game3
  rw [bind_congr fun a =>
    simulateQ_gcmInstImpl_false_run'_eq_gcmTupleImplReject a adv none false]
  exact probOutput_simulateQ_consumeLazy_run'_eq gcmTupleImplReject
    (fun t => t matches OEncrypt _) gcmTupleImplReject_indep adv none

end Instrumented

/-! ## Endpoints (criteria 5/6): `game0` = real, `game4` = random

Both are `Pr[= true | ·]` equalities against
`AEADScheme.securityExpFixedBit (gcmOneTimeAEAD prp L hL) adv <bit>`, carrying
`[NeverFail prp.keygen]` as the only extra hypothesis (ROADMAP criterion 6; on the
current VCVio checkout the instance is derivable for ANY `ProbComp` via the blanket
total-PMF-lift instance, so it is redundant but harmless — kept for contract
stability against a future failure-capable keygen monad). These two statements are
the anchors Phase 6's triangle inequality attaches to. -/

section Endpoints

variable {K : Type}

/-- Criterion 5, left end: `game0` IS the real ACD19 experiment
(`securityExpFixedBit … false`).

Mirrors EtM `PrfHop.game0_eq_real` but SIMPLER: GCM has a single key
(`gcmOneTimeAEAD.keygen = prp.keygen`), so there is no independent-key swap, and
`game0`'s state is plain `Option C` matching the endpoint's, so the projection is
`id`, not `Prod.fst`. -/
theorem game0_eq_real (prp : PRPScheme K (BitVec 128)) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    [NeverFail prp.keygen] :
    Pr[= true | game0 prp L hL adv] =
      Pr[= true | AEADScheme.securityExpFixedBit (gcmOneTimeAEAD prp L hL) adv false] := by
  -- Unfold only the keygen projection (keep `aeadSecurityImpl` folded to match the RHS).
  have hkg : (gcmOneTimeAEAD prp L hL).keygen = prp.keygen := rfl
  unfold game0 AEADScheme.securityExpFixedBit
  rw [hkg]
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Both sides start with `prp.keygen`; descend under the single key bind.
  refine probOutput_bind_congr' prp.keygen true (fun k => ?_)
  -- Inner per-key equality: game0's skeleton impl projects onto
  -- `aeadSecurityImpl … false k` with `proj = id` (state `Option C` on both sides).
  refine congrArg (fun o => Pr[= true | o]) ?_
  refine run'_simulateQ_eq_of_query_map_eq _
    (AEADScheme.aeadSecurityImpl (gcmOneTimeAEAD prp L hL) false k) id ?hproj adv none
  case hproj =>
    intro t s
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
    · -- OUnif: both handlers are the lifted uniform oracle, state threaded unchanged.
      simp [gcmGameSkeleton, AEADScheme.aeadSecurityImpl, AEADScheme.oracleUnif,
        unifLiftStateT, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        StateT.run_monadLift, Functor.map_map]
    · -- OEncrypt: identical one-shot real-cipher bodies (the `b = false` branch of
      -- `oracleEncrypt` is `pure (ae.encrypt k a m)`, matching the skeleton's `encStar`).
      cases s <;>
        simp [gcmGameSkeleton, AEADScheme.aeadSecurityImpl, AEADScheme.oracleEncrypt,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
          StateT.run_get, StateT.run_set, StateT.run_pure, map_pure]
    · -- ODecrypt: `false || guard = guard`; the live decrypt body matches verbatim.
      simp [gcmGameSkeleton, AEADScheme.aeadSecurityImpl, AEADScheme.oracleDecrypt,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get]

end Endpoints

end GCM
