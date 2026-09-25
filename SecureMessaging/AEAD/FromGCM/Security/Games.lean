/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Construction
import SecureMessaging.AEAD.FromGCM.Security.Encoding
import ToVCVio.CryptoFoundations.WegmanCarter.Defs
import ToVCVio.OracleComp.QueryTracking.LazySampling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.EvalDist.Defs.NeverFails

/-!
# GCM: game skeleton and games

The games of the one-time IND-CCA proof of `gcmOneTimeAEAD` (indistinguishability under
chosen-ciphertext attack, one encryption per key): the adversary gets one encryption query
and any number of decryption queries, and must tell the real scheme from one that returns a
uniformly random challenge ciphertext and rejects every decryption.

Every game runs the adversary against an instance of `gcmGameSkeleton`. From `game1` to
`game3` the block cipher is replaced by one uniform tuple `(H, mask, ks)` of the three
outputs GCM uses (GHASH key, tag mask, keystream); the chain:
- `game0`: the real cipher at a sampled key, live decryption.
- `game1`: a uniform tuple sampled up front, live decryption.
- `game2`: the same tuple sampled inside the oracles at the first query (`greedyLazy`).
- `game3`: the tuple sampled at the encryption query (`consumeLazy`); decryption always rejects.
- `game4`: `game3` with the challenge ciphertext drawn uniformly.
- `game2♭`/`game3♭`: `game2`/`game3` with a forgery flag, for the identical-until-bad step
  of the authenticity hop.

The PRF reduction reuses the skeleton's tuple handler, and `game2♭`/`game3♭` are the generic
Wegman–Carter handler `wcInstImpl` at GCM's hash. The lazy-sampling caches of `game2`/`game3`
are proof artifacts, invisible to the adversary.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational
open OracleComp.WegmanCarter

/-! ## Structural instances

Pinned as `example`s so CI fails if one regresses. `DecidableEq SupportedAAD` is not needed:
the challenge guard compares the ciphertext only (ACD19 Def 2, as `oracleDecrypt` in
`AEAD/Defs.lean`). -/

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

/-- The oracles of the one-time IND-CCA game, parameterised by how the challenge ciphertext
is produced (`encStar`) and how a non-challenge decryption query is answered (`decryptResp`).
The state records the challenge ciphertext once issued: a second encryption query returns
`none`, and a decryption query repeating the challenge ciphertext is rejected whatever its
associated data (ACD19's guard, as in `AEAD/Defs.lean`).

Returned as a `QueryImpl` rather than run, so that the lazy-sampling lemmas, which act on
families `τ → QueryImpl spec (StateT σ ProbComp)`, apply to it directly. -/
def gcmGameSkeleton {ι : Type} {spec : OracleSpec ι}
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
      let eStar ← get
      if eStar == some e then pure none
      else liftM (decryptResp ad e)
  unifImpl + encImpl + decImpl

end Skeleton

/-! ## Per-tuple implementation families

The tuple `a = (H, mask, ks) : BitVec 128 × BitVec 128 × BitVec L` holds the three block-cipher
outputs one-time GCM uses (`CipherProfile.lean`): the GHASH key, the tag mask and the
keystream, flattened to `L` bits. Given the tuple, encryption and decryption are
deterministic. -/

section TupleFamilies

variable {L : ℕ}

/-- Oracles computing GCM from the tuple `a` (`game1`/`game2`): encryption masks the message
with the keystream and tags it with GHASH, decryption checks the tag and unmasks. -/
def gcmTupleImpl (a : BitVec 128 × BitVec 128 × BitVec L) :
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

/-- `gcmTupleImpl` with a decryption oracle that always rejects (`game3`). -/
def gcmTupleImplReject (a : BitVec 128 × BitVec 128 × BitVec L) :
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

/-- Game 0: the real scheme at a sampled key. It is the only game mentioning the IV; from
`game1` on the block cipher is gone and the IV matters only through which cipher inputs
produced the tuple. -/
def game0 (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let k ← prp.keygen
  (simulateQ (gcmGameSkeleton (spec := unifSpec)
      (fun ad m => pure ((gcmOneTimeAEAD prp iv L hL).encrypt k ad m))
      (fun ad e => pure ((gcmOneTimeAEAD prp iv L hL).decrypt k ad e))
      (oracleUnif (BitVec L × BitVec 128))) adv).run' none

/-- Game 1: the block cipher's outputs replaced by one uniform tuple, sampled up front. -/
-- `_prp`/`_hL` are unused in the body but kept to pin `K`/`L` and align the signature
-- with the other games.
def game1 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let a ← ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
  (simulateQ (gcmTupleImpl a) adv).run' none

/-- Game 2: `game1` with the tuple sampled at the adversary's first query instead of up
front; the state gains a one-slot cache for it. -/
noncomputable def game2 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool :=
  (simulateQ (greedyLazy gcmTupleImpl) adv).run' (none, none)

/-- Let `t` be a query other than encryption. Then running `gcmTupleImplReject a t` from any
state gives the same result (response and next state) for every tuple `a`. -/
theorem gcmTupleImplReject_indep :
    ∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)).Domain)
      (s : Option (BitVec L × BitVec 128)) (a₁ a₂ : BitVec 128 × BitVec 128 × BitVec L),
      (fun t => t matches OEncrypt _) t = false →
      (gcmTupleImplReject a₁ t).run s = (gcmTupleImplReject a₂ t).run s := by
  intro t s a₁ a₂ h
  rcases t with (n | am) | ac
  · -- OUnif: the lifted unif handler never mentions the tuple.
    rfl
  · -- OEncrypt: the hit predicate holds, contradicting `h`.
    simp at h
  · -- ODecrypt: `pure none` (behind the challenge guard) never mentions the tuple.
    rfl

/-- Game 3: decryption always rejects, and the tuple is sampled at the encryption query. -/
noncomputable def game3 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool :=
  (simulateQ (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _))
    adv).run' (none, none)

/-- Oracles drawing the challenge ciphertext uniformly and rejecting every decryption
(`game4`). The tuple argument is ignored; it is there only so that `game4` can be stated
through `consumeLazy` like `game3`. -/
def gcmRandRejectImpl (_a : BitVec 128 × BitVec 128 × BitVec L) :
    QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128)) ProbComp) :=
  gcmGameSkeleton (spec := unifSpec)
    (fun _ _ => liftM ($ᵗ (BitVec L × BitVec 128) : ProbComp (BitVec L × BitVec 128)))
    (fun _ _ => pure none)
    (oracleUnif (BitVec L × BitVec 128))

/-- Game 4: `game3` with the challenge ciphertext drawn uniformly instead of computed from
the tuple. -/
noncomputable def game4 (_prp : PRPScheme K (BitVec 128)) (L : ℕ) (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool :=
  (simulateQ (consumeLazy gcmRandRejectImpl (fun t => t matches OEncrypt _))
    adv).run' (none, none)

end Games

/-! ## Instrumented pair: `game3♭` / `game2♭`

`game2` and `game3` differ only in what a decryption query returns when the tag verifies. Two
games that behave identically until a flag is raised differ by at most the probability of the
flag, so both are restated with a `forged` flag set whenever a tag verifies, and the
authenticity hop bounds their distance by the probability of that flag. The Lean names
`game2Flat`/`game3Flat` spell `game2♭`/`game3♭`.

The flag update reads the tuple at decryption queries, so these variants cannot use
`consumeLazy`; the tuple is sampled up front, and the projection lemmas below recover
`game2`/`game3`. -/

section Instrumented

variable {K : Type} {L : ℕ}

/-- `gcmTupleImpl` (`b = true`) or `gcmTupleImplReject` (`b = false`) with a `forged` flag
added to the state, set and never cleared once a decryption query's tag verifies. It is the
generic Wegman–Carter handler `wcInstImpl`
(`ToVCVio/CryptoFoundations/WegmanCarter/Defs.lean`) at
`hash := fun H p => ghash H (gcmEncode p.1 p.2)`, `enc := id` and `(· ^^^ ks)` as both pad and
unpad; the encoding sits inside `hash` rather than `enc` because GHASH on raw block lists is not
AXU (`Axu.lean`). The response depends on `b` only in the branch that sets the flag, so the two
variants agree on every query that leaves the flag clear. -/
def gcmInstImpl (a : BitVec 128 × BitVec 128 × BitVec L) (b : Bool) :
    QueryImpl (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128))
      (StateT (Option (BitVec L × BitVec 128) × Bool) ProbComp) :=
  wcInstImpl (fun (H : BitVec 128) (p : SupportedAAD × BitVec L) => ghash H (gcmEncode p.1 p.2))
    id a.1 a.2.1 (· ^^^ a.2.2) (· ^^^ a.2.2) b

/-- Game 3♭: `game3` with the forgery flag, tuple sampled up front. -/
def game3Flat (_prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let a ← ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
  (simulateQ (gcmInstImpl a false) adv).run' (none, false)

/-- Game 2♭: `game2` with the forgery flag, tuple sampled up front. -/
def game2Flat (_prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    ProbComp Bool := do
  let a ← ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
  (simulateQ (gcmInstImpl a true) adv).run' (none, false)

/-! ### Projection lemmas: the flag is write-only, so erasing it recovers the plain games. -/

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
    simp [gcmInstImpl, wcInstImpl, gcmTupleImpl, gcmGameSkeleton, oracleUnif, unifLiftStateT,
      StateT.run_monadLift, Prod.map, Functor.map_map]
  · -- OEncrypt: identical one-shot bodies; the flag is written back unchanged.
    cases challenge <;>
      simp [gcmInstImpl, wcInstImpl, gcmTupleImpl, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map]
  · -- ODecrypt: guard split, then `ok` split; live return matches `gcmTupleImpl`'s
    -- verification body and the flag write is erased by the projection.
    by_cases hguard : challenge = some e
    all_goals
      simp [gcmInstImpl, wcInstImpl, gcmTupleImpl, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure,
        Prod.map, ← apply_ite, beq_iff_eq, hguard]

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
    simp [gcmInstImpl, wcInstImpl, gcmTupleImplReject, gcmGameSkeleton, oracleUnif, unifLiftStateT,
      StateT.run_monadLift, Prod.map, Functor.map_map]
  · -- OEncrypt: identical one-shot bodies; the flag is written back unchanged.
    cases challenge <;>
      simp [gcmInstImpl, wcInstImpl, gcmTupleImplReject, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map]
  · -- ODecrypt: both `ok` branches return `none`; the flag write is erased by the
    -- projection, matching the unconditional `pure none`.
    by_cases hguard : challenge = some e
    all_goals
      simp [gcmInstImpl, wcInstImpl, gcmTupleImplReject, gcmGameSkeleton, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure,
        Prod.map, beq_iff_eq, hguard]

theorem game2Flat_eq_game2 (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    evalDist (game2Flat prp L hL adv) = evalDist (game2 prp L hL adv) := by
  unfold game2Flat game2
  rw [bind_congr fun a =>
    simulateQ_gcmInstImpl_true_run'_eq_gcmTupleImpl a adv none false]
  exact probOutput_simulateQ_greedyLazy_run'_eq gcmTupleImpl adv none

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

/-! ## Endpoints: `game0` is the real experiment, `game4` the random one -/

section Endpoints

variable {K : Type}

/-- `game0` outputs `true` with the same probability as the real ACD19 experiment, the one with
challenge bit `false`. -/
theorem game0_eq_real (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    Pr[= true | game0 prp iv L hL adv] =
      Pr[= true | AEADScheme.securityExpFixedBit (gcmOneTimeAEAD prp iv L hL) adv false] := by
  -- Unfold only the keygen projection (keep `aeadSecurityImpl` folded to match the RHS).
  have hkg : (gcmOneTimeAEAD prp iv L hL).keygen = prp.keygen := rfl
  unfold game0 AEADScheme.securityExpFixedBit
  rw [hkg]
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Both sides start with `prp.keygen`; descend under the single key bind.
  refine probOutput_bind_congr' prp.keygen true (fun k => ?_)
  -- Inner per-key equality: game0's skeleton impl projects onto
  -- `aeadSecurityImpl … false k` with `proj = id` (state `Option C` on both sides).
  refine congrArg (fun o => Pr[= true | o]) ?_
  refine run'_simulateQ_eq_of_query_map_eq _
    (AEADScheme.aeadSecurityImpl (gcmOneTimeAEAD prp iv L hL) false k) id ?hproj adv none
  case hproj =>
    intro t s
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
    · -- OUnif: both handlers are the lifted uniform oracle, state threaded unchanged.
      simp [gcmGameSkeleton, AEADScheme.aeadSecurityImpl, AEADScheme.oracleUnif,
        unifLiftStateT, QueryImpl.add_apply_inl,
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

/-- `game4` has the same output distribution as running `adv` against
`gcmRandRejectImpl default`, without sampling a tuple: `gcmRandRejectImpl` ignores the tuple. -/
theorem game4_eq_plain (prp : PRPScheme K (BitVec 128)) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    evalDist (game4 prp L hL adv) =
      evalDist ((simulateQ (gcmRandRejectImpl (L := L) default) adv).run' none) := by
  unfold game4
  rw [← probOutput_simulateQ_consumeLazy_run'_eq gcmRandRejectImpl
        (fun t => t matches OEncrypt _) (fun _ _ _ _ _ => rfl) adv none]
  exact DeferredSampling.evalDist_bind_const_neverFails
    ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
    (probFailure_uniformSample _)
    ((simulateQ (gcmRandRejectImpl (L := L) default) adv).run' none)

/-- `game4` outputs `true` with the same probability as the ideal ACD19 experiment, the one with
challenge bit `true`. The key is unused on the ideal side, and no hypothesis on `prp.keygen` is
needed because every `ProbComp` is failure-free. -/
theorem game4_eq_rand (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    Pr[= true | game4 prp L hL adv] =
      Pr[= true | AEADScheme.securityExpFixedBit (gcmOneTimeAEAD prp iv L hL) adv true] := by
  -- (1)-(2) Unconsume and kill the dead tuple sample: both steps are `game4_eq_plain`.
  rw [probOutput_eq_of_evalDist_eq (game4_eq_plain prp L hL adv) true]
  -- (3) RHS: the endpoint's keygen is dead on the random side; fold the tail to `.run'`.
  have hkg : (gcmOneTimeAEAD prp iv L hL).keygen = prp.keygen := rfl
  unfold AEADScheme.securityExpFixedBit
  rw [hkg]
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- (4) Kill it with losslessness; the per-key body is constant (= the LHS value by
  -- the `id`-projection).
  rw [probOutput_bind_of_const prp.keygen
      (my := fun k => (simulateQ (AEADScheme.aeadSecurityImpl (gcmOneTimeAEAD prp iv L hL)
        true k) adv).run' none)
      (fun k _ => congrArg (fun o => Pr[= true | o])
        (run'_simulateQ_eq_of_query_map_eq _
          (AEADScheme.aeadSecurityImpl (gcmOneTimeAEAD prp iv L hL) true k)
          id ?_ adv none).symm)]
  · -- `prp.keygen` is lossless, so the `(1 - Pr[⊥]) ·` factor is `1`; `rfl` pins `impl₁`.
    rw [NeverFail.probFailure_eq_zero, tsub_zero, one_mul]
  · -- Per-query `id`-projection (`impl₁` is the eager `gcmRandRejectImpl`).
    intro t s
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
    · -- OUnif: both handlers are the lifted uniform oracle, state threaded unchanged.
      simp [gcmRandRejectImpl, gcmGameSkeleton, AEADScheme.aeadSecurityImpl,
        AEADScheme.oracleUnif, unifLiftStateT, QueryImpl.add_apply_inl,
        StateT.run_monadLift, Functor.map_map]
    · -- OEncrypt: both draw the challenge uniformly from `$ᵗ (BitVec L × BitVec 128)`
      -- (the `b = true` branch of `oracleEncrypt` is the same joint product sample).
      cases s <;>
        simp [gcmRandRejectImpl, gcmGameSkeleton, AEADScheme.aeadSecurityImpl,
          AEADScheme.oracleEncrypt, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, map_pure]
    · -- ODecrypt: both sides always reject (`b = true` short-circuits `oracleDecrypt`).
      simp [gcmRandRejectImpl, gcmGameSkeleton, AEADScheme.aeadSecurityImpl,
        AEADScheme.oracleDecrypt, QueryImpl.add_apply_inr]

end Endpoints

end GCM
