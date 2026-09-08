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

variable {K : Type}

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

end Games

end GCM
