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

end GCM
