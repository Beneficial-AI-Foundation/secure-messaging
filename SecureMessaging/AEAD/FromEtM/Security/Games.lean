/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Construction
import ToVCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Relational.SimulateQ
import SecureMessaging.AEAD.FromEtM.Security.RandomOracleForgery
import SecureMessaging.AEAD.FromEtM.Security.DiscardQuerySimulate
import SecureMessaging.AEAD.FromEtM.Security.SimulateQForward
import ToVCVio.OracleComp.SimSemantics.StateT.PreservesInv
import SecureMessaging.Common.UnifLift

/-!
# Encrypt-then-MAC — game and reduction definitions

The OracleSpec-polymorphic game skeleton, its `unifSpec` oracle handler, the four games
`game0`–`game3` (instantiated at `spec = unifSpec`), and the PRF / IND$-CPA reductions
(`prfReduction`, `encReduction`). Shared by every game-hop file.
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

/-! ## Type abbreviations -/

/-- Random oracle cache for the tag function `(AD × C_e) → T`. -/
-- The `DecidableEq (AD × C_e)` instance is unused in the underlying `QueryCache`
-- but kept to align with `EtmGameState` and the games built on this cache.
@[nolint unusedArguments]
abbrev TagCache (AD C_e T : Type) [DecidableEq (AD × C_e)] [SampleableType T] :=
  ((AD × C_e) →ₒ T).QueryCache

/-- Game state for the EtM security games: the challenge ciphertext (if
encryption was called) paired with the random oracle cache. -/
abbrev EtmGameState (AD C_e T : Type) [DecidableEq (AD × C_e)] [SampleableType T] :=
  Option (C_e × T) × TagCache AD C_e T

/-! ## Game skeleton -/

section Skeleton

/-- Parameterized EtM security game skeleton, polymorphic over the oracle spec.

Games instantiate with `spec := unifSpec` (= ProbComp).
Reductions instantiate with `spec := PRFOracleSpec` etc., forwarding
oracle queries through the parameters.

Additional setup (e.g., sampling a PRF key) happens OUTSIDE the skeleton
via closures captured by the oracle parameters.

The `unifImpl` parameter forwards the adversary's `unifSpec` queries to
`OracleComp spec`. For games (`spec = unifSpec`), this is the identity lift.
For reductions, this lifts through the SubSpec coercion.

NRS14 Lemma 3 + Appendix A.2: game-hopping proof structure for A5. -/
noncomputable def etmGameSkeleton
    {ι : Type} {spec : OracleSpec ι}
    (keygen_e : OracleComp spec K_e)
    (decrypt_c : K_e → C_e → Option M)
    (initCache : TagCache AD C_e T)
    (encryptMsg : K_e → M → StateT (TagCache AD C_e T) (OracleComp spec) C_e)
    (computeTag : AD × C_e → StateT (TagCache AD C_e T) (OracleComp spec) T)
    (verifyTag : AD × C_e → T → StateT (TagCache AD C_e T) (OracleComp spec) Bool)
    (unifImpl : QueryImpl unifSpec
        (StateT (EtmGameState AD C_e T) (OracleComp spec)))
    (adversary : OneTimeCCAAdversary AD M (C_e × T))
    : OracleComp spec Bool := do
  let ke ← keygen_e
  let encImpl : QueryImpl (AD × M →ₒ Option (C_e × T))
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    fun (ad, m) => do
      let (challenge, qc) ← get
      match challenge with
      | some _ => pure none
      | none => do
        let (c, qc1) ← (encryptMsg ke m).run qc
        let (t, qc2) ← (computeTag (ad, c)).run qc1
        set (some (c, t), qc2)
        return some (c, t)
  let decImpl : QueryImpl (AD × (C_e × T) →ₒ Option M)
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    fun (ad, (c, t)) => do
      let (challenge, qc) ← get
      if challenge == some (c, t) then pure none
      else do
        let (ok, qc') ← (verifyTag (ad, c) t).run qc
        set (challenge, qc')
        if ok then pure (decrypt_c ke c) else pure none
  let impl := unifImpl + encImpl + decImpl
  let (b', _) ← (simulateQ impl adversary).run (none, initCache)
  return b'

end Skeleton

/-! ## Uniform oracle implementation (for games with spec = unifSpec) -/

/-- Forward `unifSpec` queries through `ProbComp` to `StateT GameState ProbComp`. -/
noncomputable def gameUnifImpl :
    QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) ProbComp) :=
  unifLiftStateT (EtmGameState AD C_e T) unifSpec

/-! ## Game instantiations (spec = unifSpec = ProbComp)

Each game is a skeleton instantiation with `spec := unifSpec`. All use state
type `TagCache` (empty cache `∅` when the random oracle is not needed).
Most hops change exactly one conceptual component. The game2 → game3 hop
changes both `encryptMsg` and `computeTag`, but the `computeTag` change
is distributional equality (the cache is written but never read once verify
is disabled, and a one-time fresh RO query is uniform). -/

/-- Game 0: real EtM. PRF key sampled outside skeleton, closed over in tag operations.

NRS14 Lemma 3: starting game (real nAE experiment). -/
noncomputable def game0
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) : ProbComp Bool := do
  let km ← prf.keygen
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun (ad, c) => pure (prf.eval km (ad, c)))
    (fun (ad, c) t => pure (t == prf.eval km (ad, c)))
    gameUnifImpl
    adv

/-- Game 1: PRF replaced with lazy random oracle.

NRS14 Lemma 3, eq. (4): replace F^tag with random ρ.
Deviation: single encryption query (q_e = 1). -/
noncomputable def game1
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun q => ((AD × C_e) →ₒ T).randomOracle q)
    (fun (ad, c) t => do
      let t' ← ((AD × C_e) →ₒ T).randomOracle (ad, c)
      pure (t == t'))
    gameUnifImpl
    adv

/-- Game 2: decrypt always rejects. Real encryption, random oracle tag.

NRS14 Appendix A.2: disable decryption by bounding forgery probability.
Each decrypt query at a fresh random oracle point verifies with probability
`1/|T|`; union bound over `q_d` queries gives `q_d/|T|`. -/
noncomputable def game2
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun q => ((AD × C_e) →ₒ T).randomOracle q)
    (fun _ _ => pure false)
    gameUnifImpl
    adv

/-- Game 2′: like `game2` (decrypt always rejects), but `verifyTag` first makes the
random-oracle query and *then* rejects unconditionally. This keeps the random-oracle
cache evolving identically to `game1` (needed for the identical-until-bad step), while the
unconditional rejection means the verify query reveals nothing — so `game2′` and `game2`
are equal as distributions (`game2'_eq_game2`, via the discarded-query brick).

NRS14 Appendix A.2: the intermediate game used to couple `game1` and `game2`. -/
noncomputable def game2'
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun q => ((AD × C_e) →ₒ T).randomOracle q)
    (fun (ad, c) _ => do
      let _ ← ((AD × C_e) →ₒ T).randomOracle (ad, c)
      pure false)
    gameUnifImpl
    adv

/-- Game 3: decrypt always rejects (random encrypt, random tag, no decryption).
Cache unused but present for type uniformity.

NRS14 Figure 4, right column: `$` oracle (random bits) + `⊥` oracle
(always reject). This is the ideal nAE experiment. -/
noncomputable def game3
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun _ _ => liftM ($ᵗ C_e : ProbComp C_e))
    (fun _ => liftM ($ᵗ T : ProbComp T))
    (fun _ _ => pure false)
    gameUnifImpl
    adv

/-! ## Reduction instantiations

Reductions are skeleton instantiations with different `spec`, so they can
serve as adversaries for the underlying primitive's security game.

- `prfReduction`: game0 → game1 hop. Instantiates the skeleton with
  `spec = PRFOracleSpec`, forwarding tag queries to the external oracle.
- `encReduction`: game2 → game3 hop. Instantiates the skeleton with
  `spec = indCPASpec`, forwarding encryption to its oracle, sampling tags
  uniformly, and always rejecting decrypt (since `verifyTag = pure false`
  in both game2 and game3, no `ke` or `se.decrypt` access is needed).

Both reduction bodies are skeleton instantiations that forward the relevant
oracle queries (tag queries for `prfReduction`, encryption queries for
`encReduction`) to the external primitive oracle; see each definition below. -/

/-- PRF reduction: skeleton with `spec = PRFOracleSpec`, tag queries forwarded
to the external oracle (which is either the real PRF or a random function).

NRS14 Lemma 3, eq. (4): reduction B(A) that distinguishes F^tag from ρ.

The body is a skeleton instantiation where `computeTag` and `verifyTag` forward
their queries to `OracleSpec.query (Sum.inr (ad, c))` — the PRF/random oracle
provided by the experiment. -/
noncomputable def prfReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    : PRFAdversary (AD × C_e) T :=
  let spec := unifSpec + ((AD × C_e) →ₒ T)
  let unifImpl : QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    unifLiftStateT (EtmGameState AD C_e T) spec
  etmGameSkeleton (spec := spec)
    (OracleComp.liftComp se.keygen spec)
    se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun q => do
      let t ← liftM (liftM (spec.query (Sum.inr q)) :
        OracleComp spec T)
      pure t)
    (fun (ad, c) t => do
      let t' ← liftM (liftM (spec.query (Sum.inr (ad, c))) :
        OracleComp spec T)
      pure (t == t'))
    unifImpl
    adv

/-- IND$-CPA reduction: skeleton with `spec = indCPASpec`, encryption queries
forwarded to the external oracle (which is either real encryption or random).

NRS14 Lemma 3, privacy reduction D₁(A).

The reduction forwards encryption to `OracleSpec.query (Sum.inr m)` — the
real/random encryption oracle — samples tags uniformly, and always rejects
decrypt (since `verifyTag = pure false` in both game2 and game3). No access
to `ke` or `se.decrypt` is needed.

Because the skeleton's key slot is never observed (`encryptMsg` ignores `_ke`
and `verifyTag = pure false` makes `decrypt_c` unreachable), it is instantiated
with the trivial `pure default` rather than `se.keygen`. This keeps exactly one
`se.keygen` sample per side in the `game2_game3_le_enc` equalities (the IND$-CPA
experiment's own key), so the dead bind cancels structurally without needing
`se.keygen` to be lossless. `decrypt_c` is `fun _ _ => none` for the same reason
(the branch is unreachable), which also avoids decrypting under a key distinct
from the oracle's. Requires `[Inhabited K_e]` (every key space is inhabited). -/
-- `_se` is unused in the body but kept to pin the key type `K_e` and to align
-- the reduction's signature with `prfReduction` and the security theorems.
@[nolint unusedArguments]
noncomputable def encReduction [Inhabited K_e]
    (_se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    : DetSEAlg.IndCPAAdversary M C_e :=
  let spec := unifSpec + (M →ₒ Option C_e)
  let unifImpl : QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    unifLiftStateT (EtmGameState AD C_e T) spec
  etmGameSkeleton (spec := spec)
    (pure default : OracleComp spec K_e)
    (fun _ _ => none) ∅
    (fun _ke m => do
      let oc ← liftM (liftM (spec.query (Sum.inr m)) :
        OracleComp spec (Option C_e))
      match oc with
      | some c => pure c
      -- Unreachable: the skeleton gates encryption to fire at most once, so the
      -- IND$-CPA oracle (whose `none` means "already queried") is never `none`
      -- here. If the skeleton is ever changed to allow multiple encrypt queries,
      -- this dead branch must be revisited rather than returning `default`.
      | none => pure default)
    (fun _ => liftM ($ᵗ T : ProbComp T))
    (fun _ _ => pure false)
    unifImpl
    adv
