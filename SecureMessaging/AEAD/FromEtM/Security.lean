/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.AEAD.FromEtM.Construction
import SecureMessaging.ToVCVio.SampleableTypeProd
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Relational.SimulateQ
import SecureMessaging.ToVCVio.RandomOracleForgery
import SecureMessaging.ToVCVio.IdenticalUntilBad
import SecureMessaging.ToVCVio.DiscardQuerySimulate
import SecureMessaging.ToVCVio.ProbEventCoupling
import SecureMessaging.ToVCVio.TVDistConvexity
import SecureMessaging.ToVCVio.SimulateQForward
import SecureMessaging.ToVCVio.StateTInvariant
import SecureMessaging.ToVCVio.UnifLift

/-!
# Encrypt-then-MAC — Security

Security theorem for the EtM construction: the one-time IND-CCA advantage of
`etmAEAD se prf` is bounded by the PRF advantage of `prf`, the IND$-CPA
advantage of `se`, and `q_d/|T|` (tag-guessing probability per decryption
query, where `q_d` upper-bounds the adversary's decryption queries).

## Paper References

Our construction adapts **scheme A5** (= A2.100_111) from NRS14 Figure 2.
The security proof adapts **Theorem 1** (for A5), with:
- Concrete bound from **Figure 9**: `Adv^nAE ≤ Adv^prf + Adv^ivE + q_d/2^τ`
- Proof structure from **Lemma 3** (common opening) + **Appendix A.2** (auth bound)

## Structure

The proof uses an **OracleSpec-polymorphic game skeleton** so that games
(instantiated with `spec = unifSpec` = `ProbComp`) and reductions
(instantiated with `spec = PRFOracleSpec` or the IND$-CPA spec) are direct
instantiations of the same definition. The hop proofs use `simulateQ`
compositionality.

Note: intermediate games cannot be `AEADScheme` instances because game hops
change internal components (e.g., replacing PRF with random oracle) while
preserving the oracle interface.

## NRS14 Correspondence

| Lean definition | NRS14 reference |
|---|---|
| `etmAEAD` | Figure 2, scheme A5, adapted: no nonce, one-time keys |
| `DetSEAlg` / `distAdvantage` | Section 2, ivE scheme / `Adv^ivE` (one query) |
| `PRFScheme` / `prfAdvantage` | Section 2, function family F / `Adv^prf` |
| `decryptQueryBound` / `q_d` | `q_d` in Appendix A.2; `IsQueryBoundP` on decrypt index |
| `game0` | Lemma 3 starting game (Figure 4 left: `Enc` + `Dec`) |
| `game1` | Lemma 3 eq. (4): replace F^tag with random ρ |
| `game2` | Appendix A.2: disable decryption (forgery bound) |
| `game3` | Figure 4 right column: `$` + `⊥` oracles |
| `game0_game1_le_prf` | Lemma 3 eq. (4): PRF hop, cost `Adv^prf` |
| `game1_game2_le_auth` | Appendix A.2, A5 Case 1: auth bound `q_d/2^τ` (see note) |
| `game2_game3_le_enc` | Lemma 3, privacy reduction D₁: cost `Adv^ivE` |
| `etmAEAD_security` | Theorem 1 for A5; Figure 9 bound |
| `prfReduction` | Lemma 3: adversary B(A) |
| `encReduction` | Lemma 3: privacy reduction D₁(A) |

Note on `game1_game2_le_auth`: the `q_d` factor is proved *directly*, by
per-distinct-point lazy-sampling accounting (`probForge_le_queryBound_div_card`),
**not** via NRS14's Lemma-2 single-decryption-query hybrid.
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
    (adversary : OneTime_CCA_Adversary AD M (C_e × T))
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
  ToVCVio.unifLiftStateT (EtmGameState AD C_e T) unifSpec

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
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool := do
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
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool :=
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
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool :=
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
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool :=
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
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool :=
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
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    : PRFAdversary (AD × C_e) T :=
  let spec := unifSpec + ((AD × C_e) →ₒ T)
  let unifImpl : QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    ToVCVio.unifLiftStateT (EtmGameState AD C_e T) spec
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
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    : DetSEAlg.IndCPA_Adversary M C_e :=
  let spec := unifSpec + (M →ₒ Option C_e)
  let unifImpl : QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    ToVCVio.unifLiftStateT (EtmGameState AD C_e T) spec
  etmGameSkeleton (spec := spec)
    (pure default : OracleComp spec K_e)
    (fun _ _ => none) ∅
    (fun _ke m => do
      let oc ← liftM (liftM (spec.query (Sum.inr m)) :
        OracleComp spec (Option C_e))
      match oc with
      | some c => pure c
      | none => pure default)
    (fun _ => liftM ($ᵗ T : ProbComp T))
    (fun _ _ => pure false)
    unifImpl
    adv

/-! ## Game-hop lemma signatures -/

omit [Inhabited C_e] [Inhabited T] in
/-- Game 0 equals the real AEAD experiment.
NRS14 Lemma 3: starting game = real nAE experiment.

Proof strategy:
1. Swap `km`/`ke` sampling order using `probEvent_bind_bind_swap`
   (independent `ProbComp` samples).
2. Show the skeleton oracle impl with state `(Option (C_e × T), TagCache)` projected via
   `Prod.fst` equals `aeadSecurityImpl (etmAEAD se prf) false (ke, km)` with state
   `Option (C_e × T)`. This holds because `computeTag = pure (prf.eval km q)` and
   `verifyTag = pure (t == prf.eval km (ad, c))` don't modify the `TagCache`.
3. Apply `run'_simulateQ_eq_of_query_map_eq` to project away the invariant `TagCache = ∅`. -/
theorem game0_eq_real
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    Pr[= true | game0 se prf adv] =
      Pr[= true | AEADScheme.securityExpFixedBit (etmAEAD se prf) adv false] := by
  -- Tail helper: `(simulateQ impl adv).run s >>= take-fst = (simulateQ impl adv).run' s`.
  -- Unfold only `etmAEAD.keygen` (keep `aeadSecurityImpl` folded to match the RHS
  -- `securityExpFixedBit` impl).
  have hkg : (etmAEAD se prf).keygen
      = (se.keygen >>= fun ke => prf.keygen >>= fun km =>
          (pure (ke, km) : ProbComp (K_e × K_m))) := rfl
  unfold game0 etmGameSkeleton AEADScheme.securityExpFixedBit
  rw [hkg]
  simp only [bind_assoc, pure_bind]
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Swap the two independent key samplers so both sides start with `se.keygen`.
  simp only [← probEvent_eq_eq_probOutput]
  rw [probEvent_bind_bind_swap prf.keygen se.keygen]
  simp only [probEvent_eq_eq_probOutput]
  -- Descend under the two key binds; reduce to the per-key inner equality.
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  refine probOutput_bind_congr' prf.keygen true (fun km => ?_)
  -- Inner: project away the invariant `TagCache` via `Prod.fst`.
  rw [run'_simulateQ_eq_of_query_map_eq _
        (AEADScheme.aeadSecurityImpl (etmAEAD se prf) false (ke, km))
        Prod.fst ?hproj adv (none, ∅)]
  case hproj =>
    intro t s
    obtain ⟨ch, qc⟩ := s
    rcases t with (n | am) | ac
    · -- uniform-sampling oracle: state threaded unchanged on both sides
      simp [AEADScheme.aeadSecurityImpl, gameUnifImpl, AEADScheme.oracleUnif,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, Prod.map]
    · -- encryption oracle
      obtain ⟨ad, m⟩ := am
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleEncrypt, etmAEAD,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          map_pure, Prod.map]
    · -- decryption oracle
      obtain ⟨ad, c, t⟩ := ac
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleDecrypt, etmAEAD,
          QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure] <;>
        split_ifs <;>
        simp [StateT.run_pure, map_pure, Prod.map]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Game 0 → real PRF experiment: the `game0` distribution equals the real PRF experiment run on
`prfReduction`. The "real" half of NRS14 Lemma 3, eq. (4). -/
theorem game0_eq_prfRealExp
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    Pr[= true | game0 se prf adv] =
      Pr[= true | prf.prfRealExp (prfReduction se adv)] := by
  -- RHS: unfold the reduction + experiment, fold the inner skeleton run to `run'`,
  -- collapse the nested `simulateQ` via `mapStateTBase`, forward `liftComp se.keygen`
  -- (the upstream `simulateQ_prfRealQueryImpl_liftComp` is the `unifSpec`-transparency fact).
  unfold PRFScheme.prfRealExp prfReduction etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq, simulateQ_bind,
    QueryImpl.simulateQ_mapStateTBase_run', PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
  -- LHS: unfold game0 + skeleton, fold its run to `run'`.
  unfold game0 etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Both sides: `prf.keygen` then `se.keygen`, same order; descend both.
  refine probOutput_bind_congr' prf.keygen true (fun k => ?_)
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  -- Per-key inner equality: game0's oracle impl equals the mapped reduction impl
  -- (`computeTag`/`verifyTag` forward to the real PRF oracle = `pure (prf.eval k ·)`).
  -- Clean projection (proj = id): caches stay `∅` on both sides, no invariant needed.
  refine congrArg (fun o => Pr[= true | o]) ?_
  refine run'_simulateQ_eq_of_query_map_eq _ _ id ?hproj adv (none, ∅)
  case hproj =>
    intro t s
    obtain ⟨ch, qc⟩ := s
    rcases t with (n | am) | ac
    · -- uniform-sampling oracle: forwarded through both impls unchanged
      have hq : simulateQ (prf.prfRealQueryImpl k)
          (liftM (OracleSpec.query n) :
            OracleComp (unifSpec + ((AD × C_e) →ₒ T)) (unifSpec.Range n))
          = (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
        PRFScheme.simulateQ_prfRealQueryImpl_liftComp prf k
          (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
      simp [gameUnifImpl, QueryImpl.mapStateTBase, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, hq, StateT.run_monadLift,
        Functor.map_map]
    · -- encryption oracle: `se.encrypt ke m` + tag forwarded to `pure (prf.eval k (ad,c))`
      obtain ⟨ad, m⟩ := am
      cases ch <;>
        simp [QueryImpl.mapStateTBase,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          PRFScheme.prfRealQueryImpl, map_pure]
    · -- decryption oracle: verify forwards to `pure (prf.eval k (ad,c))`, compares tag
      obtain ⟨ad, c, t⟩ := ac
      cases ch <;>
        simp [QueryImpl.mapStateTBase, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          simulateQ_bind, PRFScheme.prfRealQueryImpl] <;>
        split_ifs <;>
        simp [*, StateT.run_pure, map_pure, simulateQ_bind,
          simulateQ_pure]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Game 1 → ideal PRF experiment: the `game1` distribution equals the ideal PRF experiment run
on `prfReduction`. The "ideal" half of NRS14 Lemma 3, eq. (4); this is the heavier of the two
halves, since it must relocate the outer lazy-RO cache into the (always-`∅`) inner `TagCache`. -/
theorem game1_eq_prfIdealExp
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    Pr[= true | game1 se adv] =
      Pr[= true | PRFScheme.prfIdealExp (prfReduction se adv)] := by
  -- RHS: collapse the nested `simulateQ`, forward keygen (the upstream
  -- `simulateQ_prfIdealQueryImpl_liftComp` is the cache-threading `unifSpec`-transparency fact),
  -- then push the outer `.run' ∅` through the `liftM se.keygen` bind so both sides start with
  -- `se.keygen` (the cache threads through unchanged).
  unfold PRFScheme.prfIdealExp prfReduction etmGameSkeleton
  -- Targeted push of `run'` through the `liftM se.keygen` bind. Stated as a local `have` (a
  -- one-line `simp` fact) rather than via the general `StateT.run'_bind'`, which unfolds *every*
  -- `run'`-of-bind and would dismantle the per-key `simulateQ … .run'` recovered below.
  have hpush : ∀ {β : Type} (G : K_e → StateT (TagCache AD C_e T) ProbComp β)
      (s : TagCache AD C_e T),
      ((liftM se.keygen : StateT (TagCache AD C_e T) ProbComp K_e) >>= G).run' s
        = se.keygen >>= fun a => (G a).run' s :=
    fun G s => by
      simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, bind_map_left, map_bind]
  simp only [bind_pure_comp, ← StateT.run'_eq, simulateQ_bind,
    QueryImpl.simulateQ_mapStateTBase_run', PRFScheme.simulateQ_prfIdealQueryImpl_liftComp,
    hpush]
  -- LHS: game1.
  unfold game1 etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- A forwarded function query `Sum.inr q` is answered by the lazy random oracle at `q`. This is
  -- exactly the upstream `simulateQ_prfIdealQueryImpl_inr`; the local restatement just pins the
  -- ambient spec annotation so it matches syntactically in the `simp only` decrypt branches below.
  have hroI : ∀ (q : AD × C_e),
      simulateQ (PRFScheme.prfIdealQueryImpl (D := AD × C_e) (R := T))
        (liftM (OracleSpec.query (Sum.inr q) :
            OracleQuery (unifSpec + ((AD × C_e) →ₒ T)) T) :
          OracleComp (unifSpec + ((AD × C_e) →ₒ T)) T)
        = (((AD × C_e) →ₒ T).randomOracle q :
            StateT ((AD × C_e →ₒ T).QueryCache) ProbComp T) :=
    fun q => PRFScheme.simulateQ_prfIdealQueryImpl_inr q
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  refine congrArg (fun o => Pr[= true | o]) ?_
  -- Flatten the nested `StateT EtmGameState (StateT QueryCache ProbComp)` into a single
  -- `StateT (EtmGameState × QueryCache) ProbComp`, then project the joint state back to
  -- game1's `EtmGameState`, RELOCATING the outer RO `QueryCache` into the (always-`∅`)
  -- inner `TagCache` slot, under the invariant "inner cache stays `∅`".
  conv_rhs => rw [StateT.run'_eq _ ((none, ∅) : EtmGameState AD C_e T)]
  rw [← simulateQ_flattenStateT_run']
  refine (run'_simulateQ_eq_of_query_map_eq_inv' _ _
      (fun s : EtmGameState AD C_e T × TagCache AD C_e T => s.1.2 = (∅ : TagCache AD C_e T))
      (fun s : EtmGameState AD C_e T × TagCache AD C_e T => (s.1.1, s.2))
      ?hinv ?hproj adv ((none, ∅), ∅) ?hs).symm
  case hs => rfl
  case hinv =>
    -- Inner-cache invariant: the reduction forwards every tag query to the *external* RO
    -- (the outer `QueryCache`) and never writes the inner `TagCache`, so the inner cache
    -- stays `∅` on every execution path of every oracle. With the composition-level Issue-4
    -- bricks (`ToVCVio.flattenStateT_mapStateTBase_run_preserves_inv`) this reduces to a
    -- per-query invariant of the *reduction's own oracle body alone* — no peeling of
    -- `support` through `mapStateTBase`/`flattenStateT`/the outer `simulateQ`.
    -- `inner` is the `prfReduction` skeleton oracle handler (state `EtmGameState`), `outer`
    -- is `prfIdealQueryImpl` (state `QueryCache`); the invariant lives on the inner TagCache.
    intro t s hs
    refine ToVCVio.flattenStateT_mapStateTBase_run_preserves_inv _ _
      (fun g : EtmGameState AD C_e T => g.2 = (∅ : TagCache AD C_e T)) ?_ t s hs
    -- Per-query inner invariant: each reduction oracle threads the inner TagCache unchanged
    -- (unif forwards via the lifted `unifSpec`; encrypt/decrypt forward their tag queries to
    -- the external oracle without writing the inner cache).
    clear hs s t
    intro t s hs y hy
    obtain ⟨ch, ic⟩ := s
    simp only at hs
    subst hs
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
    · simp only [add_apply_inl, StateT.run_pure, liftM_pure, bind_pure, StateT.run_monadLift,
        monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
        beq_iff_eq, StateT.run_map, Functor.map_map, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, support_map] at hy
      obtain ⟨a, _, rfl⟩ := hy; rfl
    · cases ch <;>
        simp only [add_apply_inl, add_apply_inr, StateT.run_pure, liftM_pure, bind_pure,
          StateT.run_monadLift, monadLift_self, bind_pure_comp, liftM_map, bind_map_left,
          pure_bind, Prod.mk.eta, beq_iff_eq, StateT.run_map, Functor.map_map,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
          StateT.run_set, map_pure, support_map, support_liftM, OracleQuery.input_query,
          OracleQuery.cont_query, Set.range_id, Set.image_univ, support_pure] at hy
      · obtain ⟨a, _, rfl⟩ := hy; rfl
      · subst hy; rfl
    · -- decryption oracle: `verifyTag` forwards to the external oracle and threads the inner
      -- cache unchanged; the verify `if … then pure … else pure …` keeps the cache `∅`.
      cases ch with
      | none =>
        simp only [add_apply_inr, StateT.run_pure, liftM_pure, bind_pure, StateT.run_monadLift,
          monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
          beq_iff_eq, StateT.run_map, Functor.map_map, ← apply_ite, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, reduceCtorEq, ↓reduceIte, StateT.run_set, map_pure,
          support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
          Set.range_id, Set.image_univ] at hy
        obtain ⟨a, _, rfl⟩ := hy; rfl
      | some val =>
        by_cases hv : val = c <;>
          simp only [add_apply_inr, StateT.run_pure, liftM_pure, bind_pure, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
            beq_iff_eq, StateT.run_map, Functor.map_map, ← apply_ite, QueryImpl.add_apply_inr, hv,
            StateT.run_bind, StateT.run_get, ↓reduceIte, support_pure, Option.some.injEq,
            StateT.run_set, map_pure, support_map, support_liftM, OracleQuery.input_query,
            OracleQuery.cont_query, Set.range_id, Set.image_univ] at hy
        · subst hy; rfl
        · obtain ⟨a, _, rfl⟩ := hy; rfl
  case hproj =>
    intro t s hs
    obtain ⟨⟨ch, ic⟩, oc⟩ := s
    simp only at hs
    subst hs
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
    · -- uniform-sampling oracle: forwarded through both impls; cache relocated unchanged
      have hq : simulateQ (PRFScheme.prfIdealQueryImpl (D := AD × C_e) (R := T))
          (liftM (OracleSpec.query n) :
            OracleComp (unifSpec + ((AD × C_e) →ₒ T)) (unifSpec.Range n))
          = (liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :
              StateT ((AD × C_e →ₒ T).QueryCache) ProbComp (unifSpec.Range n)) :=
        PRFScheme.simulateQ_prfIdealQueryImpl_liftComp
          (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
      rw [ToVCVio.flattenStateT_mapStateTBase_apply_run]
      simp [gameUnifImpl,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, hq,
        StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
    · -- encryption oracle: `se.encrypt ke m` + tag = `randomOracle (ad,c)` on the relocated
      -- cache; the inner TagCache (∅) is dropped by proj
      rw [ToVCVio.flattenStateT_mapStateTBase_apply_run]
      cases ch <;>
        simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift,
          StateT.run_pure, simulateQ_map, hroI, Prod.map, Functor.map_map]
    · -- decryption oracle: verify = `randomOracle (ad,c)` compare; same relocation.
      -- After the (shared) RO query, the verify result is a `pure`, so `simulateQ` is the
      -- identity and the nested-state reassoc lines up with game1's direct run.
      rw [ToVCVio.flattenStateT_mapStateTBase_apply_run]
      cases ch with
      | none =>
        simp only [add_apply_inr, StateT.run_pure, liftM_pure, bind_pure, StateT.run_monadLift,
          monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
          beq_iff_eq, StateT.run_map, Functor.map_map, QueryImpl.add_apply_inr, StateT.run_bind,
          StateT.run_get, reduceCtorEq, ↓reduceIte, StateT.run_set, simulateQ_bind, hroI,
          QueryImpl.withCaching_apply, bind_assoc, map_bind, Prod.map, id_eq]
        refine bind_congr fun a => ?_
        split_ifs <;> simp [StateT.run_pure, simulateQ_pure]
      | some val =>
        by_cases hv : val = (c.1, c.2)
        · subst hv
          simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
            StateT.run_monadLift, StateT.run_pure,
            simulateQ_pure, Prod.map, Functor.map_map]
        · simp only [add_apply_inr, StateT.run_pure, liftM_pure, bind_pure, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, Prod.mk.eta,
            beq_iff_eq, StateT.run_map, Functor.map_map, QueryImpl.add_apply_inr, StateT.run_bind,
            StateT.run_get, Option.some.injEq, hv, ↓reduceIte, StateT.run_set, simulateQ_bind,
            hroI, QueryImpl.withCaching_apply, bind_assoc, map_bind, Prod.map, id_eq]
          refine bind_congr fun a => ?_
          split_ifs <;> simp [StateT.run_pure, simulateQ_pure]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Game 0 → 1: PRF hop. Gap bounded by PRF advantage.

NRS14 Lemma 3, eq. (4): replace F^tag with random ρ. The two reduction-equals-experiment
equalities `game0_eq_prfRealExp` and `game1_eq_prfIdealExp` combine here, since both sides
share the same `prfAdvantage` shape. -/
theorem game0_game1_le_prf
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    |(Pr[= true | game0 se prf adv]).toReal -
     (Pr[= true | game1 se adv]).toReal| ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) := by
  unfold PRFScheme.prfAdvantage
  rw [game0_eq_prfRealExp se prf adv, game1_eq_prfIdealExp se adv]

/-! ### Auth hop: bad-flag-instrumented games

For the identical-until-bad step we instrument `game1`/`game2'` with a monotone `forged : Bool`
flag set whenever a (non-challenge) decrypt query's tag verifies against the random oracle —
the "forgery" event. The state becomes `EtmGameState × Bool`. The parameter `b` selects the
return behaviour on a successful verify: `b = true` returns the real decryption (= `game1`),
`b = false` rejects (= `game2'`); both set the flag identically, so the two impls agree on
every non-bad transition (`tvDist_simulateQ_le_probEvent_output_bad_probComp`). -/

/-- Uniform-sampling oracle on the flag-augmented state. -/
noncomputable def authUnifImpl :
    QueryImpl unifSpec (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  ToVCVio.unifLiftStateT (EtmGameState AD C_e T × Bool) unifSpec

/-- Encryption oracle on the flag-augmented state (real encryption, random-oracle tag);
the flag is threaded unchanged. -/
noncomputable def authEncImpl (se : DetSEAlg K_e M C_e) (ke : K_e) :
    QueryImpl (AD × M →ₒ Option (C_e × T))
      (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  fun (ad, m) => do
    let ((challenge, qc), forged) ← get
    match challenge with
    | some _ => pure none
    | none => do
      let (t, qc') ← (((AD × C_e) →ₒ T).randomOracle (ad, se.encrypt ke m)).run qc
      set ((some (se.encrypt ke m, t), qc'), forged)
      return some (se.encrypt ke m, t)

/-- Decryption oracle on the flag-augmented state. The challenge-ciphertext guard rejects;
otherwise the random oracle is queried, the `forged` flag is set on a successful verify, and
(`b = true`) the real decryption is returned or (`b = false`) the query is rejected. -/
noncomputable def authDecImpl (se : DetSEAlg K_e M C_e) (b : Bool) (ke : K_e) :
    QueryImpl (AD × (C_e × T) →ₒ Option M)
      (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  fun (ad, (c, t)) => do
    let ((challenge, qc), forged) ← get
    if challenge == some (c, t) then pure none
    else do
      let (t', qc') ← (((AD × C_e) →ₒ T).randomOracle (ad, c)).run qc
      let ok := t == t'
      set ((challenge, qc'), forged || ok)
      if ok then (if b then pure (se.decrypt ke c) else pure none) else pure none

/-- Complete flag-instrumented oracle set for the auth hop (`b = true` ≈ `game1`,
`b = false` ≈ `game2'`). -/
noncomputable def authInstImpl (se : DetSEAlg K_e M C_e) (b : Bool) (ke : K_e) :
    QueryImpl (aeadOneTimeCCASpec AD M (C_e × T))
      (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  authUnifImpl (AD := AD) (C_e := C_e) (T := T) + authEncImpl (AD := AD) (T := T) se ke +
    authDecImpl (AD := AD) (T := T) se b ke

/-- Forge reduction: a `ToVCVio.ForgeAdversary` over `forgeSpec (AD × C_e) T` built from the
AEAD adversary at a fixed key `ke`. It is a skeleton instantiation (`spec = forgeSpec`) that
forwards the EtM tag computation to the **eval** oracle (`D →ₒ R`) and the EtM verification to
the **verify** oracle (`D × R →ₒ Bool`), discarding the final guess bit (only the `forged` flag
in the forge experiment's state matters). Structurally analogous to `prfReduction`.

NRS14 Appendix A.2: the reduction `B(A)` witnessing the forge bound. Each decrypt query becomes
one verify query, so `B`'s verify-query count matches `A`'s decrypt-query count `q_d`. -/
noncomputable def forgeReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    (ke : K_e) : ToVCVio.ForgeAdversary (AD × C_e) T :=
  let spec := ToVCVio.forgeSpec (AD × C_e) T
  let unifImpl : QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    ToVCVio.unifLiftStateT (EtmGameState AD C_e T) spec
  (Function.const Bool () <$>
    etmGameSkeleton (spec := spec)
      (pure ke)
      se.decrypt ∅
      (fun _ke m => pure (se.encrypt ke m))
      (fun q => do
        let t ← liftM (liftM (spec.query (Sum.inl (Sum.inr q))) : OracleComp spec T)
        pure t)
      (fun (ad, c) t => do
        let ok ← liftM (liftM (spec.query (Sum.inr ((ad, c), t))) : OracleComp spec Bool)
        pure ok)
      unifImpl
      adv : OracleComp spec Unit)

/-- Combined (collapsed) handler for the forge reduction: the AEAD oracle interface implemented
directly on the joint state `EtmGameState × ForgeState`, threading the reduction's local
`EtmGameState` (challenge + an unused, always-`∅` `TagCache`) alongside the forge experiment's
`ForgeState` (lazy-RO cache + eval'd points + `forged` flag).

This is the `simulateQ`-collapse target for `(simulateQ forgeImpl (forgeReduction se adv ke)).run`:
pushing `forgeImpl` through the reduction's inner skeleton handler (`mapStateTBase`) and flattening
the nested `StateT` yields exactly this handler (cf. the PRF hop's `hideal`). The encrypt oracle
forwards the tag computation to the forge **eval** oracle (recording the challenge point as the
unique eval'd point); the decrypt oracle forwards verification to the forge **verify** oracle
(setting `forged` on a successful verify at a not-eval'd point). -/
noncomputable def forgeJointImpl (se : DetSEAlg K_e M C_e) (ke : K_e) :
    QueryImpl (aeadOneTimeCCASpec AD M (C_e × T))
      (StateT (EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T) ProbComp) :=
  -- unif oracle: thread both states unchanged
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T) ProbComp))
  -- encrypt oracle
  + (fun (ad, m) => do
      let (eg, fs) ← get
      match eg.1 with
      | some _ => pure none
      | none => do
        let c := se.encrypt ke m
        let (t, cache') ← (((AD × C_e) →ₒ T).randomOracle (ad, c)).run fs.1
        set (((some (c, t), eg.2) : EtmGameState AD C_e T),
          ((cache', insert (ad, c) fs.2.1, fs.2.2) : ToVCVio.ForgeState (AD × C_e) T))
        return some (c, t) :
      QueryImpl (AD × M →ₒ Option (C_e × T))
        (StateT (EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T) ProbComp))
  -- decrypt oracle
  + (fun (ad, (c, t)) => do
      let (eg, fs) ← get
      if eg.1 == some (c, t) then pure none
      else do
        let (resp, cache') ← (((AD × C_e) →ₒ T).randomOracle (ad, c)).run fs.1
        let hit : Bool := t == resp
        let fs' : ToVCVio.ForgeState (AD × C_e) T :=
          (cache', fs.2.1, fs.2.2 || (hit && decide ((ad, c) ∉ fs.2.1)))
        set ((eg, fs') : EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T)
        if hit then pure (se.decrypt ke c) else pure none :
      QueryImpl (AD × (C_e × T) →ₒ Option M)
        (StateT (EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T) ProbComp))

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Step C of the auth hop: `game2'` (verify queries the RO then rejects unconditionally)
has the same output distribution as `game2` (rejects directly). The discarded verify RO query
reveals nothing, so removing it preserves the distribution
(`ToVCVio.evalDist_simulateQ_run'_discardRO`, the RO-mediated discarded-query brick), lifted
through the skeleton. -/
theorem game2'_eq_game2
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    Pr[= true | game2' se adv] = Pr[= true | game2 se adv] := by
  -- Fold the skeleton tail `let (b', _) ← run; return b'` to `run'`.
  -- Both games: `se.keygen` then the per-key skeleton run; descend through keygen.
  unfold game2' game2 etmGameSkeleton
  simp only [bind_pure_comp, ← StateT.run'_eq]
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  -- Per key: the two interpreters differ only in `decImpl`'s `verifyTag` — `game2'` makes a
  -- discarded random-oracle query at `(ad, c)` before rejecting, `game2` rejects directly.
  -- Reduce the `Pr` equality to a `𝒟` equality and apply the generic discarded-query brick.
  rw [probOutput_def, probOutput_def]
  refine congrFun (congrArg DFunLike.coe ?_) true
  refine ToVCVio.evalDist_simulateQ_run'_discardRO
    (D := AD × C_e) (R := T) _ _ ?h₁ ?hstep adv none ∅
  case h₁ =>
    -- `game2`'s interpreter respects the RO: the only cache access is `computeTag = randomOracle`
    -- inside `encrypt`; `verifyTag = pure false` and the unif oracle never touch the cache.
    -- Exhibit the body `B` that recomputes each oracle's response/state as an `OracleComp` over
    -- `unifSpec + ((AD × C_e) →ₒ T)` (uniform sampling for unif, an RO query for the challenge
    -- tag, pure transitions everywhere else).
    refine ⟨fun t s => ?_, fun t s qc => ?_⟩
    · -- The body `B t s`.
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
      · -- unif: forward a uniform sample, state unchanged.
        exact (do
          let u ← liftM ((unifSpec + ((AD × C_e) →ₒ T)).query (Sum.inl n))
          pure (u, s))
      · -- encrypt: if challenge set return none; else encrypt + RO-tag, set challenge.
        exact (match s with
          | some _ => pure (none, s)
          | none => do
            let t' ← liftM ((unifSpec + ((AD × C_e) →ₒ T)).query
              (Sum.inr (ad, se.encrypt ke m)))
            pure (some (se.encrypt ke m, t'), some (se.encrypt ke m, t')))
      · -- decrypt: reject unconditionally (`verifyTag = pure false`), state unchanged.
        exact pure (none, s)
    · -- The body matches the first interpreter's run, reshaped.
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
      · -- unif: both sides forward a uniform sample, cache + challenge unchanged.
        simp only [QueryImpl.add_apply_inl, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, simulateQ_pure, StateT.run_pure]
        rw [show ((ToVCVio.roImpl (AD × C_e) T) (Sum.inl n)).run qc =
              (fun u => (u, qc)) <$> (liftM (OracleSpec.query (spec := unifSpec) n) :
                ProbComp ((unifSpec + ((AD × C_e) →ₒ T)).Range (Sum.inl n))) from by
            rw [ToVCVio.roImpl, QueryImpl.add_apply_inl]; unfold unifFwdImpl
            rw [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl]
            simp [StateT.run_monadLift, bind_pure_comp, HasQuery.query]]
        unfold gameUnifImpl
        simp only [QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
          bind_pure_comp, Functor.map_map]
        erw [OracleComp.liftM_run_StateT]
        simp only [bind_pure_comp]
        rfl
      · -- encrypt: case on whether the challenge is already set.
        cases s <;>
          simp [ToVCVio.roImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
            StateT.run_bind, StateT.run_get,
            StateT.run_set, StateT.run_pure, map_bind, Functor.map_map]
      · -- decrypt: reject unconditionally; case on the challenge guard, both reject identically.
        by_cases hg : s = some (c, tg) <;>
          simp [ToVCVio.roImpl, QueryImpl.add_apply_inr,
            StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, map_pure,
            beq_iff_eq, hg]
  case hstep =>
    -- Per-query disjunction over the adversary spec sum `(unif + encrypt) + decrypt`.
    intro t s qc
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
    · -- uniform-sampling oracle: identical handlers (left disjunct)
      left; rfl
    · -- encryption oracle: identical handlers (`computeTag`/`encryptMsg` unchanged)
      left
      cases s <;>
        simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure]
    · -- decryption oracle: `verifyTag` differs. On the challenge guard both reject without a
      -- query (left disjunct); otherwise `game2'` prepends a discarded RO query at `(ad, c)`
      -- (right disjunct).
      by_cases hg : s = some (c, tg)
      · left
        simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_pure,
          beq_iff_eq, hg]
      · right
        refine ⟨(ad, c), ?_⟩
        simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_set,
          StateT.run_pure, beq_iff_eq, hg, map_bind, Functor.map_map]

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Per-key identical-until-bad bound (auth hop, brick 3): the flag-instrumented `b = true`
and `b = false` simulations agree on every non-forged transition (they differ only in the
verify return when `ok = true`, which also sets the monotone `forged` flag), so the per-key TV
distance between them is at most the forge probability of the `b = true` simulation
(`ToVCVio.tvDist_simulateQ_le_probEvent_output_bad_probComp`). -/
theorem tvDist_authInst_le_probForge
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) (ke : K_e) :
    tvDist ((simulateQ (authInstImpl se true ke) adv).run' ((none, ∅), false))
        ((simulateQ (authInstImpl se false ke) adv).run' ((none, ∅), false)) ≤
      (Pr[fun z : Bool × (EtmGameState AD C_e T × Bool) => z.2.2 = true |
          (simulateQ (authInstImpl se true ke) adv).run ((none, ∅), false)]).toReal := by
  -- Bad-flag monotonicity: the flag is only ever replaced by `forged` or `forged || ok`,
  -- so once `true` it stays `true`, for both `b = true` and `b = false`.
  have hmono : ∀ (b : Bool) (t : (aeadOneTimeCCASpec AD M (C_e × T)).Domain)
      (p : EtmGameState AD C_e T × Bool), p.2 = true →
      ∀ z ∈ support ((authInstImpl se b ke t).run p), z.2.2 = true := by
    intro b t p hp z hz
    obtain ⟨⟨ch, qc⟩, fl⟩ := p
    simp only at hp; subst hp
    -- In every branch the output state's flag is `true` (threaded `forged`, or `forged || ok`
    -- with `forged = true`), so the support membership pins `z` to a tuple with `z.2.2 = true`.
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
    · -- uniform-sampling oracle: state (hence flag) threaded unchanged
      simp only [add_apply_inl, authInstImpl, authUnifImpl, QueryImpl.ofLift_eq_id',
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, support_map, support_liftM,
        OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hz
      obtain ⟨a, rfl⟩ := hz; rfl
    · -- encryption oracle: flag written back unchanged (`forged = true`)
      simp only [authInstImpl, authEncImpl, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr] at hz
      cases ch with
      | none =>
        simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, bind_pure_comp, StateT.run_monadLift, monadLift_self,
          StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map] at hz
        obtain ⟨a, _, rfl⟩ := hz; rfl
      | some val =>
        simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, bind_pure_comp, StateT.run_pure, support_pure] at hz
        obtain rfl := hz; rfl
    · -- decryption oracle: flag becomes `forged || ok = true`
      simp only [authInstImpl, authDecImpl, QueryImpl.add_apply_inr] at hz
      cases ch with
      | none =>
        simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, ← apply_ite, bind_pure_comp, reduceCtorEq, ↓reduceIte,
          Bool.true_or, StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_set,
          map_pure, Functor.map_map, support_map] at hz
        obtain ⟨a, _, rfl⟩ := hz; rfl
      | some val =>
        by_cases hguard : val = (c, tg)
        · simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
            StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure, support_pure] at hz
          obtain rfl := hz; rfl
        · simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
            StateT.run_get, pure_bind, ← apply_ite, bind_pure_comp, Option.some.injEq, hguard,
            ↓reduceIte, Bool.true_or, StateT.run_monadLift, monadLift_self, StateT.run_map,
            StateT.run_set, map_pure, Functor.map_map, support_map] at hz
          obtain ⟨a, _, rfl⟩ := hz; rfl
  -- Agreement off the bad step: the `b = true`/`b = false` impls differ only in the
  -- decrypt return on `ok = true`, which also sets the flag to `true`. So for outputs with
  -- flag `false` the two impls have equal probability (unif/encrypt: `b` unused; decrypt:
  -- the `ok = true` branch yields flag `true`, excluded; the `ok = false` branch returns
  -- `none` regardless of `b`).
  have hagree : ∀ (t : (aeadOneTimeCCASpec AD M (C_e × T)).Domain)
      (s : EtmGameState AD C_e T) (u : (aeadOneTimeCCASpec AD M (C_e × T)).Range t)
      (s' : EtmGameState AD C_e T),
      Pr[= (u, (s', false)) | (authInstImpl se true ke t).run (s, false)] =
        Pr[= (u, (s', false)) | (authInstImpl se false ke t).run (s, false)] := by
    intro t s u s'
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
    · -- uniform-sampling oracle: `b` unused, impls identical at this index
      simp [authInstImpl, QueryImpl.add_apply_inl]
    · -- encryption oracle: `b` unused, impls identical at this index
      simp [authInstImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    · -- decryption oracle
      obtain ⟨ch, qc⟩ := s
      simp only [authInstImpl, QueryImpl.add_apply_inr, authDecImpl]
      by_cases hg : ch = some (c, tg)
      · -- challenge-guard rejects: `pure none`, `b` unused
        simp [hg, StateT.run_bind, StateT.run_get, StateT.run_pure]
      · -- verify: equal probability per random-oracle sample
        simp only [add_apply_inr, beq_iff_eq, QueryImpl.withCaching_apply, StateT.run_bind,
          StateT.run_get, pure_bind, ↓reduceIte, hg, Bool.false_or, StateT.run_monadLift,
          monadLift_self, bind_pure_comp, StateT.run_set, bind_map_left, Bool.false_eq_true,
          ite_self, StateT.run_map, map_pure, Functor.map_map]
        refine probOutput_bind_congr' _ _ fun p => ?_
        obtain ⟨t', qc'⟩ := p
        -- `tg = t'` (forged): both outputs have flag `true` ≠ target flag `false` → both 0;
        -- `tg ≠ t'` (reject): output `none` regardless of `b`.
        by_cases hok : tg = t' <;>
          simp [hok, ← OracleComp.pure_def, probOutput_pure_eq_indicator,
            Set.mem_singleton_iff, Prod.ext_iff]
  exact ToVCVio.tvDist_simulateQ_le_probEvent_output_bad_probComp
    (authInstImpl se true ke) (authInstImpl se false ke) adv (none, ∅)
    hagree (hmono true) (hmono false)

omit [Inhabited C_e] [Inhabited T] [SampleableType C_e] in
/-- Per-key forge-probability collapse (auth hop, the heaviest sub-proof): the per-key game's
forge probability (the `b = true` simulation's `forged` flag) is at most the `forged`
probability of the eval+verify lazy-RO forge experiment run on `forgeReduction`. The proof
collapses the nested forge `simulateQ` to the single combined handler `forgeJointImpl` over the
same adversary `adv`, then applies the generic coupling brick
`ToVCVio.probEvent_snd_le_of_relTriple` with a joint-state invariant (NRS14 App. A.2). -/
theorem probForge_authInst_le_forgeReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) (ke : K_e) :
    (Pr[fun z : Bool × (EtmGameState AD C_e T × Bool) => z.2.2 = true |
        (simulateQ (authInstImpl se true ke) adv).run ((none, ∅), false)]).toReal ≤
      (Pr[fun z : Unit × ToVCVio.ForgeState (AD × C_e) T => z.2.2.2 = true |
          (simulateQ ToVCVio.forgeImpl (forgeReduction se adv ke)).run
            (∅, ∅, false)]).toReal := by
  -- The proof relates the two experiments at the ENNReal level (`.toReal` is monotone on
  -- the relevant non-⊤ probabilities), then collapses the nested forge `simulateQ` to a
  -- single combined handler over the SAME adversary `adv`, and finally applies the generic
  -- coupling brick `probEvent_snd_le_of_relTriple` with a joint-state invariant.
  --
  -- Combined RHS handler: the AEAD oracles forwarded into the joint state
  -- `EtmGameState × ForgeState` (the `simulateQ`-collapse target for the forge run).
  set impl₂ :
      QueryImpl (aeadOneTimeCCASpec AD M (C_e × T))
        (StateT (EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T) ProbComp) :=
    forgeJointImpl se ke with himpl₂
  -- Joint-state invariant coupling the instrumented-game state `(EtmGameState × Bool)` with
  -- the combined RHS state `(EtmGameState × ForgeState)`: the challenge slot and the lazy-RO
  -- cache agree, the set of eval'd points is contained in the challenge ciphertext, the RO
  -- maps the challenge point to the challenge tag, and the game's bad flag implies the
  -- forge `forged` flag.
  set R_state :
      (EtmGameState AD C_e T × Bool) →
        (EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T) → Prop :=
    fun s₁ s₂ =>
      -- challenge agrees
      s₁.1.1 = s₂.1.1 ∧
      -- RO cache agrees (game's TagCache = forge's RO cache)
      s₁.1.2 = s₂.2.1 ∧
      -- eval'd points ⊆ challenge ciphertext (with matching RO value)
      (∀ p ∈ s₂.2.2.1, ∃ c t, s₂.1.1 = some (c, t) ∧ p = (Prod.fst p, c) ∧
          s₂.2.1 (Prod.fst p, c) = some t) ∧
      -- game bad flag ⟹ forge forged flag
      (s₁.2 = true → s₂.2.2.2 = true)
    with hR_state
  -- ENNReal-level event inequality, then transport to `.toReal`.
  refine ENNReal.toReal_mono ?hne ?hle
  case hne =>
    exact ne_top_of_le_ne_top one_ne_top probEvent_le_one
  case hle =>
    -- (i) Reduction collapse: rewrite the forge run as a `simulateQ impl₂ adv` run.
    have hRHScollapse :
        Pr[fun z : Unit × ToVCVio.ForgeState (AD × C_e) T => z.2.2.2 = true |
            (simulateQ ToVCVio.forgeImpl (forgeReduction se adv ke)).run (∅, ∅, false)] =
          Pr[fun z : Bool × (EtmGameState AD C_e T × ToVCVio.ForgeState (AD × C_e) T) =>
                z.2.2.2.2 = true |
            (simulateQ impl₂ adv).run ((none, ∅), (∅, ∅, false))] := by
      -- Mechanical nested-`simulateQ` collapse: `forgeReduction = const () <$> skeleton`,
      -- the skeleton ends `let (b',_) ← (simulateQ inner adv).run (none,∅); return b'`, and
      -- `simulateQ forgeImpl ((simulateQ inner adv).run s)` flattens to
      -- `simulateQ ((forgeImpl.mapStateTBase inner).flattenStateT) adv` via
      -- `simulateQ_mapStateTBase_run` + `simulateQ_flattenStateT_run` (cf. `hideal`).
      -- The forge event `z.2.2.2` on `Unit × ForgeState` matches `z.2.2.2.2` on the joint
      -- output `Bool × (EtmGameState × ForgeState)` after reassociating the states.
      -- `hflat` proves the flattened collapsed handler equals `forgeJointImpl` per query
      -- (unif/encrypt/decrypt forward to the corresponding `forgeImpl` summand); the event
      -- composition then reindexes definitionally to the joint `forged` flag.
      unfold forgeReduction etmGameSkeleton
      simp only [pure_bind, simulateQ_map, StateT.run_map, probEvent_map,
        Function.const, StateT.run_bind, StateT.run_pure,
        bind_pure_comp]
      rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
      -- The flattened collapsed handler equals the hand-written joint handler
      -- `forgeJointImpl`.
      rw [show (ToVCVio.forgeImpl.mapStateTBase _).flattenStateT
            = forgeJointImpl se ke from ?hflat,
        ← himpl₂, probEvent_map]
      case hflat =>
        funext t
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
        · -- unif oracle: both handlers forward `query n` to the same lifted uniform sample
          have hufwd : simulateQ ToVCVio.forgeImpl
              (liftM (OracleSpec.query n) :
                OracleComp (ToVCVio.forgeSpec (AD × C_e) T) (unifSpec.Range n))
              = ToVCVio.forgeUnifImpl n := by
            have hq : (liftM (OracleSpec.query n) :
                  OracleComp (ToVCVio.forgeSpec (AD × C_e) T) (unifSpec.Range n))
                = (OracleSpec.query (spec := ToVCVio.forgeSpec (AD × C_e) T)
                    (Sum.inl (Sum.inl n))) := rfl
            rw [hq]
            simp [ToVCVio.forgeImpl, QueryImpl.add_apply_inl]
          ext ⟨eg, fs⟩ : 2
          simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
            forgeJointImpl,
            StateT.run_monadLift, StateT.run_mk,
                  
            bind_pure_comp, Functor.map_map,
            monadLift_self]
          erw [OracleComp.liftM_run_StateT, OracleComp.liftM_run_StateT]
          rw [simulateQ_bind]
          erw [hufwd]
          simp only [simulateQ_pure, ToVCVio.forgeUnifImpl, QueryImpl.liftTarget_apply,
            QueryImpl.ofLift_apply, StateT.run_bind, StateT.run_pure,
            bind_assoc, pure_bind,
            ← bind_pure_comp]
          erw [OracleComp.liftM_run_StateT]
          simp only [Functor.map_map, bind_pure_comp,
            ]
        · -- encrypt oracle: forwards the tag query to the shared eval RO, records challenge
          have hefwd : ∀ q : AD × C_e, simulateQ ToVCVio.forgeImpl
              (liftM (OracleSpec.query (spec := ToVCVio.forgeSpec (AD × C_e) T)
                  (Sum.inl (Sum.inr q))) :
                OracleComp (ToVCVio.forgeSpec (AD × C_e) T) T)
              = ToVCVio.evalRO q := by
            intro q
            simp [ToVCVio.forgeImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
          ext ⟨⟨ch, qc⟩, fs⟩ : 2
          rw [ToVCVio.flattenStateT_mapStateTBase_apply_run]
          cases ch <;>
            simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, forgeJointImpl,
              StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, simulateQ_map,
              simulateQ_pure, hefwd, ToVCVio.evalRO, bind_pure_comp, map_bind,
              Functor.map_map, pure_bind]
        · -- decrypt oracle: forwards the verify query to the shared verify RO
          have hvfwd : ∀ p : (AD × C_e) × T, simulateQ ToVCVio.forgeImpl
              (liftM (OracleSpec.query (spec := ToVCVio.forgeSpec (AD × C_e) T)
                  (Sum.inr p)) :
                OracleComp (ToVCVio.forgeSpec (AD × C_e) T) Bool)
              = ToVCVio.verifyAgainstRO p := by
            intro p
            simp [ToVCVio.forgeImpl, QueryImpl.add_apply_inr]
          ext ⟨⟨ch, qc⟩, fs⟩ : 2
          rw [ToVCVio.flattenStateT_mapStateTBase_apply_run]
          by_cases heq : ch = some (c, tg)
          · simp [heq, QueryImpl.add_apply_inr, forgeJointImpl,
              StateT.run_bind, StateT.run_get,
              StateT.run_monadLift, StateT.run_pure,
              simulateQ_pure, bind_pure_comp, Functor.map_map,
              pure_bind]
          · simp only [add_apply_inr, liftM_pure, Prod.mk.eta, StateT.run_monadLift,
              monadLift_self, bind_pure_comp, Functor.map_map, liftM_map, bind_map_left, pure_bind,
              beq_iff_eq, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, heq,
              ↓reduceIte, StateT.run_set, simulateQ_bind, hvfwd, ToVCVio.verifyAgainstRO,
              QueryImpl.withCaching_apply, decide_not, bind_assoc, map_bind, forgeJointImpl,
              QueryImpl.ofLift_eq_id']
            refine bind_congr fun a => ?_
            by_cases hok : tg = a.1 <;>
              simp [hok, StateT.run_pure, simulateQ_pure,
                ]
      -- The composed event reindexes to the forge `forged` flag on the joint output.
      rfl
    rw [hRHScollapse]
    -- (ii) Coupling brick: the game's flag (`z.2.2 = true`) implies the forge flag
    -- (`z.2.2.2.2 = true`) under `R_state`, which is preserved per-query.
    refine ToVCVio.probEvent_snd_le_of_relTriple
      (authInstImpl se true ke) impl₂ R_state adv ?himpl
      ((none, ∅), false) ((none, ∅), (∅, ∅, false)) ?hs
      (flag₁ := fun s₁ => s₁.2 = true)
      (flag₂ := fun s₂ => s₂.2.2.2 = true)
      ?himp
    case hs =>
      -- initial states are related: challenges/caches both empty, no eval'd points, flags off
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro p hp; simp at hp
      · intro h; exact absurd h (by simp)
    case himp =>
      -- flag implication is the last conjunct of `R_state`
      intro a b hR hflag; exact hR.2.2.2 hflag
    case himpl =>
      -- Per-query relational correspondence: each AEAD oracle, run under the instrumented
      -- game handler and under the combined forge handler from `R_state`-related states,
      -- produces equal output bits and `R_state`-related successor states. The unif oracle
      -- threads both states unchanged; encrypt forwards the tag query to the shared RO and
      -- records the challenge as the unique eval'd point (re-establishing `evald ⊆ challenge`
      -- and `ρ(challenge)=tag`); decrypt forwards the verify to the shared RO — on a
      -- non-challenge `ok` it sets the game flag and, since `evald ⊆ challenge` forces the
      -- point to be non-eval'd, also sets the forge `forged` flag (NRS14 App. A.2).
      -- [scheme-specific coupling; the genuine crypto invariant of the auth hop]
      intro t s₁ s₂ hRs
      obtain ⟨⟨ch₁, qc₁⟩, fl₁⟩ := s₁
      obtain ⟨⟨ch₂, qc₂⟩, fs₂⟩ := s₂
      obtain ⟨hch, hqc, hev, hflagimp⟩ := hRs
      simp only at hch hqc
      subst hch; subst hqc
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
      · -- unif oracle: both handlers thread state unchanged and sample the same uniform value
        -- Both handlers forward the same `liftM (query n)` and thread their states
        -- unchanged, so couple the shared uniform sample diagonally and re-use the
        -- incoming `R_state` components for the unchanged successor states.
        simp only [himpl₂, hR_state, forgeJointImpl, authInstImpl, authUnifImpl,
          QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
        refine ProgramLogic.Relational.relTriple_bind
          (ProgramLogic.Relational.relTriple_refl _) ?_
        intro a b hab
        simp only [ProgramLogic.Relational.EqRel] at hab; subst hab
        exact ProgramLogic.Relational.relTriple_pure_pure
          ⟨rfl, rfl, rfl, hev, hflagimp⟩
      · -- encrypt oracle: forwards the tag to the shared RO; records the challenge as the
        -- unique eval'd point, re-establishing `evald ⊆ challenge` and `ρ(challenge)=tag`
        simp only [himpl₂, hR_state, forgeJointImpl, authInstImpl, authEncImpl,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        cases ch₁ with
        | some val =>
            -- challenge already set: both handlers return `pure none`, state unchanged,
            -- so the postcondition is the incoming eval'd/flag clauses of `R_state`.
            simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
              StateT.run_get, pure_bind, bind_pure_comp, StateT.run_pure, Prod.forall,
              Prod.mk.injEq, true_and, ↓existsAndEq, ProgramLogic.Relational.relTriple_iff_relWP,
              MAlgRelOrdered.relWP_pure, Option.some.injEq]
            simp only at hev hflagimp
            refine ⟨fun a b hab => ?_, hflagimp⟩
            obtain ⟨c, t, hsome, hpeq, hcache⟩ := hev (a, b) hab
            obtain rfl : b = c := by simpa using congrArg Prod.snd hpeq
            exact ⟨t, by simpa using hsome, hcache⟩
        | none =>
            -- old challenge `none` ⇒ the eval'd set is empty (`hev` is vacuous), and both
            -- handlers query the SAME random oracle on the SAME cache `fs₂.1`. Couple that
            -- sample diagonally; the successor challenge/cache agree and the only eval'd
            -- point `(ad, c)` matches the new challenge with `ρ(ad,c) = tag`.
            simp only at hev
            have hevald : fs₂.2.1 = (∅ : Finset (AD × C_e)) := by
              by_contra hne
              obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hne
              obtain ⟨c, t, hcontra, -, -⟩ := hev p hp
              exact absurd hcontra (by simp)
            simp only [add_apply_inl, add_apply_inr, QueryImpl.withCaching_apply, StateT.run_bind,
              StateT.run_get, pure_bind, bind_pure_comp, StateT.run_monadLift, monadLift_self,
              StateT.run_map, StateT.run_set, map_pure, Functor.map_map, hevald, insert_empty_eq,
              Prod.forall, Prod.mk.injEq, true_and, ↓existsAndEq,
              ProgramLogic.Relational.relTriple_iff_relWP,
              ProgramLogic.Relational.relWP_iff_couplingPost]
            rw [← ProgramLogic.Relational.relWP_iff_couplingPost,
              ← ProgramLogic.Relational.relTriple_iff_relWP]
            -- couple the shared random-oracle sample diagonally, casing on cache hit/miss
            -- so the new cache is explicit and `ρ(ad,c) = tag` is available
            cases hca : fs₂.1 (ad, se.encrypt ke m) with
            | some u =>
                -- cache hit: the RO returns the cached `u`, cache unchanged; the new eval'd
                -- point `(ad, c)` is consistent because `fs₂.1 (ad, c) = some u`.
                simp only [StateT.run_pure, map_pure]
                refine ProgramLogic.Relational.relTriple_pure_pure
                  ⟨rfl, rfl, rfl, ?_, hflagimp⟩
                intro a₁ b hmem
                rw [Finset.mem_singleton] at hmem
                obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hmem
                exact ⟨u, rfl, hca⟩
            | none =>
                -- cache miss: sample the tag, insert into the cache via `cacheQuery`; couple
                -- the shared uniform sample diagonally. The new cache maps the new eval'd
                -- point `(ad, c)` to the freshly sampled tag (`cacheQuery_self`).
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  StateT.run_modifyGet, bind_pure_comp,
                  Functor.map_map]
                rw [← bind_pure_comp, ← bind_pure_comp]
                refine ProgramLogic.Relational.relTriple_bind
                  (ProgramLogic.Relational.relTriple_refl _) ?_
                intro a b hab
                simp only [ProgramLogic.Relational.EqRel] at hab; subst hab
                refine ProgramLogic.Relational.relTriple_pure_pure
                  ⟨rfl, rfl, rfl, ?_, hflagimp⟩
                intro a₁ b hmem
                rw [Finset.mem_singleton, Prod.mk.injEq] at hmem
                obtain ⟨hb1, hb2⟩ := hmem
                subst hb1; subst hb2
                exact ⟨a, rfl, QueryCache.cacheQuery_self fs₂.1 (a₁, se.encrypt ke m) a⟩
      · -- decrypt oracle: forwards verify to the shared RO; on a non-challenge `ok` sets the
        -- game flag, and (since `evald ⊆ challenge`) the point is not eval'd so
        -- `forged` fires
        simp only at hev hflagimp
        simp only [himpl₂, hR_state]
        simp only [authInstImpl, authDecImpl, forgeJointImpl, QueryImpl.add_apply_inr]
        erw [StateT.run_bind, StateT.run_bind, StateT.run_get, StateT.run_get]
        simp only [pure_bind]
        by_cases hg : ch₁ = some (c, tg)
        · simp only [hg, beq_self_eq_true, if_true]
          exact ProgramLogic.Relational.relTriple_pure_pure
            ⟨rfl, rfl, rfl, hg ▸ hev, hflagimp⟩
        · simp only [beq_iff_eq, hg, if_false]
          set ro := (((AD × C_e) →ₒ T).randomOracle (ad, c)).run fs₂.1 with hro
          -- Support facts for the shared RO query: the resulting cache extends `fs₂.1`
          -- (existing entries persist) and maps the queried point `(ad, c)` to the response.
          have hsupp : ∀ p ∈ support ro,
              fs₂.1 ≤ p.2 ∧ p.2 (ad, c) = some p.1 := by
            intro p hp
            rw [hro] at hp
            rcases hlk : fs₂.1 (ad, c) with _ | u
            · -- cache miss: the RO samples and inserts `(ad, c) ↦ p.1`
              rw [QueryImpl.withCaching_run_none _ hlk] at hp
              rw [support_map] at hp
              obtain ⟨v, _, rfl⟩ := hp
              refine ⟨QueryCache.le_cacheQuery (cache := fs₂.1) hlk, ?_⟩
              simp only [QueryCache.cacheQuery_self]
            · -- cache hit: the RO returns the cached value, leaving the cache unchanged
              rw [QueryImpl.withCaching_run_some _ hlk] at hp
              rw [support_pure] at hp
              simp only [Set.mem_singleton_iff] at hp
              subst hp
              exact ⟨le_refl _, hlk⟩
          erw [StateT.run_bind, StateT.run_bind,
            OracleComp.liftM_run_StateT, OracleComp.liftM_run_StateT]
          simp only [bind_assoc, pure_bind, if_true]
          -- Diagonal coupling of the shared RO query carrying the support facts.
          have hcouple : ProgramLogic.Relational.RelTriple ro ro
              (fun a b => a = b ∧ fs₂.1 ≤ a.2 ∧ a.2 (ad, c) = some a.1) := by
            rw [ProgramLogic.Relational.relTriple_iff_relWP,
              ProgramLogic.Relational.relWP_iff_couplingPost]
            refine ⟨_root_.SPMF.Coupling.refl (𝒟[ro]), ?_⟩
            intro z hz
            rcases (mem_support_bind_iff (𝒟[ro])
              (fun a => (pure (a, a) : SPMF _)) z).1 hz with ⟨a, ha, hz'⟩
            have ha_supp : a ∈ support ro :=
              (mem_support_iff (mx := ro) (x := a)).2
                (by simpa [probOutput_def] using
                  (mem_support_iff (mx := 𝒟[ro]) (x := a)).1 ha)
            have hzEq : z = (a, a) := by
              simpa [support_pure, Set.mem_singleton_iff] using hz'
            subst hzEq
            exact ⟨rfl, hsupp a ha_supp⟩
          refine ProgramLogic.Relational.relTriple_bind hcouple ?_
          rintro ⟨t', qc'⟩ ⟨resp, cache'⟩ ⟨hEq, hmono, hqcc⟩
          simp only [Prod.mk.injEq] at hEq
          obtain ⟨rfl, rfl⟩ := hEq
          erw [StateT.run_bind, StateT.run_bind, StateT.run_set, StateT.run_set]
          simp only [pure_bind]
          -- The successor evald-clause: existing eval'd points persist in the grown cache
          -- `qc'` (cache monotonicity), with the challenge slot unchanged at `ch₁`.
          have hevald : ∀ p ∈ fs₂.2.1, ∃ c_1 t, ch₁ = some (c_1, t) ∧
              p = (p.1, c_1) ∧ qc' (p.1, c_1) = some t := by
            intro p hp
            obtain ⟨c_1, t, hchal, hpeq, hlk⟩ := hev p hp
            exact ⟨c_1, t, hchal, hpeq, hmono hlk⟩
          by_cases hok : tg = t'
          · -- `ok = true`: the queried point `(ad, c)` is NOT eval'd (NRS14 App. A.2), so the
            -- forge `forged` flag fires; outputs both equal `se.decrypt ke c`.
            have hnotin : (ad, c) ∉ fs₂.2.1 := by
              intro hin
              obtain ⟨c_1, t, hchal, hpeq, hlk⟩ := hev (ad, c) hin
              -- `hpeq : (ad, c) = (ad, c_1)` forces `c_1 = c`
              simp only [Prod.mk.injEq, true_and] at hpeq
              subst hpeq
              -- the queried point is cached with value `t` in `fs₂.1`, hence in `qc'`
              have hqt : qc' (ad, c) = some t := hmono hlk
              -- so `t = t'`; with `tg = t'` we get `ch₁ = some (c, tg)`, contradicting `hg`
              have htt : t = t' := by
                have := hqt.symm.trans hqcc
                rwa [Option.some.injEq] at this
              apply hg
              rw [hchal, htt, hok]
            subst hok
            simp only [if_true]
            refine ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, rfl, rfl, hevald, ?_⟩
            intro _
            simp only [beq_self_eq_true, hnotin, not_false_eq_true, decide_true,
              Bool.and_true, Bool.or_true]
          · -- `ok = false`: verification fails, both reject (`none`); flags threaded
            -- unchanged.
            simp only [hok, if_false]
            have hbeq : (tg == t') = false := by
              simp only [beq_eq_false_iff_ne, ne_eq, hok, not_false_eq_true]
            simp only [hbeq, Bool.or_false, Bool.false_and]
            refine ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, rfl, rfl, hevald, ?_⟩
            intro hfl
            exact hflagimp hfl

omit [Inhabited C_e] [SampleableType C_e] in
/-- Query-bound transfer (auth hop adapter): each decrypt query of `adv` becomes exactly one
verify query in `forgeReduction`, so the reduction makes at most `q_d` verify queries whenever
`adv` makes at most `q_d` decrypt queries. -/
theorem forgeReduction_isQueryBoundP
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) (ke : K_e)
    (q_d : ℕ) (hqd : AEADScheme.decryptQueryBound adv q_d) :
    (forgeReduction se adv ke).IsQueryBoundP
      (ToVCVio.isVerifyQuery (D := AD × C_e) (R := T)) q_d := by
  -- `forgeSpec`'s `IsUniformSpec` witness (needed by the query-bound lemma) wants `Fintype T`;
  -- the tag type is sampleable, so it is finite.
  letI : Fintype T := SampleableType.Fintype T
  unfold forgeReduction etmGameSkeleton
  simp only [pure_bind, bind_pure_comp, Functor.map_map]
  rw [isQueryBoundP_def, isQueryBound_map_iff, ← isQueryBoundP_def]
  -- Split the adversary spec sum `(unifSpec+encrypt)+decrypt`: only decrypt (`Sum.inr`)
  -- satisfies the bound predicate, so the left (unif/encrypt) handlers issue 0 verify
  -- queries and the decrypt handler issues exactly 1. Each handler is discharged by
  -- per-handler `.run`-unwrapping (StateT `MonadLiftT` fusion of the `ofLift` forwarder),
  -- then `isQueryBoundP_query_iff` (encrypt eval / decrypt verify) and
  -- `IsQueryBoundP.liftComp_subSpec` (cross-spec unif lift). Cf. VCVio `CmaToNma` `hfwd`.
  refine ToVCVio.simulateQ_run_add_inr_of_step (fun t => by simp) hqd ?hleft ?hdec
    (fun t hnp => absurd (by simp) hnp) (none, ∅)
  case hleft =>
    intro t s
    rcases t with n | ⟨ad, m⟩
    · -- unif forwarder: one (lifted) unif query, not a verify query
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
      erw [OracleComp.liftM_run_StateT]
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      -- the lift sends `query n : OracleQuery unifSpec` to `forgeSpec` at
      -- `Sum.inl (Sum.inl n)`,
      -- which never `matches Sum.inr _`, so the forwarder makes no verify queries
      change (liftM (OracleSpec.query
          (Sum.inl (Sum.inl n) : (ToVCVio.forgeSpec (AD × C_e) T).Domain) :
            OracleQuery (ToVCVio.forgeSpec (AD × C_e) T) _) :
          OracleComp (ToVCVio.forgeSpec (AD × C_e) T) _).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_iff]
      simp [ToVCVio.isVerifyQuery]
    · -- encrypt forwarder: one eval query `Sum.inl (Sum.inr _)`, not a verify query
      simp only [QueryImpl.add_apply_inr]
      obtain ⟨ch, qc⟩ := s
      cases ch with
      | none =>
          simp only [add_apply_inr, StateT.run_pure, liftM_pure, bind_pure, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, liftM_map, bind_map_left, pure_bind, StateT.run_bind,
            StateT.run_get, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            isQueryBoundP_map_iff]
          exact (isQueryBoundP_query_iff
              (p := ToVCVio.isVerifyQuery (D := AD × C_e) (R := T))
              (Sum.inl (Sum.inr (ad, se.encrypt ke m))) 0).mpr
            (fun h => absurd h (by simp [ToVCVio.isVerifyQuery]))
      | some val =>
          simp [StateT.run_bind, StateT.run_get, StateT.run_pure]
  case hdec =>
    -- decrypt forwarder: one verify query `Sum.inr _`
    intro t hp s; obtain ⟨ad, c, tg⟩ := t; obtain ⟨ch, qc⟩ := s
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hg : ch = some (c, tg)
    · simp only [hg, beq_self_eq_true, ↓reduceIte, StateT.run_pure]
      exact isQueryBoundP_pure ToVCVio.isVerifyQuery (none, some (c, tg), qc) 1
    · simp only [beq_iff_eq, hg, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind]
      erw [OracleComp.liftM_run_StateT, OracleComp.liftM_run_StateT]
      simp only [StateT.run_pure, bind_assoc, pure_bind]
      refine (isQueryBoundP_bind (m := 0)
        ((isQueryBoundP_query_iff (p := ToVCVio.isVerifyQuery)
          (Sum.inr ((ad, c), tg)) 1).mpr (fun _ => Nat.one_pos))
        (fun x _ => ?_)).mono (le_refl 1)
      rcases hb : (x : Bool) with _ | _ <;>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, isQueryBoundP_pure]

omit [Inhabited C_e] [SampleableType C_e] in
/-- Game 1 → 2: auth bound. Gap bounded by `q_d` times tag-guessing probability.

NRS14 Appendix A.2, A5 Case 1: each decrypt query at a fresh random oracle
point verifies with probability `1/|T|`. Union bound over `q_d` decrypt
queries gives `q_d/|T|`. The hypothesis `hqd` ties `q_d` to the adversary
via `IsQueryBoundP`: `adv` makes at most `q_d` decrypt-oracle queries
(structurally, on every execution path). -/
theorem game1_game2_le_auth
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d) :
    |(Pr[= true | game1 se adv]).toReal -
     (Pr[= true | game2 se adv]).toReal| ≤
      ↑q_d * (Fintype.card T : ℝ)⁻¹ := by
  -- NRS14 Appendix A.2, A5 Case 1. Couple `game1` and `game2` through the intermediate
  -- `game2'` (verify queries the RO then rejects unconditionally):
  --   |Pr[game1] - Pr[game2]|
  --     = |Pr[game1] - Pr[game2']|          (hC: game2' = game2, discarded-query brick)
  --     ≤ tvDist(game1, game2')             (abs_probOutput_toReal_sub_le_tvDist)
  --     ≤ q_d/|T|                           (htv: identical-until-bad + forge brick)
  -- Step C: `game2' = game2`. game2' rejects unconditionally, so its verify RO query reveals
  -- nothing — removing it preserves the distribution (`evalDist_simulateQ_run'_discardRO`, the
  -- RO-mediated discarded-query brick), lifted through the skeleton.
  have hC : Pr[= true | game2' se adv] = Pr[= true | game2 se adv] :=
    game2'_eq_game2 se adv
  -- Steps A+B: identical-until-bad (game1 vs game2' agree off the forge step) bounds the TV
  -- distance by the forge probability; the eval+verify forge brick bounds that by q_d/|T|.
  have htv : tvDist (game1 se adv) (game2' se adv) ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ := by
    -- Per-key flag-instrumented simulations: `Y₁ ke` ≈ game1 (real return on verify),
    -- `Y₂ ke` ≈ game2' (always reject), both threading the `forged` flag.
    set Y₁ : K_e → ProbComp Bool :=
      fun ke => (simulateQ (authInstImpl se true ke) adv).run' ((none, ∅), false) with hY₁
    set Y₂ : K_e → ProbComp Bool :=
      fun ke => (simulateQ (authInstImpl se false ke) adv).run' ((none, ∅), false) with hY₂
    -- Abbreviation: the forge probability of the `b = true` instrumented simulation per key.
    set forgeProb : K_e → ℝ := fun ke =>
      (Pr[fun z : Bool × (EtmGameState AD C_e T × Bool) => z.2.2 = true |
          (simulateQ (authInstImpl se true ke) adv).run ((none, ∅), false)]).toReal
      with hforgeProb
    -- Fold the skeleton's `let (b', _) ← run; return b'` to `run'`.
    -- (1) Flag projection: each game = keygen >>= per-key flag-instrumented sim. The `forged`
    -- flag is write-only (does not affect the state transition or the output bit), so dropping
    -- it via `proj = Prod.fst` recovers the un-instrumented game
    -- (`run'_simulateQ_eq_of_query_map_eq`).
    -- The per-oracle `hproj` obligation: unif/encrypt thread the flag unchanged; decrypt's
    -- flag-write is dropped by `Prod.fst`, leaving the same state transition and output bit.
    have hproj_unif : ∀ (b : Bool) (ke : K_e) (n : ℕ) (s : EtmGameState AD C_e T × Bool),
        Prod.map id Prod.fst <$>
            (authInstImpl se b ke (Sum.inl (Sum.inl n))).run s =
          (gameUnifImpl (AD := AD) (C_e := C_e) (T := T) n).run (Prod.fst s) := by
      intro b ke n s
      obtain ⟨⟨ch, qc⟩, fl⟩ := s
      simp [authInstImpl, authUnifImpl, gameUnifImpl, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, StateT.run_monadLift, Prod.map, Functor.map_map]
    have hflag1 : game1 se adv = se.keygen >>= Y₁ := by
      rw [hY₁]
      unfold game1 etmGameSkeleton
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine bind_congr fun ke => ?_
      refine (run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst ?hproj adv ((none, ∅), false)).symm
      case hproj =>
        intro t s
        obtain ⟨⟨ch, qc⟩, fl⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
        · exact hproj_unif true ke n ((ch, qc), fl)
        · -- encryption oracle: flag threaded unchanged, dropped by `Prod.fst`
          cases ch <;>
            simp [authInstImpl, authEncImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
              StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map,
              Functor.map_map]
        · -- decryption oracle (b = true): RO + compare, real return on `ok`, flag dropped
          cases ch with
          | none =>
            simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map,
              ← apply_ite]
          | some val =>
            by_cases hguard : val = (c, tg) <;>
              simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
                StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map,
                ← apply_ite, beq_iff_eq, hguard]
    have hflag2 : game2' se adv = se.keygen >>= Y₂ := by
      rw [hY₂]
      unfold game2' etmGameSkeleton
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine bind_congr fun ke => ?_
      refine (run'_simulateQ_eq_of_query_map_eq _ _ Prod.fst ?hproj adv ((none, ∅), false)).symm
      case hproj =>
        intro t s
        obtain ⟨⟨ch, qc⟩, fl⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c, tg⟩
        · exact hproj_unif false ke n ((ch, qc), fl)
        · cases ch <;>
            simp [authInstImpl, authEncImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
              StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map,
              Functor.map_map]
        · -- decryption oracle (b = false): RO then reject unconditionally, flag dropped
          cases ch with
          | none =>
            simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map]
          | some val =>
            by_cases hguard : val = (c, tg) <;>
              simp [authInstImpl, authDecImpl, QueryImpl.add_apply_inr, StateT.run_bind,
                StateT.run_get, StateT.run_set, StateT.run_pure, Prod.map, Functor.map_map,
                beq_iff_eq, hguard]
    rw [hflag1, hflag2]
    -- (3) Per-key identical-until-bad (brick 3): the `b = true`/`b = false` impls agree on every
    -- non-forged transition (they differ only in the verify return when `ok = true`, which also
    -- sets the flag) and the flag is monotone, so the per-key TV distance is ≤ forge probability.
    have hbad : ∀ ke, tvDist (Y₁ ke) (Y₂ ke) ≤ forgeProb ke := by
      intro ke
      rw [hY₁, hY₂, hforgeProb]
      exact tvDist_authInst_le_probForge se adv ke
    -- (4) Per-key forge bound (forge reduction + brick 1): the forge event reduces to the
    -- eval+verify lazy-RO forgery experiment, bounded by `q_d/|T|` via `hqd`.
    have hforge : ∀ ke, forgeProb ke ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ := by
      intro ke
      rw [hforgeProb]
      exact le_trans (probForge_authInst_le_forgeReduction se adv ke)
        (ToVCVio.probForge_le_queryBound_div_card (forgeReduction se adv ke) q_d
          (forgeReduction_isQueryBoundP se adv ke q_d hqd))
    -- Combine (3)+(4): per-key TV ≤ q_d/|T|.
    have htv_ke : ∀ ke, tvDist (Y₁ ke) (Y₂ ke) ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ :=
      fun ke => le_trans (hbad ke) (hforge ke)
    -- Convexity over the key: a per-key TV bound lifts through the `se.keygen` bind
    -- (`ToVCVio.tvDist_bind_left_le_const`, the real-valued companion of VCVio's
    -- `ofReal_tvDist_bind_left_le_const`).
    exact ToVCVio.tvDist_bind_left_le_const se.keygen Y₁ Y₂ (by positivity) htv_ke
  calc |(Pr[= true | game1 se adv]).toReal - (Pr[= true | game2 se adv]).toReal|
      = |(Pr[= true | game1 se adv]).toReal - (Pr[= true | game2' se adv]).toReal| := by
        rw [hC]
    _ ≤ tvDist (game1 se adv) (game2' se adv) :=
        abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ ↑q_d * (Fintype.card T : ℝ)⁻¹ := htv

omit [Inhabited T] in
/-- Game 2 → 3: IND$-CPA hop. Gap bounded by encryption advantage.

NRS14 Lemma 3, privacy reduction D₁(A). Since `verifyTag = pure false` in
both game2 and game3, no decrypt query ever reaches `se.decrypt`. The
IND$-CPA reduction only needs to simulate encryption (forward to its oracle)
and decryption (always reject). The `computeTag` change from random oracle
to `$ᵗ T` is distributional equality: the cache is written but never read
(verify disabled), and a one-time fresh RO query is uniformly distributed. -/
theorem game2_game3_le_enc [Inhabited K_e]
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    |(Pr[= true | game2 se adv]).toReal -
     (Pr[= true | game3 se adv]).toReal| ≤
      DetSEAlg.distAdvantage se (encReduction se adv) := by
  -- NRS14 Lemma 3, privacy reduction D₁(A).
  -- RO-to-uniform: since verifyTag = pure false in both games, the TagCache
  -- is write-only. A fresh RO query on a never-read input is uniformly
  -- distributed, so replacing randomOracle with $ᵗ T preserves the distribution.
  -- After this substitution, game2 and game3 differ only in encryptMsg:
  --   game2: se.encrypt ke m (real)
  --   game3: $ᵗ C_e (random)
  -- This is exactly the IND$-CPA distinguishing experiment.
  -- game2 = DetSEAlg.securityExpFixedBit se (encReduction se adv) false
  -- game3 = DetSEAlg.securityExpFixedBit se (encReduction se adv) true
  --
  -- Discovered proof path (both directions are probOutput equalities, then `abs_sub_comm`):
  --   `securityExpFixedBit se (encReduction se adv) b` unfolds to a NESTED simulateQ:
  --   `simulateQ (indCPAImpl se b k) (encReduction…)`, where `encReduction` itself is
  --   `simulateQ encRedImpl adv` over `EtmGameState`. Collapse the nesting with
  --   `simulateQ_mapStateTBase_run` (VCVio `…/SimSemantics/StateT/Basic.lean`):
  --     simulateQ outer ((simulateQ inner oa).run s)
  --       = (simulateQ (outer.mapStateTBase inner) oa).run s
  --   giving a SINGLE `simulateQ (indCPAImpl.mapStateTBase encRedImpl) adv` over state
  --   `EtmGameState` with base monad `StateT Bool ProbComp` (the Bool = indCPA "encrypt
  --   called" flag). Split the leading `se.keygen` with `simulateQ_bind` +
  --   `simulateQ_liftComp` (forwarded). Then relate the combined impl to game3's impl via
  --   the invariant-gated projection `map_run_simulateQ_eq_of_query_map_eq_inv'`, with
  --   invariant `Bool = challenge.isSome` (the indCPA flag stays in sync with the skeleton's
  --   one-time challenge), projecting the Bool away.
  --   game3 direction: clean (encRedImpl tag = $ᵗ T already matches game3). game2 direction:
  --   additionally needs RO→uniform (game2's randomOracle tag = encRedImpl's $ᵗ T), justified
  --   as in `stepA` below (write-only cache, one-time fresh query uniform).
  have hg3 : Pr[= true | game3 se adv] =
      Pr[= true | DetSEAlg.securityExpFixedBit se (encReduction se adv) true] := by
    unfold DetSEAlg.securityExpFixedBit encReduction etmGameSkeleton
    -- Nested simulateQ collapses to a single `simulateQ (indCPAImpl.mapStateTBase encRedImpl)`.
    -- (Do the collapse alone — adding StateT.run_* here blocks `mapStateTBase_run` from firing.)
    simp only [simulateQ_bind, simulateQ_pure, pure_bind,
      QueryImpl.simulateQ_mapStateTBase_run]
    simp only [bind_pure_comp, ← StateT.run'_eq]
    unfold game3 etmGameSkeleton
    simp only [bind_pure_comp, ← StateT.run'_eq]
    refine probOutput_bind_congr' se.keygen true (fun key => ?_)
    -- Flatten the nested `StateT EtmGameState (StateT Bool ProbComp)` into a single
    -- `StateT (EtmGameState × Bool) ProbComp` (the indCPA "encrypt called" flag joins the state).
    conv_rhs => rw [StateT.run'_eq _ (none, ∅)]
    rw [← simulateQ_flattenStateT_run']
    -- Project the joint `(EtmGameState × Bool)` state back to `EtmGameState`, dropping the
    -- indCPA flag, under the invariant `flag = challenge.isSome`. The flattened reduction impl
    -- then agrees per-query with game3's impl, so the simulations coincide (impl₂ unifies with
    -- game3's oracle impl on the LHS).
    -- Forwarding helper (shared by `hinv`/`hproj`): the IND$-CPA outer impl passes a lifted
    -- `unifSpec` *computation* through unchanged (its uniform oracle is the identity; the
    -- indCPA flag is threaded).
    rw [← run'_simulateQ_eq_of_query_map_eq_inv'
          _ _ (fun s => s.2 = s.1.1.isSome) Prod.fst ?hinv ?hproj adv ((none, ∅), false) ?hs]
    case hs => rfl
    case hinv =>
      -- Each query preserves `flag = challenge.isSome`: the unif and decrypt oracles leave both
      -- `challenge` and the flag untouched; the one-time encryption query sets `challenge` to
      -- `some` and flips the indCPA flag to `true` in the same step.
      intro t s hs y hy
      obtain ⟨⟨ch, qc⟩, b⟩ := s
      simp only at hs
      subst hs
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
      · -- uniform-sampling oracle: state + flag unchanged
        have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            (liftM (OracleSpec.query n) :
              OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
            = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
          ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
            (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
        simp only [add_apply_inl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
          StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
          bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
          QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
          simulateQ_map, hq, StateT.run_mk, StateT.run_map, Functor.map_map, support_map,
          support_liftM, OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
          Set.image_univ] at hy
        obtain ⟨_, rfl⟩ := hy
        rfl
      · -- encryption oracle: challenge none→some sets the flag to true alongside
        have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            ((liftM ($ᵗ T : ProbComp T) :
                StateT (TagCache AD C_e T)
                  (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
            = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
          ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
            ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
        cases ch with
        | none =>
          simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk,
            Option.isSome_none, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
            simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
            DetSEAlg.oracleEncrypt, ↓reduceIte, map_bind, id_map, simulateQ_map, Bool.false_eq_true,
            simulateQ_pure, hqT, liftM_map, support_bind, support_uniformSample, Set.mem_univ,
            support_map, Set.image_univ, Set.iUnion_true] at hy
          obtain ⟨_, ⟨x, rfl⟩, a, rfl⟩ := hy
          rfl
        | some v =>
          simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk,
            Option.isSome_some, simulateQ_pure, map_pure, support_pure] at hy
          subst hy; rfl
      · -- decryption oracle: `verifyTag = pure false` rejects; state + flag unchanged
        cases ch with
        | none =>
          simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_none,
            reduceCtorEq, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
            support_pure] at hy
          subst hy; rfl
        | some v =>
          simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_some,
            Option.some.injEq, support_map] at hy
          split_ifs at hy <;>
            (simp only [StateT.run_map, StateT.run_set, map_pure, simulateQ_pure, StateT.run_pure,
              support_pure, Set.image_singleton] at hy
             obtain rfl := Set.eq_of_mem_singleton hy
             rfl)
    case hproj =>
      -- Per-query agreement: the flattened reduction impl, projected onto `EtmGameState`
      -- (dropping the indCPA flag), equals game3's oracle impl on states satisfying the invariant.
      intro t s hs
      obtain ⟨⟨ch, qc⟩, b⟩ := s
      simp only at hs
      subst hs
      rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
      · -- uniform-sampling oracle: forward the lifted sample, flag threaded unchanged
        have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            (liftM (OracleSpec.query n) :
              OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
            = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
          ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
            (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
        simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
          DetSEAlg.oracleUnif, gameUnifImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          hq, StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
      · -- encryption oracle: `oracleEncrypt true` samples `$ᵗ C_e` and sets the flag, matching
        -- game3's encrypt (challenge none→some); the `$ᵗ T` tag is forwarded unchanged
        have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
              se.oracleEncrypt true key)
            ((liftM ($ᵗ T : ProbComp T) :
                StateT (TagCache AD C_e T)
                  (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
            = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
          ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
            ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
        cases ch <;>
          simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
            DetSEAlg.oracleEncrypt, DetSEAlg.oracleUnif, QueryImpl.add_apply_inl,
            QueryImpl.add_apply_inr, hqT,
            StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
      · -- decryption oracle: `verifyTag = pure false` rejects; state and flag unchanged
        cases ch <;>
          simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, QueryImpl.add_apply_inr,
            StateT.run_bind, StateT.run_get, StateT.run_set,
            StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
        split_ifs <;>
          simp [StateT.run_set, StateT.run_pure]
  have hg2 : Pr[= true | game2 se adv] =
      Pr[= true | DetSEAlg.securityExpFixedBit se (encReduction se adv) false] := by
    -- Step A (RO→uniform): replace game2's random-oracle tag with a fresh `$ᵗ T`. The cache is
    -- write-only (`verifyTag = pure false`) and the single encryption query hits a fresh point,
    -- so the tag is uniform; project the cache away (invariant `challenge = none → cache = ∅`).
    have stepA : Pr[= true | game2 se adv] =
        Pr[= true | (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
            (fun ke m => pure (se.encrypt ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
            (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool)] := by
      unfold game2 etmGameSkeleton
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine probOutput_bind_congr' se.keygen true (fun key => ?_)
      rw [run'_simulateQ_eq_of_query_map_eq_inv'
            _ _ (fun s => s.1 = none → s.2 = (∅ : TagCache AD C_e T))
            (fun s => (s.1, (∅ : TagCache AD C_e T))) ?hinv ?hproj adv (none, ∅) ?hs]
      case hs => intro _; rfl
      case hinv =>
        intro t s hs y hy
        obtain ⟨ch, qc⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: state unchanged, so `inv` is preserved (= `hs`)
          simp only [add_apply_inl, gameUnifImpl, QueryImpl.ofLift_eq_id', StateT.run_pure,
            liftM_pure, QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, Prod.mk.eta, beq_iff_eq, Bool.false_eq_true, ↓reduceIte,
            QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
            StateT.run_monadLift, monadLift_self, support_map, support_liftM,
            OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hy
          obtain ⟨_, rfl⟩ := hy
          exact hs
        · -- encryption oracle: challenge becomes `some`, so `inv` holds vacuously
          cases ch with
          | none =>
            have hqc : qc = (∅ : TagCache AD C_e T) := hs rfl
            subst hqc
            simp only [add_apply_inl, add_apply_inr, StateT.run_pure, liftM_pure,
              QueryImpl.withCaching_apply, uniformSampleImpl, StateT.run_bind, StateT.run_get,
              pure_bind, bind_pure_comp, Prod.mk.eta, beq_iff_eq, Bool.false_eq_true, ↓reduceIte,
              QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_monadLift,
              monadLift_self, StateT.run_modifyGet, Functor.map_map, liftM_map, bind_map_left,
              StateT.run_map, StateT.run_set, map_pure, support_map, support_uniformSample,
              Set.image_univ] at hy
            obtain ⟨a, rfl⟩ := hy
            simp
          | some v =>
            simp only [add_apply_inl, add_apply_inr, StateT.run_pure, liftM_pure,
              QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get, pure_bind,
              bind_pure_comp, Prod.mk.eta, beq_iff_eq, Bool.false_eq_true, ↓reduceIte,
              QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, support_pure] at hy
            obtain rfl := Set.eq_of_mem_singleton hy
            simp
        · -- decryption oracle: `verifyTag = pure false` rejects; state unchanged (= `hs`)
          cases ch with
          | none =>
            simp only [add_apply_inr, StateT.run_pure, liftM_pure, QueryImpl.withCaching_apply,
              StateT.run_bind, StateT.run_get, pure_bind, bind_pure_comp, Prod.mk.eta, beq_iff_eq,
              Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inr, reduceCtorEq, StateT.run_map,
              StateT.run_set, map_pure, support_pure] at hy
            obtain rfl := Set.eq_of_mem_singleton hy; exact hs
          | some v =>
            simp only [add_apply_inr, StateT.run_pure, liftM_pure, QueryImpl.withCaching_apply,
              StateT.run_bind, StateT.run_get, pure_bind, bind_pure_comp, Prod.mk.eta, beq_iff_eq,
              Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inr, Option.some.injEq] at hy
            split_ifs at hy <;>
              (obtain rfl := Set.eq_of_mem_singleton hy; exact hs)
      case hproj =>
        intro t s hs
        obtain ⟨ch, qc⟩ := s
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: state threaded unchanged on both sides, cache reset by proj
          simp [gameUnifImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
            StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
        · -- encryption oracle: at `ch = none` the cache is `∅` (invariant), so the random oracle
          -- query is fresh and equals `$ᵗ T`, matching the `$ᵗ T`-tag skeleton; the cache write
          -- is dropped by proj
          cases ch with
          | none =>
            have hqc : qc = (∅ : TagCache AD C_e T) := hs rfl
            subst hqc
            simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_set, StateT.run_monadLift, StateT.run_pure,
              uniformSampleImpl, Prod.map, Functor.map_map]
          | some v =>
            simp [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
              StateT.run_get, StateT.run_monadLift, StateT.run_pure, Prod.map]
        · -- decryption oracle: `verifyTag = pure false` rejects; state unchanged, cache untouched
          cases ch <;>
            simp [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, Prod.map]
          split_ifs <;>
            simp [StateT.run_set, StateT.run_pure, Prod.map]
    -- Step B (`hg3` machinery at `b = false`): the `$ᵗ T`-tag game equals the IND$-CPA real
    -- experiment, since `oracleEncrypt false key m = se.encrypt key m` matches the game's encrypt.
    have stepB : Pr[= true | (etmGameSkeleton (spec := unifSpec) se.keygen se.decrypt ∅
            (fun ke m => pure (se.encrypt ke m)) (fun _ => liftM ($ᵗ T : ProbComp T))
            (fun _ _ => pure false) gameUnifImpl adv : ProbComp Bool)] =
        Pr[= true | DetSEAlg.securityExpFixedBit se (encReduction se adv) false] := by
      unfold DetSEAlg.securityExpFixedBit encReduction etmGameSkeleton
      simp only [simulateQ_bind, simulateQ_pure, pure_bind,
        QueryImpl.simulateQ_mapStateTBase_run]
      simp only [bind_pure_comp, ← StateT.run'_eq]
      refine probOutput_bind_congr' se.keygen true (fun key => ?_)
      conv_rhs => rw [StateT.run'_eq _ (none, ∅)]
      rw [← simulateQ_flattenStateT_run']
      rw [← run'_simulateQ_eq_of_query_map_eq_inv'
            _ _ (fun s => s.2 = s.1.1.isSome) Prod.fst ?hinv ?hproj adv ((none, ∅), false) ?hs]
      case hs => rfl
      case hinv =>
        intro t s hs y hy
        obtain ⟨⟨ch, qc⟩, b⟩ := s
        simp only at hs
        subst hs
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: state + flag unchanged
          have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              (liftM (OracleSpec.query n) :
                OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
              = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
            ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
              (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
          simp only [add_apply_inl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
            bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
            QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
            simulateQ_map, hq, StateT.run_mk, StateT.run_map, Functor.map_map, support_map,
            support_liftM, OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
            Set.image_univ] at hy
          obtain ⟨_, rfl⟩ := hy
          rfl
        · -- encryption oracle: challenge none→some sets the flag to true alongside
          have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              ((liftM ($ᵗ T : ProbComp T) :
                  StateT (TagCache AD C_e T)
                    (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
              = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
            ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
              ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
          cases ch with
          | none =>
            simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif,
              QueryImpl.ofLift_eq_id', StateT.run_bind, StateT.run_monadLift, monadLift_self,
              bind_pure_comp, bind_map_left, liftM_bind, bind_assoc, Prod.mk.eta, beq_iff_eq,
              StateT.run_pure, liftM_pure, ite_self, pure_bind, QueryImpl.add_apply_inl,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_none,
              StateT.run_map, StateT.run_set, map_pure, Functor.map_map, simulateQ_bind,
              simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
              DetSEAlg.oracleEncrypt, Bool.false_eq_true, ↓reduceIte, map_bind, id_map,
              simulateQ_map, simulateQ_pure, hqT, liftM_map, support_map, support_uniformSample,
              Set.image_univ] at hy
            obtain ⟨a, rfl⟩ := hy
            rfl
          | some v =>
            simp only [add_apply_inl, add_apply_inr, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif,
              QueryImpl.ofLift_eq_id', StateT.run_bind, StateT.run_monadLift, monadLift_self,
              bind_pure_comp, bind_map_left, liftM_bind, bind_assoc, Prod.mk.eta, beq_iff_eq,
              StateT.run_pure, liftM_pure, ite_self, pure_bind, QueryImpl.add_apply_inl,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_some,
              simulateQ_pure, map_pure, support_pure] at hy
            obtain rfl := Set.eq_of_mem_singleton hy; rfl
        · -- decryption oracle: `verifyTag = pure false` rejects; state + flag unchanged
          cases ch with
          | none =>
            simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
              DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
              StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
              bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_none,
              reduceCtorEq, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
              support_pure] at hy
            subst hy; rfl
          | some v =>
            simp only [add_apply_inr, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
              DetSEAlg.indCPAImpl, DetSEAlg.oracleUnif, QueryImpl.ofLift_eq_id', StateT.run_bind,
              StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left, liftM_bind,
              bind_assoc, Prod.mk.eta, beq_iff_eq, StateT.run_pure, liftM_pure, ite_self, pure_bind,
              QueryImpl.add_apply_inr, StateT.run_get, StateT.run_mk, Option.isSome_some,
              Option.some.injEq, support_map] at hy
            split_ifs at hy <;>
              (simp only [StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
                  StateT.run_pure, support_pure, Set.image_singleton] at hy
               obtain rfl := Set.eq_of_mem_singleton hy
               rfl)
      case hproj =>
        intro t s hs
        obtain ⟨⟨ch, qc⟩, b⟩ := s
        simp only at hs
        subst hs
        rcases t with (n | ⟨ad, m⟩) | ⟨ad, c⟩
        · -- uniform-sampling oracle: forward the lifted sample, flag threaded unchanged
          have hq : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              (liftM (OracleSpec.query n) :
                OracleComp (unifSpec + (M →ₒ Option C_e)) (unifSpec.Range n))
              = liftM (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n)) :=
            ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
              (liftM (OracleSpec.query n) : OracleComp unifSpec (unifSpec.Range n))
          simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
            DetSEAlg.oracleUnif, gameUnifImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
            hq, StateT.run_bind, StateT.run_monadLift, Prod.map, Functor.map_map]
        · -- encryption oracle: `oracleEncrypt false key m = se.encrypt key m` matches the game;
          -- the `$ᵗ T` tag is forwarded unchanged
          have hqT : simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT Bool ProbComp) +
                se.oracleEncrypt false key)
              ((liftM ($ᵗ T : ProbComp T) :
                  StateT (TagCache AD C_e T)
                    (OracleComp (unifSpec + (M →ₒ Option C_e))) T).run qc)
              = liftM ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T)) :=
            ToVCVio.simulateQ_id'_liftTarget_add_liftComp _
              ((fun t => (t, qc)) <$> ($ᵗ T : ProbComp T))
          cases ch <;>
            simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, DetSEAlg.indCPAImpl,
              DetSEAlg.oracleEncrypt, DetSEAlg.oracleUnif, QueryImpl.add_apply_inl,
              QueryImpl.add_apply_inr, hqT, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
        · -- decryption oracle: `verifyTag = pure false` rejects; state and flag unchanged
          cases ch <;>
            simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, QueryImpl.add_apply_inr,
              StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_monadLift, StateT.run_pure, Prod.map, Functor.map_map]
          split_ifs <;>
            simp [StateT.run_set, StateT.run_pure]
    rw [stepA, stepB]
  unfold DetSEAlg.distAdvantage
  rw [hg2, hg3]
  exact le_of_eq (abs_sub_comm _ _)

omit [Inhabited C_e] [Inhabited T] in
/-- Game 3 equals the random AEAD experiment.

The hypothesis `hkm` says `prf.keygen` never fails (`Pr[⊥ | prf.keygen] = 0`). It is
needed because the `b = true` (random) experiment samples `km ← prf.keygen` whereas
`game3` does not — `km` is dead code once encryption is randomized and decryption always
rejects. Dropping a bind of a computation that can fail rescales the output probability by
`(1 - Pr[⊥ | prf.keygen])` (`probOutput_bind_const`), so the two experiments coincide
exactly only when `prf.keygen` is lossless. Every real PRF keygen (`$ᵗ K`) satisfies this. -/
theorem game3_eq_rand
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    (hkm : Pr[⊥ | prf.keygen] = 0) :
    Pr[= true | game3 se adv] =
      Pr[= true | AEADScheme.securityExpFixedBit (etmAEAD se prf) adv true] := by
  -- NRS14 Figure 4, right column: ideal nAE experiment.
  have hkg : (etmAEAD se prf).keygen
      = (se.keygen >>= fun ke => prf.keygen >>= fun km =>
          (pure (ke, km) : ProbComp (K_e × K_m))) := rfl
  unfold game3 etmGameSkeleton AEADScheme.securityExpFixedBit
  rw [hkg]
  simp only [bind_assoc, pure_bind]
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Both sides start with `se.keygen`; descend it.
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  -- RHS samples a dead `km`; its body is constant in `km` (= the LHS value by projection).
  rw [probOutput_bind_of_const prf.keygen
        (my := fun km => (simulateQ (AEADScheme.aeadSecurityImpl (etmAEAD se prf)
          true (ke, km)) adv).run' none)
        (fun km _ => congrArg (fun o => Pr[= true | o])
          (run'_simulateQ_eq_of_query_map_eq _
            (AEADScheme.aeadSecurityImpl (etmAEAD se prf) true (ke, km))
            Prod.fst ?_ adv ((none, ∅) : EtmGameState AD C_e T)).symm)]
  · -- `prf.keygen` is lossless, so the `(1 - Pr[⊥]) ·` factor is `1`; `rfl` pins `impl₁`.
    rw [hkm, tsub_zero, one_mul]
  · -- per-query projection (`impl₁` now pinned to game3's oracle implementation)
    intro t s
    obtain ⟨ch, qc⟩ := s
    rcases t with (n | am) | ac
    · -- uniform-sampling oracle
      simp [AEADScheme.aeadSecurityImpl, gameUnifImpl, AEADScheme.oracleUnif,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, Prod.map]
    · -- encryption oracle: random `(c, t)` vs `$ᵗ (C_e × T)` (product sampling)
      obtain ⟨ad, m⟩ := am
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleEncrypt, etmAEAD,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          uniformSample_prod_eq_bind, bind_assoc, map_pure, Prod.map]
    · -- decryption oracle: both always reject
      obtain ⟨ad, c, t⟩ := ac
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleDecrypt, etmAEAD,
          QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          map_pure, Prod.map]
      split_ifs <;> simp [StateT.run_set, StateT.run_pure, map_pure, Prod.map]

/-! ## Main security theorem -/

/-- **EtM one-time IND-CCA security** (NRS14 Theorem 1 for A5, adapted).

The one-time IND-CCA distinguishing advantage of `etmAEAD se prf` is bounded
by the PRF advantage, the tag-guessing probability per decryption query, and
the IND$-CPA advantage:

  `Adv^{ot-cca-ror}_{EtM}(A) ≤ Adv^{prf}(B) + q_d/|T| + Adv^{ind$}(D)`

where `B = prfReduction se adv` and `D = encReduction se adv` are explicit
reductions (skeleton instantiations), and `q_d` upper-bounds the adversary's
number of decryption queries (tied to `adv` via `decryptQueryBound`, i.e.
`IsQueryBoundP` on the decrypt-oracle index).

NRS14 Figure 9 bound: `Adv^nAE ≤ Adv^prf_F(B) + Adv^ivE_E(D₁) + q_d/2^τ`.
Our one-time adaptation: `Adv^ivE → Adv^{ind$-cpa}`, `2^τ → |T|`. -/
theorem etmAEAD_security [Inhabited K_e]
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d)
    (hkm : Pr[⊥ | prf.keygen] = 0) :
    AEADScheme.distAdvantage (etmAEAD se prf) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) +
      ↑q_d * (Fintype.card T : ℝ)⁻¹ +
      DetSEAlg.distAdvantage se (encReduction se adv) := by
  -- NRS14 Theorem 1 / Figure 9: triangle inequality over the game sequence.
  -- distAdvantage = |Pr[rand = 1] - Pr[real = 1]|
  --              = |Pr[game3 = 1] - Pr[game0 = 1]|    (by game0_eq_real, game3_eq_rand)
  -- By triangle inequality:
  --   |game3 - game0| ≤ |game0 - game1| + |game1 - game2| + |game2 - game3|
  -- Substituting the three hop bounds gives the result.
  unfold AEADScheme.distAdvantage
  rw [← game3_eq_rand se prf adv hkm, ← game0_eq_real se prf adv]
  calc |(Pr[= true | game3 se adv]).toReal -
        (Pr[= true | game0 se prf adv]).toReal|
    _ ≤ |(Pr[= true | game0 se prf adv]).toReal -
         (Pr[= true | game1 se adv]).toReal| +
        |(Pr[= true | game1 se adv]).toReal -
         (Pr[= true | game2 se adv]).toReal| +
        |(Pr[= true | game2 se adv]).toReal -
         (Pr[= true | game3 se adv]).toReal| := by
          set g0 := (Pr[= true | game0 se prf adv]).toReal
          set g1 := (Pr[= true | game1 se adv]).toReal
          set g2 := (Pr[= true | game2 se adv]).toReal
          set g3 := (Pr[= true | game3 se adv]).toReal
          have h1 := abs_sub_le g3 g2 g0
          have h2 := abs_sub_le g2 g1 g0
          have h3 : |g2 - g3| = |g3 - g2| := abs_sub_comm g2 g3
          have h4 : |g1 - g2| = |g2 - g1| := abs_sub_comm g1 g2
          have h5 : |g0 - g1| = |g1 - g0| := abs_sub_comm g0 g1
          linarith
    _ ≤ PRFScheme.prfAdvantage prf (prfReduction se adv) +
        ↑q_d * (Fintype.card T : ℝ)⁻¹ +
        DetSEAlg.distAdvantage se (encReduction se adv) :=
      add_le_add (add_le_add (game0_game1_le_prf se prf adv)
        (game1_game2_le_auth se adv q_d hqd)) (game2_game3_le_enc se adv)
