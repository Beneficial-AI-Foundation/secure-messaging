/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Games
import SecureMessaging.AEAD.FromGCM.Security.Counter
import SecureMessaging.AEAD.FromGCM.Security.CipherProfile
import ToVCVio.OracleComp.Constructions.BitVec
import ToVCVio.OracleComp.QueryTracking.RandomOracle.FreshQueries
import VCVio.OracleComp.QueryTracking.Iter
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# GCM: the PRF hop (`game0` → `game1`)

Replacing the block cipher's outputs by uniform values costs the pseudorandom-function (PRF)
advantage of one explicit distinguisher, `prfReduction`. The distinguisher queries its
function oracle at the `⌈L/128⌉ + 2` inputs GCM uses (GHASH key, tag mask, keystream blocks)
before running the adversary, so its query list is fixed and independent of the adversary.

Main results:
- `game0_eq_prfRealExp`, `game1_eq_prfIdealExp`: with a real cipher the distinguisher runs
  `game0`, with a random function it runs `game1`.
- `game0_game1_le_prf`: hence `|Pr[game1] − Pr[game0]|` is at most its PRF advantage.
- `game1_eq_game2`: moving the tuple sample inside the oracles changes nothing.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational

/-! ## The eager PRF reduction -/

/-- The PRF distinguisher built from a GCM adversary. It fetches the GHASH key at `0`, the tag
mask at `j0 iv` and the `⌈L/128⌉` keystream blocks along the counter chain from its function
oracle, then runs `adv` against `gcmTupleImpl` at that tuple; the tail makes no further
function-oracle query. Fetching everything up front keeps the query count fixed at
`⌈L/128⌉ + 2`, whatever the adversary does. -/
-- The outer ascription to `OracleComp (PRFOracleSpec …) Bool` is required: `PRFAdversary`
-- is a two-argument abbrev whose *second* argument is the oracle range, not the return
-- type, so `do`-notation would otherwise unify the monad with `PRFAdversary (BitVec 128)`
-- and fail to find `Monad`/`MonadLiftT` instances.
noncomputable def prfReduction (iv : BitVec 96) (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.PRFAdversary (BitVec 128) (BitVec 128) :=
  (do
    let h ← liftM (OracleSpec.query (Sum.inr (0 : BitVec 128)) :
        OracleQuery (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) (BitVec 128))
    let mask ← liftM (OracleSpec.query (Sum.inr (j0 iv)) :
        OracleQuery (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) (BitVec 128))
    let blocks ← (counterChain (inc32 (j0 iv)) ((L + 127) / 128)).mapM
      (fun t => liftM (OracleSpec.query (Sum.inr t) :
        OracleQuery (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) (BitVec 128)))
    OracleComp.liftComp
      ((simulateQ (gcmTupleImpl (h, mask, blocksToBitVec blocks L)) adv).run' none)
      (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) :
    OracleComp (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) Bool)

/-! ## Profile-to-tuple bridges

`CipherProfile.lean` describes encryption and decryption with the keystream as a list of
blocks; the games carry it flattened to `L` bits. The two agree at `blocksToBitVec`. -/

section Bridges

variable {L : ℕ}

/-- `keystream`, the NIST SP 800-38D §6.5 formula `MSB_p(blocks[0] ‖ blocks[1] ‖ …)`, is
`blocksToBitVec` at block width 128. -/
theorem keystream_eq_blocksToBitVec (blocks : List (BitVec 128)) (p : ℕ) :
    keystream blocks p = blocksToBitVec blocks p :=
  rfl

lemma gcmEncryptSpec_eq_tuple (h mask : BitVec 128)
    (ksBlocks : List (BitVec 128)) (ad : SupportedAAD) (m : BitVec L) :
    gcmEncryptSpec h mask ksBlocks ad.1.2 m =
      (m ^^^ blocksToBitVec ksBlocks L,
       ghash h (gcmEncode ad (m ^^^ blocksToBitVec ksBlocks L)) ^^^ mask) := by
  simp only [gcmEncryptSpec, keystream_eq_blocksToBitVec, gcmEncode]

-- The trailing `rfl` closes an `ite`-instance-level difference only: after
-- `simp only` both sides print identically, but the `Decidable` arguments of the two
-- `ite`s are not syntactically equal.
lemma gcmDecryptSpec_eq_tuple (h mask : BitVec 128)
    (ksBlocks : List (BitVec 128)) (ad : SupportedAAD) (ct : BitVec L × BitVec 128) :
    gcmDecryptSpec h mask ksBlocks ad.1.2 ct =
      if ct.2 = ghash h (gcmEncode ad ct.1) ^^^ mask
      then some (ct.1 ^^^ blocksToBitVec ksBlocks L) else none := by
  simp only [gcmDecryptSpec, keystream_eq_blocksToBitVec, gcmEncode]
  rfl

end Bridges

/-! ## `game1 = game2`: the lazy-sampling hop -/

section LazyHop

variable {K : Type}

/-- Sampling the tuple up front or at the adversary's first query gives the same
distribution. -/
theorem game1_eq_game2 (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    evalDist (game1 prp L hL adv) = evalDist (game2 prp L hL adv) := by
  unfold game1 game2
  exact probOutput_simulateQ_greedyLazy_run'_eq gcmTupleImpl adv none

end LazyHop

/-! ## The real-side projection: `game0` = `prfRealExp (prfReduction …)` -/

section RealProjection

variable {K : Type}

/-- At a fixed key, the real scheme's oracles are `gcmTupleImpl` at the tuple of the cipher's
outputs on GCM's inputs. -/
lemma run'_game0Impl_eq_tupleImpl (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L) (k : K)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    (simulateQ (gcmGameSkeleton (spec := unifSpec)
        (fun ad m => pure ((gcmOneTimeAEAD prp iv L hL).encrypt k ad m))
        (fun ad e => pure ((gcmOneTimeAEAD prp iv L hL).decrypt k ad e))
        (oracleUnif (BitVec L × BitVec 128))) adv).run' none =
      (simulateQ (gcmTupleImpl (prp.toBlockCipher.perm k 0,
        prp.toBlockCipher.perm k (j0 iv),
        blocksToBitVec ((counterChain (inc32 (j0 iv)) ((L + 127) / 128)).map
          (prp.toBlockCipher.perm k)) L)) adv).run' none := by
  refine run'_simulateQ_eq_of_query_map_eq _ _ id ?hproj adv none
  case hproj =>
    intro t s
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
    · -- OUnif: both handlers are the lifted uniform oracle, state threaded unchanged.
      simp [gcmGameSkeleton, gcmTupleImpl, oracleUnif, unifLiftStateT,
        StateT.run_monadLift, Functor.map_map]
    · -- OEncrypt: one-shot; the real cipher body becomes the tuple body by
      -- profile + encryption bridge.
      cases s <;>
        simp [gcmGameSkeleton, gcmTupleImpl, StateT.run_bind, StateT.run_get,
          StateT.run_set, StateT.run_pure, map_pure,
          gcmOneTimeAEAD_encrypt_profile prp iv hL k, gcmEncryptSpec_eq_tuple]
    · -- ODecrypt: shared challenge guard; the live verification body becomes the tuple
      -- body by profile + decryption bridge.
      simp [gcmGameSkeleton, gcmTupleImpl, StateT.run_bind, StateT.run_get,
        gcmOneTimeAEAD_decrypt_profile prp iv hL k, gcmDecryptSpec_eq_tuple]

theorem game0_eq_prfRealExp (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    Pr[= true | game0 prp iv L hL adv] =
      Pr[= true | (prp.toPRFScheme).prfRealExp (prfReduction iv L adv)] := by
  -- Keygen alignment is definitional: `toPRFScheme` keeps `keygen` and sets `eval := perm`.
  have hkg : (prp.toPRFScheme).keygen = prp.keygen := rfl
  unfold game0 PRFScheme.prfRealExp prfReduction
  rw [hkg]
  -- Collapse the eager fetches (`H`, `mask`, the keystream block list) and erase the
  -- `liftComp` on the closed tail. `simp only` is mandatory here: full `simp` would first
  -- apply `simulateQ_spec_query` and reduce past the forwarding lemmas.
  simp only [simulateQ_bind, simulateQ_list_mapM, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, PRFScheme.prfRealQueryImpl_apply_inr, map_pure, id_eq,
    List.mapM_pure, PRFScheme.simulateQ_prfRealQueryImpl_liftComp, pure_bind]
  -- Both sides are now the same `prp.keygen` bind; descend and project per key.
  refine probOutput_bind_congr' prp.keygen true (fun k => ?_)
  exact congrArg (fun o => Pr[= true | o]) (run'_game0Impl_eq_tupleImpl prp iv L hL k adv)

end RealProjection

/-! ## The ideal-side cache peel

VCVio's ideal PRF is a lazily sampled random function: a query at a new point draws a fresh
uniform value, a repeated point returns the cached one. The `⌈L/128⌉ + 2` query points are
pairwise distinct (`cipherInputs_pairwise_ne`), so every query is fresh. This is one of the two
places `hL` enters the PRF hop: `inc32` wraps modulo `2³²`, and for a long enough message the
counter chain would repeat a point and the peel would return a cached value instead of a fresh
draw. The other is the real-side decrypt projection above, where `gcmDecrypt`'s length check
must pass (`gcmOneTimeAEAD_decrypt_profile`). -/

section IdealPeel

/-- A random-oracle query at a point not in the cache is a fresh uniform draw, after which the
continuation runs from the extended cache. -/
private lemma run'_randomOracle_bind_of_none {D R β : Type} [DecidableEq D] [SampleableType R]
    (t : D) (c : (D →ₒ R).QueryCache) (hc : c t = none)
    (G : R → StateT ((D →ₒ R).QueryCache) ProbComp β) :
    (((D →ₒ R).randomOracle t >>= G : StateT ((D →ₒ R).QueryCache) ProbComp β)).run' c =
      ($ᵗ R : ProbComp R) >>= fun u => (G u).run' (c.cacheQuery t u) := by
  rw [StateT.run'_eq, StateT.run_bind,
    QueryImpl.withCaching_run_none uniformSampleImpl hc]
  simp [bind_map_left, StateT.run'_eq]

/-- In the ideal PRF experiment, `prfReduction`'s `⌈L/128⌉ + 2` queries are answered by that
many independent uniform draws. `hL` makes the query points distinct; for a message long
enough to wrap the 32-bit counter a repeated point returns its cached value and the
statement is false. -/
lemma prfIdealExp_prfReduction_eq (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.prfIdealExp (prfReduction iv L adv) =
      (($ᵗ (BitVec 128) : ProbComp _) >>= fun h =>
       ($ᵗ (BitVec 128) : ProbComp _) >>= fun mask =>
       (counterChain (inc32 (j0 iv)) ((L + 127) / 128)).mapM
         (fun _ => ($ᵗ (BitVec 128) : ProbComp _)) >>= fun blocks =>
       (simulateQ (gcmTupleImpl (h, mask, blocksToBitVec blocks L)) adv).run' none) := by
  unfold PRFScheme.prfIdealExp prfReduction
  -- Collapse the eager fetches to random-oracle calls and erase the `liftComp` on the
  -- closed tail. `simp only` is mandatory: full `simp` would reduce past the forwarding
  -- lemmas via `simulateQ_spec_query`.
  simp only [simulateQ_bind, simulateQ_list_mapM, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, PRFScheme.prfIdealQueryImpl_apply_inr, id_map,
    PRFScheme.simulateQ_prfIdealQueryImpl_liftComp]
  -- The peels are applied in term mode (`Eq.trans`), not by `rw`: in the goal the bound
  -- variable's type is the reducible `(PRFOracleSpec _ _).Range (Sum.inr _)`, so keyed
  -- matching would have to solve `Range (Sum.inr ?d) =?= BitVec 128`. Term elaboration
  -- unifies up to definitional unfolding.
  -- Peel 1: the hash-key fetch at `0`, against the empty cache.
  refine Eq.trans (run'_randomOracle_bind_of_none (0 : BitVec 128) ∅
    (QueryCache.empty_apply _) _) ?_
  refine bind_congr fun h => ?_
  -- Peel 2: the tag-mask fetch at `J₀`; `J₀ ≠ 0`, so the entry just written is invisible.
  have h10 : ((∅ : (BitVec 128 →ₒ BitVec 128).QueryCache).cacheQuery 0 h) (j0 iv) = none := by
    rw [QueryCache.cacheQuery_of_ne _ _ (j0_ne_zero iv)]
    exact QueryCache.empty_apply _
  refine Eq.trans (run'_randomOracle_bind_of_none (j0 iv) _ h10 _) ?_
  refine bind_congr fun mask => ?_
  -- The keystream loop: `0 :: J₀ :: counterChain (inc₃₂ J₀) ⌈L/128⌉` is `Pairwise (· ≠ ·)`, whose
  -- three components are what the fresh-queries lemma asks for: the tail-of-tail
  -- `Pairwise` is the chain's `Nodup`, and the two head clauses give freshness of every
  -- chain point against the two cached entries.
  have hpw := cipherInputs_pairwise_ne iv hL
  rw [List.pairwise_cons] at hpw
  obtain ⟨h0, hpw⟩ := hpw
  rw [List.pairwise_cons] at hpw
  obtain ⟨h1, hnd⟩ := hpw
  refine randomOracle.run'_mapM_randomOracle_fresh _ _ hnd ?_ _
  intro t ht
  rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm (h1 t ht)),
    QueryCache.cacheQuery_of_ne _ _ (Ne.symm (h0 t (List.mem_cons_of_mem _ ht)))]
  exact QueryCache.empty_apply _

end IdealPeel

/-! ## The ideal-side projection: `game1` = `prfIdealExp (prfReduction …)`

After the peel, the ideal experiment draws `⌈L/128⌉` uniform keystream blocks where `game1`
draws one uniform `BitVec L`; concatenating independent uniform blocks and truncating to `L`
bits is uniform (`evalDist_blocksToBitVec_uniform`). Truncation is not injective, so this
step is an equality of distributions, not of terms. -/

section IdealProjection

variable {K : Type}

/-- Drawing `⌈L/128⌉` uniform blocks and flattening them to `L` bits is, under any
continuation, the same as drawing one uniform `BitVec L`. -/
private lemma evalDist_keystream_bind {β : Type} (icb : BitVec 128) (L : ℕ)
    (f : BitVec L → ProbComp β) :
    𝒟[(counterChain icb ((L + 127) / 128)).mapM (fun _ => ($ᵗ (BitVec 128) : ProbComp _)) >>=
        fun blocks => f (blocksToBitVec blocks L)] =
      𝒟[($ᵗ (BitVec L) : ProbComp _) >>= f] := by
  have hlen : (counterChain icb ((L + 127) / 128)).length = (L + 127) / 128 :=
    counterChain_length icb _
  have h1 : 𝒟[(fun blocks => blocksToBitVec blocks L) <$>
      (counterChain icb ((L + 127) / 128)).mapM
        (fun _ => ($ᵗ (BitVec 128) : ProbComp _))] = 𝒟[($ᵗ (BitVec L) : ProbComp _)] := by
    refine Eq.trans (evalDist_map_eq_of_evalDist_eq
      (evalDist_mapM_const_uniform (R := BitVec 128)
        (counterChain icb ((L + 127) / 128))) _) ?_
    rw [Functor.map_map, hlen]
    exact evalDist_blocksToBitVec_uniform ((L + 127) / 128) L (by omega)
  rw [← bind_map_left]
  exact evalDist_bind_congr_fst h1 f

theorem game1_eq_prfIdealExp (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    Pr[= true | game1 prp L hL adv] =
      Pr[= true | PRFScheme.prfIdealExp (prfReduction iv L adv)] := by
  rw [prfIdealExp_prfReduction_eq iv L hL adv]
  refine probOutput_eq_of_evalDist_eq ?_ true
  unfold game1
  -- Split `(H, mask, ks)` into three independent draws. `uniformSample_prod_eq_bind` is a
  -- term equality, so this is plain `rw`, with no distributional step yet.
  rw [uniformSample_prod_eq_bind (BitVec 128) (BitVec 128 × BitVec L)]
  simp only [bind_assoc, pure_bind]
  rw [uniformSample_prod_eq_bind (BitVec 128) (BitVec L)]
  simp only [bind_assoc, pure_bind]
  -- Both sides now share the `H` and mask draws; only the keystream factor differs.
  refine evalDist_bind_congr' _ (fun h => evalDist_bind_congr' _ (fun mask => ?_))
  exact (evalDist_keystream_bind _ L _).symm

/-- The PRF hop: replacing the block cipher by a random function changes the adversary's
success probability by at most the PRF advantage of `prfReduction`. -/
theorem game0_game1_le_prf (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    |(Pr[= true | game1 prp L hL adv]).toReal -
      (Pr[= true | game0 prp iv L hL adv]).toReal| ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) := by
  unfold PRFScheme.prfAdvantage
  rw [game0_eq_prfRealExp prp iv L hL adv, game1_eq_prfIdealExp prp iv L hL adv]
  -- `prfAdvantage` is `|real − ideal|`; the hop is stated as `|ideal − real|`.
  exact le_of_eq (abs_sub_comm _ _)

end IdealProjection

/-! ## The reduction's query complexity -/

/-- `prfReduction` makes at most `⌈L/128⌉ + 2` function-oracle queries, whatever the
adversary does. This records the reduction's cost; the security proof does not use it. -/
theorem prfReduction_isQueryBoundP (iv : BitVec 96) (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    (prfReduction iv L adv).IsQueryBoundP (· matches Sum.inr _) ((L + 127) / 128 + 2) := by
  have key : (prfReduction iv L adv).IsQueryBoundP (· matches Sum.inr _)
      (1 + (1 + ((L + 127) / 128 * 1 + 0))) := by
    unfold prfReduction
    refine isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).mpr (by omega)) fun h _ => ?_
    refine isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).mpr (by omega))
      fun mask _ => ?_
    refine isQueryBoundP_bind ?_ fun blocks _ => ?_
    · refine (isQueryBoundP_listMapM_const (k := 1)
        (fun x => (isQueryBoundP_query_iff _ (Sum.inr x) 1).mpr (by omega)) _).mono ?_
      rw [counterChain_length]
    · exact IsQueryBoundP.liftComp_subSpec (p := fun _ => False) (by simp) (by simp)
  exact key.mono (by omega)

end GCM
