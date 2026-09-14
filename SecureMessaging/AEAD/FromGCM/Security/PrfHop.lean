/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Games
import SecureMessaging.AEAD.FromGCM.Security.Counter
import SecureMessaging.AEAD.FromGCM.Security.CipherProfile
import SecureMessaging.AEAD.FromGCM.Security.OneTimePad
import ToVCVio.OracleComp.QueryTracking.RandomOracle.FreshQueries
import VCVio.OracleComp.QueryTracking.Iter
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# GCM: the PRF hop (`game0` → `game1`)

Idealize the block cipher: replace the three separated cipher outputs of one-time GCM
(`CipherProfile.lean`) by the answers of a random function, at the cost of the PRF
advantage of one explicit reduction.

Contents:
- `prfReduction`: the named eager PRF distinguisher. It fetches the hash key, the tag mask
  and all `⌈L/128⌉` keystream blocks from its function oracle before running the adversary,
  then runs the closed `gcmTupleImpl` game at the fetched tuple. Its query list is fixed, of
  length `⌈L/128⌉ + 2`, regardless of the adversary's decryption traffic.
- `gcmEncryptSpec_eq_tuple`/`gcmDecryptSpec_eq_tuple`: the profile-to-tuple bridges. The
  block-list specs of `CipherProfile.lean` equal the `gcmTupleImpl` oracle bodies at
  `ks := blocksToBitVec ksBlocks L`.
- `game1_eq_game2`: the lazy-sampling hop, moving the eager tuple sample inside the oracles
  at zero advantage cost.
- `run'_game0Impl_eq_tupleImpl`/`game0_eq_prfRealExp`: the real-side projection. Running
  `prfReduction` in the real PRF experiment is exactly `game0`.
- `prfIdealExp_prfReduction_eq`/`game1_eq_prfIdealExp`: the ideal-side projection. The lazy
  random oracle answers the eager query prefix with that many independent uniforms, which
  reshape into `game1`'s single tuple `(H, mask, ks)`.
- `game0_game1_le_prf`: the hop's bound
  `|Pr[game1] − Pr[game0]| ≤ prfAdvantage prp.toPRFScheme (prfReduction L adv)`.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational

/-! ## The eager PRF reduction -/

/-- The PRF distinguisher for the GCM hash key, tag mask and keystream: one explicit named
reduction rather than an existential.

`prfReduction L adv` queries its function oracle at exactly the cipher inputs of one-time
GCM at the all-zero IV (`gcmOneTimeAEAD_encrypt_profile`): the GHASH key at `0`, the tag
mask at `J₀ = 1`, and the GCTR keystream at `counterChain 2 ⌈L/128⌉`. It then runs `adv`
against the closed tuple game `gcmTupleImpl (h, mask, blocksToBitVec blocks L)`, lifted
back into the PRF spec; that tail makes no function query, so the eager prefix is all of
the reduction's oracle traffic.

The queries happen before the adversary runs, so the query list is the *fixed*
`0 :: 1 :: counterChain 2 ⌈L/128⌉`, of length `1 + 1 + ⌈L/128⌉ = ⌈L/128⌉ + 2` by
`counterChain_length`, independently of how many decryption queries the adversary makes; an
on-demand reduction would make the count adversary-dependent. `prfReduction_isQueryBoundP`
below records that count, and the switching bound (`PrpSwitch.lean`) derives the same count
from the literal query list. Distinctness of the query points, needed on the ideal side, is
`cipherInputs_pairwise_ne`, which is where `ValidMsgLength` enters; the definition itself
carries no such hypothesis. -/
-- The outer ascription to `OracleComp (PRFOracleSpec …) Bool` is required: `PRFAdversary`
-- is a two-argument abbrev whose *second* argument is the oracle range, not the return
-- type, so `do`-notation would otherwise unify the monad with `PRFAdversary (BitVec 128)`
-- and fail to find `Monad`/`MonadLiftT` instances.
noncomputable def prfReduction (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.PRFAdversary (BitVec 128) (BitVec 128) :=
  (do
    let h ← liftM (OracleSpec.query (Sum.inr (0 : BitVec 128)) :
        OracleQuery (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) (BitVec 128))
    let mask ← liftM (OracleSpec.query (Sum.inr (1 : BitVec 128)) :
        OracleQuery (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) (BitVec 128))
    let blocks ← (counterChain 2 ((L + 127) / 128)).mapM
      (fun t => liftM (OracleSpec.query (Sum.inr t) :
        OracleQuery (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) (BitVec 128)))
    OracleComp.liftComp
      ((simulateQ (gcmTupleImpl (h, mask, blocksToBitVec blocks L)) adv).run' none)
      (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) :
    OracleComp (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) Bool)


section Bridges

variable {L : ℕ}

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


section RealProjection

variable {K : Type}

/-- Per-key projection: at a fixed key `k`, `game0`'s oracle implementation (the real
scheme's `encrypt`/`decrypt`) projects onto the per-tuple family `gcmTupleImpl` at the real
tuple `(CIPH_k(0), CIPH_k(1), blocksToBitVec (CIPH_k ∘ counterChain 2 ⌈L/128⌉) L)`.

The projection is `id`: both sides carry the same state `Option (BitVec L × BitVec 128)`
(the challenge ciphertext), so there is no cache to erase and no state invariant to
maintain. The three branches:

* `OUnif`: both handlers are `oracleUnif`, threading the state unchanged;
* `OEncrypt`: `gcmOneTimeAEAD_encrypt_profile` turns the scheme's `encrypt` into
  `gcmEncryptSpec` at exactly this tuple's components, and `gcmEncryptSpec_eq_tuple`
  flattens the keystream block list, landing on `gcmTupleImpl`'s `encStar` body verbatim;
* `ODecrypt`: the same with `gcmOneTimeAEAD_decrypt_profile` (whose validity guard comes
  from `hL` and the AAD's own `ValidAADLength` witness) and `gcmDecryptSpec_eq_tuple`. The
  ACD19 ciphertext-only challenge guard `(← get) == some e` is shared by both sides, so
  only the `decryptResp` bodies differ. -/
lemma run'_game0Impl_eq_tupleImpl (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L) (k : K)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    (simulateQ (gcmGameSkeleton (spec := unifSpec)
        (fun ad m => pure ((gcmOneTimeAEAD prp L hL).encrypt k ad m))
        (fun ad e => pure ((gcmOneTimeAEAD prp L hL).decrypt k ad e))
        (oracleUnif (BitVec L × BitVec 128))) adv).run' none =
      (simulateQ (gcmTupleImpl (prp.toBlockCipher.perm k 0, prp.toBlockCipher.perm k 1,
        blocksToBitVec ((counterChain 2 ((L + 127) / 128)).map
          (prp.toBlockCipher.perm k)) L)) adv).run' none := by
  refine run'_simulateQ_eq_of_query_map_eq _ _ id ?hproj adv none
  case hproj =>
    intro t s
    rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
    · -- OUnif: both handlers are the lifted uniform oracle, state threaded unchanged.
      simp [gcmGameSkeleton, gcmTupleImpl, oracleUnif, unifLiftStateT,
        QueryImpl.liftTarget_apply, StateT.run_monadLift, Functor.map_map]
    · -- OEncrypt: one-shot; the real cipher body becomes the tuple body by
      -- profile + encryption bridge.
      cases s <;>
        simp [gcmGameSkeleton, gcmTupleImpl, StateT.run_bind, StateT.run_get,
          StateT.run_set, StateT.run_pure, map_pure,
          gcmOneTimeAEAD_encrypt_profile prp hL k, gcmEncryptSpec_eq_tuple]
    · -- ODecrypt: shared challenge guard; the live verification body becomes the tuple
      -- body by profile + decryption bridge.
      simp [gcmGameSkeleton, gcmTupleImpl, StateT.run_bind, StateT.run_get,
        gcmOneTimeAEAD_decrypt_profile prp hL k, gcmDecryptSpec_eq_tuple]

theorem game0_eq_prfRealExp (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    Pr[= true | game0 prp L hL adv] =
      Pr[= true | (prp.toPRFScheme).prfRealExp (prfReduction L adv)] := by
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
  exact congrArg (fun o => Pr[= true | o]) (run'_game0Impl_eq_tupleImpl prp L hL k adv)

end RealProjection


section IdealPeel

/-- A random-oracle query at a point not in the cache is a fresh uniform draw, after which the
continuation runs from the extended cache. -/
private lemma run'_randomOracle_bind_of_none {D R β : Type} [DecidableEq D] [SampleableType R]
    (t : D) (c : (D →ₒ R).QueryCache) (hc : c t = none)
    (G : R → StateT ((D →ₒ R).QueryCache) ProbComp β) :
    (((D →ₒ R).randomOracle t >>= G : StateT ((D →ₒ R).QueryCache) ProbComp β)).run' c =
      ($ᵗ R : ProbComp R) >>= fun u => (G u).run' (c.cacheQuery t u) := by
  have hunif : (uniformSampleImpl (spec := (D →ₒ R)) t) = ($ᵗ R : ProbComp R) := rfl
  rw [StateT.run'_eq, StateT.run_bind,
    QueryImpl.withCaching_run_none uniformSampleImpl hc]
  simp [bind_map_left, StateT.run'_eq, hunif]

/-- The ideal experiment of `prfReduction`, peeled: the lazy random oracle answers the
`⌈L/128⌉ + 2` eager queries with that many independent uniform draws, and the query cache
disappears with them.

This is a `ProbComp`-*term* equality, not merely an `evalDist` one: every step is exact
(`withCaching_run_none` at a miss, and the term-level `run'_mapM_randomOracle_fresh`).

`hL` is not a convenience hypothesis. The two singleton peels need only
`(1 : BitVec 128) ≠ 0` (`decide`), but the keystream loop needs the chain to be `Nodup` and
disjoint from the two already-cached points `{0, 1}`, and both come from
`cipherInputs_pairwise_ne hL`. Without `ValidMsgLength L` the statement is false (see the
section docstring). -/
lemma prfIdealExp_prfReduction_eq (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.prfIdealExp (prfReduction L adv) =
      (($ᵗ (BitVec 128) : ProbComp _) >>= fun h =>
       ($ᵗ (BitVec 128) : ProbComp _) >>= fun mask =>
       (counterChain 2 ((L + 127) / 128)).mapM
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
  -- Peel 2: the tag-mask fetch at `1`; `1 ≠ 0`, so the entry just written is invisible.
  have h10 : ((∅ : (BitVec 128 →ₒ BitVec 128).QueryCache).cacheQuery 0 h) 1 = none := by
    rw [QueryCache.cacheQuery_of_ne _ _ (by decide : (1 : BitVec 128) ≠ 0)]
    exact QueryCache.empty_apply _
  refine Eq.trans (run'_randomOracle_bind_of_none (1 : BitVec 128) _ h10 _) ?_
  refine bind_congr fun mask => ?_
  -- The keystream loop: `0 :: 1 :: counterChain 2 ⌈L/128⌉` is `Pairwise (· ≠ ·)`, whose
  -- three components are what the fresh-queries lemma asks for: the tail-of-tail
  -- `Pairwise` is the chain's `Nodup`, and the two head clauses give freshness of every
  -- chain point against the two cached entries.
  have hpw := cipherInputs_pairwise_ne hL
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


section IdealProjection

variable {K : Type}

/-- Distributionally equal computations can be swapped under a `bind` with a fixed
continuation. VCVio's `evalDist_bind_congr_left` fixes the computation and varies the
continuation, which is the other direction. -/
private lemma evalDist_bind_left {α β : Type} {x y : ProbComp α} (h : 𝒟[x] = 𝒟[y])
    (f : α → ProbComp β) : 𝒟[x >>= f] = 𝒟[y >>= f] := by
  rw [evalDist_bind, evalDist_bind, h]

/-- Drawing `⌈L/128⌉` uniform blocks and flattening them to `L` bits is, under any
continuation, the same as drawing one uniform `BitVec L`. -/
private lemma evalDist_keystream_bind {β : Type} (L : ℕ) (f : BitVec L → ProbComp β) :
    𝒟[(counterChain 2 ((L + 127) / 128)).mapM (fun _ => ($ᵗ (BitVec 128) : ProbComp _)) >>=
        fun blocks => f (blocksToBitVec blocks L)] =
      𝒟[($ᵗ (BitVec L) : ProbComp _) >>= f] := by
  have hlen : (counterChain (2 : BitVec 128) ((L + 127) / 128)).length = (L + 127) / 128 :=
    counterChain_length 2 _
  have h1 : 𝒟[(fun blocks => blocksToBitVec blocks L) <$>
      (counterChain (2 : BitVec 128) ((L + 127) / 128)).mapM
        (fun _ => ($ᵗ (BitVec 128) : ProbComp _))] = 𝒟[($ᵗ (BitVec L) : ProbComp _)] := by
    refine Eq.trans (evalDist_map_eq_of_evalDist_eq
      (evalDist_mapM_const_uniform (R := BitVec 128)
        (counterChain (2 : BitVec 128) ((L + 127) / 128))) _) ?_
    rw [Functor.map_map, hlen]
    exact evalDist_blocksToBitVec_uniform ((L + 127) / 128) L (by omega)
  rw [← bind_map_left]
  exact evalDist_bind_left h1 f

theorem game1_eq_prfIdealExp (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    Pr[= true | game1 prp L hL adv] =
      Pr[= true | PRFScheme.prfIdealExp (prfReduction L adv)] := by
  rw [prfIdealExp_prfReduction_eq L hL adv]
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
  exact (evalDist_keystream_bind L _).symm

/-- The PRF hop: idealizing the block cipher costs exactly the PRF advantage of the named
reduction `prfReduction L adv`.

This is the PRF term of the final bound, stated as `|Pr[game1] − Pr[game0]|`, the order the
triangle inequality in `Security/Assembly.lean` consumes. Since `prfAdvantage` is defined
as `|real − ideal|` and the two projections put `game0` on the real side and `game1` on the
ideal side, the two differ by `abs_sub_comm` only.

No hypothesis beyond `hL` and no PRF/PRP assumption enters: the bound is unconditional in
the block cipher. It is usable because `prfReduction` is explicit and its query count is
the fixed `⌈L/128⌉ + 2` (`counterChain_length`) rather than adversary-dependent; the
switching bound (`PrpSwitch.lean`) is stated against this same reduction and needs that
count. -/
theorem game0_game1_le_prf (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    |(Pr[= true | game1 prp L hL adv]).toReal -
      (Pr[= true | game0 prp L hL adv]).toReal| ≤
      PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction L adv) := by
  unfold PRFScheme.prfAdvantage
  rw [game0_eq_prfRealExp prp L hL adv, game1_eq_prfIdealExp prp L hL adv]
  -- `prfAdvantage` is `|real − ideal|`; the hop is stated as `|ideal − real|`.
  exact le_of_eq (abs_sub_comm _ _)

end IdealProjection

/-! ## The real-side projection: `game0` = `prfRealExp (prfReduction …)` -/

/-- `prfReduction` makes at most `⌈L/128⌉ + 2` function-oracle calls, for symbolic `L` and
independently of the adversary's decryption traffic: the reduction fetches its whole query list
`0 :: 1 :: counterChain 2 ⌈L/128⌉` eagerly and its tail makes no function query at all. The
count is exact by construction; it is stated as an upper bound because `IsQueryBoundP` has no
lower-bound counterpart in VCVio.

The switching term in `Security/PrpSwitch.lean` derives `q = n + 2` from the literal length of
the query list rather than from this bound, so this theorem is the reduction's resource
statement, not an input to the security proof. -/
theorem prfReduction_isQueryBoundP (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    (prfReduction L adv).IsQueryBoundP (· matches Sum.inr _) ((L + 127) / 128 + 2) := by
  have key : (prfReduction L adv).IsQueryBoundP (· matches Sum.inr _)
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
