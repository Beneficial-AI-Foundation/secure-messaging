/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Games
import SecureMessaging.AEAD.FromGCM.Security.Counter
import ToVCVio.CryptoFoundations.PRF
import ToVCVio.OracleComp.QueryTracking.RandomOracle.FreshQueries

/-!
# GCM — the PRF hop (`game0` → `game1`)

Idealize the block cipher: replace the three separated cipher outputs of one-time GCM
(`CipherProfile.lean`) by the answers of a random function, at the cost of the PRF
advantage of one explicit reduction.

Contents:
- `prfReduction` — the named EAGER PRF distinguisher (REQ-01/REQ-06): it fetches the
  hash key, the tag mask and all `⌈L/128⌉` keystream blocks from its function oracle
  BEFORE running the adversary, then runs the closed `gcmTupleImpl` game at the fetched
  tuple. Its query list is fixed and its length is `⌈L/128⌉ + 2` regardless of how much
  decryption traffic the adversary generates.
- `counterChain_length` — the length fact behind that query count.
- `gcmEncryptSpec_eq_tuple` / `gcmDecryptSpec_eq_tuple` — the profile-to-tuple bridges
  deferred by 02-01: the block-list specs of `CipherProfile.lean` equal the
  `gcmTupleImpl` oracle bodies at `ks := blocksToBitVec ksBlocks L`.
- `game1_eq_game2` — the lazy-sampling hop, moving the eager tuple sample inside the
  oracles (premise-free, zero advantage cost).
- `run'_game0Impl_eq_tupleImpl` / `game0_eq_prfRealExp` — the REAL-side projection:
  running `prfReduction` in the real PRF experiment is exactly `game0`.

The projection of `prfReduction` onto the ideal PRF experiment, and the bound
`|Pr[game1] − Pr[game0]| ≤ prfAdvantage`, are proven in the companion plans of this phase.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational

/-! ## Counter-chain length

`counterChain` is defined by recursion on the block count in `AEAD/GCM.lean`; this is the
only structural fact about it the PRF hop needs (it fixes `prfReduction`'s query count).
It lives here rather than in `Counter.lean` so no Phase-1 file is touched. -/

/-- `counterChain icb m` has exactly `m` blocks — one cipher call per message block. -/
lemma counterChain_length (icb : BitVec 128) (m : ℕ) :
    (counterChain icb m).length = m := by
  induction m generalizing icb with
  | zero => rfl
  | succ n ih => simp [counterChain, ih]

/-! ## The eager PRF reduction -/

/-- **The PRF distinguisher for the GCM hash key / tag mask / keystream** (REQ-01,
REQ-06: one explicit, named reduction rather than an existential).

`prfReduction L adv` fetches its own function oracle at exactly the cipher inputs of
one-time GCM at the all-zero IV (`gcmOneTimeAEAD_encrypt_profile`): the GHASH key at `0`,
the tag mask at `J₀ = 1`, and the GCTR keystream at `counterChain 2 ⌈L/128⌉`. It then runs
`adv` against the closed tuple game `gcmTupleImpl (h, mask, blocksToBitVec blocks L)`,
lifted back into the PRF spec — the tail makes NO function query, so all oracle traffic of
the reduction is the eager prefix.

Design (EAGER, not on demand): the queries happen before the adversary runs, so the query
list is the *fixed* list `0 :: 1 :: counterChain 2 ⌈L/128⌉`, of length
`1 + 1 + ⌈L/128⌉ = ⌈L/128⌉ + 2` by `counterChain_length`, independently of how many
decryption queries the adversary makes. That constant is what Phase 9's
`IsQueryBoundP`-style query-bound induction and the PRP/PRF switching lemma consume; an
on-demand reduction would make the count adversary-dependent. Distinctness of those query
points (needed on the ideal side) is `cipherInputs_pairwise_ne`, which is where
`ValidMsgLength` enters — the definition itself carries no such hypothesis. -/
-- The outer ascription to `OracleComp (PRFOracleSpec …) Bool` is required: `PRFAdversary`
-- is a two-argument abbrev whose *second* argument is the oracle range, not the return
-- type, so `do`-notation would otherwise unify the monad with `PRFAdversary (BitVec 128)`
-- and fail to find `Monad`/`MonadLiftT` instances. The body's spelling is unchanged.
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

/-! ## Profile-to-tuple bridges

`CipherProfile.lean` states the cipher-call profile with the keystream as a *block list*
`ksBlocks : List (BitVec 128)`; the game skeleton's tuple carries the *flattened*
keystream `ks : BitVec L` (02-01 deliberately deferred the bridge to this phase). The two
lemmas below close that gap: at `ks := blocksToBitVec ksBlocks L` the spec functions are
literally the `gcmTupleImpl` encrypt/decrypt bodies, so the real-side projection can
rewrite the scheme's oracles into tuple form in one step.

The keystream leg is `keystream_eq_blocksToBitVec` (definitional, `OneTimePad.lean`) and
the GHASH argument needs no massaging: 01-05 chose `gcmEncode`'s body to match the spec
bodies verbatim. -/

section Bridges

variable {L : ℕ}

/-- `gcmEncryptSpec` at a keystream block list is the `gcmTupleImpl` encryption body at
the flattened keystream `blocksToBitVec ksBlocks L`. -/
lemma gcmEncryptSpec_eq_tuple (h mask : BitVec 128)
    (ksBlocks : List (BitVec 128)) (ad : SupportedAAD) (m : BitVec L) :
    gcmEncryptSpec h mask ksBlocks ad.1.2 m =
      (m ^^^ blocksToBitVec ksBlocks L,
       ghash h (gcmEncode ad (m ^^^ blocksToBitVec ksBlocks L)) ^^^ mask) := by
  simp only [gcmEncryptSpec, keystream_eq_blocksToBitVec, gcmEncode]

/-- `gcmDecryptSpec` at a keystream block list is the `gcmTupleImpl` decryption body at
the flattened keystream `blocksToBitVec ksBlocks L`. -/
-- The trailing `rfl` discharges an `ite`-instance-level difference only: after
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

/-- **ROADMAP Phase 3 criterion 3**: `game1` and `game2` have the same output
distribution — moving the tuple sample from the top level into the oracles costs nothing.

One application of `probOutput_simulateQ_greedyLazy_run'_eq` does it, at
`implFam := gcmTupleImpl` and `s := none`: `game1`'s body is verbatim the brick's LHS and
`game2`'s is its RHS at the empty cache `(none, none)`. Two things make this a one-liner
rather than a hop with side conditions:

* the WHOLE tuple `τ = BitVec 128 × BitVec 128 × BitVec L` moves at once — `greedyLazy`
  holds a single `Option τ` slot, so there is no per-component commutation to justify;
* the brick is premise-free (no `h_indep`, unlike `consumeLazy`), so it applies to the
  live-decryption `game2` as well: zero advantage cost. -/
theorem game1_eq_game2 (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    evalDist (game1 prp L hL adv) = evalDist (game2 prp L hL adv) := by
  unfold game1 game2
  exact probOutput_simulateQ_greedyLazy_run'_eq gcmTupleImpl adv none

end LazyHop

/-! ## The real-side projection: `game0` = `prfRealExp (prfReduction …)`

Half of ROADMAP Phase 3 criterion 2. The eager design makes this the EtM
`game0_eq_prfRealExp` pattern minus its two hard parts:

* no nested-`simulateQ` collapse — the reduction's tail is a *closed* `ProbComp` injected
  with `OracleComp.liftComp`, which `PRFScheme.simulateQ_prfRealQueryImpl_liftComp` erases
  outright (there is no per-call forwarding to fold);
* no key swap — GCM has a single key and `(prp.toPRFScheme).keygen = prp.keygen` is `rfl`,
  so no `[NeverFail prp.keygen]` and no `probEvent_bind_bind_swap` are needed.

What remains: collapse the three eager fetches to `pure` of the real cipher outputs
(`simulateQ_prfRealQueryImpl_inr` for `H`/`mask`, `simulateQ_prfRealQueryImpl_mapM_inr`
for the keystream block list), then a per-key `id`-projection of `game0`'s handler onto
`gcmTupleImpl` at the real tuple. -/

section RealProjection

variable {K : Type}

/-- Per-key projection: at a fixed key `k`, `game0`'s oracle implementation — the real
scheme's `encrypt`/`decrypt` — projects onto the per-tuple family `gcmTupleImpl` at the
REAL tuple `(CIPH_k(0), CIPH_k(1), blocksToBitVec (CIPH_k ∘ counterChain 2 ⌈L/128⌉) L)`.

The projection is `id`: both sides carry the same state `Option (BitVec L × BitVec 128)`
(the challenge ciphertext), so there is no cache to erase and no state invariant to
maintain. The three branches:

* `OUnif` — both handlers are `oracleUnif`, threading the state unchanged;
* `OEncrypt` — `gcmOneTimeAEAD_encrypt_profile` turns the scheme's `encrypt` into
  `gcmEncryptSpec` at exactly this tuple's components, and `gcmEncryptSpec_eq_tuple`
  flattens the keystream block list, landing on `gcmTupleImpl`'s `encStar` body verbatim;
* `ODecrypt` — the same with `gcmOneTimeAEAD_decrypt_profile` (whose validity guard is
  already discharged by `hL` and the AAD's own `ValidAADLength` witness) and
  `gcmDecryptSpec_eq_tuple`. The ACD19 ciphertext-only challenge guard
  `(← get) == some e` is shared by both sides, so only the `decryptResp` bodies differ. -/
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

/-- **ROADMAP Phase 3 criterion 2, real side**: running `prfReduction` in the real PRF
experiment of the PRF view of the block cipher IS `game0`.

Stated at the `Pr[= true | ·]` level, which is the form `prfAdvantage` consumes by
rewriting in the assembly of `game0_game1_le_prf`.

Proof shape: the reduction's eager prefix collapses to `pure` of the real cipher outputs
and its `liftComp`'d tail loses the PRF spec, leaving both sides as the SAME
`prp.keygen`-bind; `probOutput_bind_congr'` descends under that single key sample and
`run'_game0Impl_eq_tupleImpl` closes the per-key body. -/
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
  simp only [simulateQ_bind, PRFScheme.simulateQ_prfRealQueryImpl_inr,
    PRFScheme.simulateQ_prfRealQueryImpl_mapM_inr,
    PRFScheme.simulateQ_prfRealQueryImpl_liftComp, pure_bind]
  -- Both sides are now the same `prp.keygen` bind; descend and project per key.
  refine probOutput_bind_congr' prp.keygen true (fun k => ?_)
  exact congrArg (fun o => Pr[= true | o]) (run'_game0Impl_eq_tupleImpl prp L hL k adv)

end RealProjection

/-! ## The ideal-side cache peel

The other half of ROADMAP Phase 3 criterion 2 starts here. Running `prfReduction` in the
IDEAL PRF experiment answers its `⌈L/128⌉ + 2` eager function queries with a *lazy* random
oracle: each query first consults the `QueryCache`, and only a cache MISS samples a fresh
uniform. The payoff of the eager design is that the cache exists only during the query
prefix — the adversary never touches the function oracle — so instead of a state-relocation
invariant (the hard part of EtM's ideal side, `AEAD/FromEtM/Security/PrfHop.lean:141`) all
that is needed is: every one of the `⌈L/128⌉ + 2` queries misses.

That is exactly `cipherInputs_pairwise_ne hL` (Phase 1 criterion 2), and it is where
`ValidMsgLength` becomes load-bearing rather than cosmetic: `inc32` wraps modulo `2 ^ 32`
(`AEAD/GCM.lean`), so for an unrestricted `L` the counter chain can return to the hash-key
point `0` and the random oracle would answer that query with the CACHED `H` instead of a
fresh uniform — the peel below would then be false. `ValidMsgLength`'s
`L ≤ 2 ^ 39 - 256` conjunct rules the wrap out. -/

section IdealPeel

/-- One cache-miss peel step: a lazy random-oracle query at a point absent from the cache
is a top-level uniform draw, after which the continuation runs from the extended cache.

`randomOracle` is `uniformSampleImpl.withCaching` (reducible), so this is
`QueryImpl.withCaching_run_none` at the miss, plus a targeted push of `run'` through the
single leading bind — deliberately NOT the global `@[simp] StateT.run'_bind'`, which would
also dismantle the folded `simulateQ … |>.run' none` in the tail (research Pitfall 3). -/
private lemma run'_randomOracle_bind_of_none {D R β : Type} [DecidableEq D] [SampleableType R]
    (t : D) (c : (D →ₒ R).QueryCache) (hc : c t = none)
    (G : R → StateT ((D →ₒ R).QueryCache) ProbComp β) :
    (((D →ₒ R).randomOracle t >>= G : StateT ((D →ₒ R).QueryCache) ProbComp β)).run' c =
      ($ᵗ R : ProbComp R) >>= fun u => (G u).run' (c.cacheQuery t u) := by
  have hunif : (uniformSampleImpl (spec := (D →ₒ R)) t) = ($ᵗ R : ProbComp R) := rfl
  rw [StateT.run'_eq, StateT.run_bind,
    QueryImpl.withCaching_run_none uniformSampleImpl hc]
  simp [bind_map_left, StateT.run'_eq, hunif]

/-- **The ideal experiment of `prfReduction`, peeled**: the lazy random oracle answers the
`⌈L/128⌉ + 2` eager queries with that many INDEPENDENT uniform draws, and the query cache
disappears with them.

This is a `ProbComp`-*term* equality, not merely an `evalDist` one: every step is exact
(`withCaching_run_none` at a miss, and 03-01's `run'_mapM_randomOracle_fresh`, which is
itself term-level).

`hL` is not a convenience hypothesis. The two singleton peels need only `(1 : BitVec 128) ≠ 0`
(`decide`), but the keystream loop needs the chain to be `Nodup` AND disjoint from the two
already-cached points `{0, 1}`, and both come from `cipherInputs_pairwise_ne hL`. Without
`ValidMsgLength L` the statement is false (see the section docstring). -/
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
  simp only [simulateQ_bind, PRFScheme.simulateQ_prfIdealQueryImpl_inr,
    PRFScheme.simulateQ_prfIdealQueryImpl_mapM_inr,
    PRFScheme.simulateQ_prfIdealQueryImpl_liftComp]
  -- The peels are applied in TERM mode (`Eq.trans`), not by `rw`: in the goal the bound
  -- variable's type is the reducible `(PRFOracleSpec _ _).Range (Sum.inr _)`, so keyed
  -- matching would have to solve `Range (Sum.inr ?d) =?= BitVec 128` (03-01's α-pinning
  -- wall). Term elaboration unifies up to definitional unfolding and just works.
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
  -- three components are exactly what the fresh-queries brick asks for — the tail-of-tail
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

end GCM
