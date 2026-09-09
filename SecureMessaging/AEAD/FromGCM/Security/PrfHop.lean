/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Games
import SecureMessaging.AEAD.FromGCM.Security.Counter

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

The projections of `prfReduction` onto the real and ideal PRF experiments, and the bound
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

end GCM
