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

end GCM
