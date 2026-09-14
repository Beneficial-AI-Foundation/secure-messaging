/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.PRP.Defs
import SecureMessaging.AEAD.FromGCM.Security.PrfHop
import ToVCVio.EvalDist.UniformInjection

/-!
# GCM: PRP/PRF switching

The PRP/PRF switching inequality at `prfReduction`. It lets the *PRF* security assumption on
GCM's block cipher be replaced by a *PRP* security assumption, which is what a block cipher
actually is, at the cost of one explicit additive term `(n + 2)(n + 1) / 2¹²⁹` with
`n = ⌈L/128⌉`. The replacement itself is performed in `Security.lean`
(`gcmOneTimeAEAD_security`), which applies the one-sided form to the PRF summand of
`gcmOneTimeAEAD_security_prf`, leaving PRP security of the block cipher as
the only remaining assumption of the GCM bound.

## Main results

- `prpIdealExp_prfReduction_eq`: the PRP-ideal experiment at `prfReduction L adv` peels to a
  single uniform-permutation draw followed by the closed adversary tail.
- `abs_prfAdvantage_sub_prpAdvantage_le`: the switching inequality, two-sided:
  `|Adv^prf(prp.toPRFScheme, prfReduction L adv) − Adv^prp(prp, prfReduction L adv)|
  ≤ (n + 2)(n + 1) / 2¹²⁹`.
- `prfAdvantage_le_prpAdvantage_switching`: its one-sided corollary, obtained by `abs_le.mp`.

## Where the constant comes from

The query count is `q = n + 2` with `n = ⌈L/128⌉ = (L + 127) / 128`. It enters this file as the
length of the *literal* query list `0 :: 1 :: counterChain 2 n` that `prfReduction` fetches
eagerly (the hash key at `0`, the tag mask at `1`, and one keystream block per message block),
computed by two `List.length_cons` steps plus `counterChain_length` (`Security/PrfHop.lean`).
`prfReduction_isQueryBoundP` (`Security/PrfHop.lean`) states the same count in `IsQueryBoundP`
form, but is *not* used here: the proof below takes the exact length and performs no
`IsQueryBoundP` step.

The generic bound is `q(q − 1) / (2 * card X)`; at `card (BitVec 128) = 2¹²⁸` this is
`q(q − 1) / 2¹²⁹`, and at `q = n + 2` it is `(n + 2)(n + 1) / 2¹²⁹`.

The factor `2` inside `2¹²⁹` is the **pair count**: there are `C(q, 2) = q(q − 1)/2` unordered
pairs of query points, each colliding under a uniform function with probability `2⁻¹²⁸`. It is
neither a tag length nor a two-sided-advantage factor. The query count `q` is also distinct from
the block count `n`: `q = n + 2`, the two extra queries being the hash key and the tag mask.

## Why the `(2¹²⁸)!`-sized permutation draw is never evaluated

`prfReduction` is non-adaptive on its function oracle: it fetches a fixed list of points before
the adversary runs, and its tail makes no function query at all. So
`prpIdealExp_prfReduction_eq` peels the whole eager prefix *deterministically*, every answer
being the value `π t` of the drawn permutation, and the `$ᵗ (Equiv.Perm (BitVec 128))` draw is
then consumed by the fixed-list uniformity theorem
(`OracleComp.evalDist_map_uniformPerm_eq_uniformDistinct`, `ToVCVio/CryptoFoundations/`), which
rewrites `pts.map π` as a without-replacement draw over `Fin q ↪ BitVec 128`. No simulator
substitution happens, and no lazy random-permutation simulator exists in this development or is
needed here: fixed-list granularity is all a non-adaptive distinguisher requires.

## Where the generic infrastructure lives

Everything GCM-free lives in `ToVCVio/`:

- `ToVCVio/CryptoFoundations/PRPSwitching.lean`: the fixed-list without-replacement sampler
  `sampleDistinctFrom` and the uniformity theorem relating it to `pts.map π`.
- `ToVCVio/EvalDist/UniformInjection.lean`: the assembled fixed-list switching bound
  `OracleComp.tvDist_map_uniformPerm_mapM_const_uniform_le`, together with the exact
  uniform-through-an-injection TV distance and the birthday arithmetic behind it.

What remains here is instantiation at `prfReduction`'s own query list and the GCM bookkeeping.

## References

- [BR] Bellare, Rogaway. *Code-Based Game-Playing Proofs and the Security of Triple Encryption.*
  EUROCRYPT 2006, https://eprint.iacr.org/2004/331.pdf, the PRP/PRF switching lemma.
-/

open OracleSpec OracleComp GCM AEADScheme PRPScheme

namespace GCM

/-! ## The PRP-ideal peel -/

/-- In the PRP-ideal experiment, `prfReduction`'s queries are answered by a uniformly random
permutation `π` evaluated at the fixed query points. No `hL` is needed: unlike the lazily
sampled random function, `π` answers deterministically. -/
theorem prpIdealExp_prfReduction_eq (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRPScheme.prpIdealExp (X := BitVec 128) (prfReduction L adv) =
      (($ᵗ (Equiv.Perm (BitVec 128)) : ProbComp _) >>= fun π =>
        (simulateQ (gcmTupleImpl
          (π 0, π 1,
            ToVCVio.blocksToBitVec
              ((counterChain 2 ((L + 127) / 128)).map (fun x => π x)) L)) adv).run'
          none) := by
  unfold PRPScheme.prpIdealExp prfReduction
  refine bind_congr fun π => ?_
  simp only [simulateQ_bind, simulateQ_prpQueryImpl_mapM_inr,
    simulateQ_prpQueryImpl_liftComp, pure_bind]
  rw [show simulateQ (prpQueryImpl fun x => π x)
        (liftM (OracleSpec.query (Sum.inr (0 : BitVec 128))) :
          OracleComp (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) _)
        = pure (π 0) from simulateQ_prpQueryImpl_inr _ _,
      show simulateQ (prpQueryImpl fun x => π x)
        (liftM (OracleSpec.query (Sum.inr (1 : BitVec 128))) :
          OracleComp (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) _)
        = pure (π 1) from simulateQ_prpQueryImpl_inr _ _]
  rfl

/-! ## The list-shape bridge

Both peeled ideal experiments are `D >>= tail` for the same closed tail, once the
two-singletons-plus-list shape is reconciled against a single query list
`pts = 0 :: 1 :: counterChain 2 ⌈L/128⌉`. `cipherInputsTail` is that tail, read off a list by
`headI`/`tail` so that it reduces by `rfl` on a two-element-plus-rest cons, with no `match` and
no default branch. -/

section Bridge

variable {L : ℕ}

/-- The adversary run of `prfReduction` as a function of the list of oracle answers: GHASH
key, tag mask, then the keystream blocks. -/
private noncomputable def cipherInputsTail
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (l : List (BitVec 128)) : ProbComp Bool :=
  (simulateQ (gcmTupleImpl
    (l.headI, l.tail.headI, ToVCVio.blocksToBitVec l.tail.tail L)) adv).run' none

/-- The PRP-ideal experiment as `D >>= cipherInputsTail adv`, `D` the image of a uniform
permutation on the query list. -/
private lemma prpIdealExp_eq_bind_tail
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRPScheme.prpIdealExp (X := BitVec 128) (prfReduction L adv) =
      (((fun π : Equiv.Perm (BitVec 128) =>
            ((0 : BitVec 128) :: (1 : BitVec 128) ::
              counterChain 2 ((L + 127) / 128)).map π) <$>
          ($ᵗ (Equiv.Perm (BitVec 128)) : ProbComp (Equiv.Perm (BitVec 128)))) >>=
        cipherInputsTail adv) := by
  rw [prpIdealExp_prfReduction_eq L adv, bind_map_left]
  refine bind_congr fun π => ?_
  rw [List.map_cons, List.map_cons]
  rfl

/-- The PRF-ideal experiment as `D >>= cipherInputsTail adv`, `D` one independent uniform
draw per query point. -/
private lemma prfIdealExp_eq_bind_tail (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.prfIdealExp (prfReduction L adv) =
      ((((0 : BitVec 128) :: (1 : BitVec 128) ::
            counterChain 2 ((L + 127) / 128)).mapM
          (fun _ => ($ᵗ (BitVec 128) : ProbComp (BitVec 128)))) >>=
        cipherInputsTail adv) := by
  rw [prfIdealExp_prfReduction_eq L hL adv]
  simp only [List.mapM_cons, bind_assoc, pure_bind]
  rfl

end Bridge

/-! ## The switching inequality -/

/-- The PRP/PRF switching inequality at `prfReduction`, two-sided:
`|Adv^{prf}(prp.toPRFScheme, B) − Adv^{prp}(prp, B)| ≤ q(q − 1) / 2¹²⁹` at
`B = prfReduction L adv`, `q = ⌈L/128⌉ + 2`.

The two-sided form is no harder than the one-sided one because `PRPScheme.prpRealExp` is
*defined* to be `PRFScheme.prfRealExp prp.toPRFScheme`: the two games share one real term `R`,
the two advantages are `|R − I_prf|` and `|R − I_prp|`, and `abs_abs_sub_abs_le_abs_sub` gives
`||R − I_prf| − |R − I_prp|| ≤ |I_prf − I_prp|`. The rest is a total-variation computation
between two product distributions, the uniform permutation's image on a fixed list of
pairwise-distinct points versus that many i.i.d. uniforms. It is not an instance of a general
adaptive Bellare-Rogaway framework, of which this development contains none.

`hL` supplies `cipherInputs_pairwise_ne` (`Security/Counter.lean`), i.e. the `Nodup` of
`0 :: 1 :: counterChain 2 ⌈L/128⌉`, which is the hypothesis the generic bound needs, and it is
also what the PRF-side cache-miss peel `prfIdealExp_prfReduction_eq` requires. Without
`ValidMsgLength L` it is the chosen proof route that breaks, not necessarily the inequality:
VCVio's PRF-ideal side is a cached lazy random oracle, so a repeated query point would be
answered consistently on both sides, which is Bellare and Rogaway's own "remove duplicate
queries without loss of generality" step.

The proof uses the query list's exact length (`List.length_cons` twice plus
`counterChain_length`), not an upper bound, and therefore does not apply
`prfReduction_isQueryBoundP` (`Security/PrfHop.lean`), which states the same count on its own.
The bound *is* monotone in `q`, so an upper bound would have sufficed; it is simply not the
route taken. -/
theorem abs_prfAdvantage_sub_prpAdvantage_le {K : Type}
    (prp : PRPScheme K (BitVec 128)) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    |PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction L adv) -
      PRPScheme.prpAdvantage prp (prfReduction L adv)| ≤
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) := by
  -- (1) The two games share one real term: `PRPScheme.prpRealExp` is *defined* to be
  -- `PRFScheme.prfRealExp prp.toPRFScheme`, so unfolding it makes the two advantages
  -- `|R - I_prf|` and `|R - I_prp|` over a literally identical `R`.
  unfold PRFScheme.prfAdvantage PRPScheme.prpAdvantage PRPScheme.prpRealExp
  -- (2) `||a| - |b|| ≤ |a - b|`, the two-sided inequality; its one-sided sibling
  -- `abs_sub_abs_le_abs_sub` would only give the corollary below.
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  rw [show ∀ r i j : ℝ, r - i - (r - j) = j - i from fun _ _ _ => by ring]
  -- (3) The Bool-level bridge from a difference of `Pr[= true]` values to TV distance.
  refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
  -- (4) Both ideal experiments become `D >>= cipherInputsTail adv` over the same query list.
  rw [prpIdealExp_eq_bind_tail adv, prfIdealExp_eq_bind_tail hL adv]
  -- (5) The data-processing inequality pushes the bound through that shared closed tail.
  refine (tvDist_bind_right_le _ _ _).trans ?_
  -- (6) The generic fixed-list switching bound, at `pts := 0 :: 1 :: counterChain 2 ⌈L/128⌉`,
  -- whose `Nodup` is `cipherInputs_pairwise_ne hL` (`List.Nodup` *is* `Pairwise (· ≠ ·)`).
  refine (OracleComp.tvDist_map_uniformPerm_mapM_const_uniform_le _
    (cipherInputs_pairwise_ne hL)).trans ?_
  -- The arithmetic: the list has length `⌈L/128⌉ + 2` by `counterChain_length` and two
  -- `List.length_cons` steps, and `Fintype.card (BitVec 128) = 2¹²⁸`, so
  -- `q(q - 1) / (2 * card X)` is exactly `(n + 2)(n + 1) / 2¹²⁹`.
  rw [List.length_cons, List.length_cons, counterChain_length]
  -- Not `card_bitVec`: the `Fintype (BitVec 128)` instance the generic bound carries is
  -- `FinEnum.instFintype (FinEnum.instBitVec 128)`, not `BitVec`'s own, and `rw`/`simp only`
  -- with `card_bitVec` finds no match (verified: "`simp` made no progress"). Going through
  -- `FinEnum.card_eq_fintypeCard`, whose `[Fintype α]` is instance-implicit and therefore
  -- unifies with whatever the goal carries, lands on the instance-free `FinEnum.card`. Same
  -- route as `card_bitVec128_enn` (`Security/GhashAXU.lean`).
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  refine le_of_eq ?_
  push_cast
  ring

/-- One-sided form of `abs_prfAdvantage_sub_prpAdvantage_le`. -/
theorem prfAdvantage_le_prpAdvantage_switching {K : Type}
    (prp : PRPScheme K (BitVec 128)) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction L adv) ≤
      PRPScheme.prpAdvantage prp (prfReduction L adv) +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) := by
  have h := (abs_le.mp (abs_prfAdvantage_sub_prpAdvantage_le prp L hL adv)).2
  linarith

end GCM
