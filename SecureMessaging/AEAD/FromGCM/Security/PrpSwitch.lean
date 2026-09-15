/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.PRP
import ToVCVio.CryptoFoundations.PRPSwitching
import SecureMessaging.AEAD.FromGCM.Security.PrfHop

/-!
# GCM: PRP/PRF switching

A block cipher is modelled as a pseudorandom permutation (PRP), but the PRF hop assumed it
to be a pseudorandom function. The switching lemma of Bellare and Rogaway [BR] bounds the
difference: a distinguisher making `q` queries at distinct points tells a random permutation
from a random function with probability at most `q(q − 1) / (2 · 2¹²⁸)`, the chance that two
of its `q` uniform answers collide.

Here `q = n + 2` with `n = ⌈L/128⌉`, the length of the fixed query list of `prfReduction`
(GHASH key, tag mask, `n` keystream blocks), giving `(n + 2)(n + 1) / 2¹²⁹`. The list is
fixed, so the random permutation is only ever seen through its values on that list, and its
points are distinct by `cipherInputs_pairwise_ne`, which needs `hL`, so those values are a
without-replacement sample; the generic bound is `tvDist_map_uniformPerm_mapM_const_uniform_le`
in `ToVCVio/EvalDist/UniformInjection.lean`.

Main results:
- `abs_prfAdvantage_sub_prpAdvantage_le`: the PRF and PRP advantages of `prfReduction` differ
  by at most `(n + 2)(n + 1) / 2¹²⁹`.
- `prfAdvantage_le_prpAdvantage_switching`: the one-sided form used by `Security.lean`.

## References

- [BR] Bellare, Rogaway. *Code-Based Game-Playing Proofs and the Security of Triple Encryption.*
  EUROCRYPT 2006, https://eprint.iacr.org/2004/331.pdf
-/

open OracleSpec OracleComp GCM AEADScheme PRPScheme

namespace GCM

/-! ## The PRP-ideal peel -/

/-- In the PRP-ideal experiment, `prfReduction`'s queries are answered by a uniformly random
permutation `π` evaluated at the fixed query points. No `hL` is needed: unlike the lazily
sampled random function, `π` answers deterministically. -/
theorem prpIdealExp_prfReduction_eq (iv : BitVec 96) (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRPScheme.prpIdealExp (X := BitVec 128) (prfReduction iv L adv) =
      (($ᵗ (Equiv.Perm (BitVec 128)) : ProbComp _) >>= fun π =>
        (simulateQ (gcmTupleImpl
          (π 0, π (j0 iv),
            ToVCVio.blocksToBitVec
              ((counterChain (inc32 (j0 iv)) ((L + 127) / 128)).map (fun x => π x))
              L)) adv).run' none) := by
  unfold PRPScheme.prpIdealExp prfReduction
  refine bind_congr fun π => ?_
  simp only [simulateQ_bind, simulateQ_prpQueryImpl_mapM_inr,
    simulateQ_prpQueryImpl_liftComp, pure_bind]
  -- The two singleton queries are rewritten in term mode: `simp only` with
  -- `simulateQ_prpQueryImpl_inr` fails to fire against the reducible `Range (Sum.inr _)` type.
  rw [show simulateQ (prpQueryImpl fun x => π x)
        (liftM (OracleSpec.query (Sum.inr (0 : BitVec 128))) :
          OracleComp (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) _)
        = pure (π 0) from simulateQ_prpQueryImpl_inr _ _,
      show simulateQ (prpQueryImpl fun x => π x)
        (liftM (OracleSpec.query (Sum.inr (j0 iv))) :
          OracleComp (PRFScheme.PRFOracleSpec (BitVec 128) (BitVec 128)) _)
        = pure (π (j0 iv)) from simulateQ_prpQueryImpl_inr _ _]
  rfl

/-! ## The list-shape bridge

Both ideal experiments are written as `D >>= cipherInputsTail adv`, with `D` the answers to
the single query list `0 :: j0 iv :: counterChain (inc32 (j0 iv)) ⌈L/128⌉`. -/

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
private lemma prpIdealExp_eq_bind_tail (iv : BitVec 96)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRPScheme.prpIdealExp (X := BitVec 128) (prfReduction iv L adv) =
      (((fun π : Equiv.Perm (BitVec 128) =>
            ((0 : BitVec 128) :: j0 iv ::
              counterChain (inc32 (j0 iv)) ((L + 127) / 128)).map π) <$>
          ($ᵗ (Equiv.Perm (BitVec 128)) : ProbComp (Equiv.Perm (BitVec 128)))) >>=
        cipherInputsTail adv) := by
  rw [prpIdealExp_prfReduction_eq iv L adv, bind_map_left]
  refine bind_congr fun π => ?_
  rw [List.map_cons, List.map_cons]
  rfl

/-- The PRF-ideal experiment as `D >>= cipherInputsTail adv`, `D` one independent uniform
draw per query point. -/
private lemma prfIdealExp_eq_bind_tail (iv : BitVec 96) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.prfIdealExp (prfReduction iv L adv) =
      ((((0 : BitVec 128) :: j0 iv ::
            counterChain (inc32 (j0 iv)) ((L + 127) / 128)).mapM
          (fun _ => ($ᵗ (BitVec 128) : ProbComp (BitVec 128)))) >>=
        cipherInputsTail adv) := by
  rw [prfIdealExp_prfReduction_eq iv L hL adv]
  simp only [List.mapM_cons, bind_assoc, pure_bind]
  rfl

end Bridge

/-! ## The switching inequality -/

/-- PRP/PRF switching [BR] at `prfReduction`: its PRF and PRP advantages differ by at most
`q(q − 1) / 2¹²⁹` with `q = ⌈L/128⌉ + 2`. The two advantages share the real experiment, since
`prpRealExp` is `prfRealExp` at `toPRFScheme`, so the bound is the distance between the two
ideal experiments. `hL` makes the query points distinct; with a repeated point the proof
route, though not necessarily the inequality, breaks. -/
theorem abs_prfAdvantage_sub_prpAdvantage_le {K : Type}
    (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    |PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) -
      PRPScheme.prpAdvantage prp (prfReduction iv L adv)| ≤
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
  rw [prpIdealExp_eq_bind_tail iv adv, prfIdealExp_eq_bind_tail iv hL adv]
  -- (5) The data-processing inequality pushes the bound through that shared closed tail.
  refine (tvDist_bind_right_le _ _ _).trans ?_
  -- (6) The generic fixed-list switching bound, at
  -- `pts := 0 :: J₀ :: counterChain (inc₃₂ J₀) ⌈L/128⌉`, whose `Nodup` is
  -- `cipherInputs_pairwise_ne iv hL` (`List.Nodup` *is* `Pairwise (· ≠ ·)`).
  refine (OracleComp.tvDist_map_uniformPerm_mapM_const_uniform_le _
    (cipherInputs_pairwise_ne iv hL)).trans ?_
  -- The arithmetic: the list has length `⌈L/128⌉ + 2` by `counterChain_length` and two
  -- `List.length_cons` steps, and `Fintype.card (BitVec 128) = 2¹²⁸`, so
  -- `q(q - 1) / (2 * card X)` is exactly `(n + 2)(n + 1) / 2¹²⁹`.
  rw [List.length_cons, List.length_cons, counterChain_length, ToVCVio.natCast_card_bitVec]
  refine le_of_eq ?_
  push_cast
  ring

/-- One-sided form of `abs_prfAdvantage_sub_prpAdvantage_le`. -/
theorem prfAdvantage_le_prpAdvantage_switching {K : Type}
    (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv) ≤
      PRPScheme.prpAdvantage prp (prfReduction iv L adv) +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) := by
  have h := (abs_le.mp (abs_prfAdvantage_sub_prpAdvantage_le prp iv L hL adv)).2
  linarith

end GCM
