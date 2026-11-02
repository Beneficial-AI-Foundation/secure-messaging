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
difference.

`prfReduction` queries its function oracle at the fixed list
`0 :: J₀ :: counterChain (inc₃₂ J₀) n`, with `n = ⌈L/128⌉`, and then runs the GCM adversary on
the answers alone. So it is a `PRPScheme.fixedQueryAdversary`, and the generic bound
`PRPScheme.abs_prfAdvantage_sub_prpAdvantage_fixedQuery_le` applies with `q = n + 2` and
`N = 2¹²⁸`. For a supported message length (`hL : ValidMsgLength L`) the points of the list are
distinct by `cipherInputs_pairwise_ne`. The bound is `(n + 2)(n + 1) / 2¹²⁹`.

Main results:
- `prfReduction_eq_fixedQueryAdversary`: `prfReduction` as a fixed-query adversary.
- `abs_prfAdvantage_sub_prpAdvantage_le`: the PRF and PRP advantages of `prfReduction` differ
  by at most `(n + 2)(n + 1) / 2¹²⁹`.
- `prfAdvantage_le_prpAdvantage_switching`: the one-sided form used by `Security.lean`.

## References

- [BR] Bellare, Rogaway. *Code-Based Game-Playing Proofs and the Security of Triple Encryption.*
  EUROCRYPT 2006, https://eprint.iacr.org/2004/331.pdf
-/

open OracleSpec OracleComp GCM AEADScheme PRPScheme

namespace GCM

variable {L : ℕ}

/-- The adversary run of `prfReduction` as a function of the list of oracle answers: GHASH
key, tag mask, then the keystream blocks. -/
private noncomputable def cipherInputsTail
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (l : List (BitVec 128)) : ProbComp Bool :=
  (simulateQ (gcmTupleImpl
    (l.headI, l.tail.headI, ToVCVio.blocksToBitVec l.tail.tail L)) adv).run' none

/-- `prfReduction` queries its function oracle at `0`, `J₀` and the counter chain from
`inc₃₂(J₀)`, then runs the GCM adversary on the answers. -/
theorem prfReduction_eq_fixedQueryAdversary (iv : BitVec 96)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    prfReduction iv L adv =
      fixedQueryAdversary ((0 : BitVec 128) :: j0 iv ::
        counterChain (inc32 (j0 iv)) ((L + 127) / 128)) (cipherInputsTail adv) := by
  unfold prfReduction fixedQueryAdversary
  simp only [List.mapM_cons, bind_assoc, pure_bind]
  rfl

/-- PRP/PRF switching [BR] at `prfReduction`. Let `L` be a supported message length
(`hL : ValidMsgLength L`) and `q = ⌈L/128⌉ + 2`. Then the PRF and PRP advantages of
`prfReduction` differ by at most `q(q − 1) / 2¹²⁹`. The proof needs `hL` only to make the `q`
query points distinct: a longer message wraps the 32-bit counter and repeats a point. -/
theorem abs_prfAdvantage_sub_prpAdvantage_le {K : Type}
    (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    |(PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv)).toReal -
      (PRPScheme.prpAdvantage prp (prfReduction iv L adv)).toReal| ≤
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) := by
  rw [prfReduction_eq_fixedQueryAdversary]
  refine (abs_prfAdvantage_sub_prpAdvantage_fixedQuery_le prp _
    (cipherInputs_pairwise_ne iv hL) _).trans ?_
  -- The list has length `⌈L/128⌉ + 2` and `Fintype.card (BitVec 128) = 2¹²⁸`.
  rw [List.length_cons, List.length_cons, counterChain_length, ToVCVio.natCast_card_bitVec]
  refine le_of_eq ?_
  push_cast
  ring

/-- One-sided form of `abs_prfAdvantage_sub_prpAdvantage_le`. -/
-- ANCHOR: prfAdvantage_le_prpAdvantage_switching
theorem prfAdvantage_le_prpAdvantage_switching {K : Type}
    (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    (PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv)).toReal ≤
      (PRPScheme.prpAdvantage prp (prfReduction iv L adv)).toReal +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ)
-- ANCHOR_END: prfAdvantage_le_prpAdvantage_switching
    := by
  have h := (abs_le.mp (abs_prfAdvantage_sub_prpAdvantage_le prp iv L hL adv)).2
  linarith

end GCM
