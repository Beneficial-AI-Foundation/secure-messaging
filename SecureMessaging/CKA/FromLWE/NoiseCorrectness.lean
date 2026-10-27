/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Correctness.Exchange
import SecureMessaging.CKA.FromLWE.ReconciliationCorrectness

/-!
# First-exchange noise and failure

The first honest exchange fails only if an entry of its actual noise matrix lies outside the
strict reconciliation radius. This event contains every failure outcome, so its probability bounds
failure from above. It does not characterize failure exactly.
-/

open OracleComp ENNReal

namespace lweCKA

/-- Sample the first exchange and return its sender-minus-receiver noise matrix. -/
def firstExchangeNoiseExp
    (p : Params) (χ : ProbComp (Scalar p)) : ProbComp (SharedMatrix p) := do
  let ik ← initKeyGen p χ
  let r ← sampleSendACoins p χ
  return r.secret * ik.error - r.error * ik.secret + r.extra

/-- The sender-minus-receiver value is the first-exchange noise matrix. -/
theorem firstExchangeValue_sub_eq_noise
    (p : Params) (ik : InitKey p) (r : SendACoins p) :
    (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra) -
        ((r.secret * ik.baseMatrix + r.error) * ik.secret) =
      r.secret * ik.error - r.error * ik.secret + r.extra := by
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc]
  abel

/-- A first-exchange mismatch requires a noise entry outside the strict safe radius. -/
theorem firstExchange_mismatch_imp_largeNoise
    (p : Params) (hp : p.WellFormed)
    (ik : InitKey p) (r : SendACoins p)
    (hmismatch :
      reconcile p ((r.secret * ik.baseMatrix + r.error) * ik.secret)
          (makeHint p (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) ≠
        extract p (r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra)) :
    ∃ i j : Fin p.nbar,
      2 ^ (p.discardBits - 2) ≤
        modularDistance p
          ((r.secret * ik.error - r.error * ik.secret + r.extra) i j) 0 := by
  by_contra hlarge
  push Not at hlarge
  apply hmismatch
  apply reconcile_eq_extract_of_modularDistance_lt p hp
  intro i j
  have hvalue := congrArg (fun m => m i j) (firstExchangeValue_sub_eq_noise p ik r)
  have hdistance :
      modularDistance p
          (((r.secret * ik.baseMatrix + r.error) * ik.secret) i j)
          ((r.secret * (ik.baseMatrix * ik.secret + ik.error) + r.extra) i j) =
        modularDistance p
          ((r.secret * ik.error - r.error * ik.secret + r.extra) i j) 0 := by
    simp only [Matrix.sub_apply] at hvalue
    unfold modularDistance
    rw [← hvalue]
    simp only [sub_zero, zero_sub, neg_sub]
    rw [min_comm]
  rw [hdistance]
  exact hlarge i j

/-- First-exchange failure is bounded by the corresponding large-noise event. -/
theorem firstExchangeFailureProb_le_noiseTail
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    firstExchangeFailureProb p χ ≤
      Pr{let delta ← firstExchangeNoiseExp p χ}[∃ i j : Fin p.nbar,
          2 ^ (p.discardBits - 2) ≤ modularDistance p (delta i j) 0] := by
  rw [firstExchangeFailureProb]
  simp only [firstExchangeFailureExp, firstExchangeNoiseExp, OracleComp.prEvent_bind_eq_tsum,
    prEvent_pure]
  gcongr with ik r
  split_ifs with hmismatch hlarge
  · exact le_rfl
  · exact False.elim
      (hlarge (firstExchange_mismatch_imp_largeNoise p hp ik r (of_decide_eq_true hmismatch)))
  · exact zero_le
  · exact le_rfl

end lweCKA
