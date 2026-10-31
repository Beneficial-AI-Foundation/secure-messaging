/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.Constructions.EpochChoice
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KEM
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KDF

/-!
# Reductions that choose the epoch at random

`kemReduction` and `kdfReduction` attack the challenge of one fixed epoch `e`. The reductions of
this module first draw `e ← epochChoice q`, which is uniform on `{1, …, q}` when `q > 0` and is
`1` when `q = 0`. They then run the reduction for `e`:

- `kemMixReduction A q` is an IND-CPA adversary against the KEM;
- `kdfMixReduction A q` is a distinguisher in the key-derivation game `kdfContextExp`. In this
  game the distinguisher first chooses an epoch label `e`. It then receives either `kdfOK u e`
  for a uniform KEM key `u`, or a uniform epoch key.

For `q > 0`, the difference between the acceptance probabilities of each reduction is the average
over `e ∈ {1, …, q}` of the same difference for the reduction at `e`
(`kemMixReduction_signed_gap`, `kdfMixReduction_signed_gap`). At each `e` the two differences add
up to the difference between two consecutive hybrids, so their sum over `e` telescopes
(`hybrid_gap_eq_query_factor`).
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace MLKEMBraid.NoAuth

variable (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
  [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- The IND-CPA adversary against `P.kem` that draws `e ← epochChoice q` and runs `kemReduction` at
`e`. The epoch `e` is uniform on `{1, …, q}` when `q > 0`, and `e = 1` when `q = 0`. -/
-- ANCHOR: kemMixReduction
def kemMixReduction (A : Adversary P irl) (q : ℕ) : P.kem.IND_CPA_Adversary where
  State := P.PK × ℕ
  preChallenge pk := do pure (pk, ← epochChoice q)
  postChallenge
    | (_, 0), _, _ => pure false
    | (pk, e + 1), c, k => stoppedRun
        (simImpl P hMac irl (e + 1)
          { pk, ct1 := (P.inc.splitC c).1, ct2 := (P.inc.splitC c).2, key := k })
        (simStop (e + 1)) A (simInit P hMac)
-- ANCHOR_END: kemMixReduction

/-- The key-derivation adversary that draws `e ← epochChoice q`, announces `e` as its label and
runs `kdfReduction` at `e`. The epoch `e` is uniform on `{1, …, q}` when `q > 0`, and `e = 1` when
`q = 0`. -/
-- ANCHOR: kdfMixReduction
def kdfMixReduction (A : Adversary P irl) (q : ℕ) : KDFContextAdversary P where
  State := ℕ
  context := do let e ← epochChoice q; pure (e, e)
  guess e x := kdfReduction P hMac irl A e x
-- ANCHOR_END: kdfMixReduction

/-! ## Averaging over the epoch -/

omit [DecidableEq P.EpochKey] in
/-- For `q ≠ 0`, the probability that `kemMixReduction A q` outputs `true` on the real key, minus
the same probability on a uniform key, is the average over `e ∈ {1, …, q}` of the same difference
for `kemReduction A e`. -/
theorem kemMixReduction_signed_gap (A : Adversary P irl) (q : ℕ) (hq : q ≠ 0) :
    (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (kemMixReduction P hMac irl A q) true)}[x = true]).toReal -
    (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (kemMixReduction P hMac irl A q) false)}[x = true]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      ((Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemReduction P hMac irl A (i.val + 1)) true)}[x = true]).toReal -
       (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemReduction P hMac irl A (i.val + 1)) false)}[x = true]).toReal) := by
  have hb : ∀ b : Bool,
      (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemMixReduction P hMac irl A q) b)}[x = true]).toReal =
      (q : ℝ)⁻¹ * ∑ i : Fin q,
        (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemReduction P hMac irl A (i.val + 1)) b)}[x = true]).toReal := by
    intro b
    -- Key generation does not depend on the epoch, so the epoch can be drawn first.
    have hswap : Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemMixReduction P hMac irl A q) b)}[x = true] =
        Pr{let x ← (do
          let e ← epochChoice q
          P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
            (kemReduction P hMac irl A e) b)}[x = true] := by
      refine EvalDistEq.prEvent_eq ?_ _
      unfold KEMScheme.IND_CPA_Experiment
      simp only [kemMixReduction, ProbCompRuntime.probComp,
        ProbCompRuntime.liftProbComp, ProbCompLift.id, bind_assoc, pure_bind]
      refine (OracleComp.EvalDistEq.bind_bind_swap P.kem.keygen (epochChoice q) _).trans ?_
      refine EvalDistEq.bind_right _ fun e => ?_
      rcases e with _ | e <;> simp only [kemReduction, pure_bind] <;> exact EvalDistEq.rfl
    rw [hswap, toReal_prEvent_epochChoice_bind q hq]
  rw [hb true, hb false, Finset.sum_sub_distrib, mul_sub]

/-- For `q ≠ 0`, the probability that `kdfMixReduction A q` outputs `true` in `kdfContextExp` on a
derived key, minus the same probability on a uniform epoch key, is the average over
`e ∈ {1, …, q}` of the same difference for `kdfReduction A e` in `kdfExp` at `e`. -/
theorem kdfMixReduction_signed_gap (A : Adversary P irl) (q : ℕ) (hq : q ≠ 0) :
    (Pr{let x ← kdfContextExp P (kdfMixReduction P hMac irl A q) true}[x = true]).toReal -
    (Pr{let x ← kdfContextExp P (kdfMixReduction P hMac irl A q) false}[x = true]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      ((Pr{let x ← (kdfExp P (i.val + 1)
        (kdfReduction P hMac irl A (i.val + 1)) true)}[x = true]).toReal -
       (Pr{let x ← (kdfExp P (i.val + 1)
        (kdfReduction P hMac irl A (i.val + 1)) false)}[x = true]).toReal) := by
  have hd : ∀ derived : Bool,
      (Pr{let x ← kdfContextExp P (kdfMixReduction P hMac irl A q) derived}[x = true]).toReal =
      (q : ℝ)⁻¹ * ∑ i : Fin q,
        (Pr{let x ← (kdfExp P (i.val + 1)
          (kdfReduction P hMac irl A (i.val + 1)) derived)}[x = true]).toReal := by
    intro derived
    simp only [kdfContextExp, kdfMixReduction, bind_assoc, pure_bind]
    exact toReal_prEvent_epochChoice_bind q hq _ _
  rw [hd true, hd false, Finset.sum_sub_distrib, mul_sub]

/-! ## Telescoping over the hybrids -/

/-- Let `p_i` be the probability that the hybrid with uniform keys through epoch `i` outputs
`true`. Let `Δ_KEM` be the acceptance probability of `kemMixReduction A q` on the real key minus
that on a random key, and `Δ_KDF` the acceptance probability of `kdfMixReduction A q` in
`kdfContextExp` on a derived key minus that on a uniform key. For every `q`,
`p_0 - p_q = q · (Δ_KEM + Δ_KDF)`. -/
theorem hybrid_gap_eq_query_factor (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (A : Adversary P irl) (q : ℕ) :
    (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal -
      (Pr{let x ← hybrid P hMac irl A q}[x = true]).toReal =
    (q : ℝ) *
      (((Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemMixReduction P hMac irl A q) true)}[x = true]).toReal -
        (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemMixReduction P hMac irl A q) false)}[x = true]).toReal) +
       ((Pr{let x ← kdfContextExp P (kdfMixReduction P hMac irl A q) true}[x = true]).toReal -
        (Pr{let x ← (kdfContextExp P (kdfMixReduction P hMac irl A q)
          false)}[x = true]).toReal)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hpos
  · simp
  have hq : q ≠ 0 := hpos.ne'
  rw [kemMixReduction_signed_gap P hMac irl A q hq, kdfMixReduction_signed_gap P hMac irl A q hq,
    ← mul_add, ← Finset.sum_add_distrib, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hq),
    one_mul]
  simp_rw [kem_signed_gap_eq P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A,
    kdf_signed_gap_eq P hMac irl A, sub_add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (Pr{let x ← hybrid P hMac irl A i}[x = true]).toReal -
    (Pr{let x ← hybrid P hMac irl A (i + 1)}[x = true]).toReal) q, Finset.sum_range_sub']

end MLKEMBraid.NoAuth
