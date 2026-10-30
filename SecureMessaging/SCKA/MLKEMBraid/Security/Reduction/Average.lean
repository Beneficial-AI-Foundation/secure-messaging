/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.EvalDist.BoolDist
import ToVCVio.OracleComp.Constructions.EpochChoice
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KEM
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KDF

/-!
# Reductions that choose the epoch at random

`kemReduction` and `kdfReduction` target the challenge of one fixed epoch `e`. The reductions in
this module first draw `e` uniformly from `{1, …, q}` (`epochChoice q`) and then run the
reduction for `e`:

- `kemMixReduction A q` is an IND-CPA adversary against the KEM;
- `kdfMixReduction A q` is a distinguisher in the key-derivation game `kdfContextExp`.

In `kdfContextExp` the distinguisher first chooses an epoch label `e`. It then receives either
`kdfOK u e` for a uniform KEM key `u`, or a uniform epoch key. `kdfAdvantage` is its
distinguishing advantage.

Since the epoch is uniform, the difference between the two outcomes of each reduction is the
average over `e ∈ {1, …, q}` of the same difference for the reduction at `e`
(`kemMixReduction_signed_gap`, `kdfMixReduction_signed_gap`). At each `e` these differences add up
to the difference between two consecutive hybrids, so their sum over `e` telescopes
(`hybrid_gap_eq_query_factor`).
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace MLKEMBraid.NoAuth

variable (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
  [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- The IND-CPA adversary against `P.kem` that draws an epoch `e ∈ {1, …, q}` and runs
`kemReduction` at `e`. -/
def kemMixReduction (A : Adversary P irl) (q : ℕ) : P.kem.IND_CPA_Adversary where
  State := P.PK × ℕ
  preChallenge pk := do pure (pk, ← epochChoice q)
  postChallenge st c k :=
    match st.2 with
    | 0 => pure false
    | e + 1 => stoppedRun
        (simImpl P hMac irl (e + 1) ⟨st.1, (P.inc.splitC c).1, (P.inc.splitC c).2, k⟩)
        (simStop (e + 1)) A (simInit P hMac)

/-- A key-derivation distinguisher that first chooses the epoch label. -/
structure KDFContextAdversary (P : Parameters ProbComp) where
  /-- The information kept between choosing the label and guessing. -/
  State : Type
  /-- Choose the epoch label and the kept information. -/
  context : ProbComp (ℕ × State)
  /-- Guess from the kept information and the epoch key received. -/
  guess : State → P.EpochKey → ProbComp Bool

/-- Key-derivation game. The label `e` is chosen first; then `kdfExp` runs the fixed-epoch game at
`e`: with `derived = true` the distinguisher receives `kdfOK u e` for uniform `u`, with `false` a
uniform epoch key. -/
def kdfContextExp (C : KDFContextAdversary P) (derived : Bool) : ProbComp Bool := do
  let c ← C.context
  kdfExp P c.1 (C.guess c.2) derived

/-- Distinguishing advantage of a key-derivation adversary. -/
noncomputable def kdfAdvantage (C : KDFContextAdversary P) : ℝ :=
  (𝒟[kdfContextExp P C true].boolDist 𝒟[kdfContextExp P C false]).toReal

/-- The key-derivation adversary that draws `e ∈ {1, …, q}` and runs `kdfReduction` at `e`. -/
def kdfMixReduction (A : Adversary P irl) (q : ℕ) : KDFContextAdversary P where
  State := ℕ
  context := do let e ← epochChoice q; pure (e, e)
  guess e x := kdfReduction P hMac irl A e x

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
    rw [hswap]
    let : NeZero q := ⟨hq⟩
    simp only [epochChoice, hq, ↓reduceDIte, bind_map_left, (prEvent_bind_eq_sum_fintype _),
      SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, ← Finset.mul_sum]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun _ _ => (prEvent_ne_top _))]
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
    let : NeZero q := ⟨hq⟩
    simp only [kdfContextExp, kdfMixReduction, bind_assoc, pure_bind, epochChoice, hq,
      ↓reduceDIte, bind_map_left, (prEvent_bind_eq_sum_fintype _),
      SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, ← Finset.mul_sum]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun _ _ => (prEvent_ne_top _))]
  rw [hd true, hd false, Finset.sum_sub_distrib, mul_sub]

/-! ## Telescoping over the hybrids -/

/-- Let `p_i` be the probability that the hybrid with uniform keys through epoch `i` outputs
`true`. For every `q`, `p_0 - p_q` is `q` times the sum of two differences: the real-key minus
the random-key acceptance probability of `kemMixReduction A q` in the IND-CPA experiment, and
the derived-key minus the uniform-key acceptance probability of `kdfMixReduction A q` in
`kdfContextExp`. -/
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
