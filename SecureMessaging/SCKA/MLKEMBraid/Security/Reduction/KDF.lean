/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Stopping

/-!
# The uniform-input KDF reduction

Adjacent numerical-epoch hybrids differ at the selected challenge. Stopping and once-used
challenge installation identify the difference between their acceptance probabilities with the
difference between the two outcomes of the supplied KDF distinguisher (`kdf_signed_gap_eq`).
No codec-correctness hypothesis is needed for this equality.
-/

open OracleSpec OracleComp

namespace MLKEMBraid.NoAuth

/-- **`kdfReduction`**: the uniform-input KDF distinguisher for epoch `e`. For `e = 0` it returns
`false`. Otherwise it runs the repaired game of `A` once, stopped with `false` when `e` becomes
exposed, sampling all KEM material itself; an eligible challenge of `e` is answered with the test
value `x`, earlier epochs with uniform keys and later epochs with their real keys. -/
def kdfReduction (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (e : ℕ) : P.EpochKey → ProbComp Bool :=
  fun x => match e with
    | 0 => pure false
    | e + 1 => stoppedRun (traceImplAt P hMac irl (e + 1) none none (some x)
        (fun t => if t < e + 1 then .uniform else .real)) (targetStop (e + 1)) A
        (initTrace P hMac)

/-- **`kdf_signed_gap_eq`**: for every `n`, the probability that `kdfReduction` at epoch `n + 1`
outputs `true` on a derived key `kdfOK u (n + 1)` with `u` uniform, minus the same probability on
a uniform epoch key, is the acceptance probability of the hybrid with a derived uniform key at
epoch `n + 1` minus that of the hybrid with uniform keys through epoch `n + 1`. No
code-correctness assumption is used. -/
theorem kdf_signed_gap_eq (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (n : ℕ) :
    (Pr{let x ← kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) true}[x = true]).toReal -
      (Pr{let x ← kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) false}[x = true]).toReal =
    (Pr{let x ← rawHybrid P hMac irl A (n + 1)}[x = true]).toReal -
      (Pr{let x ← hybrid P hMac irl A (n + 1)}[x = true]).toReal := by
  have hJH : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform else Mode.real) =
        (if t ≤ n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right ht, ite_eq_right (by omega)]
  have hJD : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right ht, ite_eq_right h]
  have hHD : ∀ t, t ≠ n + 1 →
      (if t ≤ n + 1 then Mode.uniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  have hgap := signedGap_stop hMac irl
    (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
    (fun t => if t ≤ n + 1 then .uniform else .real) (n + 1) hJH A
  have hJ : Pr{let x ← (stoppedRun (traceImpl P hMac irl true
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac))}[x = true] =
      Pr{let x ← kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) true}[x = true] := by
    rw [← traceImplAt_none hMac irl (n + 1), ← stoppedRun_chalSample hMac irl (n + 1) none none _
      ((fun u => P.kdfOK u (n + 1)) <$> ($ᵗ P.K)) (fun k => by simp [challengeValue])]
    simp only [kdfExp, kdfReduction, ↓reduceIte, bind_map_left, map_bind,
      traceImplAt_congr hMac irl (n + 1) none none _ _ _ hJD]
  have hH : Pr{let x ← (stoppedRun (traceImpl P hMac irl true
        (fun t => if t ≤ n + 1 then .uniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac))}[x = true] =
      Pr{let x ← kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) false}[x = true] := by
    rw [← traceImplAt_none hMac irl (n + 1), ← stoppedRun_chalSample hMac irl (n + 1) none none _
      ($ᵗ P.EpochKey) (fun k => by simp [challengeValue])]
    simp only [kdfExp, kdfReduction, Bool.false_eq_true, ↓reduceIte, map_bind,
      traceImplAt_congr hMac irl (n + 1) none none _ _ _ hHD]
  unfold rawHybrid hybrid
  rw [hgap, hJ, hH]

end MLKEMBraid.NoAuth
