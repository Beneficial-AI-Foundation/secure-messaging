/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Stopping

/-!
# The uniform-input KDF reduction

Adjacent numerical-epoch hybrids differ at the selected challenge. Stopping and once-used
challenge installation identify their gap with the supplied KDF distinguisher's advantage.
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

/-- **`kdf_gap_eq`**: for a positive epoch `e`, the gap between the hybrid with the derived
uniform key at `e` and the hybrid with a uniform key at `e` is the uniform-input KDF advantage of
`kdfReduction` at `e`. No code-correctness assumption is used. -/
theorem kdf_gap_eq (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (e : ℕ) (he : 0 < e) :
    (rawHybrid P hMac irl A e).boolDistAdvantage (hybrid P hMac irl A e) =
      (kdfExp P e (kdfReduction P hMac irl A e) true).boolDistAdvantage
        (kdfExp P e (kdfReduction P hMac irl A e) false) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  have hJH : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform else Mode.real) =
        (if t ≤ n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg ht, if_neg (by omega)]
  have hJD : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg ht, if_neg h]
  have hHD : ∀ t, t ≠ n + 1 →
      (if t ≤ n + 1 then Mode.uniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hgap := signedGap_stop hMac irl
    (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
    (fun t => if t ≤ n + 1 then .uniform else .real) (n + 1) hJH A
  have hJ : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] =
      Pr[= true | kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) true] := by
    rw [← traceImplAt_none hMac irl (n + 1), ← stoppedRun_chalSample hMac irl (n + 1) none none _
      ((fun u => P.kdfOK u (n + 1)) <$> ($ᵗ P.K)) (fun k => by simp [challengeValue])]
    simp only [kdfExp, kdfReduction, ↓reduceIte, bind_map_left,
      traceImplAt_congr hMac irl (n + 1) none none _ _ _ hJD]
  have hH : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t ≤ n + 1 then .uniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] =
      Pr[= true | kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) false] := by
    rw [← traceImplAt_none hMac irl (n + 1), ← stoppedRun_chalSample hMac irl (n + 1) none none _
      ($ᵗ P.EpochKey) (fun k => by simp [challengeValue])]
    simp only [kdfExp, kdfReduction, Bool.false_eq_true, ↓reduceIte,
      traceImplAt_congr hMac irl (n + 1) none none _ _ _ hHD]
  unfold ProbComp.boolDistAdvantage rawHybrid hybrid
  rw [hgap, hJ, hH]

end MLKEMBraid.NoAuth
