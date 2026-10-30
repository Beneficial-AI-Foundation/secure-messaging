/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Projection
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Sampling
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# The IND-CPA experiments of the KEM reduction

The real-key and the random-key IND-CPA experiments of `kemReduction A e` are the stopped repaired
games with the key pair and the first-stage encapsulation of `e` installed. Installing each sample
once removes it again. Stopping at the exposure of `e` then identifies the difference between the
two experiments with the difference between adjacent hybrids (`kem_signed_gap_eq`).
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

section KEMGap

variable [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
  [DecidableEq P.Sym] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

omit [DecidableEq P.EpochKey] in
/-- The fixed-bit IND-CPA experiment of `kemReduction`, with the challenge ciphertext split into
the first-stage sample and its deterministic second part. -/
theorem indCPAExpProb_kemReduction (A : Adversary P irl) (n : ℕ) (b : Bool) :
    Pr{let x ← KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) b}[x = true] =
      Pr{let y ← do
        let x ← P.kem.keygen
        let c ← P.inc.encaps1 (P.inc.toHeader x.1)
        let u ← ($ᵗ P.K)
        stoppedRun (simImpl P hMac irl (n + 1)
          ⟨x.1, c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader x.1) (P.inc.toVector x.1),
            if b then c.2.2 else u⟩) (simStop (n + 1)) A (simInit P hMac)}[y = true] := by
  have h : KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) b =
      P.kem.keygen >>= fun x => P.kem.encaps x.1 >>= fun ck => ($ᵗ P.K) >>= fun u =>
        stoppedRun (simImpl P hMac irl (n + 1) ⟨x.1, (P.inc.splitC ck.1).1,
          (P.inc.splitC ck.1).2, if b then ck.2 else u⟩) (simStop (n + 1)) A (simInit P hMac) := by
    simp only [KEMScheme.indCPAExpProb, KEMScheme.indCPAPrefix, bind_assoc]
    refine bind_congr fun x => ?_
    obtain ⟨pk, sk⟩ := x
    simp only [kemReduction, pure_bind]
  rw [h]
  simp only [map_bind]
  refine prEvent_bind_congr_of_support _ _ _ fun x _ => ?_
  rw [encaps_eq_map x.1, bind_map_left]
  simp only [Equiv.apply_symm_apply]

/-- **The real-key experiment** of `kemReduction` is the stopped repaired game with real keys
from `e` on. -/
theorem kem_real_side (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct) (n : ℕ)
    (A : Adversary P irl) :
    Pr{let x ← KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) true}[x = true] =
      Pr{let x ← (stoppedRun (traceImplAt P hMac irl (n + 1) none none none
        (fun t => if t < n + 1 then .uniform else .real)) (targetStop (n + 1)) A
        (initTrace P hMac))}[x = true] := by
  rw [indCPAExpProb_kemReduction hMac irl A n true,
    ← stoppedRun_installBoth hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1) none
      _ A]
  refine prEvent_bind_congr_of_support _ _ _ fun x hx =>
    prEvent_bind_congr_of_support _ _ _ fun c hc => ?_
  obtain ⟨pk, sk⟩ := x
  obtain ⟨es, c1, k⟩ := c
  simp only [↓reduceIte]
  rw [OracleComp.prEvent_bind_const]
  exact simStep_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1)
    (P.kdfOK k (n + 1)) ⟨pk, c1, _, k⟩ rfl sk es k rfl none (fun _ h => by cases h)
    (fun _ => rfl) hx hc A

/-- **The random-key experiment** of `kemReduction` is the stopped repaired game with a derived
uniform key installed at `e`. -/
theorem kem_rand_side (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct) (n : ℕ)
    (A : Adversary P irl) :
    Pr{let x ← KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) false}[x = true] =
      Pr{let x ← do
        let u ← ($ᵗ P.K)
        stoppedRun (traceImplAt P hMac irl (n + 1) none none
          (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
          (targetStop (n + 1)) A (initTrace P hMac)}[x = true] := by
  rw [indCPAExpProb_kemReduction hMac irl A n false]
  have h1 : ∀ x ∈ support P.kem.keygen, ∀ c ∈ support (P.inc.encaps1 (P.inc.toHeader x.1)),
      ∀ u : P.K,
      Pr{let y ← (stoppedRun (simImpl P hMac irl (n + 1)
          ⟨x.1, c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader x.1) (P.inc.toVector x.1),
            if false then c.2.2 else u⟩) (simStop (n + 1)) A (simInit P hMac))}[y = true] =
        Pr{let y ← (stoppedRun (traceImplAt P hMac irl (n + 1) (some x) (some c)
          (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
          (targetStop (n + 1)) A (initTrace P hMac))}[y = true] := by
    intro x hx c hc u
    obtain ⟨pk, sk⟩ := x
    obtain ⟨es, c1, k⟩ := c
    exact simStep_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1)
      (P.kdfOK u (n + 1)) ⟨pk, c1, _, u⟩ rfl sk es k rfl (some (P.kdfOK u (n + 1)))
      (fun _ h => (Option.some.inj h).symm) (fun h => by cases h) hx hc A
  calc _ = Pr{let y ← do
          let x ← P.kem.keygen
          let c ← P.inc.encaps1 (P.inc.toHeader x.1)
          let u ← ($ᵗ P.K)
          stoppedRun (traceImplAt P hMac irl (n + 1) (some x) (some c)
            (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
            (targetStop (n + 1)) A (initTrace P hMac)}[y = true] :=
        prEvent_bind_congr_of_support _ _ _ fun x hx =>
          prEvent_bind_congr_of_support _ _ _ fun c hc =>
            prEvent_bind_congr_of_support _ _ _ fun u _ => h1 x hx c hc u
    _ = _ := (prEvent_swap3 _ _ _ _).trans
        (prEvent_bind_congr_of_support _ _ _ fun _ _ =>
          stoppedRun_installBoth hMac irl hHdrCorrect hEkCorrect
            hCt1Correct hCt2Correct (n + 1) _ _ A)

end KEMGap

/-- **`kem_signed_gap_eq`**: for every `n`, the probability that `kemReduction` at epoch `n + 1`
outputs `true` on the real key, minus the same probability on a uniform key, is the acceptance
probability of the hybrid with uniform keys through epoch `n` minus that of the hybrid with a
derived uniform key at epoch `n + 1`. -/
theorem kem_signed_gap_eq (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (n : ℕ) :
    (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemReduction P hMac irl A (n + 1)) true)}[x = true]).toReal -
      (Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemReduction P hMac irl A (n + 1)) false)}[x = true]).toReal =
    (Pr{let x ← hybrid P hMac irl A n}[x = true]).toReal -
      (Pr{let x ← rawHybrid P hMac irl A (n + 1)}[x = true]).toReal := by
  have hHD : (fun t => if t ≤ n then Mode.uniform else Mode.real) =
      fun t => if t < n + 1 then Mode.uniform else Mode.real := by
    funext t
    by_cases h : t < n + 1
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  have hHJ : ∀ t, t ≠ n + 1 →
      (if t ≤ n then Mode.uniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform
          else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h, ite_eq_right ht]
  have hJD : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform
        else Mode.real) = (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right ht, ite_eq_right h]
  have hgap := signedGap_stop hMac irl
    (fun t => if t ≤ n then .uniform else .real)
    (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
    (n + 1) hHJ A
  have hH : Pr{let x ← (stoppedRun (traceImpl P hMac irl true
        (fun t => if t ≤ n then .uniform else .real)) (targetStop (n + 1)) A
        (initTrace P hMac))}[x = true] =
      Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemReduction P hMac irl A (n + 1)) true)}[x = true] := by
    rw [← KEMScheme.indCPAExpProb_prEvent_true_eq,
      kem_real_side hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct n A,
      ← traceImplAt_none hMac irl (n + 1), hHD]
  have hJ : Pr{let x ← (stoppedRun (traceImpl P hMac irl true
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac))}[x = true] =
      Pr{let x ← (P.kem.IND_CPA_Experiment ProbCompRuntime.probComp
        (kemReduction P hMac irl A (n + 1)) false)}[x = true] := by
    rw [← KEMScheme.indCPAExpProb_prEvent_true_eq,
      kem_rand_side hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct n A,
      ← traceImplAt_none hMac irl (n + 1),
      ← stoppedRun_chalSample hMac irl (n + 1) none none
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
        ((fun u => P.kdfOK u (n + 1)) <$> ($ᵗ P.K)) (fun k => by simp [challengeValue]),
      bind_map_left]
    simp only [traceImplAt_congr hMac irl (n + 1) none none _ _ _ hJD]
  unfold hybrid rawHybrid
  rw [hgap, hH, hJ]

end MLKEMBraid.NoAuth
