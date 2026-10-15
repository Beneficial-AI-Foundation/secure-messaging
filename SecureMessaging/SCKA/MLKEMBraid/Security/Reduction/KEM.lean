/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Projection
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Sampling
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# Primitive KEM experiments of the masked reduction

The real and random KEM branches correspond to the stopped repaired experiments with both
selected samples installed. Once-only installation removes those samples, and the signed-gap
stop identifies the unchanged IND-CPA normalization with the adjacent numerical-epoch gap.
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
    Pr[= true | KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) b] =
      Pr[= true | P.kem.keygen >>= fun x => P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
        ($ᵗ P.K) >>= fun u => stoppedRun (simImpl P hMac irl (n + 1)
          ⟨x.1, c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader x.1) (P.inc.toVector x.1),
            if b then c.2.2 else u⟩) (simStop (n + 1)) A (simInit P hMac)] := by
  have h : KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) b =
      P.kem.keygen >>= fun x => P.kem.encaps x.1 >>= fun ck => ($ᵗ P.K) >>= fun u =>
        stoppedRun (simImpl P hMac irl (n + 1) ⟨x.1, (P.inc.splitC ck.1).1,
          (P.inc.splitC ck.1).2, if b then ck.2 else u⟩) (simStop (n + 1)) A (simInit P hMac) := by
    simp only [KEMScheme.indCPAExpProb, KEMScheme.indCPAPrefix, bind_assoc]
    refine bind_congr fun x => ?_
    obtain ⟨pk, sk⟩ := x
    simp only [kemReduction, pure_bind]
  rw [h]
  refine probOutput_bind_congr fun x _ => ?_
  rw [encaps_eq_map x.1, bind_map_left]
  simp only [Equiv.apply_symm_apply]

/-- **The real-key experiment** of `kemReduction` is the stopped repaired game with real keys
from `e` on. -/
theorem kem_real_side (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct) (n : ℕ)
    (A : Adversary P irl) :
    Pr[= true | KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) true] =
      Pr[= true | stoppedRun (traceImplAt P hMac irl (n + 1) none none none
        (fun t => if t < n + 1 then .uniform else .real)) (targetStop (n + 1)) A
        (initTrace P hMac)] := by
  rw [indCPAExpProb_kemReduction hMac irl A n true,
    ← stoppedRun_installBoth hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1) none
      _ A]
  refine probOutput_bind_congr fun x hx => probOutput_bind_congr fun c hc => ?_
  obtain ⟨pk, sk⟩ := x
  obtain ⟨es, c1, k⟩ := c
  simp only [↓reduceIte]
  rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
  exact simStep_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1)
    (P.kdfOK k (n + 1)) ⟨pk, c1, _, k⟩ rfl sk es k rfl none (fun _ h => by cases h)
    (fun _ => rfl) hx hc A

/-- **The random-key experiment** of `kemReduction` is the stopped repaired game with a derived
uniform key installed at `e`. -/
theorem kem_rand_side (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct) (n : ℕ)
    (A : Adversary P irl) :
    Pr[= true | KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) false] =
      Pr[= true | ($ᵗ P.K) >>= fun u => stoppedRun (traceImplAt P hMac irl (n + 1) none none
        (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] := by
  rw [indCPAExpProb_kemReduction hMac irl A n false]
  have h1 : ∀ x ∈ support P.kem.keygen, ∀ c ∈ support (P.inc.encaps1 (P.inc.toHeader x.1)),
      ∀ u : P.K,
      Pr[= true | stoppedRun (simImpl P hMac irl (n + 1)
          ⟨x.1, c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader x.1) (P.inc.toVector x.1),
            if false then c.2.2 else u⟩) (simStop (n + 1)) A (simInit P hMac)] =
        Pr[= true | stoppedRun (traceImplAt P hMac irl (n + 1) (some x) (some c)
          (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
          (targetStop (n + 1)) A (initTrace P hMac)] := by
    intro x hx c hc u
    obtain ⟨pk, sk⟩ := x
    obtain ⟨es, c1, k⟩ := c
    exact simStep_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1)
      (P.kdfOK u (n + 1)) ⟨pk, c1, _, u⟩ rfl sk es k rfl (some (P.kdfOK u (n + 1)))
      (fun _ h => (Option.some.inj h).symm) (fun h => by cases h) hx hc A
  calc _ = Pr[= true | P.kem.keygen >>= fun x => P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
          ($ᵗ P.K) >>= fun u => stoppedRun (traceImplAt P hMac irl (n + 1) (some x) (some c)
            (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
            (targetStop (n + 1)) A (initTrace P hMac)] :=
        probOutput_bind_congr fun x hx => probOutput_bind_congr fun c hc =>
          probOutput_bind_congr fun u _ => h1 x hx c hc u
    _ = _ := (probOutput_swap3 _ _ _ _ _).trans
        (probOutput_bind_congr fun _ _ => stoppedRun_installBoth hMac irl hHdrCorrect hEkCorrect
          hCt1Correct hCt2Correct (n + 1) _ _ A)

end KEMGap

/-- **`kem_gap_eq`**: for a positive epoch `e`, the gap between the hybrid with uniform keys
before `e` and the hybrid with a derived uniform key at `e` is the IND-CPA advantage of
`kemReduction` at `e`. -/
theorem kem_gap_eq (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (e : ℕ) (he : 0 < e) :
    (hybrid P hMac irl A (e - 1)).boolDistAdvantage (rawHybrid P hMac irl A e) =
      P.kem.IND_CPA_Advantage ProbCompRuntime.probComp (kemReduction P hMac irl A e) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  have hHD : (fun t => if t ≤ n + 1 - 1 then Mode.uniform else Mode.real) =
      fun t => if t < n + 1 then Mode.uniform else Mode.real := by
    funext t
    by_cases h : t < n + 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hHJ : ∀ t, t ≠ n + 1 →
      (if t ≤ n + 1 - 1 then Mode.uniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform
          else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, if_neg ht]
  have hJD : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform
        else Mode.real) = (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg ht, if_neg h]
  have hgap := signedGap_stop hMac irl
    (fun t => if t ≤ n + 1 - 1 then .uniform else .real)
    (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
    (n + 1) hHJ A
  have hH : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t ≤ n + 1 - 1 then .uniform else .real)) (targetStop (n + 1)) A
        (initTrace P hMac)] =
      Pr[= true | P.kem.IND_CPA_Exp ProbCompRuntime.probComp (kemReduction P hMac irl A (n + 1))
        true] := by
    rw [← KEMScheme.indCPAExpProb_probOutput_true_eq,
      kem_real_side hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct n A,
      ← traceImplAt_none hMac irl (n + 1), hHD]
  have hJ : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] =
      Pr[= true | P.kem.IND_CPA_Exp ProbCompRuntime.probComp (kemReduction P hMac irl A (n + 1))
        false] := by
    rw [← KEMScheme.indCPAExpProb_probOutput_true_eq,
      kem_rand_side hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct n A,
      ← traceImplAt_none hMac irl (n + 1),
      ← stoppedRun_chalSample hMac irl (n + 1) none none
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
        ((fun u => P.kdfOK u (n + 1)) <$> ($ᵗ P.K)) (fun k => by simp [challengeValue]),
      bind_map_left]
    simp only [traceImplAt_congr hMac irl (n + 1) none none _ _ _ hJD]
  unfold ProbComp.boolDistAdvantage hybrid rawHybrid
  rw [hgap, hH, hJ, KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist]

end MLKEMBraid.NoAuth
