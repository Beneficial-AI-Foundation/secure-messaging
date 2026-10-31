/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Receive
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Send
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Trace

/-!
# The simulator and the installed trace game

With the key pair and the first-stage encapsulation of `e` installed, the repaired invariant
determines the ciphertext and the output keys that the simulator needs for receives and
challenges. So each query of the simulator agrees with the query of the installed trace game on
the simulator view of the state. The ToVCVio result `prEvent_optionRun_eq_of_state_map` on runs
and maps of states then gives the same acceptance probability for the stopped runs.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- The invariant of the repaired trace game with the key pair `(pk, sk)` and first-stage
sample `(es, c1, k)` installed at `e`. -/
def SimInv (hMac : P.Mac = Unit) (e : ℕ) (pk : P.PK) (sk : P.SK) (es : P.inc.St) (c1 : P.inc.C₁)
    (k : P.K) (s : TraceState P) : Prop :=
  InstInv hMac e (some (pk, sk)) (some (es, c1, k)) s

section SimInvLemmas

variable {hMac : P.Mac = Unit} {e : ℕ} {pk : P.PK} {sk : P.SK} {es : P.inc.St} {c1 : P.inc.C₁}
  {k : P.K} {s : TraceState P}

/-- The repaired invariant of `SimInv`. -/
theorem SimInv.repair (h : SimInv hMac e pk sk es c1 k s) : RepairInv hMac s.transcript s.game :=
  (h.1.1 (Or.inl rfl)).1

/-- Under `SimInv`, the second ciphertext part of the recorded samples of `e` is `c2`. -/
theorem SimInv.ct2 (h : SimInv hMac e pk sk es c1 k s) {c2 : P.inc.C₂}
    (hc2 : c2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk)) :
    ∀ pk' sk' es' c1' k', (s.transcript e).keypair = some (pk', sk') →
      (s.transcript e).encaps1 = some (es', c1', k') →
      c2 = P.hEnc2.encaps2Det es' (P.inc.toHeader pk') (P.inc.toVector pk') := by
  intro pk' sk' es' c1' k' hkp hec
  rcases h.2.1 (pk, sk) rfl with h1 | h1
  · rw [h1] at hkp
    cases hkp
  rcases h.2.2 (es, c1, k) rfl with h2 | h2
  · rw [h2] at hec
    cases hec
  rw [h1] at hkp
  rw [h2] at hec
  obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp
  obtain ⟨rfl, rfl, rfl⟩ : es = es' ∧ c1 = c1' ∧ k = k' := by simpa using hec
  exact hc2

/-- Under `SimInv`, a recorded key of `e` is the derived key of the installed sample. -/
theorem SimInv.key (h : SimInv hMac e pk sk es c1 k s) :
    ∀ kk, lookupKey s.game e = some kk → kk = P.kdfOK k e := by
  intro kk hk
  have hR := h.repair
  have hk2 : ∀ party : Bool, (if party then s.game.keyA else s.game.keyB) e = some kk →
      kk = P.kdfOK k e := by
    intro party hp
    rw [hR.keys party e] at hp
    by_cases hc : 0 < e ∧ e ≤ (if party then s.game.stA else s.game.stB).completedEpoch
    · rw [ite_eq_left hc] at hp
      rcases h.2.2 (es, c1, k) rfl with h2 | h2
      · rw [h2] at hp
        cases hp
      · rw [h2] at hp
        simpa using hp.symm
    · rw [ite_eq_right hc] at hp
      cases hp
  have hk' : s.game.keyA e = some kk ∨ s.game.keyB e = some kk := by
    unfold lookupKey at hk
    cases hA : s.game.keyA e <;> simp_all
  rcases hk' with hp | hp
  · exact hk2 true (by simpa using hp)
  · exact hk2 false (by simpa using hp)

end SimInvLemmas

/-- The simulator view of the literal initial trace state is the simulator's initial state. -/
theorem simOf_initTrace (hMac : P.Mac = Unit) (e : ℕ) (v : P.EpochKey) :
    simOf e v (initTrace P hMac) = simInit P hMac := by
  have h1 : (relabel e v fun _ => (none : Option P.EpochKey)) = fun _ => none :=
    funext fun t => by simp [relabel]
  have h2 : (eraseAt e fun _ => ({ keypair := none, encaps1 := none } : EpochTranscript P)) =
      fun _ => { keypair := none, encaps1 := none } :=
    funext fun t => by simp [eraseAt]
  simp [simOf, simGameOf, initTrace, simInit, SCKAScheme.initGameState, maskState,
    MLKEMBraid.initA, MLKEMBraid.initB, h1, h2]

section SimStep

variable [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
  [DecidableEq P.Sym] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- Every query of the simulator agrees with the installed trace game under `SimInv`. -/
theorem simImpl_step (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v) (sk : P.SK)
    (es : P.inc.St) (k : P.K)
    (hc2 : ch.ct2 = P.hEnc2.encaps2Det es (P.inc.toHeader ch.pk) (P.inc.toVector ch.pk))
    (xo : Option P.EpochKey) (hxo : ∀ x, xo = some x → x = v)
    (hxk : xo = none → v = P.kdfOK k e) :
    ∀ q s, SimInv hMac e ch.pk sk es ch.ct1 k s →
      StepSim e v ((simImpl P hMac irl e ch q).run (simOf e v s))
        ((traceImplAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) xo
          (fun t => if t < e then .uniform else .real) q).run s) :=
  stepSim_add _ (stepSim_add _ (stepSim_add _ (stepSim_add _ (stepSim_add _
    (stepSim_add _ (stepSim_add _ (stepSim_add _ (stepSim_add _
      (fun t s _ => unif_step t s)
      (fun t s _ => plainStep hMac irl e v ch hv sk es k true t s))
      (fun t s _ => plainStep hMac irl e v ch hv sk es k false t s))
      (fun n s hs => recvStep hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e v ch hv
        true n s hs.repair (hs.ct2 hc2)))
      (fun n s hs => recvStep hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e v ch hv
        false n s hs.repair (hs.ct2 hc2)))
      (fun t s _ => leakStep hMac irl e v ch hv sk es k true t s))
      (fun t s _ => leakStep hMac irl e v ch hv sk es k false t s))
      (fun t s hs => challenge_step xo t s hxo
        (fun hn kk hk => (hs.key kk hk).trans (hxk hn).symm)))
      (fun t s _ => by cases t; exact corruptA_step s))
      (fun t s _ => by cases t; exact corruptB_step s)

/-- **Simulation.** With the challenge key pair and first-stage sample installed at `e`, the
masked simulator and the installed trace game accept with the same probability. -/
theorem simStep_eq (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v) (sk : P.SK)
    (es : P.inc.St) (k : P.K)
    (hc2 : ch.ct2 = P.hEnc2.encaps2Det es (P.inc.toHeader ch.pk) (P.inc.toVector ch.pk))
    (xo : Option P.EpochKey) (hxo : ∀ x, xo = some x → x = v)
    (hxk : xo = none → v = P.kdfOK k e)
    (hkp : (ch.pk, sk) ∈ support P.kem.keygen)
    (hec : (es, ch.ct1, k) ∈ support (P.inc.encaps1 (P.inc.toHeader ch.pk)))
    (A : Adversary P irl) :
    Pr{let x ← stoppedRun (simImpl P hMac irl e ch) (simStop e) A (simInit P hMac)}[x = true] =
      Pr{let x ← (stoppedRun (traceImplAt P hMac irl e (some (ch.pk, sk))
        (some (es, ch.ct1, k)) xo (fun t => if t < e then .uniform else .real)) (targetStop e) A
        (initTrace P hMac))}[x = true] := by
  rw [← simOf_initTrace hMac e v]
  exact prEvent_optionRun_eq_of_state_map
    (stopOnState (traceImplAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) xo
      (fun t => if t < e then .uniform else .real)) (targetStop e))
    (stopOnState (simImpl P hMac irl e ch) (simStop e)) (simOf e v)
    (SimInv hMac e ch.pk sk es ch.ct1 k)
    (fun q s hs z hz _ => by
      obtain ⟨w, hw, rfl⟩ := OracleComp.mem_support_stopOnState hz
      exact traceImplAt_instInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e
        (ch.pk, sk) (some (es, ch.ct1, k)) (some (es, ch.ct1, k)) xo _ hkp
        (fun c h => by cases h; exact hec) (Or.inr rfl) q s hs w hw)
    (fun q s hs => stopOnState_simOf _ _ q s
      (simImpl_step hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e v ch hv sk es k
        hc2 xo hxo hxk q s hs))
    A (initTrace P hMac)
    ⟨traceInv_init hMac true, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩

end SimStep

end MLKEMBraid.NoAuth
