/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Receive
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# Opp-UniKEM-CKA One-Step Score Bounds

For one query from a reachable, failure-free tracked state `(s, b)`:

* a send query (`SendA` or `SendB`) increases the expected score `S` by at
  most `epsilon`, instantiated with the factor correctness error;
* every other query preserves `S` on its support, hence does not increase
  its expectation.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

open SCKAScheme.sckaCorrectnessSpec

namespace Reduction.Internal

/-- Run one correctness oracle step while updating the sticky KEM-failure bit. -/
def trackedCorrectnessImpl [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
        ProbComp) :=
  fun t p => do
    let z ← ((SCKAScheme.sckaCorrectnessImpl
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1
    let bad' := p.2 || currentKEMFailure kem onoff hDet z.2
    pure (z.1, (z.2, bad'))

/-- The tracked invariant: failure is already recorded, or the game state is
reachable and its current KEM material is consistent. -/
def trackedInv [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) : Prop :=
  p.2 = true ∨
    reachableInv kem onoff ecEk ecCt0 ecCt1 p.1 ∧
      currentKEMFailure kem onoff hDet p.1 = false

/-- Once the sticky failure bit is set, one tracked step has expected score at
most the current score plus any nonnegative allowance. -/
lemma tracked_step_score_le_of_bad [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
    (hbad : p.2 = true) (epsilon : ℝ≥0∞) :
    expectedPayoff
        (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p)
        (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff p + epsilon := by
  refine (expectedPayoff_le_one _ _ ?_).trans ?_
  · intro z
    exact trackedFailureScore_le_one kem onoff z.2
  · simp [trackedFailureScore, hbad]

/-- Whether an oracle query is `SendA` or `SendB`, the only queries that run
KEM key generation or offline or online encapsulation. -/
def isSendQuery
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain) : Bool :=
  match t with
  | OSendA | OSendB => true
  | _ => false

/-- The proposition that a correctness-oracle query is a send query. -/
def IsSendQuery
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain) : Prop :=
  isSendQuery t = true

/-- Decides whether a correctness-oracle query is `SendA` or `SendB`. -/
instance : DecidablePred (IsSendQuery (Sym := Sym)) :=
  fun t => inferInstanceAs (Decidable (isSendQuery t = true))

/-- From a reachable state without a current KEM failure, `SendA` increases
the expected tracked score by at most the factor correctness error. -/
lemma tracked_sendA_score_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
        (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) OSendA).run
          (s, false))
        (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) +
        factorCorrectnessError kem onoff := by
  change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2)))
      (fun z => trackedFailureScore kem onoff z.2) ≤ _
  cases hdk : s.stA.dkA with
  | none =>
      simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get,
        scheme, sendA, bind_assoc, pure_bind]
      simp only [hdk, zero_add, bind_pure_comp, StateT.run_monadLift,
        monadLift_self, Bool.false_or, bind_map_left, StateT.run_map,
        StateT.run_set, map_pure]
      rw [expectedPayoff_map]
      change expectedPayoff kem.keygen (fun kp =>
        trackedFailureScore kem onoff
          (sendAKeygenState onoff ecEk s kp,
            currentKEMFailure kem onoff hDet (sendAKeygenState onoff ecEk s kp))) ≤ _
      refine (expectedPayoff_mono kem.keygen _
        (fun kp => currentFailurePotential kem onoff
          (installAKeypair onoff s kp.1 kp.2)) ?_).trans ?_
      · intro kp
        have hbad := installAKeypair_currentKEMFailure_false kem onoff hDet
          ecEk ecCt0 ecCt1 s hs hdk kp.1 kp.2
        have hbad' : currentKEMFailure kem onoff hDet
            (sendAKeygenState onoff ecEk s kp) = false := by
          simpa [currentKEMFailure, sendAKeygenState, installAKeypair] using hbad
        unfold trackedFailureScore
        rw [hbad']
        simp [currentFailurePotential, sendAKeygenState, installAKeypair]
      · exact keygen_failurePotential_le kem onoff ecEk ecCt0 ecCt1 s hs hdk
  | some sk =>
      rcases hs with ⟨T, hInv⟩
      have hekSome : s.stA.ekA.isSome := by
        simpa [hdk] using hInv.keypairAShape
      obtain ⟨pk, hek⟩ := Option.isSome_iff_exists.mp hekSome
      let ich := if s.stA.ack.ekRec then s.stA.ich else s.stA.ich + 1
      let ch? : Option (ℕ × Sym) :=
        if s.stA.ack.ekRec then none else some (ecEk.encode pk ich)
      let msg : Message Sym := (ch?, s.stA.ack, s.stA.t, none)
      let s' := { s with
        stA := { s.stA with ich := ich }
        tcurA := s.stA.t - 1
        msgA := Function.update s.msgA (s.nA + 1) (some (msg, s.stA.t - 1))
        nA := s.nA + 1
        correct := s.correct && decide (s.tcurA ≤ s.stA.t - 1) }
      have hpot : currentFailurePotential kem onoff s' =
          currentFailurePotential kem onoff s := by
        exact currentFailurePotential_congr kem onoff s s' rfl rfl rfl rfl
          rfl rfl rfl
      have hfail' : currentKEMFailure kem onoff hDet s' = false := by
        simpa [s', currentKEMFailure] using hfail
      have hrun : (do
          let y ← (SCKAScheme.oracleSendA
            (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
          pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) =
          pure (some (s.stA.t - 1, none, msg),
            (s', currentKEMFailure kem onoff hDet s')) := by
        simp [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, scheme, sendA,
          hdk, hek, ich, ch?, msg, s']
      rw [hrun, expectedPayoff_pure]
      simp [trackedFailureScore, hfail', hpot]

/-- From a reachable state without a current KEM failure, `SendB` increases
the expected tracked score by at most the factor correctness error. -/
lemma tracked_sendB_score_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
        (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) OSendB).run
          (s, false))
        (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) +
        factorCorrectnessError kem onoff := by
  change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2)))
      (fun z => trackedFailureScore kem onoff z.2) ≤ _
  rcases hs with ⟨T, hInv⟩
  cases hct0 : s.stB.ct0 with
  | none =>
      have hst : s.stB.stCt = none := by
        simpa [hct0] using hInv.offBShape
      have hct1 : s.stB.ct1 = none := by
        have hoff : (T s.stB.t).off = none := by
          simpa [hct0, hst, optionPair] using hInv.offB
        have hon : (T s.stB.t).on = none := by
          by_contra hne
          simpa [hoff] using (T s.stB.t).on_off
            (Option.isSome_iff_ne_none.mpr hne)
        have hmap := hInv.onB
        rw [hon] at hmap
        simpa using hmap.symm
      cases hack : s.stB.ack.ctRec with
      | false =>
          let msg (off : onoff.St × onoff.C₀) : Message Sym :=
            (some (ecCt0.encode off.2 1), s.stB.ack, s.stB.t, some 0)
          have hrun : (do
              let y ← (SCKAScheme.oracleSendB
                (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
              pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) =
              (fun off =>
                (some (s.stB.t - 1, none, msg off),
                  (sendBOffState onoff s off 1 (msg off),
                    currentKEMFailure kem onoff hDet
                      (sendBOffState onoff s off 1 (msg off))))) <$>
                onoff.encapsOff := by
            simp [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
              scheme, sendB, hct0, hack, msg, sendBOffState, sendBNoneState]
          rw [hrun, expectedPayoff_map]
          simp_rw [sendBOffState_score kem onoff hDet s _ 1 _ hct1]
          unfold expectedPayoff
          simpa [trackedFailureScore] using
            off_failurePotential_le kem onoff ecEk ecCt0 ecCt1 s
              ⟨T, hInv⟩ hct0
      | true =>
          cases hek : s.stB.ekA with
          | none =>
              let msg : Message Sym := (none, s.stB.ack, s.stB.t, none)
              have hrun : (do
                  let y ← (SCKAScheme.oracleSendB
                    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
                  pure (y.1, (y.2,
                    false || currentKEMFailure kem onoff hDet y.2))) =
                  (fun off =>
                    (some (s.stB.t - 1, none, msg),
                      (sendBOffState onoff s off s.stB.ich msg,
                        currentKEMFailure kem onoff hDet
                          (sendBOffState onoff s off s.stB.ich msg)))) <$>
                    onoff.encapsOff := by
                simp [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
                  scheme, sendB, hct0, hack, hek, msg, sendBOffState,
                  sendBNoneState]
              rw [hrun, expectedPayoff_map]
              simp_rw [sendBOffState_score kem onoff hDet s _ s.stB.ich _ hct1]
              unfold expectedPayoff
              simpa [trackedFailureScore] using
                off_failurePotential_le kem onoff ecEk ecCt0 ecCt1 s
                  ⟨T, hInv⟩ hct0
          | some pk =>
              obtain ⟨sk, ht, hekA, hdk⟩ :=
                newOff_source_shape kem onoff ecEk ecCt0 ecCt1 s ⟨T, hInv⟩
                  pk hek hct0
              let msg (out : onoff.C₁ × K) : Message Sym :=
                (some (ecCt1.encode out.1 1), s.stB.ack, s.stB.t, some 1)
              have hrun : (do
                  let y ← (SCKAScheme.oracleSendB
                    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
                  pure (y.1, (y.2,
                    false || currentKEMFailure kem onoff hDet y.2))) =
                  onoff.encapsOff >>= fun off =>
                    (fun out =>
                      (some (s.stB.t - 1, some s.stB.t, msg out),
                        (sendBOffOnState onoff s off out.1 out.2 (msg out),
                          currentKEMFailure kem onoff hDet
                            (sendBOffOnState onoff s off out.1 out.2
                              (msg out))))) <$>
                      onoff.encapsOn off.1 pk := by
                simp [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
                  scheme, sendB, hct0, hack, hek, hct1, msg,
                  sendBOffOnState, sendBKeyState]
              have hinner (off : onoff.St × onoff.C₀) :
                  expectedPayoff
                      ((fun out =>
                        (some (s.stB.t - 1, some s.stB.t, msg out),
                          (sendBOffOnState onoff s off out.1 out.2 (msg out),
                            currentKEMFailure kem onoff hDet
                              (sendBOffOnState onoff s off out.1 out.2
                                (msg out))))) <$>
                        onoff.encapsOn off.1 pk)
                      (fun z => trackedFailureScore kem onoff z.2) =
                    failureAfterBoth kem onoff pk sk off.1 off.2 := by
                rw [expectedPayoff_map]
                unfold expectedPayoff
                rw [failureAfterBoth_eq_indicator kem onoff hDet]
                refine congrArg
                  (fun x : ℝ≥0∞ => Pr[⊥ | onoff.encapsOn off.1 pk] + x) ?_
                refine tsum_congr fun out => ?_
                congr 1
                exact sendBOffOnState_score kem onoff hDet s sk off out.1 out.2
                  (msg out) ht hdk
              rw [hrun, expectedPayoff_bind]
              have hpot : currentFailurePotential kem onoff s =
                  failureAfterKeypair kem onoff pk sk := by
                simp [currentFailurePotential, ht, hct1, hekA, hdk, hst, hct0,
                  optionPair]
              calc
                (Pr[⊥ | onoff.encapsOff] +
                  ∑' off : onoff.St × onoff.C₀, Pr[= off | onoff.encapsOff] *
                    expectedPayoff
                      ((fun out =>
                        (some (s.stB.t - 1, some s.stB.t, msg out),
                          (sendBOffOnState onoff s off out.1 out.2 (msg out),
                            currentKEMFailure kem onoff hDet
                              (sendBOffOnState onoff s off out.1 out.2
                                (msg out))))) <$>
                        onoff.encapsOn off.1 pk)
                      (fun z => trackedFailureScore kem onoff z.2)) =
                    failureAfterKeypair kem onoff pk sk := by
                      unfold failureAfterKeypair
                      refine congrArg
                        (fun x : ℝ≥0∞ => Pr[⊥ | onoff.encapsOff] + x) ?_
                      refine tsum_congr fun off => ?_
                      rw [hinner]
                _ ≤ trackedFailureScore kem onoff (s, false) +
                    factorCorrectnessError kem onoff := by
                      simp [trackedFailureScore, hpot]
  | some ct0 =>
      have hstSome : s.stB.stCt.isSome := by
        simpa [hct0] using hInv.offBShape
      obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hstSome
      cases hack : s.stB.ack.ctRec with
      | false =>
          let ich := s.stB.ich + 1
          let msg : Message Sym :=
            (some (ecCt0.encode ct0 ich), s.stB.ack, s.stB.t, some 0)
          let s' := sendBNoneState onoff s { s.stB with ich := ich } msg
          have hpot : currentFailurePotential kem onoff s' =
              currentFailurePotential kem onoff s := by
            exact currentFailurePotential_congr kem onoff s s' rfl rfl rfl rfl
              rfl rfl rfl
          have hfail' : currentKEMFailure kem onoff hDet s' = false := by
            simpa [s', sendBNoneState, currentKEMFailure] using hfail
          have hrun : (do
              let y ← (SCKAScheme.oracleSendB
                (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
              pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) =
              pure (some (s.stB.t - 1, none, msg),
                (s', currentKEMFailure kem onoff hDet s')) := by
            simp [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
              scheme, sendB, hct0, hack, ich, msg, s', sendBNoneState]
          rw [hrun, expectedPayoff_pure]
          simp [trackedFailureScore, hfail', hpot]
      | true =>
          cases hek : s.stB.ekA with
          | none =>
              let msg : Message Sym := (none, s.stB.ack, s.stB.t, none)
              let s' := sendBNoneState onoff s s.stB msg
              have hpot : currentFailurePotential kem onoff s' =
                  currentFailurePotential kem onoff s := by
                exact currentFailurePotential_congr kem onoff s s'
                  rfl rfl rfl rfl rfl rfl rfl
              have hfail' : currentKEMFailure kem onoff hDet s' = false := by
                simpa [s', sendBNoneState, currentKEMFailure] using hfail
              have hrun : (do
                  let y ← (SCKAScheme.oracleSendB
                    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
                  pure (y.1, (y.2,
                    false || currentKEMFailure kem onoff hDet y.2))) =
                  pure (some (s.stB.t - 1, none, msg),
                    (s', currentKEMFailure kem onoff hDet s')) := by
                simp [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
                  scheme, sendB, hct0, hack, hek, msg, s', sendBNoneState]
              rw [hrun, expectedPayoff_pure]
              simp [trackedFailureScore, hfail', hpot]
          | some pk =>
              cases hct1 : s.stB.ct1 with
              | none =>
                  obtain ⟨sk, ht, hekA, hdk⟩ :=
                    online_source_shape kem onoff ecEk ecCt0 ecCt1 s ⟨T, hInv⟩
                      pk st ct0 hek hst hct0 hct1
                  let msg (out : onoff.C₁ × K) : Message Sym :=
                    (some (ecCt1.encode out.1 1), s.stB.ack, s.stB.t, some 1)
                  have hrun : (do
                      let y ← (SCKAScheme.oracleSendB
                        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
                      pure (y.1, (y.2,
                        false || currentKEMFailure kem onoff hDet y.2))) =
                      (fun out =>
                        (some (s.stB.t - 1, some s.stB.t, msg out),
                          (sendBOnState onoff s out.1 out.2 (msg out),
                            currentKEMFailure kem onoff hDet
                              (sendBOnState onoff s out.1 out.2 (msg out))))) <$>
                        onoff.encapsOn st pk := by
                    simp [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
                      scheme, sendB, hct0, hack, hek, hct1, hst, msg,
                      sendBOnState, sendBKeyState]
                  rw [hrun, expectedPayoff_map]
                  have hscore : expectedPayoff (onoff.encapsOn st pk) (fun out =>
                      trackedFailureScore kem onoff
                        (sendBOnState onoff s out.1 out.2 (msg out),
                          currentKEMFailure kem onoff hDet
                            (sendBOnState onoff s out.1 out.2 (msg out)))) =
                      failureAfterBoth kem onoff pk sk st ct0 := by
                    unfold expectedPayoff
                    rw [failureAfterBoth_eq_indicator kem onoff hDet]
                    refine congrArg
                      (fun x : ℝ≥0∞ => Pr[⊥ | onoff.encapsOn st pk] + x) ?_
                    refine tsum_congr fun out => ?_
                    congr 1
                    exact sendBOnState_score kem onoff hDet s sk ct0 out.1 out.2
                      (msg out) ht hdk hct0
                  rw [hscore]
                  have hpot : currentFailurePotential kem onoff s =
                      failureAfterBoth kem onoff pk sk st ct0 := by
                    simp [currentFailurePotential, ht, hct1, hekA, hdk, hst,
                      hct0, optionPair]
                  simp [trackedFailureScore, hpot]
              | some ct1 =>
                  let ich := s.stB.ich + 1
                  let msg : Message Sym :=
                    (some (ecCt1.encode ct1 ich), s.stB.ack, s.stB.t, some 1)
                  let s' := sendBNoneState onoff s { s.stB with ich := ich } msg
                  have hpot : currentFailurePotential kem onoff s' =
                      currentFailurePotential kem onoff s := by
                    exact currentFailurePotential_congr kem onoff s s'
                      rfl rfl rfl rfl rfl rfl rfl
                  have hfail' : currentKEMFailure kem onoff hDet s' = false := by
                    simpa [s', sendBNoneState, currentKEMFailure] using hfail
                  have hrun : (do
                      let y ← (SCKAScheme.oracleSendB
                        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
                      pure (y.1, (y.2,
                        false || currentKEMFailure kem onoff hDet y.2))) =
                      pure (some (s.stB.t - 1, none, msg),
                        (s', currentKEMFailure kem onoff hDet s')) := by
                    simp [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
                      scheme, sendB, hct0, hack, hek, hct1, ich, msg, s',
                      sendBNoneState]
                  rw [hrun, expectedPayoff_pure]
                  simp [trackedFailureScore, hfail', hpot]

/-- Every non-send transition preserves the tracked score at each state in the
support of the tracked oracle computation. -/
lemma tracked_nonSend_score_support_eq [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (ht : ¬IsSendQuery t)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool))
    (hz : z ∈ support
      (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run
        (s, false))) :
    trackedFailureScore kem onoff z.2 =
      trackedFailureScore kem onoff (s, false) := by
  unfold trackedCorrectnessImpl at hz
  change z ∈ support (do
    let y ← ((SCKAScheme.sckaCorrectnessImpl
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst z
  match t with
  | OUnif n =>
      have hy' : y ∈ support
          ((SCKAScheme.oracleUnif (StA onoff Sym) (StB onoff Sym) K
            (Message Sym) n).run s) := by
        simpa [SCKAScheme.sckaCorrectnessImpl] using hy
      obtain ⟨r, rfl⟩ : ∃ r, (r, s) = y := by
        simpa [SCKAScheme.oracleUnif] using hy'
      simp [trackedFailureScore, hfail]
  | OSendA =>
      exact False.elim (ht (by simp [IsSendQuery, isSendQuery]))
  | OSendB =>
      exact False.elim (ht (by simp [IsSendQuery, isSendQuery]))
  | ORecvA n =>
      have hpot := oracleRecvA_preserves_failurePotential kem onoff hDet ecEk
        ecCt0 ecCt1 leak n s hs y hy
      have hfail' := oracleRecvA_preserves_currentFailure kem onoff hDet ecEk
        ecCt0 ecCt1 leak n s hs hfail y hy
      simp [trackedFailureScore, hfail', hpot]
  | ORecvB n =>
      have hpot := oracleRecvB_preserves_failurePotential kem onoff hDet ecEk
        ecCt0 ecCt1 leak n s hs y hy
      have hfail' := oracleRecvB_preserves_currentFailure kem onoff hDet ecEk
        ecCt0 ecCt1 leak n s hs hfail y hy
      simp [trackedFailureScore, hfail', hpot]

/-- Every non-send transition has expected tracked score at most its initial
score from a reachable state without a current KEM failure. -/
lemma tracked_nonSend_score_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (ht : ¬IsSendQuery t)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
        (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run
          (s, false))
        (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) := by
  have hnf : Pr[⊥ |
      ((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run
        (s, false)] = 0 := probFailure_eq_zero
  apply expectedPayoff_le_const_of_support _ _ _ hnf
  intro z hz
  exact le_of_eq (tracked_nonSend_score_support_eq kem onoff hDet ecEk ecCt0 ecCt1
    leak t ht s hs hfail z hz)

end Reduction.Internal

end oppUniKemCKA
