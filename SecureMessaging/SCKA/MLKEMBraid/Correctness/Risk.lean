/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Correctness
import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant
import ToVCVio.OracleComp.ExpectedPayoff
import VCVio.EvalDist.Defs.NeverFails

/-!
# Failure potential of the current epoch

An epoch's potential is `0` without a key pair, the fixed pair's KEM failure probability before
encapsulation, and afterwards the indicator that decapsulation fails to recover the recorded
epoch key (`EpochTranscript.failurePotential`).

For a state consistent with its transcript, `currentEpochFailure_eq_transcript` recovers the
epoch potential when the parties' epochs agree, and gives `0` otherwise. `failurePotential`
uses it while the correctness flag is true, and is `1` once the flag is false.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec
open ENNReal

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- `0` if decapsulating `(ct1, ct2)` with `sk` and deriving the epoch-`e` key gives `key`, and
`1` otherwise. -/
def derivedKeyFailure [DecidableEq P.EpochKey]
    (e : ℕ) (sk : P.SK) (ct1 : P.inc.C₁) (ct2 : P.inc.C₂) (key : P.EpochKey) : ℝ≥0∞ :=
  if (P.hDet.decapsDet sk (P.inc.splitC.symm (ct1, ct2))).map (fun k => P.kdfOK k e) = some key
  then 0 else 1

/-- The current-epoch contribution for a key generator in state `gen` and an encapsulator in
state `encap`, where `keys` is the encapsulator's epoch-key table. Before encapsulation, the
sampling cases use `decapsFailureProb` for the fixed key pair. After encapsulation, the comparison
cases use `derivedKeyFailure` if the encapsulator has recorded its epoch key, and `0` otherwise.
All remaining state pairs give `0`. -/
noncomputable def pairFailure [DecidableEq P.K] [DecidableEq P.EpochKey]
    (gen encap : State P AuthState) (keys : ℕ → Option P.EpochKey) : ℝ≥0∞ :=
  let test := fun sk ct1 ct2 =>
    match keys gen.epoch with
    | none => 0
    | some key => derivedKeyFailure gen.epoch sk ct1 ct2 key
  match gen, encap with
  | .keysSampled _ _ sk vec enc, .noHeaderReceived .. =>
      P.inc.decapsFailureProb P.hDet P.hEnc2 enc.payload.1 vec sk
  | .keysSampled _ _ sk vec enc, .headerReceived .. =>
      P.inc.decapsFailureProb P.hDet P.hEnc2 enc.payload.1 vec sk
  | .keysSampled _ _ sk vec _, .ct1Sampled _ _ hdr st ct1 _ _ =>
      test sk ct1 (P.hEnc2.encaps2Det st hdr vec)
  | .headerSent _ _ sk _ enc, .ct1Sampled _ _ hdr st ct1 _ _ =>
      test sk ct1 (P.hEnc2.encaps2Det st hdr enc.payload)
  | .ct1Received _ _ sk _ enc, .ct1Sampled _ _ hdr st ct1 _ _ =>
      test sk ct1 (P.hEnc2.encaps2Det st hdr enc.payload)
  | .headerSent _ _ sk _ _, .ekReceivedCt1Sampled _ _ st ct1 hdr vec _ =>
      test sk ct1 (P.hEnc2.encaps2Det st hdr vec)
  | .ct1Received _ _ sk _ _, .ekReceivedCt1Sampled _ _ st ct1 hdr vec _ =>
      test sk ct1 (P.hEnc2.encaps2Det st hdr vec)
  | .ct1Received _ _ sk _ enc, .ct1Acknowledged _ _ hdr st ct1 _ =>
      test sk ct1 (P.hEnc2.encaps2Det st hdr enc.payload)
  | .ct1Received _ _ sk ct1 _, .ct2Sampled _ _ enc =>
      test sk ct1 enc.payload.1
  | .ekSentCt1Received _ _ sk ct1 _, .ct2Sampled _ _ enc =>
      test sk ct1 enc.payload.1
  | _, _ => 0

/-- `pairFailure` of the key generator and encapsulator when their epochs agree, and `0`
otherwise. -/
noncomputable def currentEpochFailure [DecidableEq P.K] [DecidableEq P.EpochKey]
    (s : GameState P AuthState) : ℝ≥0∞ :=
  let gen := if s.stA.controlPosition.isGenerator then s.stA else s.stB
  let encap := if s.stA.controlPosition.isGenerator then s.stB else s.stA
  let keys := if s.stA.controlPosition.isGenerator then s.keyB else s.keyA
  if gen.epoch ≠ encap.epoch then 0 else pairFailure gen encap keys

/-- `currentEpochFailure` while the correctness flag is true, and `1` once it is false. -/
noncomputable def failurePotential [DecidableEq P.K] [DecidableEq P.EpochKey]
    (s : GameState P AuthState) : ℝ≥0∞ :=
  if s.correct then currentEpochFailure s else 1

/-- The failure potential recorded for epoch `e`: zero without a key pair, the key pair's
`decapsFailureProb` before encapsulation, and `derivedKeyFailure` of the recorded samples
after encapsulation. -/
noncomputable def EpochTranscript.failurePotential [DecidableEq P.K] [DecidableEq P.EpochKey]
    (tr : EpochTranscript P) (e : ℕ) : ℝ≥0∞ :=
  match tr.keypair, tr.encaps1 with
  | none, _ => 0
  | some (pk, sk), none =>
      P.inc.decapsFailureProb P.hDet P.hEnc2 (P.inc.toHeader pk) (P.inc.toVector pk) sk
  | some (pk, sk), some (encapsState, ct1, key) =>
      derivedKeyFailure e sk ct1
        (P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk))
        (P.kdfOK key e)

/-- In a consistent state, `currentEpochFailure` is the transcript potential at equal party epochs
and `0` otherwise. -/
theorem currentEpochFailure_eq_transcript [DecidableEq P.K] [DecidableEq P.EpochKey]
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) :
    currentEpochFailure s =
      if s.stA.epoch = s.stB.epoch then
        (T s.stA.epoch).failurePotential s.stA.epoch
      else 0 := by
  rcases hT with ⟨_, hControl, hPair, _, _, _, hEncaps, hLocalA, hLocalB, _, hKeys⟩
  -- For an allowed pair at epoch `e`, the local payload invariants identify the fields of the
  -- two states with the transcript samples of `e`.
  have hRecover : ∀
      (gen encap : State P AuthState) (keys : ℕ → Option P.EpochKey) (e : ℕ),
      gen.epoch = e →
      encap.epoch = e →
      AllowedStatePair gen encap →
      LocalPayloadInv auth ik T gen →
      LocalPayloadInv auth ik T encap →
      (keys e =
        if 0 < e ∧ e ≤ encap.completedEpoch then
          (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e)
        else none) →
      (∀ {c : P.inc.St × P.inc.C₁ × P.K},
        (T e).encaps1 = some c →
          0 < e ∧ e ≤ encap.completedEpoch ∧
            ∃ kp, (T e).keypair = some kp) →
      pairFailure gen encap keys = (T e).failurePotential e := by
    intro gen encap keys e hGenEpoch hEncapEpoch hAllowed
      hLocalGen hLocalEncap hKeyPeer hEncapsCurrent
    cases hg : gen <;> simp [AllowedStatePair, hg] at hAllowed
    all_goals cases he : encap
    all_goals simp [he] at hAllowed
    all_goals
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
    next =>
      rcases hLocalGen with ⟨_, hkp, henc⟩
      simp [pairFailure, EpochTranscript.failurePotential, hkp, henc]
    next =>
      rcases hLocalGen with ⟨_, pk, hkp, hvec, _, hpayload⟩
      cases hc : (T e).encaps1 with
      | none =>
          simp [pairFailure, EpochTranscript.failurePotential, hkp, hc, hvec, hpayload]
      | some c =>
          have hf := hEncapsCurrent hc
          simp [he, State.completedEpoch, State.epoch, hEncapEpoch] at hf
          omega
    next =>
      rcases hLocalGen with ⟨_, pk, hkp, hvec, _, hpayload⟩
      rcases hLocalEncap with ⟨_, henc, _⟩
      simp [pairFailure, EpochTranscript.failurePotential, hkp, henc, hvec, hpayload]
    next =>
      rcases hLocalGen with ⟨_, pk, hkp, hvec, _, _⟩
      rcases hLocalEncap with ⟨_, pk', sk', key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc, hvec, hhdrGen]
    next =>
      rcases hLocalGen with ⟨_, pk, es, c1, k, hkp, henc', _, hEncOK⟩
      have hvec := hEncOK.2
      rcases hLocalEncap with ⟨_, pk', sk', key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc', hvec, hhdrGen, hencEq]
    next =>
      rcases hLocalGen with ⟨_, pk, es, c1, k, hkp, henc', _, _⟩
      rcases hLocalEncap with
        ⟨_, pk', sk', key, hkp', henc, hhdr, hvec', _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      have hvecGen := hvec'.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toVector x.1) hkpEq).symm
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc', hhdrGen, hvecGen, hencEq]
    next =>
      rcases hLocalGen with ⟨_, pk, es, k, hkp, henc', hEncOK⟩
      have hvec := hEncOK.2
      rcases hLocalEncap with ⟨_, pk', sk', key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc', hvec,
        hhdrGen, hencEq]
    next =>
      rcases hLocalGen with ⟨_, pk, es, k, hkp, henc', _⟩
      rcases hLocalEncap with
        ⟨_, pk', sk', key, hkp', henc, hhdr, hvec', _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      have hvecGen := hvec'.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toVector x.1) hkpEq).symm
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc', hhdrGen,
        hvecGen, hencEq]
    next =>
      rcases hLocalGen with ⟨_, pk, es, k, hkp, henc', hEncOK⟩
      have hvec := hEncOK.2
      rcases hLocalEncap with ⟨_, pk', sk', key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc', hvec,
        hhdrGen, hencEq]
    next =>
      rcases hLocalGen with ⟨_, pk, es, k, hkp, henc', -⟩
      rcases hLocalEncap with ⟨_, pk', sk', es', c1', k', hkp', henc, hEncOK'⟩
      have hpayload := hEncOK'.2
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := hkp.symm.trans hkp'
      have hencEq := henc'.symm.trans henc
      simp only [Option.some.injEq, Prod.mk.injEq] at hkpEq hencEq
      obtain ⟨rfl, rfl⟩ := hkpEq
      obtain ⟨rfl, rfl, rfl⟩ := hencEq
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc', hpayload]
    next =>
      rcases hLocalGen with ⟨_, pk, es, k, hkp, henc', _⟩
      rcases hLocalEncap with ⟨_, pk', sk', es', c1', k', hkp', henc, hEncOK'⟩
      have hpayload := hEncOK'.2
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := hkp.symm.trans hkp'
      have hencEq := henc'.symm.trans henc
      simp only [Option.some.injEq, Prod.mk.injEq] at hkpEq hencEq
      obtain ⟨rfl, rfl⟩ := hkpEq
      obtain ⟨rfl, rfl, rfl⟩ := hencEq
      simp [pairFailure, EpochTranscript.failurePotential, State.epoch,
        hGenEpoch, hKeyPeer, hkp, henc', hpayload]
  -- Identify the generator and the encapsulator from the roles.
  have hRoleA := (hControl.roles true).1
  have hRoleB := (hControl.roles false).1
  simp only [GameState.stateAt, ↓reduceIte] at hRoleA
  simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hRoleB
  by_cases hepoch : s.stA.epoch = s.stB.epoch
  · rw [if_pos hepoch]
    by_cases hrole : s.stA.controlPosition.isGenerator = true
    · have hAllowed := hPair.1.1 hepoch hrole
      have hKeyPeer := hKeys false s.stA.epoch
      simp only [Bool.false_eq_true, ↓reduceIte] at hKeyPeer
      rw [hrole] at hRoleA
      have hOdd : s.stA.epoch % 2 = 1 := of_decide_eq_true hRoleA.symm
      have hEncapsCurrent :
          ∀ {c : P.inc.St × P.inc.C₁ × P.K},
            (T s.stA.epoch).encaps1 = some c →
              0 < s.stA.epoch ∧
              s.stA.epoch ≤ s.stB.completedEpoch ∧
                ∃ kp, (T s.stA.epoch).keypair = some kp := by
        intro c hc
        rcases hEncaps s.stA.epoch c.1 c.2.1 c.2.2 hc with ⟨hpos, hbound, pk, sk, hkp, _⟩
        have hbound' : s.stA.epoch ≤ s.stB.completedEpoch := by simpa [hOdd] using hbound
        exact ⟨hpos, hbound', (pk, sk), hkp⟩
      simp only [currentEpochFailure, hrole, if_true]
      rw [if_neg (not_ne_iff.mpr hepoch)]
      change pairFailure s.stA s.stB s.keyB = (T s.stA.epoch).failurePotential s.stA.epoch
      exact hRecover s.stA s.stB s.keyB s.stA.epoch rfl hepoch.symm
        hAllowed hLocalA hLocalB hKeyPeer hEncapsCurrent
    · have hroleFalse : s.stA.controlPosition.isGenerator = false :=
        Bool.eq_false_of_not_eq_true hrole
      rw [hroleFalse] at hRoleA
      have hEven : s.stA.epoch % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one s.stA.epoch with hzero | hone
        · exact hzero
        · simp [hone] at hRoleA
      have hroleB : s.stB.controlPosition.isGenerator = true := by
        simpa [← hepoch, hEven] using hRoleB
      have hAllowed := hPair.2.1 hepoch.symm hroleB
      have hKeyPeer := hKeys true s.stA.epoch
      simp only [↓reduceIte] at hKeyPeer
      have hEncapsCurrent :
          ∀ {c : P.inc.St × P.inc.C₁ × P.K},
            (T s.stA.epoch).encaps1 = some c →
              0 < s.stA.epoch ∧
              s.stA.epoch ≤ s.stA.completedEpoch ∧
                ∃ kp, (T s.stA.epoch).keypair = some kp := by
        intro c hc
        rcases hEncaps s.stA.epoch c.1 c.2.1 c.2.2 hc with ⟨hpos, hbound, pk, sk, hkp, _⟩
        have hbound' : s.stA.epoch ≤ s.stA.completedEpoch := by simpa [hEven] using hbound
        exact ⟨hpos, hbound', (pk, sk), hkp⟩
      simp only [currentEpochFailure, hroleFalse, Bool.false_eq_true, ↓reduceIte]
      rw [if_neg (not_ne_iff.mpr hepoch.symm)]
      change pairFailure s.stB s.stA s.keyA = (T s.stA.epoch).failurePotential s.stA.epoch
      exact hRecover s.stB s.stA s.keyA s.stA.epoch hepoch.symm rfl
        hAllowed hLocalB hLocalA hKeyPeer hEncapsCurrent
  · rw [if_neg hepoch]
    by_cases hrole : s.stA.controlPosition.isGenerator = true
    · simp only [currentEpochFailure, hrole, if_true]
      rw [if_pos hepoch]
    · have hroleFalse : s.stA.controlPosition.isGenerator = false :=
        Bool.eq_false_of_not_eq_true hrole
      simp only [currentEpochFailure, hroleFalse, Bool.false_eq_true, ↓reduceIte]
      rw [if_pos (Ne.symm hepoch)]

/-- The version of `currentEpochFailure_eq_transcript` using `party` to name the epoch. -/
theorem currentEpochFailure_eq_transcript_party [DecidableEq P.K] [DecidableEq P.EpochKey]
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) :
    currentEpochFailure s =
      if (s.stateAt party).epoch = (s.stateAt (!party)).epoch then
        (T (s.stateAt party).epoch).failurePotential (s.stateAt party).epoch
      else 0 := by
  rw [currentEpochFailure_eq_transcript auth hT]
  cases party
  · by_cases heq : s.stA.epoch = s.stB.epoch
    · simp only [GameState.stateAt, Bool.not_false, Bool.false_eq_true, ↓reduceIte, heq]
    · simp only [GameState.stateAt, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        if_neg heq, if_neg (Ne.symm heq)]
  · rfl

end MLKEMBraid
