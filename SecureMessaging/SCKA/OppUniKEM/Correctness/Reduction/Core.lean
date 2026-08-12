/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.Invariant
import SecureMessaging.KEM.OnOffKEM.CorrectnessError

/-!
# Opp-UniKEM-CKA Reduction Core

Definitions of the tracked correctness game, for a game state `s`:

* `currentKEMFailure` (`bad s`) — a completed current epoch decapsulated
  inconsistently;
* `currentFailurePotential` (`V s`) — the residual correctness error of
  the KEM epoch in progress;
* `trackedFailureScore` (`S (s, b)`) — `1` once the failure bit `b` is
  set, `V s` otherwise;
* the initial game state, with empty KEM state at epoch one.

The basic laws bound `V` and `S` by `1`, identify the state components
they depend on, and describe how epoch advancement resets or preserves
them; later modules use these laws without unfolding the score.
-/

open ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec

namespace Reduction.Internal

/-- A's initial local state, at epoch one with no KEM material or chunks. -/
def initialA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    StA onoff Sym :=
  { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
    ack := { ekRec := false, ctRec := false } }

/-- B's initial local state, at epoch one with no KEM material or chunks. -/
def initialB
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    StB onoff Sym :=
  { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
    lch := ∅, ack := { ekRec := false, ctRec := false } }

/-- The initial correctness-game state built from the empty party states. -/
def initialGame [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) :=
  SCKAScheme.initGameState (initialA kem onoff) (initialB kem onoff)

/-- The conditional correctness error of the KEM epoch in progress, given
the samples already drawn: `failureAfterKeypair` after A's key pair,
`failureAfterOff` after B's offline sample, `failureAfterBoth` after both,
and `0` when no sample has been drawn or the online sample has completed the
epoch.  When A is one epoch ahead of B, B's material belongs to the
completed preceding epoch and only A's new key pair contributes. -/
noncomputable def currentFailurePotential [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    ℝ≥0∞ :=
  if s.stA.t = s.stB.t then
    if s.stB.ct1.isSome then 0
    else
      match optionPair s.stA.ekA s.stA.dkA,
          optionPair s.stB.stCt s.stB.ct0 with
      | none, none => 0
      | some kp, none => failureAfterKeypair kem onoff kp.1 kp.2
      | none, some off => failureAfterOff kem onoff off.1 off.2
      | some kp, some off =>
          failureAfterBoth kem onoff kp.1 kp.2 off.1 off.2
  else
    match optionPair s.stA.ekA s.stA.dkA with
    | none => 0
    | some kp => failureAfterKeypair kem onoff kp.1 kp.2

/-- The probability that the tracked execution has already produced an
inconsistent epoch (`1` when the failure Boolean is set) or that the epoch
in progress completes inconsistently (`currentFailurePotential` otherwise). -/
noncomputable def trackedFailureScore [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    ℝ≥0∞ :=
  if p.2 then 1 else currentFailurePotential kem onoff p.1

end Reduction.Internal

/-- Whether the current epoch has completed inconsistently: both parties are
in the same epoch, A holds a secret key, B holds both ciphertext components
and a key, and decapsulation disagrees.  The check reads B's own `ct0`, so
the failure is detected as soon as B draws the online sample, before A
decodes the ciphertext.  Incomplete epochs, and the completed epoch left at
B while A is one epoch ahead, give `false`. -/
def currentKEMFailure [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Bool :=
  if s.stA.t = s.stB.t then
    match s.stA.dkA, s.stB.ct0, s.stB.ct1, s.keyB s.stB.t with
    | some dk, some ct0, some ct1, some key =>
        decide (hDet.decapsDet dk (onoff.split.symm (ct0, ct1)) ≠ some key)
    | _, _, _, _ => false
  else false

namespace Reduction.Internal

/-- `currentKEMFailure` is unchanged when all fields inspected by it agree. -/
lemma currentKEMFailure_congr [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (htA : s'.stA.t = s.stA.t) (htB : s'.stB.t = s.stB.t)
    (hdk : s'.stA.dkA = s.stA.dkA) (hct0 : s'.stB.ct0 = s.stB.ct0)
    (hct1 : s'.stB.ct1 = s.stB.ct1)
    (hkey : s'.keyB s'.stB.t = s.keyB s.stB.t) :
    currentKEMFailure kem onoff hDet s' = currentKEMFailure kem onoff hDet s := by
  unfold currentKEMFailure
  rw [htA, htB, hdk, hct0, hct1]
  have hkey' : s'.keyB s.stB.t = s.keyB s.stB.t := by
    calc
      s'.keyB s.stB.t = s'.keyB s'.stB.t := congrArg s'.keyB htB.symm
      _ = s.keyB s.stB.t := hkey
  rw [hkey']

/-- Advancing B into A's epoch with no offline ciphertext cannot set `bad`. -/
lemma currentKEMFailure_recvB_advance_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t + 1) (htA : s'.stA.t = s.stA.t)
    (htB : s'.stB.t = s.stB.t + 1) (hct0 : s'.stB.ct0 = none) :
    currentKEMFailure kem onoff hDet s' = false := by
  simp [currentKEMFailure, htA, htB, hepoch, hct0]

/-- Advancing A one epoch ahead of B cannot set `bad`. -/
lemma currentKEMFailure_recvA_advance_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t) (htA : s'.stA.t = s.stA.t + 1)
    (htB : s'.stB.t = s.stB.t) :
    currentKEMFailure kem onoff hDet s' = false := by
  have hne : s'.stA.t ≠ s'.stB.t := by omega
  simp [currentKEMFailure, hne]

/-- The residual current-epoch failure potential is at most one. -/
lemma currentFailurePotential_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    currentFailurePotential kem onoff s ≤ 1 := by
  classical
  unfold currentFailurePotential
  by_cases ht : s.stA.t = s.stB.t
  · rw [if_pos ht]
    by_cases hon : s.stB.ct1.isSome
    · rw [if_pos hon]
      exact bot_le
    · rw [if_neg hon]
      cases hkp : optionPair s.stA.ekA s.stA.dkA with
      | none =>
          cases hoff : optionPair s.stB.stCt s.stB.ct0 with
          | none =>
              change (0 : ℝ≥0∞) ≤ 1
              exact bot_le
          | some off =>
              change failureAfterOff kem onoff off.1 off.2 ≤ 1
              exact failureAfterOff_le_one kem onoff off.1 off.2
      | some kp =>
          cases hoff : optionPair s.stB.stCt s.stB.ct0 with
          | none =>
              change failureAfterKeypair kem onoff kp.1 kp.2 ≤ 1
              exact failureAfterKeypair_le_one kem onoff kp.1 kp.2
          | some off =>
              change failureAfterBoth kem onoff kp.1 kp.2 off.1 off.2 ≤ 1
              exact failureAfterBoth_le_one kem onoff kp.1 kp.2 off.1 off.2
  · rw [if_neg ht]
    cases hkp : optionPair s.stA.ekA s.stA.dkA with
    | none =>
        change (0 : ℝ≥0∞) ≤ 1
        exact bot_le
    | some kp =>
        change failureAfterKeypair kem onoff kp.1 kp.2 ≤ 1
        exact failureAfterKeypair_le_one kem onoff kp.1 kp.2

/-- The tracked failure score is at most one. -/
lemma trackedFailureScore_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    trackedFailureScore kem onoff p ≤ 1 := by
  unfold trackedFailureScore
  split <;> simp_all [currentFailurePotential_le_one kem onoff]

/-- `currentFailurePotential` is unchanged when all KEM fields it reads agree. -/
lemma currentFailurePotential_congr [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (htA : s'.stA.t = s.stA.t) (htB : s'.stB.t = s.stB.t)
    (hek : s'.stA.ekA = s.stA.ekA) (hdk : s'.stA.dkA = s.stA.dkA)
    (hst : s'.stB.stCt = s.stB.stCt) (hct0 : s'.stB.ct0 = s.stB.ct0)
    (hct1 : s'.stB.ct1 = s.stB.ct1) :
    currentFailurePotential kem onoff s' =
      currentFailurePotential kem onoff s := by
  unfold currentFailurePotential
  rw [htA, htB, hek, hdk, hst, hct0, hct1]

/-- Advancing B into A's epoch preserves the residual failure potential. -/
lemma currentFailurePotential_recvB_advance [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t + 1)
    (htA : s'.stA.t = s.stA.t) (hek : s'.stA.ekA = s.stA.ekA)
    (hdk : s'.stA.dkA = s.stA.dkA) (htB : s'.stB.t = s.stB.t + 1)
    (hst : s'.stB.stCt = none) (hct0 : s'.stB.ct0 = none)
    (hct1 : s'.stB.ct1 = none) :
    currentFailurePotential kem onoff s' =
      currentFailurePotential kem onoff s := by
  have hne : s.stA.t ≠ s.stB.t := by omega
  have heq' : s'.stA.t = s'.stB.t := by omega
  unfold currentFailurePotential
  rw [if_neg hne, if_pos heq', hek, hdk, hst, hct0, hct1]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, optionPair]
  cases s.stA.ekA <;> cases s.stA.dkA <;> rfl

/-- Advancing A after online encapsulation preserves the zero failure potential. -/
lemma currentFailurePotential_recvA_advance [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t) (hon : s.stB.ct1.isSome)
    (htA : s'.stA.t = s.stA.t + 1) (hek : s'.stA.ekA = none)
    (hdk : s'.stA.dkA = none) (htB : s'.stB.t = s.stB.t)
    (hst : s'.stB.stCt = s.stB.stCt) (hct0 : s'.stB.ct0 = s.stB.ct0)
    (hct1 : s'.stB.ct1 = s.stB.ct1) :
    currentFailurePotential kem onoff s' =
      currentFailurePotential kem onoff s := by
  have hne' : s'.stA.t ≠ s'.stB.t := by omega
  have hon' : s'.stB.ct1.isSome := by simpa [hct1] using hon
  unfold currentFailurePotential
  rw [hst, hct0, if_pos hon', if_pos hepoch, if_pos hon, if_neg hne', hek, hdk]
  rfl

end Reduction.Internal

end oppUniKemCKA
