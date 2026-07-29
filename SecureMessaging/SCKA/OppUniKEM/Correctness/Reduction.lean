/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect
import SecureMessaging.SCKA.OppUniKEM.Correctness.KEM
import ToVCVio.OracleComp.ExpectedPayoff
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Opp-UniKEM-CKA — Reduction to KEM Correctness

Main results, for `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak`,
`G(Adv) := SCKAScheme.correctnessExp Π Adv`, `ε := kem.correctnessError`,
and
correct erasure codes with positive reconstruction thresholds:

* `correctness_failure_le_reduction` — for at most `q` send queries
  (`SendQueryBound Adv q`), `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge_reduction` — equivalently,
  `Pr[G(Adv) = true] ≥ 1 - q · ε`;
* `correctness_failure_le_of_sendBFailureBound` — the analogous bound from
  stepwise premises (`SendBFailureBound`, `NonSendBPreservesCurrent`,
  `SendBQueryBound`).

Abbreviate `join := onoff.split⁻¹` and
`Run o s := ((SCKAScheme.sckaCorrectnessImpl Π) o).run s`.  In the proof,
`ε` is computed as `factorCorrectnessError kem onoff hDet`, which equals
`kem.correctnessError` (`factorCorrectnessError_eq`).

## Tracked game

* `bad s` (`currentKEMFailure`) — `true` iff `s.stA.t = s.stB.t` and the
  current epoch has completed inconsistently:
  `s.stA.dkA = some sk`, `s.stB.ct0 = some ct₀`, `s.stB.ct1 = some ct₁`,
  `s.keyB s.stB.t = some k`, and
  `hDet.decapsDet sk (join (ct₀, ct₁)) ≠ some k`.
* `Ô` (`trackedCorrectnessImpl`) — the game extended with a Boolean that
  stays `true` once set:
  `Ô o (s, b) := do (r, s') ← Run o s; return (r, (s', b ∨ bad s'))`.
* `J` (`trackedInv`) —
  `J (s, b) := b = true ∨ (reachableInv s ∧ bad s = false)`.

## Failure probabilities

With the conditional errors `χ`, `φ`, `ψ` of `Correctness.KEM`, associate to
a tracked state the probability that it has already failed, or that its
epoch in progress completes inconsistently:

```text
V s := 0                     no sample drawn, or epoch completed
       φ (pk, sk)            only the key pair (stA.ekA, stA.dkA) drawn
       ψ (st, ct₀)           only the offline sample (stB.stCt, stB.ct0) drawn
       χ (pk, sk, st, ct₀)   both drawn

S (s, b) := if b then 1 else V s
E_X[f]   := Pr[X = ⊥] + Σ x, Pr[X = x] · f x
```

(`currentFailurePotential`, `trackedFailureScore`, `expectedPayoff`).  The
epoch in progress reads A's key pair, and B's offline sample when
`s.stA.t = s.stB.t`; when `s.stA.t = s.stB.t + 1`, B's material belongs to
the completed previous epoch and is ignored.

## One step

For every oracle `o` and every `(s, b)` with `J (s, b)`:

```text
(r, (s', b')) ∈ supp (Ô o (s, b)) → J (s', b')
E_{Ô o (s, b)}[S] ≤ S (s, b) + ε      if o ∈ {SendA, SendB}
E_{Ô o (s, b)}[S] ≤ S (s, b)          otherwise.
```

Drawing the epoch's first sample turns `V = 0` into expectation at most `ε`
(the averaging identities of `Correctness.KEM`); drawing the other
first-stage sample has expectation exactly `V`; drawing the online sample
completes the epoch, setting `b' = bad s'` with expectation `χ = V` and
`V s' = 0`.  Receive oracles move no KEM material; their cases are proved
for every message index.

## Composition

1. `tracked_score_adversary_le` — induction over the adversary's query
   tree: `J (s, b)` and at most `q` sends give
   `E[S final] ≤ S (s, b) + q · ε`; initially `S (s₀, false) = 0`.
2. `tracked_run_project` — dropping the Boolean projects the tracked run
   onto the real game; by `J`, `correct = false` forces `b = true`, i.e.
   `S = 1`.  Hence `Pr[G(Adv) = false] ≤ q · ε`, and
   `Pr[G(Adv) = true] ≥ 1 - q · ε` follows since `G(Adv)` is total.

## Stepwise interface

`correctness_failure_le_of_sendBFailureBound` replaces the conditional
errors by two premises:
`SendBFailureBound δ` — from a state with consistent current KEM material,
one `SendB` call sets `bad` with probability at most `δ` — and
`NonSendBPreservesCurrent` — no other oracle can set `bad`.  It bounds
`Pr[G(Adv) = false] ≤ q · δ` for at most `q` `SendB` queries
(`SendBQueryBound Adv q`).
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec

section Reduction

variable [DecidableEq Sym]

/-! ## Quantitative correctness interface -/

private def initialA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    StA onoff Sym :=
  { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
    ack := { ekRec := false, ctRec := false } }

private def initialB
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    StB onoff Sym :=
  { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
    lch := ∅, ack := { ekRec := false, ctRec := false } }

private def initialGame [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) :=
  SCKAScheme.initGameState (initialA kem onoff) (initialB kem onoff)

/-- The conditional correctness error of the KEM epoch in progress, given
the samples already drawn: `failureAfterKeypair` after A's key pair,
`failureAfterOff` after B's offline sample, `failureAfterBoth` after both,
and `0` when no sample has been drawn or the online sample has completed the
epoch.  When A is one epoch ahead of B, B's material belongs to the
completed preceding epoch and only A's new key pair contributes. -/
private noncomputable def currentFailurePotential [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    ℝ≥0∞ :=
  if s.stA.t = s.stB.t then
    if s.stB.ct1.isSome then 0
    else
      match optionPair s.stA.ekA s.stA.dkA,
          optionPair s.stB.stCt s.stB.ct0 with
      | none, none => 0
      | some kp, none => failureAfterKeypair kem onoff hDet kp.1 kp.2
      | none, some off => failureAfterOff kem onoff hDet off.1 off.2
      | some kp, some off =>
          failureAfterBoth kem onoff hDet kp.1 kp.2 off.1 off.2
  else
    match optionPair s.stA.ekA s.stA.dkA with
    | none => 0
    | some kp => failureAfterKeypair kem onoff hDet kp.1 kp.2

/-- The probability that the tracked execution has already produced an
inconsistent epoch (`1` when the failure Boolean is set) or that the epoch
in progress completes inconsistently (`currentFailurePotential`
otherwise). -/
private noncomputable def trackedFailureScore [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    ℝ≥0∞ :=
  if p.2 then 1 else currentFailurePotential kem onoff hDet p.1

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

private lemma currentKEMFailure_congr [DecidableEq K]
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

private lemma currentKEMFailure_recvB_advance_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t + 1) (htA : s'.stA.t = s.stA.t)
    (htB : s'.stB.t = s.stB.t + 1) (hct0 : s'.stB.ct0 = none) :
    currentKEMFailure kem onoff hDet s' = false := by
  simp [currentKEMFailure, htA, htB, hepoch, hct0]

private lemma currentKEMFailure_recvA_advance_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t) (htA : s'.stA.t = s.stA.t + 1)
    (htB : s'.stB.t = s.stB.t) :
    currentKEMFailure kem onoff hDet s' = false := by
  have hne : s'.stA.t ≠ s'.stB.t := by omega
  simp [currentKEMFailure, hne]

private lemma currentFailurePotential_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    currentFailurePotential kem onoff hDet s ≤ 1 := by
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
              change failureAfterOff kem onoff hDet off.1 off.2 ≤ 1
              exact failureAfterOff_le_one kem onoff hDet off.1 off.2
      | some kp =>
          cases hoff : optionPair s.stB.stCt s.stB.ct0 with
          | none =>
              change failureAfterKeypair kem onoff hDet kp.1 kp.2 ≤ 1
              exact failureAfterKeypair_le_one kem onoff hDet kp.1 kp.2
          | some off =>
              change failureAfterBoth kem onoff hDet kp.1 kp.2 off.1 off.2 ≤ 1
              exact failureAfterBoth_le_one kem onoff hDet kp.1 kp.2 off.1 off.2
  · rw [if_neg ht]
    cases hkp : optionPair s.stA.ekA s.stA.dkA with
    | none =>
        change (0 : ℝ≥0∞) ≤ 1
        exact bot_le
    | some kp =>
        change failureAfterKeypair kem onoff hDet kp.1 kp.2 ≤ 1
        exact failureAfterKeypair_le_one kem onoff hDet kp.1 kp.2

private lemma trackedFailureScore_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    trackedFailureScore kem onoff hDet p ≤ 1 := by
  unfold trackedFailureScore
  split <;> simp_all [currentFailurePotential_le_one kem onoff hDet]

private lemma currentFailurePotential_congr [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (htA : s'.stA.t = s.stA.t) (htB : s'.stB.t = s.stB.t)
    (hek : s'.stA.ekA = s.stA.ekA) (hdk : s'.stA.dkA = s.stA.dkA)
    (hst : s'.stB.stCt = s.stB.stCt) (hct0 : s'.stB.ct0 = s.stB.ct0)
    (hct1 : s'.stB.ct1 = s.stB.ct1) :
    currentFailurePotential kem onoff hDet s' =
      currentFailurePotential kem onoff hDet s := by
  unfold currentFailurePotential
  rw [htA, htB, hek, hdk, hst, hct0, hct1]

private lemma currentFailurePotential_recvB_advance [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t + 1)
    (htA : s'.stA.t = s.stA.t) (hek : s'.stA.ekA = s.stA.ekA)
    (hdk : s'.stA.dkA = s.stA.dkA) (htB : s'.stB.t = s.stB.t + 1)
    (hst : s'.stB.stCt = none) (hct0 : s'.stB.ct0 = none)
    (hct1 : s'.stB.ct1 = none) :
    currentFailurePotential kem onoff hDet s' =
      currentFailurePotential kem onoff hDet s := by
  have hne : s.stA.t ≠ s.stB.t := by omega
  have heq' : s'.stA.t = s'.stB.t := by omega
  unfold currentFailurePotential
  rw [if_neg hne, if_pos heq', hek, hdk, hst, hct0, hct1]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, optionPair]
  cases s.stA.ekA <;> cases s.stA.dkA <;> rfl

private lemma currentFailurePotential_recvA_advance [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hepoch : s.stA.t = s.stB.t) (hon : s.stB.ct1.isSome)
    (htA : s'.stA.t = s.stA.t + 1) (hek : s'.stA.ekA = none)
    (hdk : s'.stA.dkA = none) (htB : s'.stB.t = s.stB.t)
    (hst : s'.stB.stCt = s.stB.stCt) (hct0 : s'.stB.ct0 = s.stB.ct0)
    (hct1 : s'.stB.ct1 = s.stB.ct1) :
    currentFailurePotential kem onoff hDet s' =
      currentFailurePotential kem onoff hDet s := by
  have hne' : s'.stA.t ≠ s'.stB.t := by omega
  unfold currentFailurePotential
  rw [if_pos hepoch, if_pos hon, if_neg hne', hek, hdk]
  rfl

private def installAKeypair
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pk : PK) (sk : SK) :=
  { s with stA := { s.stA with ekA := some pk, dkA := some sk } }

private def sendAKeygenState
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (kp : PK × SK) :=
  let ich := if s.stA.ack.ekRec then 0 else 1
  let ch? : Option (ℕ × Sym) :=
    if s.stA.ack.ekRec then none else some (ecEk.encode kp.1 ich)
  let msg : Message Sym := (ch?, s.stA.ack, s.stA.t, none)
  { s with
    stA := { s.stA with ekA := some kp.1, dkA := some kp.2, ich := ich }
    tcurA := s.stA.t - 1
    msgA := Function.update s.msgA (s.nA + 1) (some (msg, s.stA.t - 1))
    nA := s.nA + 1
    correct := s.correct && decide (s.tcurA ≤ s.stA.t - 1) }

private def sendBNoneState
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB' : StB onoff Sym) (msg : Message Sym) :=
  { s with
    stB := stB'
    tcurB := s.stB.t - 1
    msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
    nB := s.nB + 1
    correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) }

private def sendBKeyState [DecidableEq K]
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB' : StB onoff Sym) (msg : Message Sym) (key : K) :=
  let keyB' := Function.update s.keyB s.stB.t (some key)
  { s with
    stB := stB'
    tcurB := s.stB.t - 1
    keyB := keyB'
    msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
    nB := s.nB + 1
    correct := s.correct
      && decide (s.tcurB ≤ s.stB.t - 1)
      && (s.keyB s.stB.t).isNone
      && ((s.keyA s.stB.t).isNone || s.keyA s.stB.t == some key)
      && (List.range (s.stB.t - 1 + 1)).all (fun t =>
        t = 0 || (keyB' t).isSome) }

private def sendBOffState
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (off : onoff.St × onoff.C₀) (ich : ℕ) (msg : Message Sym) :=
  sendBNoneState onoff s
    { s.stB with stCt := some off.1, ct0 := some off.2, ich := ich } msg

private def sendBOnState [DecidableEq K]
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (ct1 : onoff.C₁) (key : K) (msg : Message Sym) :=
  sendBKeyState onoff s { s.stB with ct1 := some ct1, ich := 1 } msg key

private def sendBOffOnState [DecidableEq K]
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (off : onoff.St × onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (msg : Message Sym) :=
  sendBKeyState onoff s
    { s.stB with
      stCt := some off.1
      ct0 := some off.2
      ct1 := some ct1
      ich := 1 } msg key

private lemma keygen_failurePotential_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hdk : s.stA.dkA = none) :
    (Pr[⊥ | kem.keygen] + ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
      currentFailurePotential kem onoff hDet
        (installAKeypair onoff s kp.1 kp.2)) ≤
      currentFailurePotential kem onoff hDet s +
        factorCorrectnessError kem onoff hDet := by
  rcases hs with ⟨world, hInv⟩
  have hek : s.stA.ekA = none := by
    have hshape := hInv.keypairAShape
    simpa [hdk] using hshape
  by_cases ht : s.stA.t = s.stB.t
  · have hkpnone : (world s.stA.t).keypair = none := by
      simpa [hdk, hek, optionPair] using hInv.keypairA
    have honnone : (world s.stA.t).on = none := by
      by_contra hne
      have his := (world s.stA.t).on_keypair (Option.isSome_iff_ne_none.mpr hne)
      simpa [hkpnone] using his
    have hct1 : s.stB.ct1 = none := by
      have hmap := hInv.onB
      rw [← ht, honnone] at hmap
      simpa using hmap.symm
    cases hct0 : s.stB.ct0 with
    | none =>
        have hst : s.stB.stCt = none := by
          have hshape := hInv.offBShape
          simpa [hct0] using hshape
        simpa [currentFailurePotential, installAKeypair, ht, hct1, hdk, hek,
          hct0, hst, optionPair] using
          (le_of_eq (factor_failure_tower_keypair kem onoff hDet).symm)
    | some ct0 =>
        have hstSome : s.stB.stCt.isSome := by
          simpa [hct0] using hInv.offBShape
        obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hstSome
        simpa [currentFailurePotential, installAKeypair, ht, hct1, hdk, hek,
          hct0, hst, optionPair, failureAfterOff] using
          (le_self_add : failureAfterOff kem onoff hDet st ct0 ≤
            failureAfterOff kem onoff hDet st ct0 +
              factorCorrectnessError kem onoff hDet)
  · have hepoch : s.stA.t = s.stB.t + 1 := by
      have hepochBounds := hInv.epochs
      omega
    simpa [currentFailurePotential, installAKeypair, ht, hdk, hek, optionPair] using
      (le_of_eq (factor_failure_tower_keypair kem onoff hDet).symm)

private lemma installAKeypair_currentKEMFailure_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hdk : s.stA.dkA = none)
    (pk : PK) (sk : SK) :
    currentKEMFailure kem onoff hDet (installAKeypair onoff s pk sk) = false := by
  rcases hs with ⟨world, hInv⟩
  by_cases ht : s.stA.t = s.stB.t
  · have hek : s.stA.ekA = none := by
      have hshape := hInv.keypairAShape
      simpa [hdk] using hshape
    have hkpnone : (world s.stA.t).keypair = none := by
      simpa [hdk, hek, optionPair] using hInv.keypairA
    have honnone : (world s.stA.t).on = none := by
      by_contra hne
      have his := (world s.stA.t).on_keypair (Option.isSome_iff_ne_none.mpr hne)
      simpa [hkpnone] using his
    have hct1 : s.stB.ct1 = none := by
      have hmap := hInv.onB
      rw [← ht, honnone] at hmap
      simpa using hmap.symm
    simp [currentKEMFailure, installAKeypair, ht, hct1]
  · simp [currentKEMFailure, installAKeypair, ht]

private def installBOff
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (st : onoff.St) (ct0 : onoff.C₀) :=
  { s with stB := { s.stB with stCt := some st, ct0 := some ct0 } }

private lemma off_failurePotential_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hct0 : s.stB.ct0 = none) :
    (Pr[⊥ | onoff.encapsOff] +
      ∑' off : onoff.St × onoff.C₀, Pr[= off | onoff.encapsOff] *
      currentFailurePotential kem onoff hDet
        (installBOff onoff s off.1 off.2)) ≤
      currentFailurePotential kem onoff hDet s +
        factorCorrectnessError kem onoff hDet := by
  rcases hs with ⟨world, hInv⟩
  have hst : s.stB.stCt = none := by
    have hshape := hInv.offBShape
    simpa [hct0] using hshape
  have hoffnone : (world s.stB.t).off = none := by
    simpa [hct0, hst, optionPair] using hInv.offB
  have ht : s.stA.t = s.stB.t := by
    by_contra hne
    have hepochBounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hcomplete := hInv.pastComplete s.stB.t hInv.epochPosB hlt
    have honSome : (world s.stB.t).on.isSome := by
      simpa [EpochTranscript.key] using hcomplete
    have hoffSome := (world s.stB.t).on_off honSome
    simp [hoffnone] at hoffSome
  have hct1 : s.stB.ct1 = none := by
    have honnone : (world s.stB.t).on = none := by
      by_contra hne
      have honSome := Option.isSome_iff_ne_none.mpr hne
      simpa [hoffnone] using (world s.stB.t).on_off honSome
    have hmap := hInv.onB
    rw [honnone] at hmap
    simpa using hmap.symm
  cases hdk : s.stA.dkA with
  | none =>
      have hek : s.stA.ekA = none := by
        have hshape := hInv.keypairAShape
        simpa [hdk] using hshape
      simpa [currentFailurePotential, installBOff, ht, hct1, hdk, hek,
        hct0, hst, optionPair] using
        (le_of_eq (factor_failure_tower_off kem onoff hDet).symm)
  | some sk =>
      have hekSome : s.stA.ekA.isSome := by
        simpa [hdk] using hInv.keypairAShape
      obtain ⟨pk, hek⟩ := Option.isSome_iff_exists.mp hekSome
      simpa [currentFailurePotential, installBOff, ht, hct1, hdk, hek,
        hct0, hst, optionPair, failureAfterKeypair] using
        (le_self_add : failureAfterKeypair kem onoff hDet pk sk ≤
          failureAfterKeypair kem onoff hDet pk sk +
            factorCorrectnessError kem onoff hDet)

private lemma online_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (pk : PK) (st : onoff.St) (ct0 : onoff.C₀)
    (hekB : s.stB.ekA = some pk) (hst : s.stB.stCt = some st)
    (hct0 : s.stB.ct0 = some ct0) (hct1 : s.stB.ct1 = none) :
    ∃ sk, s.stA.t = s.stB.t ∧ s.stA.ekA = some pk ∧
      s.stA.dkA = some sk := by
  rcases hs with ⟨world, hInv⟩
  obtain ⟨sk, hkpB⟩ := hInv.decodedEk pk hekB
  have honnone : (world s.stB.t).on = none := by
    have hmap := hInv.onB
    rw [hct1] at hmap
    cases hon : (world s.stB.t).on with
    | none => rfl
    | some pair => simp [hon] at hmap
  have ht : s.stA.t = s.stB.t := by
    by_contra hne
    have hbounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hcomplete := hInv.pastComplete s.stB.t hInv.epochPosB hlt
    simp [EpochTranscript.key, honnone] at hcomplete
  have hkpA : (world s.stA.t).keypair = optionPair s.stA.ekA s.stA.dkA :=
    hInv.keypairA
  rw [ht, hkpB] at hkpA
  cases hekA : s.stA.ekA <;> cases hdkA : s.stA.dkA <;>
    simp [hekA, hdkA, optionPair] at hkpA
  obtain ⟨rfl, rfl⟩ := hkpA
  exact ⟨sk, ht, rfl, rfl⟩

private lemma newOff_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (pk : PK) (hekB : s.stB.ekA = some pk) (hct0 : s.stB.ct0 = none) :
    ∃ sk, s.stA.t = s.stB.t ∧ s.stA.ekA = some pk ∧
      s.stA.dkA = some sk := by
  rcases hs with ⟨world, hInv⟩
  obtain ⟨sk, hkpB⟩ := hInv.decodedEk pk hekB
  have hst : s.stB.stCt = none := by
    have hshape := hInv.offBShape
    simpa [hct0] using hshape
  have hoffnone : (world s.stB.t).off = none := by
    simpa [hct0, hst, optionPair] using hInv.offB
  have ht : s.stA.t = s.stB.t := by
    by_contra hne
    have hbounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hcomplete := hInv.pastComplete s.stB.t hInv.epochPosB hlt
    have honSome : (world s.stB.t).on.isSome := by
      simpa [EpochTranscript.key] using hcomplete
    have hoffSome := (world s.stB.t).on_off honSome
    simp [hoffnone] at hoffSome
  have hkpA := hInv.keypairA
  rw [ht, hkpB] at hkpA
  cases hekA : s.stA.ekA <;> cases hdkA : s.stA.dkA <;>
    simp [hekA, hdkA, optionPair] at hkpA
  obtain ⟨rfl, rfl⟩ := hkpA
  exact ⟨sk, ht, rfl, rfl⟩

private def installBOn
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (ct1 : onoff.C₁) (key : K) :=
  { s with
    stB := { s.stB with ct1 := some ct1 }
    keyB := Function.update s.keyB s.stB.t (some key) }

private lemma installBOn_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (sk : SK) (st : onoff.St) (ct0 : onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (ht : s.stA.t = s.stB.t) (hdk : s.stA.dkA = some sk)
    (hst : s.stB.stCt = some st) (hct0 : s.stB.ct0 = some ct0) :
    trackedFailureScore kem onoff hDet
        (installBOn onoff s ct1 key,
          currentKEMFailure kem onoff hDet (installBOn onoff s ct1 key)) =
      if hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
      then 1 else 0 := by
  by_cases hbad : hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
  · simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
      installBOn, ht, hdk, hct0, hbad, Function.update]
  · simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
      installBOn, ht, hdk, hct0, hbad, Function.update]

private lemma sendBOffState_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (off : onoff.St × onoff.C₀) (ich : ℕ) (msg : Message Sym)
    (hct1 : s.stB.ct1 = none) :
    trackedFailureScore kem onoff hDet
        (sendBOffState onoff s off ich msg,
          currentKEMFailure kem onoff hDet (sendBOffState onoff s off ich msg)) =
      currentFailurePotential kem onoff hDet
        (installBOff onoff s off.1 off.2) := by
  simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
    sendBOffState, sendBNoneState, installBOff, hct1]

private lemma sendBOnState_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (sk : SK) (ct0 : onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (msg : Message Sym) (ht : s.stA.t = s.stB.t)
    (hdk : s.stA.dkA = some sk) (hct0 : s.stB.ct0 = some ct0) :
    trackedFailureScore kem onoff hDet
        (sendBOnState onoff s ct1 key msg,
          currentKEMFailure kem onoff hDet (sendBOnState onoff s ct1 key msg)) =
      if hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
      then 1 else 0 := by
  by_cases hbad : hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
  · simp [trackedFailureScore, currentKEMFailure, sendBOnState, sendBKeyState,
      ht, hdk, hct0, hbad, Function.update]
  · simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
      sendBOnState, sendBKeyState, ht, hdk, hct0, hbad, Function.update]

private lemma sendBOffOnState_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (sk : SK) (off : onoff.St × onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (msg : Message Sym) (ht : s.stA.t = s.stB.t)
    (hdk : s.stA.dkA = some sk) :
    trackedFailureScore kem onoff hDet
        (sendBOffOnState onoff s off ct1 key msg,
          currentKEMFailure kem onoff hDet
            (sendBOffOnState onoff s off ct1 key msg)) =
      if hDet.decapsDet sk (onoff.split.symm (off.2, ct1)) ≠ some key
      then 1 else 0 := by
  by_cases hbad : hDet.decapsDet sk (onoff.split.symm (off.2, ct1)) ≠ some key
  · simp [trackedFailureScore, currentKEMFailure, sendBOffOnState, sendBKeyState,
      ht, hdk, hbad, Function.update]
  · simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
      sendBOffOnState, sendBKeyState, ht, hdk, hbad, Function.update]

private lemma recvA_kem_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (stA : StA onoff Sym) (msg : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (stA' : StA onoff Sym)
    (hrecv : recvA kem onoff hDet ecCt0 ecCt1 stA msg =
      some (key?, trcv, stA')) :
    (stA'.t = stA.t ∧ stA'.ekA = stA.ekA ∧ stA'.dkA = stA.dkA) ∨
      (stA'.t = stA.t + 1 ∧ stA'.ekA = none ∧ stA'.dkA = none ∧
        msg.2.2.1 = stA.t ∧ msg.2.2.2 = some 1 ∧ msg.1.isSome) := by
  classical
  rcases msg with ⟨ch?, ack, t, b?⟩
  by_cases ht : stA.t = t
  · simp only [recvA, ht, if_true] at hrecv
    repeat' split at hrecv
    all_goals try simp_all
    all_goals subst_vars <;> try simp_all
    all_goals rcases hrecv with ⟨_, _, hstate⟩ <;> subst stA' <;> simp_all
  · simp [recvA, ht] at hrecv
    simp_all

private lemma recvB_kem_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (stB : StB onoff Sym) (msg : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (stB' : StB onoff Sym)
    (hrecv : recvB kem onoff ecEk stB msg = some (key?, trcv, stB')) :
    (stB'.t = stB.t ∧ stB'.stCt = stB.stCt ∧ stB'.ct0 = stB.ct0 ∧
        stB'.ct1 = stB.ct1) ∨
      (stB'.t = stB.t + 1 ∧ stB'.stCt = none ∧ stB'.ct0 = none ∧
        stB'.ct1 = none ∧ stB.t < msg.2.2.1) := by
  classical
  rcases msg with ⟨ch?, ack, t, b?⟩
  by_cases ht : stB.t < t
  · right
    simp only [recvB, ht, if_true] at hrecv
    repeat' split at hrecv
    all_goals try simp_all
    all_goals subst_vars <;> try simp_all
    all_goals rcases hrecv with ⟨_, _, hstate⟩ <;> subst stB' <;> simp_all
  · left
    simp only [recvB, ht, if_false] at hrecv
    repeat' split at hrecv
    all_goals try simp_all
    all_goals subst_vars <;> try simp_all
    all_goals rcases hrecv with ⟨_, _, hstate⟩ <;> subst stB' <;> simp_all

private lemma oracleRecvB_preserves_failurePotential [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentFailurePotential kem onoff hDet z.2 =
      currentFailurePotential kem onoff hDet s := by
  rcases hs with ⟨world, hInv⟩
  cases hentry : s.msgA n with
  | none =>
      have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      rfl
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvB kem onoff ecEk s.stB msg with
      | none => simp [recvB] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stB'⟩
        have hkey : key? = none := by
          symm
          simpa [recvB] using congrArg (fun x => x.map (fun y => y.1)) hlocal
        subst key?
        have hz' : z =
            (some (trcv, none),
              { s with
                stB := stB'
                tcurB := max s.tcurB trcv
                correct := s.correct && decide (trcv = tsnd) }) := by
          simpa [SCKAScheme.oracleRecvB, hentry, scheme, hlocal,
            StateT.run_bind, StateT.run_get] using hz
        subst z
        rcases recvB_kem_source_shape kem onoff ecEk s.stB msg none trcv stB' hlocal with
          hsame | hadv
        · exact currentFailurePotential_congr kem onoff hDet _ _ rfl hsame.1
            rfl rfl hsame.2.1 hsame.2.2.1 hsame.2.2.2
        · have htbound := hInv.msgAEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t + 1 := by
            have hltA : s.stB.t < s.stA.t := hadv.2.2.2.2.trans_le htbound
            have hle := hInv.epochs.2
            omega
          exact currentFailurePotential_recvB_advance kem onoff hDet _ _ hepoch
            rfl rfl rfl hadv.1 hadv.2.1 hadv.2.2.1 hadv.2.2.2.1

private lemma oracleRecvA_preserves_failurePotential [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentFailurePotential kem onoff hDet z.2 =
      currentFailurePotential kem onoff hDet s := by
  rcases hs with ⟨world, hInv⟩
  cases hentry : s.msgB n with
  | none =>
      have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvA, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      rfl
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvA kem onoff hDet ecCt0 ecCt1 s.stA msg with
      | none => simp [recvA] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stA'⟩
        have hzA : z.2.stA = stA' := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        have hzB : z.2.stB = s.stB := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        rcases recvA_kem_source_shape kem onoff hDet ecCt0 ecCt1 s.stA msg
            key? trcv stA' hlocal with hsame | hadv
        · exact currentFailurePotential_congr kem onoff hDet _ _
            ((congrArg (fun x => x.t) hzA).trans hsame.1)
            (congrArg (fun x => x.t) hzB)
            ((congrArg (fun x => x.ekA) hzA).trans hsame.2.1)
            ((congrArg (fun x => x.dkA) hzA).trans hsame.2.2)
            (congrArg (fun x => x.stCt) hzB)
            (congrArg (fun x => x.ct0) hzB)
            (congrArg (fun x => x.ct1) hzB)
        · have htbound := hInv.msgBEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t := by
            have : s.stA.t ≤ s.stB.t := by simpa [hadv.2.2.2.1] using htbound
            exact Nat.le_antisymm this hInv.epochs.1
          have hhon := hInv.msgB n (msg, tsnd) hentry
          have hon : (world s.stA.t).on.isSome := by
            rcases msg with ⟨ch?, ack, t, b?⟩
            simp only at hadv
            have ht : t = s.stA.t := hadv.2.2.2.1
            have hb : b? = some 1 := hadv.2.2.2.2.1
            have hch : ch?.isSome := hadv.2.2.2.2.2
            obtain ⟨ch, rfl⟩ := Option.isSome_iff_exists.mp hch
            obtain ⟨ct1, key, i, hon, _⟩ : ∃ ct1 key i,
                (world s.stA.t).on = some (ct1, key) ∧
                  ch = ecCt1.encode ct1 i := by
              simpa [HonestMessageB, ht, hb] using hhon.2
            simpa [hon]
          have hct1 : s.stB.ct1.isSome := by
            have hmap := hInv.onB
            rw [← hepoch] at hmap
            cases hworld : (world s.stA.t).on with
            | none => simp [hworld] at hon
            | some pair =>
                rw [hworld] at hmap
                simpa [← hmap]
          exact currentFailurePotential_recvA_advance kem onoff hDet _ _ hepoch hct1
            ((congrArg (fun x => x.t) hzA).trans hadv.1)
            ((congrArg (fun x => x.ekA) hzA).trans hadv.2.1)
            ((congrArg (fun x => x.dkA) hzA).trans hadv.2.2.1)
            (congrArg (fun x => x.t) hzB)
            (congrArg (fun x => x.stCt) hzB)
            (congrArg (fun x => x.ct0) hzB)
            (congrArg (fun x => x.ct1) hzB)

private lemma oracleRecvB_preserves_currentFailure [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentKEMFailure kem onoff hDet z.2 = false := by
  rcases hs with ⟨world, hInv⟩
  cases hentry : s.msgA n with
  | none =>
      have : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      exact hfail
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvB kem onoff ecEk s.stB msg with
      | none => simp [recvB] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stB'⟩
        have hkey : key? = none := by
          symm
          simpa [recvB] using congrArg (fun x => x.map (fun y => y.1)) hlocal
        subst key?
        have hz' : z =
            (some (trcv, none),
              { s with
                stB := stB'
                tcurB := max s.tcurB trcv
                correct := s.correct && decide (trcv = tsnd) }) := by
          simpa [SCKAScheme.oracleRecvB, hentry, scheme, hlocal,
            StateT.run_bind, StateT.run_get] using hz
        subst z
        rcases recvB_kem_source_shape kem onoff ecEk s.stB msg none trcv stB'
            hlocal with hsame | hadv
        · rw [← hfail]
          exact currentKEMFailure_congr kem onoff hDet _ _ rfl hsame.1 rfl
            hsame.2.2.1 hsame.2.2.2 (congrArg s.keyB hsame.1)
        · have htbound := hInv.msgAEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t + 1 := by
            have hltA : s.stB.t < s.stA.t := hadv.2.2.2.2.trans_le htbound
            have hle := hInv.epochs.2
            omega
          exact currentKEMFailure_recvB_advance_false kem onoff hDet _ _ hepoch
            rfl hadv.1 hadv.2.2.1

private lemma oracleRecvA_preserves_currentFailure [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentKEMFailure kem onoff hDet z.2 = false := by
  rcases hs with ⟨world, hInv⟩
  cases hentry : s.msgB n with
  | none =>
      have : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvA, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      exact hfail
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvA kem onoff hDet ecCt0 ecCt1 s.stA msg with
      | none => simp [recvA] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stA'⟩
        have hzA : z.2.stA = stA' := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        have hzB : z.2.stB = s.stB := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        have hzKeyB : z.2.keyB = s.keyB := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        rcases recvA_kem_source_shape kem onoff hDet ecCt0 ecCt1 s.stA msg
            key? trcv stA' hlocal with hsame | hadv
        · rw [← hfail]
          exact currentKEMFailure_congr kem onoff hDet _ _
            ((congrArg (fun x => x.t) hzA).trans hsame.1)
            (congrArg (fun x => x.t) hzB)
            ((congrArg (fun x => x.dkA) hzA).trans hsame.2.2)
            (congrArg (fun x => x.ct0) hzB)
            (congrArg (fun x => x.ct1) hzB)
            (by rw [hzKeyB, hzB])
        · have htbound := hInv.msgBEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t := by
            have : s.stA.t ≤ s.stB.t := by simpa [hadv.2.2.2.1] using htbound
            exact Nat.le_antisymm this hInv.epochs.1
          exact currentKEMFailure_recvA_advance_false kem onoff hDet _ _ hepoch
            ((congrArg (fun x => x.t) hzA).trans hadv.1)
            (congrArg (fun x => x.t) hzB)
private lemma currentKEMFailure_eq_false_implies_current [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false) :
    CurrentKEMCorrect kem onoff hDet s := by
  rcases hs with ⟨world, hInv⟩
  intro dk ct0 ct1 key hdk hct0A hct1 hkeyA
  have honSome : (world s.stB.t).on.isSome := by
    have hmap := hInv.onB
    rw [hct1] at hmap
    cases hon : (world s.stB.t).on with
    | none => simp [hon] at hmap
    | some pair => simp [hon]
  have htEq : s.stA.t = s.stB.t := by
    by_contra hne
    have hepochBounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hfuture := hInv.futureOn s.stA.t hlt
    have hworldKey : (world s.stA.t).key.isSome := by
      rw [← hInv.keyB, hkeyA]
      simp
    simp [EpochTranscript.key, hfuture] at hworldKey
  obtain ⟨st, hoffA⟩ := hInv.decodedCt0 ct0 hct0A
  have hoffB : (world s.stA.t).off = optionPair s.stB.stCt s.stB.ct0 := by
    simpa [htEq] using hInv.offB
  have hct0B : s.stB.ct0 = some ct0 := by
    rw [hoffA] at hoffB
    cases hst : s.stB.stCt <;> cases hct : s.stB.ct0 <;>
      simp [hst, hct, optionPair] at hoffB ⊢
    exact hoffB.2.symm
  have hkeyB : s.keyB s.stB.t = some key := by simpa [htEq] using hkeyA
  simpa [currentKEMFailure, htEq, hdk, hct0B, hct1, hkeyB] using hfail

private def trackedCorrectnessImpl [DecidableEq K]
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

private def trackedInv [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) : Prop :=
  p.2 = true ∨
    reachableInv kem onoff ecEk ecCt0 ecCt1 p.1 ∧
      currentKEMFailure kem onoff hDet p.1 = false

private lemma tracked_step_score_le_of_bad [DecidableEq K]
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
        (fun z => trackedFailureScore kem onoff hDet z.2) ≤
      trackedFailureScore kem onoff hDet p + epsilon := by
  refine (expectedPayoff_le_one _ _ ?_).trans ?_
  · intro z
    exact trackedFailureScore_le_one kem onoff hDet z.2
  · simp [trackedFailureScore, hbad]

/-- Whether an oracle query is `SendA` or `SendB` — the only oracles that
run `kem.keygen`, `onoff.encapsOff`, or `onoff.encapsOn`. -/
private def isSendQuery
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain) : Bool :=
  match t with
  | OSendA | OSendB => true
  | _ => false

private def IsSendQuery
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain) : Prop :=
  isSendQuery t = true

private instance : DecidablePred (IsSendQuery (Sym := Sym)) :=
  fun t => inferInstanceAs (Decidable (isSendQuery t = true))

private lemma tracked_sendA_score_le [DecidableEq K]
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
        (fun z => trackedFailureScore kem onoff hDet z.2) ≤
      trackedFailureScore kem onoff hDet (s, false) +
        factorCorrectnessError kem onoff hDet := by
  change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2)))
      (fun z => trackedFailureScore kem onoff hDet z.2) ≤ _
  cases hdk : s.stA.dkA with
  | none =>
      simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get,
        scheme, sendA, bind_assoc, pure_bind]
      simp [hdk]
      rw [expectedPayoff_map]
      change expectedPayoff kem.keygen (fun kp =>
        trackedFailureScore kem onoff hDet
          (sendAKeygenState onoff ecEk s kp,
            currentKEMFailure kem onoff hDet (sendAKeygenState onoff ecEk s kp))) ≤ _
      refine (expectedPayoff_mono kem.keygen _
        (fun kp => currentFailurePotential kem onoff hDet
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
      · exact keygen_failurePotential_le kem onoff hDet ecEk ecCt0 ecCt1 s hs hdk
  | some sk =>
      rcases hs with ⟨world, hInv⟩
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
      have hpot : currentFailurePotential kem onoff hDet s' =
          currentFailurePotential kem onoff hDet s := by
        exact currentFailurePotential_congr kem onoff hDet s s' rfl rfl rfl rfl
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

private lemma tracked_sendB_score_le [DecidableEq K]
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
        (fun z => trackedFailureScore kem onoff hDet z.2) ≤
      trackedFailureScore kem onoff hDet (s, false) +
        factorCorrectnessError kem onoff hDet := by
  change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2)))
      (fun z => trackedFailureScore kem onoff hDet z.2) ≤ _
  rcases hs with ⟨world, hInv⟩
  cases hct0 : s.stB.ct0 with
  | none =>
      have hst : s.stB.stCt = none := by
        simpa [hct0] using hInv.offBShape
      have hct1 : s.stB.ct1 = none := by
        have hoff : (world s.stB.t).off = none := by
          simpa [hct0, hst, optionPair] using hInv.offB
        have hon : (world s.stB.t).on = none := by
          by_contra hne
          simpa [hoff] using (world s.stB.t).on_off
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
            off_failurePotential_le kem onoff hDet ecEk ecCt0 ecCt1 s
              ⟨world, hInv⟩ hct0
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
                off_failurePotential_le kem onoff hDet ecEk ecCt0 ecCt1 s
                  ⟨world, hInv⟩ hct0
          | some pk =>
              obtain ⟨sk, ht, hekA, hdk⟩ :=
                newOff_source_shape kem onoff ecEk ecCt0 ecCt1 s ⟨world, hInv⟩
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
                      (fun z => trackedFailureScore kem onoff hDet z.2) =
                    failureAfterBoth kem onoff hDet pk sk off.1 off.2 := by
                rw [expectedPayoff_map]
                unfold expectedPayoff
                rw [failureAfterBoth_eq_indicator]
                refine congrArg
                  (fun x : ℝ≥0∞ => Pr[⊥ | onoff.encapsOn off.1 pk] + x) ?_
                refine tsum_congr fun out => ?_
                congr 1
                exact sendBOffOnState_score kem onoff hDet s sk off out.1 out.2
                  (msg out) ht hdk
              rw [hrun, expectedPayoff_bind]
              have hpot : currentFailurePotential kem onoff hDet s =
                  failureAfterKeypair kem onoff hDet pk sk := by
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
                      (fun z => trackedFailureScore kem onoff hDet z.2)) =
                    failureAfterKeypair kem onoff hDet pk sk := by
                      unfold failureAfterKeypair
                      refine congrArg
                        (fun x : ℝ≥0∞ => Pr[⊥ | onoff.encapsOff] + x) ?_
                      refine tsum_congr fun off => ?_
                      rw [hinner]
                _ ≤ trackedFailureScore kem onoff hDet (s, false) +
                    factorCorrectnessError kem onoff hDet := by
                      simpa [trackedFailureScore, hpot] using
                        (le_self_add : failureAfterKeypair kem onoff hDet pk sk ≤
                          failureAfterKeypair kem onoff hDet pk sk +
                            factorCorrectnessError kem onoff hDet)
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
          have hpot : currentFailurePotential kem onoff hDet s' =
              currentFailurePotential kem onoff hDet s := by
            exact currentFailurePotential_congr kem onoff hDet s s' rfl rfl rfl rfl
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
              have hpot : currentFailurePotential kem onoff hDet s' =
                  currentFailurePotential kem onoff hDet s := by
                exact currentFailurePotential_congr kem onoff hDet s s'
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
                    online_source_shape kem onoff ecEk ecCt0 ecCt1 s ⟨world, hInv⟩
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
                      trackedFailureScore kem onoff hDet
                        (sendBOnState onoff s out.1 out.2 (msg out),
                          currentKEMFailure kem onoff hDet
                            (sendBOnState onoff s out.1 out.2 (msg out)))) =
                      failureAfterBoth kem onoff hDet pk sk st ct0 := by
                    unfold expectedPayoff
                    rw [failureAfterBoth_eq_indicator]
                    refine congrArg
                      (fun x : ℝ≥0∞ => Pr[⊥ | onoff.encapsOn st pk] + x) ?_
                    refine tsum_congr fun out => ?_
                    congr 1
                    exact sendBOnState_score kem onoff hDet s sk ct0 out.1 out.2
                      (msg out) ht hdk hct0
                  rw [hscore]
                  have hpot : currentFailurePotential kem onoff hDet s =
                      failureAfterBoth kem onoff hDet pk sk st ct0 := by
                    simp [currentFailurePotential, ht, hct1, hekA, hdk, hst,
                      hct0, optionPair]
                  simpa [trackedFailureScore, hpot] using
                    (le_self_add : failureAfterBoth kem onoff hDet pk sk st ct0 ≤
                      failureAfterBoth kem onoff hDet pk sk st ct0 +
                        factorCorrectnessError kem onoff hDet)
              | some ct1 =>
                  let ich := s.stB.ich + 1
                  let msg : Message Sym :=
                    (some (ecCt1.encode ct1 ich), s.stB.ack, s.stB.t, some 1)
                  let s' := sendBNoneState onoff s { s.stB with ich := ich } msg
                  have hpot : currentFailurePotential kem onoff hDet s' =
                      currentFailurePotential kem onoff hDet s := by
                    exact currentFailurePotential_congr kem onoff hDet s s'
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

private lemma tracked_nonSend_score_support_eq [DecidableEq K]
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
    trackedFailureScore kem onoff hDet z.2 =
      trackedFailureScore kem onoff hDet (s, false) := by
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
      simp [trackedFailureScore, hfail, hfail', hpot]
  | ORecvB n =>
      have hpot := oracleRecvB_preserves_failurePotential kem onoff hDet ecEk
        ecCt0 ecCt1 leak n s hs y hy
      have hfail' := oracleRecvB_preserves_currentFailure kem onoff hDet ecEk
        ecCt0 ecCt1 leak n s hs hfail y hy
      simp [trackedFailureScore, hfail, hfail', hpot]

private lemma tracked_nonSend_score_le [DecidableEq K]
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
        (fun z => trackedFailureScore kem onoff hDet z.2) ≤
      trackedFailureScore kem onoff hDet (s, false) := by
  have hnf : Pr[⊥ |
      ((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run
        (s, false)] = 0 := probFailure_eq_zero
  apply expectedPayoff_le_const_of_support _ _ _ hnf
  intro z hz
  exact le_of_eq (tracked_nonSend_score_support_eq kem onoff hDet ecEk ecCt0 ecCt1
    leak t ht s hs hfail z hz)

private lemma trackedCorrectnessImpl_project [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        ((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p =
      ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1 := by
  unfold trackedCorrectnessImpl
  change Prod.map id Prod.fst <$> (do
      let z ← ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1
      pure (z.1, (z.2, p.2 || currentKEMFailure kem onoff hDet z.2))) = _
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp

private lemma tracked_run_project [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ
          (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run p =
      (simulateQ
        (SCKAScheme.sckaCorrectnessImpl
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run p.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.sckaCorrectnessImpl
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
    Prod.fst
    (trackedCorrectnessImpl_project kem onoff hDet ecEk ecCt0 ecCt1 leak)
    adv p

private lemma correctnessExp_eq_final_map [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv =
      (fun z => z.2.correct) <$>
        (simulateQ
          (SCKAScheme.sckaCorrectnessImpl
            (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run
          (initialGame kem onoff) := by
  simp [SCKAScheme.correctnessExp, scheme, initKeyGen, initA, initB,
    initialGame, initialA, initialB, map_eq_bind_pure_comp]

private lemma trackedCorrectnessImpl_preserves
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    QueryImpl.PreservesInv
      (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1) := by
  intro t p hp z hz
  unfold trackedCorrectnessImpl at hz
  change z ∈ support (do
    let y ← ((SCKAScheme.sckaCorrectnessImpl
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1
    pure (y.1, (y.2, p.2 || currentKEMFailure kem onoff hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst z
  rcases hp with hbad | ⟨hreach, hfailOld⟩
  · left
    simp [hbad]
  have hcurrent : CurrentKEMCorrect kem onoff hDet p.1 :=
    currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
      p.1 hreach hfailOld
  have hreach' : reachableInv kem onoff ecEk ecCt0 ecCt1 y.2 := by
    match t with
    | OUnif n =>
        exact oracleUnif_preserves_reachableInv kem onoff ecEk ecCt0 ecCt1
          n p.1 hreach y hy
    | OSendA =>
        exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1
          leak hEkPos () p.1 hreach y hy
    | OSendB =>
        exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0Pos
          ecCt1 hCt1Pos leak () p.1 hreach y hy
    | ORecvA n =>
        exact oracleRecvA_preserves_reachableInv_of_current kem onoff hDet ecEk ecCt0
          hCt0Correct ecCt1 hCt1Correct hCt1Pos leak n p.1 hreach hcurrent y hy
    | ORecvB n =>
        exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEkCorrect hEkPos
          ecCt0 ecCt1 leak n p.1 hreach y hy
  by_cases hfail : currentKEMFailure kem onoff hDet y.2 = true
  · left
    simp [hfail]
  · right
    have hfailFalse : currentKEMFailure kem onoff hDet y.2 = false := by
      cases h : currentKEMFailure kem onoff hDet y.2 <;> simp [h] at hfail ⊢
    exact ⟨hreach', hfailFalse⟩

/-- From a state whose current KEM material is consistent, one `SendB` call
produces a state with `currentKEMFailure` with probability at most `δ`. -/
def SendBFailureBound [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (δ : ℝ≥0∞) : Prop :=
  ∀ s, CurrentKEMCorrect kem onoff hDet s →
    Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
      (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s] ≤ δ

/-- From a state whose current KEM material is consistent, no oracle other
than `SendB` can produce a state with `currentKEMFailure`. -/
def NonSendBPreservesCurrent [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) : Prop :=
  ∀ t, t ≠ (OSendB : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain) →
    ∀ s, CurrentKEMCorrect kem onoff hDet s →
      Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
        ((SCKAScheme.sckaCorrectnessImpl
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s] = 0

/-- Syntactic bound on the number of `SendB` queries made by a correctness
adversary. -/
def SendBQueryBound (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) : Prop :=
  adv.IsQueryBoundP
    (fun t => t = (OSendB : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)) q

/-- Syntactic bound on the total number of send queries.  Both send oracles
count: either party may draw the first sample of a fresh epoch. -/
def SendQueryBound (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) : Prop :=
  adv.IsQueryBoundP (IsSendQuery (Sym := Sym)) q

private lemma tracked_score_step_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
    (hp : trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p) :
    expectedPayoff
        (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p)
        (fun z => trackedFailureScore kem onoff hDet z.2) ≤
      trackedFailureScore kem onoff hDet p +
        if IsSendQuery t
        then factorCorrectnessError kem onoff hDet
        else 0 := by
  cases hbad : p.2 with
  | true =>
      exact tracked_step_score_le_of_bad kem onoff hDet ecEk ecCt0 ecCt1 leak
        t p hbad _
  | false =>
      have hgood : reachableInv kem onoff ecEk ecCt0 ecCt1 p.1 ∧
          currentKEMFailure kem onoff hDet p.1 = false := by
        rcases hp with hpbad | hpGood
        · simp [hbad] at hpbad
        · exact hpGood
      have hpEq : p = (p.1, false) := Prod.ext rfl hbad
      rw [hpEq]
      match t with
      | OUnif n =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_nonSend_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              (OUnif n) (by simp [IsSendQuery, isSendQuery]) _ hgood.1 hgood.2
      | OSendA =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_sendA_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              _ hgood.1 hgood.2
      | OSendB =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_sendB_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              _ hgood.1 hgood.2
      | ORecvA n =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_nonSend_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              (ORecvA n) (by simp [IsSendQuery, isSendQuery]) _ hgood.1 hgood.2
      | ORecvB n =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_nonSend_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              (ORecvB n) (by simp [IsSendQuery, isSendQuery]) _ hgood.1 hgood.2

private lemma tracked_bad_probability_le_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (oa : ProbComp
      (Bool ×
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) ×
          Bool))) :
    Pr[fun z => z.2.2 = true | oa] ≤
      expectedPayoff oa (fun z => trackedFailureScore kem onoff hDet z.2) := by
  unfold expectedPayoff
  calc
    Pr[fun z => z.2.2 = true | oa] ≤
        ∑' z, Pr[= z | oa] * trackedFailureScore kem onoff hDet z.2 := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro z hz
      simp [trackedFailureScore, hz]
    _ ≤ Pr[⊥ | oa] +
        ∑' z, Pr[= z | oa] * trackedFailureScore kem onoff hDet z.2 :=
      le_add_left le_rfl

private lemma tracked_score_adversary_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) (q : ℕ)
    (hq : SendQueryBound adv q) (epsilon : ℝ≥0∞)
    (hpres : QueryImpl.PreservesInv
      (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1))
    (hstep : ∀ t p,
      trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p →
      expectedPayoff
          (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p)
          (fun z => trackedFailureScore kem onoff hDet z.2) ≤
        trackedFailureScore kem onoff hDet p +
          if IsSendQuery t then epsilon else 0) :
    ∀ p, trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p →
      expectedPayoff
          ((simulateQ
            (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run p)
          (fun z => trackedFailureScore kem onoff hDet z.2) ≤
        trackedFailureScore kem onoff hDet p + (q : ℝ≥0∞) * epsilon := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let score := trackedFailureScore (Sym := Sym) kem onoff hDet
  unfold SendQueryBound at hq
  induction adv using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro p hp
      simpa [simulateQ_pure, StateT.run_pure, expectedPayoff_pure] using
        (le_self_add : score p ≤ score p + (q : ℝ≥0∞) * epsilon)
  | @query_bind t cont ih =>
      intro p hp
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind, expectedPayoff_bind]
      by_cases ht : IsSendQuery t
      · have hqpos : 0 < q := hcan.resolve_left (not_not_intro ht)
        have htail : ∀ z ∈ support ((tracked t).run p),
            expectedPayoff
                ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2) ≤
              score z.2 + (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) := by
          intro z hz
          exact ih z.1 (q - 1) (by simpa [ht] using hcont z.1) z.2
            (hpres t p hp z hz)
        calc
          (Pr[⊥ | (tracked t).run p] +
            ∑' z, Pr[= z | (tracked t).run p] *
              expectedPayoff ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2)) ≤
              Pr[⊥ | (tracked t).run p] +
                ∑' z, Pr[= z | (tracked t).run p] *
                (score z.2 + (((q - 1 : ℕ) : ℝ≥0∞) * epsilon)) := by
            exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => by
              by_cases hz : z ∈ support ((tracked t).run p)
              · exact mul_le_mul' le_rfl (htail z hz)
              · simp [(probOutput_eq_zero_iff _ _).2 hz])
          _ ≤ expectedPayoff ((tracked t).run p) (fun z => score z.2) +
                (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) :=
            expectedPayoff_add_const_le _ _ _
          _ ≤ (score p + epsilon) +
                (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) := by
            exact add_le_add (by simpa [tracked, Inv, score, ht] using hstep t p hp) le_rfl
          _ = score p + (q : ℝ≥0∞) * epsilon := by
            have hcast : (((q - 1 : ℕ) : ℝ≥0∞) + 1) = (q : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hqpos
            rw [← hcast, add_mul, one_mul]
            ac_rfl
      · have htail : ∀ z ∈ support ((tracked t).run p),
            expectedPayoff
                ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2) ≤
              score z.2 + ((q : ℝ≥0∞) * epsilon) := by
          intro z hz
          exact ih z.1 q (by simpa [ht] using hcont z.1) z.2
            (hpres t p hp z hz)
        calc
          (Pr[⊥ | (tracked t).run p] +
            ∑' z, Pr[= z | (tracked t).run p] *
              expectedPayoff ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2)) ≤
              Pr[⊥ | (tracked t).run p] +
                ∑' z, Pr[= z | (tracked t).run p] *
                (score z.2 + ((q : ℝ≥0∞) * epsilon)) := by
            exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => by
              by_cases hz : z ∈ support ((tracked t).run p)
              · exact mul_le_mul' le_rfl (htail z hz)
              · simp [(probOutput_eq_zero_iff _ _).2 hz])
          _ ≤ expectedPayoff ((tracked t).run p) (fun z => score z.2) +
                ((q : ℝ≥0∞) * epsilon) :=
            expectedPayoff_add_const_le _ _ _
          _ ≤ score p + ((q : ℝ≥0∞) * epsilon) := by
            simpa [tracked, Inv, score, ht] using
              add_le_add (hstep t p hp) (le_refl ((q : ℝ≥0∞) * epsilon))

private lemma tracked_step_bad_probability [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[fun z => z.2.2 = true |
      ((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run
        (s, false)] =
    Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
      ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s] := by
  change Pr[fun z => z.2.2 = true | do
      let y ← ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))] = _
  rw [show (do
      let y ← ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) =
      (fun y => (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) <$>
        ((SCKAScheme.sckaCorrectnessImpl
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s from
      (map_eq_bind_pure_comp _ _ _).symm]
  rw [probEvent_map]
  congr 1

private lemma tracked_bad_probability_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (δ : ℝ≥0∞)
    (hSend : SendBFailureBound kem onoff hDet ecEk ecCt0 ecCt1 leak δ)
    (hFree : NonSendBPreservesCurrent kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) {q : ℕ}
    (hq : SendBQueryBound adv q) :
    ∀ p, trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p → p.2 = false →
      Pr[fun z => z.2.2 = true |
        (simulateQ
          (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run p] ≤
        (q : ℝ≥0∞) * δ := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  unfold SendBQueryBound at hq
  induction adv using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro p hp hpbad
      simp [tracked, hpbad]
  | @query_bind t cont ih =>
      intro p hp hpbad
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      have hrun :
          (simulateQ tracked (query t >>= cont)).run p =
            (tracked t).run p >>= fun z => (simulateQ tracked (cont z.1)).run z.2 := by
        simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, StateT.run_bind]
      change Pr[fun z => z.2.2 = true |
        (simulateQ tracked (query t >>= cont)).run p] ≤ (q : ℝ≥0∞) * δ
      rw [hrun]
      have hpGood : CurrentKEMCorrect kem onoff hDet p.1 := by
        rcases hp with hbad | hgood
        · simp [hpbad] at hbad
        · exact currentKEMFailure_eq_false_implies_current kem onoff hDet
            ecEk ecCt0 ecCt1 p.1 hgood.1 hgood.2
      by_cases ht : t = (OSendB :
          (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
      · have hqpos : 0 < q := hcan.resolve_left (not_not_intro ht)
        subst t
        have hp_eq : p = (p.1, false) := Prod.ext rfl hpbad
        have hhead : Pr[fun z => ¬z.2.2 = false | (tracked OSendB).run p] ≤ δ := by
          calc
            Pr[fun z => ¬z.2.2 = false | (tracked OSendB).run p] =
                Pr[fun z => z.2.2 = true | (tracked OSendB).run p] := by
              refine probEvent_congr' (fun z _ => ?_) rfl
              cases z.2.2 <;> simp
            _ = Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
                ((SCKAScheme.sckaCorrectnessImpl
                  (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) OSendB).run p.1] := by
              rw [hp_eq]
              exact tracked_step_bad_probability kem onoff hDet ecEk ecCt0 ecCt1 leak
                OSendB p.1
            _ ≤ δ := hSend p.1 hpGood
        have htail : ∀ z ∈ support ((tracked OSendB).run p), z.2.2 = false →
            Pr[fun w => ¬w.2.2 = false |
              (simulateQ tracked (cont z.1)).run z.2] ≤ ((q - 1 : ℕ) : ℝ≥0∞) * δ := by
          intro z hz hzbad
          calc
            Pr[fun w => ¬w.2.2 = false |
                (simulateQ tracked (cont z.1)).run z.2] =
                Pr[fun w => w.2.2 = true |
                  (simulateQ tracked (cont z.1)).run z.2] := by
              refine probEvent_congr' (fun w _ => ?_) rfl
              cases w.2.2 <;> simp
            _ ≤ ((q - 1 : ℕ) : ℝ≥0∞) * δ :=
              ih z.1 (by simpa using hcont z.1) z.2
                (hpres OSendB p hp z hz) hzbad
        have hunion := probEvent_bind_le_add hhead htail
        have hunion' : Pr[fun z => z.2.2 = true |
            (tracked OSendB).run p >>= fun z =>
              (simulateQ tracked (cont z.1)).run z.2] ≤
              δ + ((q - 1 : ℕ) : ℝ≥0∞) * δ := by
          calc
            Pr[fun z => z.2.2 = true | (tracked OSendB).run p >>= fun z =>
                (simulateQ tracked (cont z.1)).run z.2] =
                Pr[fun z => ¬z.2.2 = false | (tracked OSendB).run p >>= fun z =>
                  (simulateQ tracked (cont z.1)).run z.2] := by
              refine probEvent_congr' (fun z _ => ?_) rfl
              cases z.2.2 <;> simp
            _ ≤ δ + ((q - 1 : ℕ) : ℝ≥0∞) * δ := hunion
        refine hunion'.trans ?_
        have hcast : (((q - 1 : ℕ) : ℝ≥0∞) + 1) = (q : ℝ≥0∞) := by
          exact_mod_cast Nat.sub_add_cancel hqpos
        rw [← hcast]
        rw [add_mul, one_mul, add_comm]
      · have hp_eq : p = (p.1, false) := Prod.ext rfl hpbad
        have hhead : Pr[fun z => ¬z.2.2 = false | (tracked t).run p] ≤ 0 := by
          calc
            Pr[fun z => ¬z.2.2 = false | (tracked t).run p] =
                Pr[fun z => z.2.2 = true | (tracked t).run p] := by
              refine probEvent_congr' (fun z _ => ?_) rfl
              cases z.2.2 <;> simp
            _ = Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
                ((SCKAScheme.sckaCorrectnessImpl
                  (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1] := by
              rw [hp_eq]
              exact tracked_step_bad_probability kem onoff hDet ecEk ecCt0 ecCt1 leak
                t p.1
            _ ≤ 0 := le_of_eq (hFree t ht p.1 hpGood)
        have htail : ∀ z ∈ support ((tracked t).run p), z.2.2 = false →
            Pr[fun w => ¬w.2.2 = false |
              (simulateQ tracked (cont z.1)).run z.2] ≤ (q : ℝ≥0∞) * δ := by
          intro z hz hzbad
          calc
            Pr[fun w => ¬w.2.2 = false |
                (simulateQ tracked (cont z.1)).run z.2] =
                Pr[fun w => w.2.2 = true |
                  (simulateQ tracked (cont z.1)).run z.2] := by
              refine probEvent_congr' (fun w _ => ?_) rfl
              cases w.2.2 <;> simp
            _ ≤ (q : ℝ≥0∞) * δ :=
              ih z.1 (by simpa [ht] using hcont z.1) z.2
                (hpres t p hp z hz) hzbad
        have hunion := probEvent_bind_le_add hhead htail
        calc
          Pr[fun z => z.2.2 = true | (tracked t).run p >>= fun z =>
              (simulateQ tracked (cont z.1)).run z.2] =
              Pr[fun z => ¬z.2.2 = false | (tracked t).run p >>= fun z =>
                (simulateQ tracked (cont z.1)).run z.2] := by
            refine probEvent_congr' (fun z _ => ?_) rfl
            cases z.2.2 <;> simp
          _ ≤ 0 + (q : ℝ≥0∞) * δ := hunion
          _ = (q : ℝ≥0∞) * δ := zero_add _

/-- Correctness of Opp-UniKEM-CKA from stepwise premises: if one `SendB`
step introduces inconsistent current-epoch KEM material with probability at
most `δ` and no other oracle can, then an adversary making at most `q`
`SendB` queries makes the correctness experiment fail with probability at
most `q * δ`.  Receive queries, including delayed, reordered, duplicated,
and replayed deliveries, are not counted. -/
-- ANCHOR: correctnessFailureLe
theorem correctness_failure_le_of_sendBFailureBound [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (δ : ℝ≥0∞)
    (hSend : SendBFailureBound kem onoff hDet ecEk ecCt0 ecCt1 leak δ)
    (hFree : NonSendBPreservesCurrent kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (hq : SendBQueryBound adv q) :
    Pr[= false |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≤
      (q : ℝ≥0∞) * δ
-- ANCHOR_END: correctnessFailureLe
    := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let s₀ := initialGame (Sym := Sym) kem onoff
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  have hinit : Inv (s₀, false) := by
    right
    refine ⟨?_, ?_⟩
    · simpa [s₀, initialGame, initialA, initialB] using
        reachableInv_init kem onoff ecEk ecCt0 ecCt1 hEkPos hCt0Pos
    · simp [currentKEMFailure, s₀, initialGame, initialA, initialB,
        SCKAScheme.initGameState]
  have hmono :
      Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] ≤
        Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := by
    refine probEvent_mono ?_
    intro z hz hincorrect
    have hzInv : Inv z.2 :=
      OracleComp.simulateQ_run_preservesInv tracked Inv hpres adv
        (s₀, false) hinit z hz
    rcases hzInv with hbad | ⟨hreach, _hcurrent⟩
    · exact hbad
    · rcases hreach with ⟨_world, hWorld⟩
      simp [hWorld.correct] at hincorrect
  have hbad :
      Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] ≤
        (q : ℝ≥0∞) * δ := by
    exact tracked_bad_probability_le kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak δ
      hSend hFree adv hq (s₀, false) hinit rfl
  calc
    Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] =
        Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] := by
      rw [correctnessExp_eq_final_map]
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      have hproject := tracked_run_project kem onoff hDet ecEk ecCt0 ecCt1
        leak adv (s₀, false)
      rw [← hproject, probEvent_map]
      congr 1
    _ ≤ Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := hmono
    _ ≤ (q : ℝ≥0∞) * δ := hbad

/-- Reduction of Opp-UniKEM-CKA correctness to KEM correctness: an adversary
making at most `q` send queries makes the correctness experiment fail with
probability at most `q * kem.correctnessError`.  Both send oracles count
toward `q`, since either party may draw the first sample of a fresh epoch;
receive queries are not counted. -/
theorem correctness_failure_le_reduction [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SendQueryBound adv q) :
    Pr[= false |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
    := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let score := trackedFailureScore (Sym := Sym) kem onoff hDet
  let s₀ := initialGame (Sym := Sym) kem onoff
  let epsilon := factorCorrectnessError kem onoff hDet
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  have hinit : Inv (s₀, false) := by
    right
    refine ⟨?_, ?_⟩
    · simpa [s₀, initialGame, initialA, initialB] using
        reachableInv_init kem onoff ecEk ecCt0 ecCt1 hEkPos hCt0Pos
    · simp [currentKEMFailure, s₀, initialGame, initialA, initialB,
        SCKAScheme.initGameState]
  have hscore₀ : score (s₀, false) = 0 := by
    simp [score, trackedFailureScore, currentFailurePotential, s₀, initialGame,
      initialA, initialB, SCKAScheme.initGameState, optionPair]
  have hscore :
      expectedPayoff ((simulateQ tracked adv).run (s₀, false))
          (fun z => score z.2) ≤
        (q : ℝ≥0∞) * epsilon := by
    have h := tracked_score_adversary_le kem onoff hDet ecEk ecCt0 ecCt1 leak
      adv q hq epsilon hpres
      (tracked_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (s₀, false) hinit
    have hscore₀' : trackedFailureScore kem onoff hDet (s₀, false) = 0 := by
      simpa [score] using hscore₀
    rw [hscore₀', zero_add] at h
    simpa [tracked, score] using h
  have hmono :
      Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] ≤
        Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := by
    refine probEvent_mono ?_
    intro z hz hincorrect
    have hzInv : Inv z.2 :=
      OracleComp.simulateQ_run_preservesInv tracked Inv hpres adv
        (s₀, false) hinit z hz
    rcases hzInv with hbad | ⟨hreach, _hcurrent⟩
    · exact hbad
    · rcases hreach with ⟨_world, hWorld⟩
      simp [hWorld.correct] at hincorrect
  calc
    Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] =
        Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] := by
      rw [correctnessExp_eq_final_map]
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      have hproject := tracked_run_project kem onoff hDet ecEk ecCt0 ecCt1
        leak adv (s₀, false)
      rw [← hproject, probEvent_map]
      congr 1
    _ ≤ Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := hmono
    _ ≤ expectedPayoff ((simulateQ tracked adv).run (s₀, false))
          (fun z => score z.2) :=
      tracked_bad_probability_le_score kem onoff hDet _
    _ ≤ (q : ℝ≥0∞) * epsilon := hscore
    _ = (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
      simp only [epsilon, factorCorrectnessError_eq]

/-- `Pr[G(Adv) = true] ≥ 1 - q * kem.correctnessError` for at most `q` send
queries. -/
theorem correctness_true_ge_reduction [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SendQueryBound adv q) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
    := by
  have h := correctness_failure_le_reduction kem onoff hDet
    ecEk hEkCorrect hEkPos ecCt0 hCt0Correct hCt0Pos
    ecCt1 hCt1Correct hCt1Pos leak adv q hq
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero] at h
  rw [tsub_le_iff_right] at h
  rw [ge_iff_le, tsub_le_iff_right]
  rwa [add_comm]

end Reduction

end oppUniKemCKA
