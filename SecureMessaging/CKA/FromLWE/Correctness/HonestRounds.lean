/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Correctness.Tape

/-!
# Honest rounds and the tape interpreter

This module relates the alternating honest-round experiment to sampled tapes and defines the
interpreter that supplies pre-sampled coins to the correctness game.
-/

open OracleComp ENNReal

namespace lweCKA

open CorrectnessInternal

/-- Run a fixed number of honest rounds, with the parties taking turns to send. -/
def honestRoundsSchemeExp
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    ℕ → ProbComp (Option (State p × State p × Bool))
  | 0 => do
      let cka := scheme p hp χ
      let ik ← cka.initKeyGen
      let stateA ← cka.initA ik
      let stateB ← cka.initB ik
      return some (stateA, stateB, false)
  | n + 1 => do
      let previous ← honestRoundsSchemeExp p hp χ n
      match previous with
      | none => return none
      | some (stateA, stateB, _) =>
          let cka := scheme p hp χ
          if n % 2 = 0 then
            let sent ← cka.sendA stateA
            match sent with
            | none => return none
            | some (senderKey, msg, stateA') =>
                match cka.recvB stateB msg with
                | none => return none
                | some (receiverKey, stateB') =>
                    return some (stateA', stateB', decide (receiverKey ≠ senderKey))
          else
            let sent ← cka.sendB stateB
            match sent with
            | none => return none
            | some (senderKey, msg, stateB') =>
                match cka.recvA stateA msg with
                | none => return none
                | some (receiverKey, stateA') =>
                    return some (stateA', stateB', decide (receiverKey ≠ senderKey))

private def oddRoundCanonical
    (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (Option (State p × State p × Bool)) := do
  let ik ← initKeyGen p χ
  let a ← sampleSendACoins p χ
  let senderValue := a.secret * (ik.baseMatrix * ik.secret + ik.error) + a.extra
  let receiverValue := (a.secret * ik.baseMatrix + a.error) * ik.secret
  return some (.aRecv ik.baseMatrix a.secret,
    .bSend ik.baseMatrix (a.secret * ik.baseMatrix + a.error),
    decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue))

private def evenRoundCanonical
    (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (Option (State p × State p × Bool)) := do
  let ik ← initKeyGen p χ
  let a ← sampleSendACoins p χ
  let b ← sampleSendBCoins p χ
  let senderValue := (a.secret * ik.baseMatrix + a.error) * b.secret + b.extra
  let receiverValue := a.secret * (ik.baseMatrix * b.secret + b.error)
  return some (.aSend ik.baseMatrix (ik.baseMatrix * b.secret + b.error),
    .bRecv ik.baseMatrix b.secret,
    decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue))

private def honestRoundStep
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (n : ℕ)
    (previous : Option (State p × State p × Bool)) :
    ProbComp (Option (State p × State p × Bool)) :=
  match previous with
  | none => pure none
  | some (stateA, stateB, _) =>
      let cka := scheme p hp χ
      if n % 2 = 0 then do
        let sent ← cka.sendA stateA
        match sent with
        | none => return none
        | some (senderKey, msg, stateA') =>
            match cka.recvB stateB msg with
            | none => return none
            | some (receiverKey, stateB') =>
                return some (stateA', stateB', decide (receiverKey ≠ senderKey))
      else do
        let sent ← cka.sendB stateB
        match sent with
        | none => return none
        | some (senderKey, msg, stateB') =>
            match cka.recvA stateA msg with
            | none => return none
            | some (receiverKey, stateA') =>
                return some (stateA', stateB', decide (receiverKey ≠ senderKey))

private theorem evalDist_odd_step_even
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (n : ℕ)
    (hn : n % 2 = 1) :
    finiteLaw (oddRoundCanonical p χ >>= honestRoundStep p hp χ n) =
      finiteLaw (evenRoundCanonical p χ) := by
  simp [oddRoundCanonical, evenRoundCanonical, honestRoundStep, hn, scheme,
    sendBrleak, eraseCoins, recvA]

private theorem evalDist_even_step_odd
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (n : ℕ)
    (hn : n % 2 = 0) :
    finiteLaw (evenRoundCanonical p χ >>= honestRoundStep p hp χ n) =
      finiteLaw (oddRoundCanonical p χ) := by
  let f : BaseMatrix p → RightMatrix p → RightMatrix p → SendACoins p →
      Option (State p × State p × Bool) := fun baseMatrix previousSecret previousError current =>
    let senderValue := current.secret * (baseMatrix * previousSecret + previousError) +
      current.extra
    let receiverValue := (current.secret * baseMatrix + current.error) * previousSecret
    some (.aRecv baseMatrix current.secret,
      .bSend baseMatrix (current.secret * baseMatrix + current.error),
      decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue))
  simpa [f, oddRoundCanonical, evenRoundCanonical, honestRoundStep, hn, scheme,
    sendArleak, eraseCoins, recvB, map_eq_bind_pure_comp, bind_assoc] using
      evalDist_evenRelevant p χ f

private theorem honestRoundsSchemeExp_succ
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (n : ℕ) :
    honestRoundsSchemeExp p hp χ (n + 1) =
      honestRoundsSchemeExp p hp χ n >>= honestRoundStep p hp χ n := by
  rfl

private theorem evalDist_honestRounds_one
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    finiteLaw (honestRoundsSchemeExp p hp χ 1) = finiteLaw (oddRoundCanonical p χ) := by
  simp [honestRoundsSchemeExp, oddRoundCanonical, scheme, initA, initB,
    sendArleak, eraseCoins, recvB]

private theorem evalDist_honestRounds_canonical
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (k : ℕ) :
    (finiteLaw (honestRoundsSchemeExp p hp χ (2 * k + 1)) =
        finiteLaw (oddRoundCanonical p χ)) ∧
      (finiteLaw (honestRoundsSchemeExp p hp χ (2 * k + 2)) =
        finiteLaw (evenRoundCanonical p χ)) := by
  induction k with
  | zero =>
      constructor
      · simpa using evalDist_honestRounds_one p hp χ
      · rw [show 2 * 0 + 2 = 1 + 1 by omega, honestRoundsSchemeExp_succ]
        exact (evalDist_bind_replace (evalDist_honestRounds_one p hp χ) _).trans
          (evalDist_odd_step_even p hp χ 1 (by decide))
  | succ k ih =>
      constructor
      · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
          honestRoundsSchemeExp_succ]
        exact (evalDist_bind_replace ih.2 _).trans
          (evalDist_even_step_odd p hp χ (2 * k + 2) (by omega))
      · rw [show 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 by omega,
          honestRoundsSchemeExp_succ]
        have hodd : finiteLaw (honestRoundsSchemeExp p hp χ (2 * (k + 1) + 1)) =
            finiteLaw (oddRoundCanonical p χ) := by
          rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
            honestRoundsSchemeExp_succ]
          exact (evalDist_bind_replace ih.2 _).trans
            (evalDist_even_step_odd p hp χ (2 * k + 2) (by omega))
        exact (evalDist_bind_replace hodd
          (honestRoundStep p hp χ (2 * (k + 1) + 1))).trans
          (evalDist_odd_step_even p hp χ (2 * (k + 1) + 1) (by omega))

private theorem evalDist_oddCanonical_last
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw ((fun out => out.map (fun z => z.2.2)) <$> oddRoundCanonical p χ) =
      finiteLaw (Option.some <$> firstExchangeFailureExp p χ) := by
  simp [oddRoundCanonical, firstExchangeFailureExp]

private theorem evalDist_evenCanonical_last
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw ((fun out => out.map (fun z => z.2.2)) <$> evenRoundCanonical p χ) =
      finiteLaw (Option.some <$> firstExchangeFailureExp p χ) := by
  calc
    finiteLaw ((fun out => out.map (fun z => z.2.2)) <$> evenRoundCanonical p χ) =
        finiteLaw (Option.some <$> secondExchangeFailureExp p χ) := by
          simp [evenRoundCanonical, secondExchangeFailureExp]
    _ = finiteLaw (Option.some <$> firstExchangeFailureExp p χ) :=
      finiteLaw_map_congr (evalDist_secondExchangeFailureExp_eq_first p χ)
        Option.some

private theorem evalDist_honestRounds_last_eq_first
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (j : ℕ) :
    finiteLaw ((fun out => out.map (fun z => z.2.2)) <$>
      honestRoundsSchemeExp p hp χ (j + 1)) =
      finiteLaw (Option.some <$> firstExchangeFailureExp p χ) := by
  by_cases hj : j % 2 = 0
  · have hround := (evalDist_honestRounds_canonical p hp χ (j / 2)).1
    have hcount : 2 * (j / 2) + 1 = j + 1 := by omega
    rw [hcount] at hround
    have hmapped : finiteLaw ((fun out => out.map (fun z => z.2.2)) <$>
        honestRoundsSchemeExp p hp χ (j + 1)) =
        finiteLaw ((fun out => out.map (fun z => z.2.2)) <$> oddRoundCanonical p χ) :=
      finiteLaw_map_congr hround (fun out => out.map (fun z => z.2.2))
    exact hmapped.trans (evalDist_oddCanonical_last p χ)
  · have hj' : j % 2 = 1 := by omega
    have hround := (evalDist_honestRounds_canonical p hp χ (j / 2)).2
    have hcount : 2 * (j / 2) + 2 = j + 1 := by omega
    rw [hcount] at hround
    have hmapped : finiteLaw ((fun out => out.map (fun z => z.2.2)) <$>
        honestRoundsSchemeExp p hp χ (j + 1)) =
        finiteLaw ((fun out => out.map (fun z => z.2.2)) <$> evenRoundCanonical p χ) :=
      finiteLaw_map_congr hround (fun out => out.map (fun z => z.2.2))
    exact hmapped.trans (evalDist_evenCanonical_last p χ)

/-- The final round through the scheme has the same mismatch distribution as the corresponding
tape round. -/
theorem evalDist_honestRoundsSchemeExp_last_eq_tape
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (j : ℕ) :
    finiteLaw ((fun out => out.map (fun z => z.2.2)) <$>
      honestRoundsSchemeExp p hp χ (j + 1)) =
      finiteLaw ((fun t => some (tapeRoundMismatch p t.1 t.2 j)) <$>
        sampleHonestTape p χ (j + 1)) := by
  have hmapped := finiteLaw_map_congr
    (evalDist_tapeRoundMismatch_eq_first p χ (j + 1) j (by omega)) Option.some
  exact (evalDist_honestRounds_last_eq_first p hp χ j).trans (by
    simpa [Functor.map_map, Function.comp_def] using hmapped.symm)

/-- The final round has the same mismatch distribution as the first exchange. -/
theorem evalDist_honestRoundsSchemeExp_last_eq_first
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (j : ℕ) :
    finiteLaw ((fun out => out.map (fun z => z.2.2)) <$>
      honestRoundsSchemeExp p hp χ (j + 1)) =
      finiteLaw (Option.some <$> firstExchangeFailureExp p χ) := by
  exact evalDist_honestRounds_last_eq_first p hp χ j

/-- Describe the states allowed during honest exchanges in which the parties take turns.
These states include a send that awaits its matching receive. -/
def honestPhase
    (p : Params) (s : CKAScheme.GameState (State p) (Key p) (Message p)) : Prop :=
  match s.lastAction, s.stA, s.stB with
  | none, .aSend _ _, .bRecv _ _ =>
      s.tA = 0 ∧ s.tB = 0 ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .recvA, .aSend _ _, .bRecv _ _ =>
      s.tA = s.tB ∧ s.tA % 2 = 0 ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendA, .aRecv _ _, .bRecv _ _ =>
      s.tA = s.tB + 1 ∧ s.tB % 2 = 0 ∧
      (∃ pub hint key, s.rhoA = some (.fromA pub hint) ∧ s.keyA = some key) ∧
      s.rhoB = none ∧ s.keyB = none
  | some .recvB, .aRecv _ _, .bSend _ _ =>
      s.tA = s.tB ∧ s.tA % 2 = 1 ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendB, .aRecv _ _, .bRecv _ _ =>
      s.tB = s.tA + 1 ∧ s.tA % 2 = 1 ∧
      (∃ pub hint key, s.rhoB = some (.fromB pub hint) ∧ s.keyB = some key) ∧
      s.rhoA = none ∧ s.keyA = none
  | _, _, _ => False

/-- The initial state of the correctness game satisfies `honestPhase`. -/
theorem honestPhase_init (p : Params) (ik : InitKey p) :
    honestPhase p (CKAScheme.initGameState (initA ik) (initB ik)) := by
  simp [honestPhase, CKAScheme.initGameState, initA, initB]

/-- Answer correctness queries using a tape of random matrices sampled in advance.
When the tape is empty, use the original query implementation. -/
def tapeCorrectnessImpl
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    QueryImpl (CKAScheme.ckaCorrectnessSpec (Message p) (Key p))
      (StateT
        (CKAScheme.GameState (State p) (Key p) (Message p) ×
          List (SendACoins p × SendBCoins p))
        ProbComp) :=
  fun q => do
    let (s, tape) ← get
    match tape with
    | [] =>
        let (out, s') ← liftM
          ((CKAScheme.ckaCorrectnessImpl (scheme p hp χ) q).run s)
        set (s', ([] : List (SendACoins p × SendBCoins p)))
        return out
    | coins :: rest =>
        let fixed : CKAScheme ProbComp
            (InitKey p) (State p) (Key p) (Message p) (Rand p) :=
          { scheme p hp χ with
            sendA := fun st => pure <| match st with
              | .aSend baseMatrix pub =>
                  let a := coins.1
                  let nextPub := a.secret * baseMatrix + a.error
                  let value := a.secret * pub + a.extra
                  some (extract p value, .fromA nextPub (makeHint p value),
                    .aRecv baseMatrix a.secret)
              | _ => none
            sendB := fun st => pure <| match st with
              | .bSend baseMatrix pub =>
                  let b := coins.2
                  let nextPub := baseMatrix * b.secret + b.error
                  let value := pub * b.secret + b.extra
                  some (extract p value, .fromB nextPub (makeHint p value),
                    .bRecv baseMatrix b.secret)
              | _ => none }
        let (out, s') ← liftM ((CKAScheme.ckaCorrectnessImpl fixed q).run s)
        set (s', if max s.tA s.tB < max s'.tA s'.tB then rest else coins :: rest)
        return out

end lweCKA
