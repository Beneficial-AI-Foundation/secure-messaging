/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Correctness.Exchange
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Sampled honest tapes

This module proves that every round of a pre-sampled honest tape has the same mismatch
distribution as the first exchange and establishes the finite-prefix union bound.
-/

open OracleComp ENNReal

namespace lweCKA

/-- Sample initialization and a finite list of random matrices for honest sends.
This list is called a tape. Each entry contains samples for both parties. -/
noncomputable def sampleHonestTape
    (p : Params) (χ : ProbComp (Scalar p)) (N : ℕ) :
    ProbComp (InitKey p × List (SendACoins p × SendBCoins p)) := do
  let ik ← initKeyGen p χ
  let tape ← OracleComp.drawList (do
    let a ← sampleSendACoins p χ
    let b ← sampleSendBCoins p χ
    return (a, b)) N
  return (ik, tape)

/-- Test whether the keys disagree in round `j` of the tape. -/
def tapeRoundMismatch
    (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) : ℕ → Bool
  | 0 =>
      match tape[(0 : ℕ)]? with
      | none => false
      | some (a, _) =>
          let senderValue := a.secret * (ik.baseMatrix * ik.secret + ik.error) + a.extra
          let receiverValue := (a.secret * ik.baseMatrix + a.error) * ik.secret
          decide (reconcile p receiverValue (makeHint p senderValue) ≠
            extract p senderValue)
  | j + 1 =>
      match tape[j]?, tape[j + 1]? with
      | some (previousA, previousB), some (a, b) =>
          let values : SharedMatrix p × SharedMatrix p :=
            if (j + 1) % 2 = 0 then
              ((a.secret * ik.baseMatrix + a.error) * previousB.secret,
                a.secret * (ik.baseMatrix * previousB.secret + previousB.error) + a.extra)
            else
              (previousA.secret * (ik.baseMatrix * b.secret + b.error),
                (previousA.secret * ik.baseMatrix + previousA.error) * b.secret + b.extra)
          decide (reconcile p values.1 (makeHint p values.2) ≠ extract p values.2)
      | _, _ => false

/-- The tape from `sampleHonestTape` always has the requested length. -/
theorem sampleHonestTape_length
    (p : Params) (χ : ProbComp (Scalar p)) (N : ℕ) :
    ∀ t ∈ support (sampleHonestTape p χ N), t.2.length = N := by
  intro t ht
  simp only [sampleHonestTape, mem_support_bind_iff, mem_support_pure_iff] at ht
  rcases ht with ⟨ik, _, tape, htape, rfl⟩
  change tape.length = N
  induction N generalizing tape with
  | zero => simpa [OracleComp.drawList] using htape
  | succ N ih =>
      simp only [OracleComp.drawList, mem_support_bind_iff, mem_support_pure_iff] at htape
      rcases htape with ⟨coins, _, tail, htail, rfl⟩
      simp [ih tail htail]

namespace CorrectnessInternal

theorem length_of_mem_support_drawList
    {R : Type} (oa : ProbComp R) (N : ℕ) :
    ∀ xs ∈ support (OracleComp.drawList oa N), xs.length = N := by
  intro xs hxs
  induction N generalizing xs with
  | zero => simpa [OracleComp.drawList] using hxs
  | succ N ih =>
      simp only [OracleComp.drawList, mem_support_bind_iff,
        mem_support_pure_iff] at hxs
      rcases hxs with ⟨x, _, tail, htail, rfl⟩
      simp [ih tail htail]

end CorrectnessInternal

open CorrectnessInternal

private theorem evalDist_drawList_get?
    {R : Type} (oa : ProbComp R) (N j : ℕ) (hj : j < N) :
    finiteLaw ((fun xs => getElem? xs j) <$> OracleComp.drawList oa N) =
      finiteLaw (Option.some <$> oa) := by
  induction N generalizing j with
  | zero => omega
  | succ N ih =>
      cases j with
      | zero =>
          simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc]
          simp only [pure_bind, Function.comp_apply, List.getElem?_cons_zero]
          refine (evalDist_bind_congr' oa (ob₂ := fun x => pure (some x)) fun x => ?_).trans ?_
          · exact lweCKA.evalDist_bind_const_neverFails
              (OracleComp.drawList oa N) (probFailure_drawList oa N) (pure (some x))
          · simp [map_eq_bind_pure_comp]
      | succ j =>
          have hj' : j < N := by omega
          simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc]
          simp only [pure_bind, Function.comp_apply, List.getElem?_cons_succ]
          rw [lweCKA.evalDist_bind_const_neverFails oa
            (probFailure_eq_zero (mx := oa))]
          simpa [map_eq_bind_pure_comp, Function.comp_apply] using ih j hj'

private theorem evalDist_drawList_adjacent
    {R : Type} (oa : ProbComp R) (N j : ℕ) (hj : j + 1 < N) :
    finiteLaw ((fun xs => (getElem? xs j, getElem? xs (j + 1))) <$>
      OracleComp.drawList oa N) =
      finiteLaw (do
        let x ← oa
        let y ← oa
        return (some x, some y)) := by
  induction N generalizing j with
  | zero => omega
  | succ N ih =>
      cases j with
      | zero =>
          have hzero : 0 < N := by omega
          simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply, List.getElem?_cons_zero, List.getElem?_cons_succ]
          refine evalDist_bind_congr' oa fun x => ?_
          have hmap := finiteLaw_map_congr
            (evalDist_drawList_get? oa N 0 hzero) (fun oy => (some x, oy))
          simpa [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc] using hmap
      | succ j =>
          have hj' : j + 1 < N := by omega
          simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply, List.getElem?_cons_succ]
          rw [lweCKA.evalDist_bind_const_neverFails oa
            (probFailure_eq_zero (mx := oa))]
          simpa [map_eq_bind_pure_comp, Function.comp_apply] using ih j hj'

private noncomputable def honestRoundCoins
    (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (SendACoins p × SendBCoins p) := do
  let a ← sampleSendACoins p χ
  let b ← sampleSendBCoins p χ
  return (a, b)

private theorem evalDist_drop {A B : Type} (mx : ProbComp A) (my : ProbComp B) :
    finiteLaw (mx >>= fun _ => my) = finiteLaw my :=
  lweCKA.evalDist_bind_const_neverFails
    mx (probFailure_eq_zero (mx := mx)) my

private theorem evalDist_drop3 {A₁ A₂ A₃ B : Type}
    (mx₁ : ProbComp A₁) (mx₂ : ProbComp A₂) (mx₃ : ProbComp A₃)
    (my : ProbComp B) :
    finiteLaw (mx₁ >>= fun _ => mx₂ >>= fun _ => mx₃ >>= fun _ => my) = finiteLaw my := by
  exact (evalDist_drop mx₁ _).trans <| (evalDist_drop mx₂ _).trans <|
    evalDist_drop mx₃ my

private theorem evalDist_drop2 {A₁ A₂ B : Type}
    (mx₁ : ProbComp A₁) (mx₂ : ProbComp A₂) (my : ProbComp B) :
    finiteLaw (mx₁ >>= fun _ => mx₂ >>= fun _ => my) = finiteLaw my := by
  exact (evalDist_drop mx₁ _).trans <| evalDist_drop mx₂ my

namespace CorrectnessInternal

theorem evalDist_bind_replace {A B : Type} {mx my : ProbComp A}
    (h : finiteLaw mx = finiteLaw my) (k : A → ProbComp B) :
    finiteLaw (mx >>= k) = finiteLaw (my >>= k) := by
  simp only [evalDist_bind, h]

end CorrectnessInternal

open CorrectnessInternal

private theorem evalDist_initBase
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw ((fun ik => ik.baseMatrix) <$> initKeyGen p χ) =
      finiteLaw (($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))) := by
  simp only [initKeyGen, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine (evalDist_bind_congr' (($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p)))
    (ob₂ := fun baseMatrix => pure baseMatrix) fun baseMatrix => ?_).trans ?_
  · exact evalDist_drop2 (sampleMatrix χ p.n p.nbar) (sampleMatrix χ p.n p.nbar)
      (pure baseMatrix)
  · simp

private theorem evalDist_roundA
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw ((fun coins => coins.1) <$> honestRoundCoins p χ) =
      finiteLaw (sampleSendACoins p χ) := by
  simp only [honestRoundCoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine (evalDist_bind_congr' (sampleSendACoins p χ)
    (ob₂ := fun a => pure a) fun a => ?_).trans ?_
  · exact evalDist_drop (sampleSendBCoins p χ) (pure a)
  · simp

private theorem evalDist_roundB
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw ((fun coins => coins.2) <$> honestRoundCoins p χ) =
      finiteLaw (sampleSendBCoins p χ) := by
  simp only [honestRoundCoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine (evalDist_drop (sampleSendACoins p χ) _).trans ?_
  simp

private theorem evalDist_roundBNoise
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw ((fun coins => (coins.2.secret, coins.2.error)) <$> honestRoundCoins p χ) =
      finiteLaw (do
        let secret ← sampleMatrix χ p.n p.nbar
        let error ← sampleMatrix χ p.n p.nbar
        return (secret, error)) := by
  simp only [honestRoundCoins, sampleSendBCoins, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  refine (evalDist_drop (sampleSendACoins p χ) _).trans ?_
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun secret => ?_
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun error => ?_
  exact evalDist_drop (sampleMatrix χ p.nbar p.nbar) (pure (secret, error))

private theorem evalDist_sendBNoise
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw ((fun coins : SendBCoins p => (coins.secret, coins.error)) <$>
      sampleSendBCoins p χ) =
      finiteLaw (do
        let secret ← sampleMatrix χ p.n p.nbar
        let error ← sampleMatrix χ p.n p.nbar
        return (secret, error)) := by
  simp only [sampleSendBCoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun secret => ?_
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun error => ?_
  exact evalDist_drop (sampleMatrix χ p.nbar p.nbar) (pure (secret, error))

namespace CorrectnessInternal

theorem evalDist_evenRelevant
    (p : Params) (χ : ProbComp (Scalar p)) {X : Type}
    (f : BaseMatrix p → RightMatrix p → RightMatrix p → SendACoins p → X) :
    finiteLaw (do
      let ik ← initKeyGen p χ
      let _ ← sampleSendACoins p χ
      let previous ← sampleSendBCoins p χ
      let current ← sampleSendACoins p χ
      return f ik.baseMatrix previous.secret previous.error current) =
      finiteLaw (do
        let ik ← initKeyGen p χ
        let current ← sampleSendACoins p χ
        return f ik.baseMatrix ik.secret ik.error current) := by
  let projected : ProbComp X := do
    let baseMatrix ← (fun ik => ik.baseMatrix) <$> initKeyGen p χ
    let previous ← (fun coins : SendBCoins p => (coins.secret, coins.error)) <$>
      sampleSendBCoins p χ
    let current ← sampleSendACoins p χ
    return f baseMatrix previous.1 previous.2 current
  calc
    finiteLaw (do
        let ik ← initKeyGen p χ
        let _ ← sampleSendACoins p χ
        let previous ← sampleSendBCoins p χ
        let current ← sampleSendACoins p χ
        return f ik.baseMatrix previous.secret previous.error current) = finiteLaw projected := by
          simp only [projected, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]
          refine evalDist_bind_congr' (initKeyGen p χ) fun ik => ?_
          exact evalDist_drop (sampleSendACoins p χ) _
    _ = finiteLaw (do
        let baseMatrix ← ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
        let previousSecret ← sampleMatrix χ p.n p.nbar
        let previousError ← sampleMatrix χ p.n p.nbar
        let current ← sampleSendACoins p χ
        return f baseMatrix previousSecret previousError current) := by
          simp only [projected]
          refine (evalDist_bind_replace (evalDist_initBase p χ) _).trans ?_
          refine evalDist_bind_congr'
              (($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))) fun baseMatrix => ?_
          refine (evalDist_bind_replace (evalDist_sendBNoise p χ) _).trans ?_
          simp only [bind_assoc, pure_bind]
    _ = finiteLaw (do
        let ik ← initKeyGen p χ
        let current ← sampleSendACoins p χ
        return f ik.baseMatrix ik.secret ik.error current) := by
      simp [initKeyGen]

end CorrectnessInternal

private theorem evalDist_evenRoundCoins_eq_first
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw (do
      let ik ← initKeyGen p χ
      let previous ← honestRoundCoins p χ
      let current ← honestRoundCoins p χ
      let receiverValue :=
        (current.1.secret * ik.baseMatrix + current.1.error) * previous.2.secret
      let senderValue := current.1.secret *
        (ik.baseMatrix * previous.2.secret + previous.2.error) + current.1.extra
      return decide (reconcile p receiverValue (makeHint p senderValue) ≠
        extract p senderValue)) =
      finiteLaw (firstExchangeFailureExp p χ) := by
  let projected : ProbComp Bool := do
    let baseMatrix ← (fun ik => ik.baseMatrix) <$> initKeyGen p χ
    let previous ←
      (fun coins => (coins.2.secret, coins.2.error)) <$> honestRoundCoins p χ
    let current ← (fun coins => coins.1) <$> honestRoundCoins p χ
    let receiverValue := (current.secret * baseMatrix + current.error) * previous.1
    let senderValue := current.secret * (baseMatrix * previous.1 + previous.2) + current.extra
    return decide (reconcile p receiverValue (makeHint p senderValue) ≠
      extract p senderValue)
  calc
    finiteLaw (do
        let ik ← initKeyGen p χ
        let previous ← honestRoundCoins p χ
        let current ← honestRoundCoins p χ
        let receiverValue :=
          (current.1.secret * ik.baseMatrix + current.1.error) * previous.2.secret
        let senderValue := current.1.secret *
          (ik.baseMatrix * previous.2.secret + previous.2.error) + current.1.extra
        return decide (reconcile p receiverValue (makeHint p senderValue) ≠
          extract p senderValue)) = finiteLaw projected := by
            simp only [projected, map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_apply]
    _ = finiteLaw (do
        let baseMatrix ← ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
        let previousSecret ← sampleMatrix χ p.n p.nbar
        let previousError ← sampleMatrix χ p.n p.nbar
        let current ← sampleSendACoins p χ
        let receiverValue := (current.secret * baseMatrix + current.error) * previousSecret
        let senderValue := current.secret *
          (baseMatrix * previousSecret + previousError) + current.extra
        return decide (reconcile p receiverValue (makeHint p senderValue) ≠
          extract p senderValue)) := by
            simp only [projected]
            refine (evalDist_bind_replace (evalDist_initBase p χ) _).trans ?_
            refine evalDist_bind_congr'
              (($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))) fun baseMatrix => ?_
            refine (evalDist_bind_replace (evalDist_roundBNoise p χ) _).trans ?_
            refine (evalDist_bind_congr' (do
              let secret ← sampleMatrix χ p.n p.nbar
              let error ← sampleMatrix χ p.n p.nbar
              return (secret, error)) (ob₂ := fun previous => do
                let current ← sampleSendACoins p χ
                let receiverValue :=
                  (current.secret * baseMatrix + current.error) * previous.1
                let senderValue := current.secret *
                  (baseMatrix * previous.1 + previous.2) + current.extra
                return decide (reconcile p receiverValue (makeHint p senderValue) ≠
                  extract p senderValue)) fun previous => ?_).trans ?_
            · exact evalDist_bind_replace (evalDist_roundA p χ) _
            · simp only [bind_assoc, pure_bind]
    _ = finiteLaw (firstExchangeFailureExp p χ) := by
      simp [firstExchangeFailureExp, initKeyGen]

private theorem evalDist_oddRoundCoins_eq_second
    (p : Params) (χ : ProbComp (Scalar p)) :
    finiteLaw (do
      let ik ← initKeyGen p χ
      let previous ← honestRoundCoins p χ
      let current ← honestRoundCoins p χ
      let receiverValue := previous.1.secret *
        (ik.baseMatrix * current.2.secret + current.2.error)
      let senderValue :=
        (previous.1.secret * ik.baseMatrix + previous.1.error) * current.2.secret +
          current.2.extra
      return decide (reconcile p receiverValue (makeHint p senderValue) ≠
        extract p senderValue)) =
      finiteLaw (secondExchangeFailureExp p χ) := by
  let projected : ProbComp Bool := do
    let ik ← initKeyGen p χ
    let previous ← (fun coins => coins.1) <$> honestRoundCoins p χ
    let current ← (fun coins => coins.2) <$> honestRoundCoins p χ
    let receiverValue := previous.secret * (ik.baseMatrix * current.secret + current.error)
    let senderValue :=
      (previous.secret * ik.baseMatrix + previous.error) * current.secret + current.extra
    return decide (reconcile p receiverValue (makeHint p senderValue) ≠
      extract p senderValue)
  calc
    finiteLaw (do
        let ik ← initKeyGen p χ
        let previous ← honestRoundCoins p χ
        let current ← honestRoundCoins p χ
        let receiverValue := previous.1.secret *
          (ik.baseMatrix * current.2.secret + current.2.error)
        let senderValue :=
          (previous.1.secret * ik.baseMatrix + previous.1.error) * current.2.secret +
            current.2.extra
        return decide (reconcile p receiverValue (makeHint p senderValue) ≠
          extract p senderValue)) = finiteLaw projected := by
            simp only [projected, map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_apply]
    _ = finiteLaw (secondExchangeFailureExp p χ) := by
      simp only [projected, secondExchangeFailureExp]
      refine evalDist_bind_congr' (initKeyGen p χ) fun ik => ?_
      refine (evalDist_bind_replace (evalDist_roundA p χ) _).trans ?_
      refine evalDist_bind_congr' (sampleSendACoins p χ) fun previous => ?_
      exact evalDist_bind_replace (evalDist_roundB p χ) _

/-- Each round within the tape has the same mismatch distribution as the first exchange. -/
theorem evalDist_tapeRoundMismatch_eq_first
    (p : Params) (χ : ProbComp (Scalar p)) (N j : ℕ) (hj : j < N) :
    finiteLaw ((fun t => tapeRoundMismatch p t.1 t.2 j) <$> sampleHonestTape p χ N) =
      finiteLaw (firstExchangeFailureExp p χ) := by
  cases j with
  | zero =>
      let mismatch (ik : InitKey p) (a : SendACoins p) : Bool :=
        let senderValue := a.secret * (ik.baseMatrix * ik.secret + ik.error) + a.extra
        let receiverValue := (a.secret * ik.baseMatrix + a.error) * ik.secret
        decide (reconcile p receiverValue (makeHint p senderValue) ≠
          extract p senderValue)
      simp only [sampleHonestTape, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      refine (evalDist_bind_congr' (initKeyGen p χ)
        (ob₂ := fun ik => mismatch ik <$> sampleSendACoins p χ) fun ik => ?_).trans ?_
      · let observe : Option (SendACoins p × SendBCoins p) → Bool
          | none => false
          | some (a, _) => mismatch ik a
        have hobserve : (fun tape => tapeRoundMismatch p ik tape 0) =
            fun tape => observe (getElem? tape 0) := by
          funext tape
          cases hcoin : getElem? tape 0 with
          | none => simp [tapeRoundMismatch, observe, hcoin]
          | some coin =>
              rcases coin with ⟨a, b⟩
              simp [tapeRoundMismatch, observe, mismatch, hcoin]
        have hcoord := finiteLaw_map_congr
          (evalDist_drawList_get? (honestRoundCoins p χ) N 0 hj) observe
        calc
          finiteLaw (OracleComp.drawList (do
              let a ← sampleSendACoins p χ
              let b ← sampleSendBCoins p χ
              return (a, b)) N >>= fun tape =>
                pure (tapeRoundMismatch p ik tape 0)) =
              finiteLaw (observe <$> (fun tape => getElem? tape 0) <$>
                OracleComp.drawList (honestRoundCoins p χ) N) := by
                  simp [honestRoundCoins, hobserve, map_eq_bind_pure_comp,
                    Function.comp_apply, bind_assoc]
          _ = finiteLaw (observe <$> Option.some <$> honestRoundCoins p χ) := hcoord
          _ = finiteLaw (mismatch ik <$> ((fun coins => coins.1) <$>
                honestRoundCoins p χ)) := by
                  simp [observe, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
          _ = finiteLaw (mismatch ik <$> sampleSendACoins p χ) :=
            finiteLaw_map_congr (evalDist_roundA p χ) (mismatch ik)
      · simp [firstExchangeFailureExp, mismatch, map_eq_bind_pure_comp]
  | succ j =>
      have hj' : j + 1 < N := by omega
      let roundMismatch (ik : InitKey p)
          (previous current : SendACoins p × SendBCoins p) : Bool :=
        let values : SharedMatrix p × SharedMatrix p :=
          if (j + 1) % 2 = 0 then
            ((current.1.secret * ik.baseMatrix + current.1.error) * previous.2.secret,
              current.1.secret *
                (ik.baseMatrix * previous.2.secret + previous.2.error) + current.1.extra)
          else
            (previous.1.secret *
                (ik.baseMatrix * current.2.secret + current.2.error),
              (previous.1.secret * ik.baseMatrix + previous.1.error) * current.2.secret +
                current.2.extra)
        decide (reconcile p values.1 (makeHint p values.2) ≠ extract p values.2)
      have hfront :
          finiteLaw ((fun t => tapeRoundMismatch p t.1 t.2 (j + 1)) <$>
            sampleHonestTape p χ N) =
            finiteLaw (do
              let ik ← initKeyGen p χ
              let previous ← honestRoundCoins p χ
              let current ← honestRoundCoins p χ
              return roundMismatch ik previous current) := by
        simp only [sampleHonestTape, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        refine evalDist_bind_congr' (initKeyGen p χ) fun ik => ?_
        change finiteLaw (OracleComp.drawList (honestRoundCoins p χ) N >>= fun tape =>
            pure (tapeRoundMismatch p ik tape (j + 1))) =
          finiteLaw (do
            let previous ← honestRoundCoins p χ
            let current ← honestRoundCoins p χ
            return roundMismatch ik previous current)
        let observe : Option (SendACoins p × SendBCoins p) ×
            Option (SendACoins p × SendBCoins p) → Bool
          | (some (previousA, previousB), some (a, b)) =>
              roundMismatch ik (previousA, previousB) (a, b)
          | _ => false
        have hobserve : (fun tape => tapeRoundMismatch p ik tape (j + 1)) =
            fun tape => observe (getElem? tape j, getElem? tape (j + 1)) := by
          funext tape
          simp only [tapeRoundMismatch]
          cases hprevious : getElem? tape j with
          | none => simp [observe]
          | some previous =>
              rcases previous with ⟨previousA, previousB⟩
              cases hcurrent : getElem? tape (j + 1) with
              | none => simp [observe]
              | some current =>
                  rcases current with ⟨a, b⟩
                  simp [observe, roundMismatch]
        have hcoord := finiteLaw_map_congr
          (evalDist_drawList_adjacent (honestRoundCoins p χ) N j hj') observe
        calc
          finiteLaw (OracleComp.drawList (honestRoundCoins p χ) N >>= fun tape =>
              pure (tapeRoundMismatch p ik tape (j + 1))) =
              finiteLaw (observe <$> (fun tape =>
                (getElem? tape j, getElem? tape (j + 1))) <$>
                  OracleComp.drawList (honestRoundCoins p χ) N) := by
                    simp [hobserve, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
          _ = finiteLaw (observe <$> (do
              let previous ← honestRoundCoins p χ
              let current ← honestRoundCoins p χ
              return (some previous, some current))) := hcoord
          _ = finiteLaw (do
              let previous ← honestRoundCoins p χ
              let current ← honestRoundCoins p χ
              return roundMismatch ik previous current) := by
                simp [observe, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
      rw [hfront]
      by_cases hparity : (j + 1) % 2 = 0
      · simpa [roundMismatch, hparity] using evalDist_evenRoundCoins_eq_first p χ
      · have hodd := evalDist_oddRoundCoins_eq_second p χ
        have hodd' : finiteLaw (do
            let ik ← initKeyGen p χ
            let previous ← honestRoundCoins p χ
            let current ← honestRoundCoins p χ
            return roundMismatch ik previous current) =
            finiteLaw (secondExchangeFailureExp p χ) := by
          simpa [roundMismatch, hparity] using hodd
        exact hodd'.trans (evalDist_secondExchangeFailureExp_eq_first p χ)

/-- The probability of any mismatch in the first `T` rounds is at most `T *
firstExchangeFailureProb`.
This sum of individual failure probabilities is a union bound. -/
theorem probEvent_tapePrefixFailure_le
    (p : Params) (χ : ProbComp (Scalar p)) (T : ℕ) :
    Pr{let t ← sampleHonestTape p χ (T + 1)}[∃ j : Fin T, tapeRoundMismatch p t.1 t.2 j.val =
        true] ≤
      (T : ℝ≥0∞) * firstExchangeFailureProb p χ := by
  let E (j : Fin T) (t : InitKey p × List (SendACoins p × SendBCoins p)) : Prop :=
    tapeRoundMismatch p t.1 t.2 j.val = true
  calc
    Pr{let t ← sampleHonestTape p χ (T + 1)}[∃ j : Fin T, tapeRoundMismatch p t.1 t.2 j.val =
        true] ≤
        Finset.sum Finset.univ (fun j : Fin T =>
          Pr{let x ← sampleHonestTape p χ (T + 1)}[(E j) x]) := by
            simpa [E] using prEvent_exists_finset_le Finset.univ
              (sampleHonestTape p χ (T + 1)) E
    _ = Finset.sum Finset.univ (fun _ : Fin T => firstExchangeFailureProb p χ) := by
      apply Finset.sum_congr rfl
      intro j _
      change Pr{let t ← sampleHonestTape p χ (T + 1)}[tapeRoundMismatch p t.1 t.2 j.val = true] = _
      simpa only [prEvent_map, firstExchangeFailureProb] using
        evalDist_ext_iff.mp
          (evalDist_tapeRoundMismatch_eq_first p χ (T + 1) j.val (by omega)) true
    _ = (T : ℝ≥0∞) * firstExchangeFailureProb p χ := by
      simp

end lweCKA
