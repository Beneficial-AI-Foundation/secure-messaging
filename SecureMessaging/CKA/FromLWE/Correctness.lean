/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Construction
import VCVio.EvalDist.IndepProduct
import VCVio.EvalDist.Option
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Correctness and failure probabilities for LWE CKA

The experiment below samples initialization and the first honest exchange.
The sender performs the first send. The receiver uses the initial secret to recover its key from
the message.
Reconciliation recovers key bits using a public hint.
It returns `true` when the complete extracted and reconciled keys disagree, so a
failure in any matrix entry counts. The experiment keeps the joint distribution of both parties'
values.
It does not assume that those values are independent.

The definitions accept arbitrary scalar noise `χ`. Their intended cryptographic
use is with `Params.WellFormed`. The theorems below relate the first exchange to later exchanges
and to the adversarial correctness game.
The final bound assumes at most `T` completed exchanges in every possible run.

## Relation to the paper's correctness requirement

Alwen, Coretti and Dodis [ACD19, Section 4.1.1, correctness paragraph after
Definition 12] require matching keys in every round with probability one.
Their LWE construction [Section 4.1.2, pp. 23–24] leaves the noise distribution
and numerical parameters abstract. Appendix C.2 (p. 55) gives a small-error condition for
reconciliation.
These passages do not give constraints on `χ` and the parameters that guarantee this condition for
every sample.
CPA security means security against chosen-plaintext attacks.
Theorem 4 assumes CPA security of Frodo. It does not prove that errors have probability zero.
References are listed in `Construction.lean`.

The referenced original Frodo paper [BCDMNNRS16, Section 4.4, Table 2] reports
positive failure probabilities for its proposed parameters. Those estimates
therefore do not establish perfect correctness of the CKA instantiation.
The concrete instantiation still needs a proof that it meets the abstract requirement.
This gap does not rule out perfect correctness for other choices of parameters and noise
distribution.

`firstExchangeFailureProb` records the exact failure probability without asserting that it is zero.
The final theorem bounds the game failure probability by `min 1 (T * firstExchangeFailureProb)`.
This bound allows positive failure probability, which relaxes the requirement in [ACD19].
Perfect correctness means that the keys agree with probability one.
The final corollary proves this property if the first exchange has zero failure probability and
the exchange bound holds.
Security of a parameter choice alone does not prove zero failure probability.
-/

open OracleComp ENNReal

namespace lweCKA

/-- Sample the first honest exchange and test whether the keys disagree.
Use the initialization and send samplers from the construction.
The result is `true` if any entry differs after key extraction and recovery. -/
def firstExchangeFailureExp (p : Params) (χ : ProbComp (Scalar p)) : ProbComp Bool := do
  -- ik.base is the shared public n × n matrix, sampled uniformly over ZMod p.q.
  -- It is the matrix conventionally written A in the mathematical construction.
  let ik ← initKeyGen p χ
  -- Sample the first sender's fresh secret, error, and extra-error matrices.
  let r ← sampleSendACoins p χ
  -- The receiver's initial public matrix P₀ = base · S₀ + E₀ (n × nbar).
  -- The sender initially holds P₀; the receiver retains S₀ = ik.secret.
  let receiverPublicMatrix := ik.base * ik.secret + ik.error
  -- The sender's outgoing public matrix P₁ = S₁ · base + E₁ (nbar × n).
  -- It accompanies the hint; S₁ = r.secret is the sender's fresh secret.
  let senderPublicMatrix := r.secret * ik.base + r.error
  -- The sender extracts its key and hint from V = S₁ · P₀ + extra (nbar × nbar).
  let senderValue := r.secret * receiverPublicMatrix + r.extra
  -- The receiver computes W = P₁ · S₀ (nbar × nbar), then uses the sender's hint.
  let receiverValue := senderPublicMatrix * ik.secret
  return decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue)

/-- The exact probability that any key entry differs in the first honest exchange.
This definition gives no upper bound below one.
VCVio also provides a finite rational evaluator for concrete executable experiments. -/
noncomputable def firstExchangeFailureProb (p : Params) (χ : ProbComp (Scalar p)) : ℝ≥0∞ :=
  Pr[= true | firstExchangeFailureExp p χ]

/-- Run the first honest exchange through the scheme operations.
The result `some true` means that the keys disagree, and `some false` means that they agree.
The result `none` means that a send or receive operation returns `none`.
The experiment includes all outcomes, including operation failures. -/
def firstExchangeSchemeExp
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    ProbComp (Option Bool) := do
  let cka := scheme p hp χ
  let ik ← cka.initKeyGen
  let senderState ← cka.initA ik
  let receiverState ← cka.initB ik
  let sent ← cka.sendA senderState
  match sent with
  | none => return none
  | some (senderKey, msg, _) =>
      match cka.recvB receiverState msg with
      | none => return none
      | some (receiverKey, _) =>
          return some (decide (receiverKey ≠ senderKey))

/-- The first exchange through the scheme gives the mismatch experiment result wrapped in `some`. -/
theorem firstExchangeSchemeExp_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    firstExchangeSchemeExp p hp χ =
      Option.some <$> firstExchangeFailureExp p χ := by
  simp [firstExchangeSchemeExp, firstExchangeFailureExp, scheme, initA, initB,
    sendArleak, eraseCoins, recvB]

/-- Neither scheme operation returns `none` during the first honest exchange. -/
theorem probOutput_firstExchangeSchemeExp_none
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    Pr[= none | firstExchangeSchemeExp p hp χ] = 0 := by
  rw [firstExchangeSchemeExp_eq_map]
  exact probOutput_some_map_none _

/-- The first exchange through the scheme has failure probability `firstExchangeFailureProb`.
A difference in any key entry counts as failure. -/
theorem probOutput_firstExchangeSchemeExp_true
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    Pr[= some true | firstExchangeSchemeExp p hp χ] =
      firstExchangeFailureProb p χ := by
  rw [firstExchangeSchemeExp_eq_map]
  exact probOutput_some_map_some _ _

/-- Transposing a noise matrix preserves its distribution after swapping the dimensions.
Each entry is sampled independently from the same distribution. -/
theorem evalDist_sampleMatrix_transpose
    {p : Params} (χ : ProbComp (Scalar p)) (rows cols : ℕ) :
    𝒟[(fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m.transpose) <$>
      sampleMatrix χ rows cols] =
      𝒟[sampleMatrix χ cols rows] := by
  apply evalDist_ext
  intro y
  rw [probOutput_map_eq_probOutput_inverse (sampleMatrix χ rows cols)
    (f := fun m : Matrix (Fin rows) (Fin cols) (Scalar p) => m.transpose)
    (g := fun m => m.transpose) (fun x => Matrix.transpose_transpose x)
    (Matrix.transpose_transpose y)]
  change Pr[= (fun i j => y j i) |
      Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ] =
    Pr[= (fun j i => y j i) |
      Fin.mOfFn cols fun _ => Fin.mOfFn rows fun _ => χ]
  rw [probOutput_mOfFn]
  simp_rw [probOutput_mOfFn]
  exact Finset.prod_comm

/-- Transposing both keys preserves whether the recovered and extracted keys disagree. -/
theorem keyMismatch_transpose
    (p : Params) (receiverValue senderValue : Shared p) :
    decide (reconcile p receiverValue.transpose (makeHint p senderValue.transpose) ≠
      extract p senderValue.transpose) =
      decide (reconcile p receiverValue (makeHint p senderValue) ≠
        extract p senderValue) := by
  apply Bool.decide_congr
  constructor
  · intro h hbase
    apply h
    funext i j
    exact congrFun (congrFun hbase j) i
  · intro h htrans
    apply h
    funext i j
    exact congrFun (congrFun htrans j) i

/-- Test whether the keys disagree in the second honest exchange.
Keep the samples from initialization and both sends, whether or not the first exchange succeeds. -/
def secondExchangeFailureExp
    (p : Params) (χ : ProbComp (Scalar p)) : ProbComp Bool := do
  let ik ← initKeyGen p χ
  let a ← sampleSendACoins p χ
  let b ← sampleSendBCoins p χ
  let firstPublicMatrix := a.secret * ik.base + a.error
  let secondPublicMatrix := ik.base * b.secret + b.error
  let senderValue := firstPublicMatrix * b.secret + b.extra
  let receiverValue := a.secret * secondPublicMatrix
  return decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue)

/-- Run two honest exchanges through the scheme and test whether the second pair of keys disagrees.
Keep the states from the first exchange, whether or not its keys agree.
The result `none` means that a send or receive operation rejects its input. -/
def secondExchangeSchemeExp
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    ProbComp (Option Bool) := do
  let cka := scheme p hp χ
  let ik ← cka.initKeyGen
  let stateA ← cka.initA ik
  let stateB ← cka.initB ik
  let firstSent ← cka.sendA stateA
  match firstSent with
  | none => return none
  | some (_, firstMsg, stateA') =>
      match cka.recvB stateB firstMsg with
      | none => return none
      | some (_, stateB') =>
          let secondSent ← cka.sendB stateB'
          match secondSent with
          | none => return none
          | some (senderKey, secondMsg, _) =>
              match cka.recvA stateA' secondMsg with
              | none => return none
              | some (receiverKey, _) =>
                  return some (decide (receiverKey ≠ senderKey))

/-- The second exchange through the scheme has the same distribution as the mathematical
experiment, including all sampled values. -/
theorem secondExchangeSchemeExp_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    secondExchangeSchemeExp p hp χ =
      Option.some <$> secondExchangeFailureExp p χ := by
  simp [secondExchangeSchemeExp, secondExchangeFailureExp, scheme, initA, initB,
    sendArleak, sendBrleak, eraseCoins, recvA, recvB]

/-- The transposed samples used by the second exchange have the same joint distribution as the
samples used by the first.
Unused samples are summed out of the distribution. No outcome is excluded. -/
theorem evalDist_secondExchangeCoins_transpose
    (p : Params) (χ : ProbComp (Scalar p)) :
    𝒟[do
      let ik ← initKeyGen p χ
      let a ← sampleSendACoins p χ
      let b ← sampleSendBCoins p χ
      return (
         ({ base := ik.base.transpose
            secret := a.secret.transpose
            error := a.error.transpose } : InitKey p),
         ({ secret := b.secret.transpose
            error := b.error.transpose
            extra := b.extra.transpose } : SendACoins p))] =
      𝒟[do
        let ik ← initKeyGen p χ
        let a ← sampleSendACoins p χ
        return (ik, a)] := by
  have hDrop { α β : Type } (mx : ProbComp α) (my : ProbComp β) :
      𝒟[mx >>= fun _ => my] = 𝒟[my] := by
    apply evalDist_ext
    intro y
    rw [probOutput_bind_const, probFailure_of_liftM_PMF]
    simp
  have hHead { α β : Type } (mx my : ProbComp α)
      (h : 𝒟[mx] = 𝒟[my]) (f : α → ProbComp β) :
      𝒟[mx >>= f] = 𝒟[my >>= f] := by
    rw [evalDist_bind, evalDist_bind, h]
  have hBase :
      𝒟[(fun m : Base p => m.transpose) <$> ($ᵗ (Base p) : ProbComp (Base p))] =
        𝒟[($ᵗ (Base p) : ProbComp (Base p))] := by
    apply evalDist_map_bijective_uniform_cross
    exact ⟨Matrix.transpose_injective,
      fun y => ⟨y.transpose, Matrix.transpose_transpose y⟩⟩
  simp only [initKeyGen, sampleSendACoins, sampleSendBCoins, bind_assoc, pure_bind]
  let mid : ProbComp (InitKey p × SendACoins p) := do
    let base ← (fun m : Base p => m.transpose) <$> ($ᵗ (Base p) : ProbComp (Base p))
    let initSecret ← (fun m => m.transpose) <$> sampleMatrix χ p.nbar p.n
    let initError ← (fun m => m.transpose) <$> sampleMatrix χ p.nbar p.n
    let sendSecret ← (fun m => m.transpose) <$> sampleMatrix χ p.n p.nbar
    let sendError ← (fun m => m.transpose) <$> sampleMatrix χ p.n p.nbar
    let sendExtra ← (fun m => m.transpose) <$> sampleMatrix χ p.nbar p.nbar
    pure (InitKey.mk base initSecret initError,
      SendACoins.mk sendSecret sendError sendExtra)
  refine Eq.trans (b := 𝒟[mid]) ?_ ?_
  · simp only [mid, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    refine evalDist_bind_congr' (($ᵗ (Base p) : ProbComp (Base p))) fun _ => ?_
    refine (hDrop (sampleMatrix χ p.n p.nbar) _).trans ?_
    refine (hDrop (sampleMatrix χ p.n p.nbar) _).trans ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
    exact hDrop (sampleMatrix χ p.nbar p.nbar) _
  · simp only [mid]
    refine (hHead _ _ hBase _).trans ?_
    refine evalDist_bind_congr' (($ᵗ (Base p) : ProbComp (Base p))) fun _ => ?_
    refine (hHead _ _ (evalDist_sampleMatrix_transpose χ p.nbar p.n) _).trans ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun _ => ?_
    refine (hHead _ _ (evalDist_sampleMatrix_transpose χ p.nbar p.n) _).trans ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun _ => ?_
    refine (hHead _ _ (evalDist_sampleMatrix_transpose χ p.n p.nbar) _).trans ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
    refine (hHead _ _ (evalDist_sampleMatrix_transpose χ p.n p.nbar) _).trans ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
    refine (hHead _ _ (evalDist_sampleMatrix_transpose χ p.nbar p.nbar) _).trans ?_
    exact evalDist_bind_congr' (sampleMatrix χ p.nbar p.nbar) fun _ => rfl

/-- The second exchange has the same mismatch distribution as the first, without assuming that the
first succeeds. -/
theorem evalDist_secondExchangeFailureExp_eq_first
    (p : Params) (χ : ProbComp (Scalar p)) :
    𝒟[secondExchangeFailureExp p χ] = 𝒟[firstExchangeFailureExp p χ] := by
  let firstMismatch : InitKey p × SendACoins p → Bool := fun coins =>
    let ik := coins.1
    let a := coins.2
    let receiverPublicMatrix := ik.base * ik.secret + ik.error
    let senderPublicMatrix := a.secret * ik.base + a.error
    let senderValue := a.secret * receiverPublicMatrix + a.extra
    let receiverValue := senderPublicMatrix * ik.secret
    decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue)
  have hSecond : secondExchangeFailureExp p χ = firstMismatch <$> (do
      let ik ← initKeyGen p χ
      let a ← sampleSendACoins p χ
      let b ← sampleSendBCoins p χ
      return (
        ({ base := ik.base.transpose
           secret := a.secret.transpose
           error := a.error.transpose } : InitKey p),
        ({ secret := b.secret.transpose
           error := b.error.transpose
           extra := b.extra.transpose } : SendACoins p))) := by
    simp only [secondExchangeFailureExp, map_eq_bind_pure_comp, Function.comp_apply,
      bind_assoc, pure_bind]
    apply bind_congr
    intro ik
    apply bind_congr
    intro a
    apply bind_congr
    intro b
    apply congrArg pure
    simpa only [firstMismatch, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose] using
      (keyMismatch_transpose p
        (a.secret * (ik.base * b.secret + b.error))
        ((a.secret * ik.base + a.error) * b.secret + b.extra)).symm
  have hFirst : firstExchangeFailureExp p χ = firstMismatch <$> (do
      let ik ← initKeyGen p χ
      let a ← sampleSendACoins p χ
      return (ik, a)) := by
    simp [firstExchangeFailureExp, firstMismatch, map_eq_bind_pure_comp]
  rw [hSecond, hFirst]
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_secondExchangeCoins_transpose p χ) firstMismatch

/-- No send or receive operation rejects its input during the first two honest exchanges. -/
theorem probOutput_secondExchangeSchemeExp_none
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    Pr[= none | secondExchangeSchemeExp p hp χ] = 0 := by
  rw [secondExchangeSchemeExp_eq_map]
  exact probOutput_some_map_none _

/-- The second exchange through the scheme has the same probability of key disagreement as the
first. -/
theorem probOutput_secondExchangeSchemeExp_true
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    Pr[= some true | secondExchangeSchemeExp p hp χ] =
      firstExchangeFailureProb p χ := by
  rw [secondExchangeSchemeExp_eq_map, probOutput_some_map_some]
  exact evalDist_ext_iff.mp (evalDist_secondExchangeFailureExp_eq_first p χ) true

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
          let senderValue := a.secret * (ik.base * ik.secret + ik.error) + a.extra
          let receiverValue := (a.secret * ik.base + a.error) * ik.secret
          decide (reconcile p receiverValue (makeHint p senderValue) ≠
            extract p senderValue)
  | j + 1 =>
      match tape[j]?, tape[j + 1]? with
      | some (previousA, previousB), some (a, b) =>
          let values : Shared p × Shared p :=
            if (j + 1) % 2 = 0 then
              ((a.secret * ik.base + a.error) * previousB.secret,
                a.secret * (ik.base * previousB.secret + previousB.error) + a.extra)
            else
              (previousA.secret * (ik.base * b.secret + b.error),
                (previousA.secret * ik.base + previousA.error) * b.secret + b.extra)
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

private theorem length_of_mem_support_drawList
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

private theorem evalDist_drawList_get?
    {R : Type} (oa : ProbComp R) (N j : ℕ) (hj : j < N) :
    evalDist ((fun xs => getElem? xs j) <$> OracleComp.drawList oa N) =
      evalDist (Option.some <$> oa) := by
  induction N generalizing j with
  | zero => omega
  | succ N ih =>
      cases j with
      | zero =>
          simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc]
          simp only [pure_bind, Function.comp_apply, List.getElem?_cons_zero]
          refine (evalDist_bind_congr' oa (ob₂ := fun x => pure (some x)) fun x => ?_).trans ?_
          · exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
              (OracleComp.drawList oa N) (OracleComp.probFailure_drawList oa N) (pure (some x))
          · simp [map_eq_bind_pure_comp]
      | succ j =>
          have hj' : j < N := by omega
          simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc]
          simp only [pure_bind, Function.comp_apply, List.getElem?_cons_succ]
          rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails oa
            (probFailure_eq_zero (mx := oa))]
          simpa [map_eq_bind_pure_comp, Function.comp_apply] using ih j hj'

private theorem evalDist_drawList_adjacent
    {R : Type} (oa : ProbComp R) (N j : ℕ) (hj : j + 1 < N) :
    evalDist ((fun xs => (getElem? xs j, getElem? xs (j + 1))) <$>
      OracleComp.drawList oa N) =
      evalDist (do
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
          have hmap := evalDist_map_eq_of_evalDist_eq
            (evalDist_drawList_get? oa N 0 hzero) (fun oy => (some x, oy))
          simpa [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc] using hmap
      | succ j =>
          have hj' : j + 1 < N := by omega
          simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply, List.getElem?_cons_succ]
          rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails oa
            (probFailure_eq_zero (mx := oa))]
          simpa [map_eq_bind_pure_comp, Function.comp_apply] using ih j hj'

private noncomputable def honestRoundCoins
    (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (SendACoins p × SendBCoins p) := do
  let a ← sampleSendACoins p χ
  let b ← sampleSendBCoins p χ
  return (a, b)

private theorem evalDist_drop {A B : Type} (mx : ProbComp A) (my : ProbComp B) :
    evalDist (mx >>= fun _ => my) = evalDist my :=
  OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    mx (probFailure_eq_zero (mx := mx)) my

private theorem evalDist_drop3 {A₁ A₂ A₃ B : Type}
    (mx₁ : ProbComp A₁) (mx₂ : ProbComp A₂) (mx₃ : ProbComp A₃)
    (my : ProbComp B) :
    evalDist (mx₁ >>= fun _ => mx₂ >>= fun _ => mx₃ >>= fun _ => my) = evalDist my := by
  exact (evalDist_drop mx₁ _).trans <| (evalDist_drop mx₂ _).trans <|
    evalDist_drop mx₃ my

private theorem evalDist_drop2 {A₁ A₂ B : Type}
    (mx₁ : ProbComp A₁) (mx₂ : ProbComp A₂) (my : ProbComp B) :
    evalDist (mx₁ >>= fun _ => mx₂ >>= fun _ => my) = evalDist my := by
  exact (evalDist_drop mx₁ _).trans <| evalDist_drop mx₂ my

private theorem evalDist_bind_replace {A B : Type} {mx my : ProbComp A}
    (h : evalDist mx = evalDist my) (k : A → ProbComp B) :
    evalDist (mx >>= k) = evalDist (my >>= k) := by
  simp only [evalDist_bind, h]

private theorem evalDist_initBase
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist ((fun ik => ik.base) <$> initKeyGen p χ) =
      evalDist (($ᵗ (Base p) : ProbComp (Base p))) := by
  simp only [initKeyGen, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine (evalDist_bind_congr' (($ᵗ (Base p) : ProbComp (Base p)))
    (ob₂ := fun base => pure base) fun base => ?_).trans ?_
  · exact evalDist_drop2 (sampleMatrix χ p.n p.nbar) (sampleMatrix χ p.n p.nbar)
      (pure base)
  · simp

private theorem evalDist_roundA
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist ((fun coins => coins.1) <$> honestRoundCoins p χ) =
      evalDist (sampleSendACoins p χ) := by
  simp only [honestRoundCoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine (evalDist_bind_congr' (sampleSendACoins p χ)
    (ob₂ := fun a => pure a) fun a => ?_).trans ?_
  · exact evalDist_drop (sampleSendBCoins p χ) (pure a)
  · simp

private theorem evalDist_roundB
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist ((fun coins => coins.2) <$> honestRoundCoins p χ) =
      evalDist (sampleSendBCoins p χ) := by
  simp only [honestRoundCoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine (evalDist_drop (sampleSendACoins p χ) _).trans ?_
  simp

private theorem evalDist_roundBNoise
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist ((fun coins => (coins.2.secret, coins.2.error)) <$> honestRoundCoins p χ) =
      evalDist (do
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
    evalDist ((fun coins : SendBCoins p => (coins.secret, coins.error)) <$>
      sampleSendBCoins p χ) =
      evalDist (do
        let secret ← sampleMatrix χ p.n p.nbar
        let error ← sampleMatrix χ p.n p.nbar
        return (secret, error)) := by
  simp only [sampleSendBCoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun secret => ?_
  refine evalDist_bind_congr' (sampleMatrix χ p.n p.nbar) fun error => ?_
  exact evalDist_drop (sampleMatrix χ p.nbar p.nbar) (pure (secret, error))

private theorem evalDist_evenRelevant
    (p : Params) (χ : ProbComp (Scalar p)) {X : Type}
    (f : Base p → Right p → Right p → SendACoins p → X) :
    evalDist (do
      let ik ← initKeyGen p χ
      let _ ← sampleSendACoins p χ
      let previous ← sampleSendBCoins p χ
      let current ← sampleSendACoins p χ
      return f ik.base previous.secret previous.error current) =
      evalDist (do
        let ik ← initKeyGen p χ
        let current ← sampleSendACoins p χ
        return f ik.base ik.secret ik.error current) := by
  let projected : ProbComp X := do
    let base ← (fun ik => ik.base) <$> initKeyGen p χ
    let previous ← (fun coins : SendBCoins p => (coins.secret, coins.error)) <$>
      sampleSendBCoins p χ
    let current ← sampleSendACoins p χ
    return f base previous.1 previous.2 current
  calc
    evalDist (do
        let ik ← initKeyGen p χ
        let _ ← sampleSendACoins p χ
        let previous ← sampleSendBCoins p χ
        let current ← sampleSendACoins p χ
        return f ik.base previous.secret previous.error current) = evalDist projected := by
          simp only [projected, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]
          refine evalDist_bind_congr' (initKeyGen p χ) fun ik => ?_
          exact evalDist_drop (sampleSendACoins p χ) _
    _ = evalDist (do
        let base ← ($ᵗ (Base p) : ProbComp (Base p))
        let previousSecret ← sampleMatrix χ p.n p.nbar
        let previousError ← sampleMatrix χ p.n p.nbar
        let current ← sampleSendACoins p χ
        return f base previousSecret previousError current) := by
          simp only [projected]
          refine (evalDist_bind_replace (evalDist_initBase p χ) _).trans ?_
          refine evalDist_bind_congr' (($ᵗ (Base p) : ProbComp (Base p))) fun base => ?_
          refine (evalDist_bind_replace (evalDist_sendBNoise p χ) _).trans ?_
          simp only [bind_assoc, pure_bind]
    _ = evalDist (do
        let ik ← initKeyGen p χ
        let current ← sampleSendACoins p χ
        return f ik.base ik.secret ik.error current) := by
          simp [initKeyGen]

private theorem evalDist_evenRoundCoins_eq_first
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist (do
      let ik ← initKeyGen p χ
      let previous ← honestRoundCoins p χ
      let current ← honestRoundCoins p χ
      let receiverValue :=
        (current.1.secret * ik.base + current.1.error) * previous.2.secret
      let senderValue := current.1.secret *
        (ik.base * previous.2.secret + previous.2.error) + current.1.extra
      return decide (reconcile p receiverValue (makeHint p senderValue) ≠
        extract p senderValue)) =
      evalDist (firstExchangeFailureExp p χ) := by
  let projected : ProbComp Bool := do
    let base ← (fun ik => ik.base) <$> initKeyGen p χ
    let previous ←
      (fun coins => (coins.2.secret, coins.2.error)) <$> honestRoundCoins p χ
    let current ← (fun coins => coins.1) <$> honestRoundCoins p χ
    let receiverValue := (current.secret * base + current.error) * previous.1
    let senderValue := current.secret * (base * previous.1 + previous.2) + current.extra
    return decide (reconcile p receiverValue (makeHint p senderValue) ≠
      extract p senderValue)
  calc
    evalDist (do
        let ik ← initKeyGen p χ
        let previous ← honestRoundCoins p χ
        let current ← honestRoundCoins p χ
        let receiverValue :=
          (current.1.secret * ik.base + current.1.error) * previous.2.secret
        let senderValue := current.1.secret *
          (ik.base * previous.2.secret + previous.2.error) + current.1.extra
        return decide (reconcile p receiverValue (makeHint p senderValue) ≠
          extract p senderValue)) = evalDist projected := by
            simp only [projected, map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_apply]
    _ = evalDist (do
        let base ← ($ᵗ (Base p) : ProbComp (Base p))
        let previousSecret ← sampleMatrix χ p.n p.nbar
        let previousError ← sampleMatrix χ p.n p.nbar
        let current ← sampleSendACoins p χ
        let receiverValue := (current.secret * base + current.error) * previousSecret
        let senderValue := current.secret *
          (base * previousSecret + previousError) + current.extra
        return decide (reconcile p receiverValue (makeHint p senderValue) ≠
          extract p senderValue)) := by
            simp only [projected]
            refine (evalDist_bind_replace (evalDist_initBase p χ) _).trans ?_
            refine evalDist_bind_congr' (($ᵗ (Base p) : ProbComp (Base p))) fun base => ?_
            refine (evalDist_bind_replace (evalDist_roundBNoise p χ) _).trans ?_
            refine (evalDist_bind_congr' (do
              let secret ← sampleMatrix χ p.n p.nbar
              let error ← sampleMatrix χ p.n p.nbar
              return (secret, error)) (ob₂ := fun previous => do
                let current ← sampleSendACoins p χ
                let receiverValue :=
                  (current.secret * base + current.error) * previous.1
                let senderValue := current.secret *
                  (base * previous.1 + previous.2) + current.extra
                return decide (reconcile p receiverValue (makeHint p senderValue) ≠
                  extract p senderValue)) fun previous => ?_).trans ?_
            · exact evalDist_bind_replace (evalDist_roundA p χ) _
            · simp only [bind_assoc, pure_bind]
    _ = evalDist (firstExchangeFailureExp p χ) := by
      simp [firstExchangeFailureExp, initKeyGen]

private theorem evalDist_oddRoundCoins_eq_second
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist (do
      let ik ← initKeyGen p χ
      let previous ← honestRoundCoins p χ
      let current ← honestRoundCoins p χ
      let receiverValue := previous.1.secret *
        (ik.base * current.2.secret + current.2.error)
      let senderValue :=
        (previous.1.secret * ik.base + previous.1.error) * current.2.secret +
          current.2.extra
      return decide (reconcile p receiverValue (makeHint p senderValue) ≠
        extract p senderValue)) =
      evalDist (secondExchangeFailureExp p χ) := by
  let projected : ProbComp Bool := do
    let ik ← initKeyGen p χ
    let previous ← (fun coins => coins.1) <$> honestRoundCoins p χ
    let current ← (fun coins => coins.2) <$> honestRoundCoins p χ
    let receiverValue := previous.secret * (ik.base * current.secret + current.error)
    let senderValue :=
      (previous.secret * ik.base + previous.error) * current.secret + current.extra
    return decide (reconcile p receiverValue (makeHint p senderValue) ≠
      extract p senderValue)
  calc
    evalDist (do
        let ik ← initKeyGen p χ
        let previous ← honestRoundCoins p χ
        let current ← honestRoundCoins p χ
        let receiverValue := previous.1.secret *
          (ik.base * current.2.secret + current.2.error)
        let senderValue :=
          (previous.1.secret * ik.base + previous.1.error) * current.2.secret +
            current.2.extra
        return decide (reconcile p receiverValue (makeHint p senderValue) ≠
          extract p senderValue)) = evalDist projected := by
            simp only [projected, map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_apply]
    _ = evalDist (secondExchangeFailureExp p χ) := by
      simp only [projected, secondExchangeFailureExp]
      refine evalDist_bind_congr' (initKeyGen p χ) fun ik => ?_
      refine (evalDist_bind_replace (evalDist_roundA p χ) _).trans ?_
      refine evalDist_bind_congr' (sampleSendACoins p χ) fun previous => ?_
      exact evalDist_bind_replace (evalDist_roundB p χ) _

/-- Each round within the tape has the same mismatch distribution as the first exchange. -/
theorem evalDist_tapeRoundMismatch_eq_first
    (p : Params) (χ : ProbComp (Scalar p)) (N j : ℕ) (hj : j < N) :
    𝒟[(fun t => tapeRoundMismatch p t.1 t.2 j) <$> sampleHonestTape p χ N] =
      𝒟[firstExchangeFailureExp p χ] := by
  cases j with
  | zero =>
      let mismatch (ik : InitKey p) (a : SendACoins p) : Bool :=
        let senderValue := a.secret * (ik.base * ik.secret + ik.error) + a.extra
        let receiverValue := (a.secret * ik.base + a.error) * ik.secret
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
        have hcoord := evalDist_map_eq_of_evalDist_eq
          (evalDist_drawList_get? (honestRoundCoins p χ) N 0 hj) observe
        calc
          evalDist (OracleComp.drawList (do
              let a ← sampleSendACoins p χ
              let b ← sampleSendBCoins p χ
              return (a, b)) N >>= fun tape =>
                pure (tapeRoundMismatch p ik tape 0)) =
              evalDist (observe <$> (fun tape => getElem? tape 0) <$>
                OracleComp.drawList (honestRoundCoins p χ) N) := by
                  simp [honestRoundCoins, hobserve, map_eq_bind_pure_comp,
                    Function.comp_apply, bind_assoc]
          _ = evalDist (observe <$> Option.some <$> honestRoundCoins p χ) := hcoord
          _ = evalDist (mismatch ik <$> ((fun coins => coins.1) <$>
                honestRoundCoins p χ)) := by
                  simp [observe, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
          _ = evalDist (mismatch ik <$> sampleSendACoins p χ) :=
            evalDist_map_eq_of_evalDist_eq (evalDist_roundA p χ) (mismatch ik)
      · simp [firstExchangeFailureExp, mismatch, map_eq_bind_pure_comp]
  | succ j =>
      have hj' : j + 1 < N := by omega
      let roundMismatch (ik : InitKey p)
          (previous current : SendACoins p × SendBCoins p) : Bool :=
        let values : Shared p × Shared p :=
          if (j + 1) % 2 = 0 then
            ((current.1.secret * ik.base + current.1.error) * previous.2.secret,
              current.1.secret *
                (ik.base * previous.2.secret + previous.2.error) + current.1.extra)
          else
            (previous.1.secret *
                (ik.base * current.2.secret + current.2.error),
              (previous.1.secret * ik.base + previous.1.error) * current.2.secret +
                current.2.extra)
        decide (reconcile p values.1 (makeHint p values.2) ≠ extract p values.2)
      have hfront :
          evalDist ((fun t => tapeRoundMismatch p t.1 t.2 (j + 1)) <$>
            sampleHonestTape p χ N) =
            evalDist (do
              let ik ← initKeyGen p χ
              let previous ← honestRoundCoins p χ
              let current ← honestRoundCoins p χ
              return roundMismatch ik previous current) := by
        simp only [sampleHonestTape, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        refine evalDist_bind_congr' (initKeyGen p χ) fun ik => ?_
        change evalDist (OracleComp.drawList (honestRoundCoins p χ) N >>= fun tape =>
            pure (tapeRoundMismatch p ik tape (j + 1))) =
          evalDist (do
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
        have hcoord := evalDist_map_eq_of_evalDist_eq
          (evalDist_drawList_adjacent (honestRoundCoins p χ) N j hj') observe
        calc
          evalDist (OracleComp.drawList (honestRoundCoins p χ) N >>= fun tape =>
              pure (tapeRoundMismatch p ik tape (j + 1))) =
              evalDist (observe <$> (fun tape =>
                (getElem? tape j, getElem? tape (j + 1))) <$>
                  OracleComp.drawList (honestRoundCoins p χ) N) := by
                    simp [hobserve, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
          _ = evalDist (observe <$> (do
              let previous ← honestRoundCoins p χ
              let current ← honestRoundCoins p χ
              return (some previous, some current))) := hcoord
          _ = evalDist (do
              let previous ← honestRoundCoins p χ
              let current ← honestRoundCoins p χ
              return roundMismatch ik previous current) := by
                simp [observe, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
        all_goals rfl
      rw [hfront]
      by_cases hparity : (j + 1) % 2 = 0
      · simpa [roundMismatch, hparity] using evalDist_evenRoundCoins_eq_first p χ
      · have hodd := evalDist_oddRoundCoins_eq_second p χ
        have hodd' : evalDist (do
            let ik ← initKeyGen p χ
            let previous ← honestRoundCoins p χ
            let current ← honestRoundCoins p χ
            return roundMismatch ik previous current) =
            evalDist (secondExchangeFailureExp p χ) := by
          simpa [roundMismatch, hparity] using hodd
        exact hodd'.trans (evalDist_secondExchangeFailureExp_eq_first p χ)

/-- The probability of any mismatch in the first `T` rounds is at most `T *
firstExchangeFailureProb`.
This sum of individual failure probabilities is a union bound. -/
theorem probEvent_tapePrefixFailure_le
    (p : Params) (χ : ProbComp (Scalar p)) (T : ℕ) :
    Pr[fun t => ∃ j : Fin T, tapeRoundMismatch p t.1 t.2 j.val = true |
      sampleHonestTape p χ (T + 1)] ≤
      (T : ℝ≥0∞) * firstExchangeFailureProb p χ := by
  let E (j : Fin T) (t : InitKey p × List (SendACoins p × SendBCoins p)) : Prop :=
    tapeRoundMismatch p t.1 t.2 j.val = true
  calc
    Pr[fun t => ∃ j : Fin T, tapeRoundMismatch p t.1 t.2 j.val = true |
        sampleHonestTape p χ (T + 1)] ≤
        Finset.sum Finset.univ (fun j : Fin T =>
          Pr[E j | sampleHonestTape p χ (T + 1)]) := by
            simpa [E] using probEvent_exists_finset_le_sum Finset.univ
              (sampleHonestTape p χ (T + 1)) E
    _ = Finset.sum Finset.univ (fun _ : Fin T => firstExchangeFailureProb p χ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← probOutput_map]
      exact evalDist_ext_iff.mp
        (evalDist_tapeRoundMismatch_eq_first p χ (T + 1) j.val (by omega)) true
    _ = (T : ℝ≥0∞) * firstExchangeFailureProb p χ := by
      simp

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
  let senderValue := a.secret * (ik.base * ik.secret + ik.error) + a.extra
  let receiverValue := (a.secret * ik.base + a.error) * ik.secret
  return some (.aRecv ik.base a.secret, .bSend ik.base (a.secret * ik.base + a.error),
    decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue))

private def evenRoundCanonical
    (p : Params) (χ : ProbComp (Scalar p)) :
    ProbComp (Option (State p × State p × Bool)) := do
  let ik ← initKeyGen p χ
  let a ← sampleSendACoins p χ
  let b ← sampleSendBCoins p χ
  let senderValue := (a.secret * ik.base + a.error) * b.secret + b.extra
  let receiverValue := a.secret * (ik.base * b.secret + b.error)
  return some (.aSend ik.base (ik.base * b.secret + b.error), .bRecv ik.base b.secret,
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
    evalDist (oddRoundCanonical p χ >>= honestRoundStep p hp χ n) =
      evalDist (evenRoundCanonical p χ) := by
  simp [oddRoundCanonical, evenRoundCanonical, honestRoundStep, hn, scheme,
    sendBrleak, eraseCoins, recvA]

private theorem evalDist_even_step_odd
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (n : ℕ)
    (hn : n % 2 = 0) :
    evalDist (evenRoundCanonical p χ >>= honestRoundStep p hp χ n) =
      evalDist (oddRoundCanonical p χ) := by
  let f : Base p → Right p → Right p → SendACoins p →
      Option (State p × State p × Bool) := fun base previousSecret previousError current =>
    let senderValue := current.secret * (base * previousSecret + previousError) +
      current.extra
    let receiverValue := (current.secret * base + current.error) * previousSecret
    some (.aRecv base current.secret, .bSend base (current.secret * base + current.error),
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
    evalDist (honestRoundsSchemeExp p hp χ 1) = evalDist (oddRoundCanonical p χ) := by
  simp [honestRoundsSchemeExp, oddRoundCanonical, scheme, initA, initB,
    sendArleak, eraseCoins, recvB]

private theorem evalDist_honestRounds_canonical
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (k : ℕ) :
    (evalDist (honestRoundsSchemeExp p hp χ (2 * k + 1)) =
        evalDist (oddRoundCanonical p χ)) ∧
      (evalDist (honestRoundsSchemeExp p hp χ (2 * k + 2)) =
        evalDist (evenRoundCanonical p χ)) := by
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
        have hodd : evalDist (honestRoundsSchemeExp p hp χ (2 * (k + 1) + 1)) =
            evalDist (oddRoundCanonical p χ) := by
          rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
            honestRoundsSchemeExp_succ]
          exact (evalDist_bind_replace ih.2 _).trans
            (evalDist_even_step_odd p hp χ (2 * k + 2) (by omega))
        exact (evalDist_bind_replace hodd
          (honestRoundStep p hp χ (2 * (k + 1) + 1))).trans
          (evalDist_odd_step_even p hp χ (2 * (k + 1) + 1) (by omega))

private theorem evalDist_oddCanonical_last
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist ((fun out => out.map (fun z => z.2.2)) <$> oddRoundCanonical p χ) =
      evalDist (Option.some <$> firstExchangeFailureExp p χ) := by
  simp [oddRoundCanonical, firstExchangeFailureExp]

private theorem evalDist_evenCanonical_last
    (p : Params) (χ : ProbComp (Scalar p)) :
    evalDist ((fun out => out.map (fun z => z.2.2)) <$> evenRoundCanonical p χ) =
      evalDist (Option.some <$> firstExchangeFailureExp p χ) := by
  calc
    evalDist ((fun out => out.map (fun z => z.2.2)) <$> evenRoundCanonical p χ) =
        evalDist (Option.some <$> secondExchangeFailureExp p χ) := by
          simp [evenRoundCanonical, secondExchangeFailureExp]
    _ = evalDist (Option.some <$> firstExchangeFailureExp p χ) :=
      evalDist_map_eq_of_evalDist_eq (evalDist_secondExchangeFailureExp_eq_first p χ)
        Option.some

private theorem evalDist_honestRounds_last_eq_first
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (j : ℕ) :
    evalDist ((fun out => out.map (fun z => z.2.2)) <$>
      honestRoundsSchemeExp p hp χ (j + 1)) =
      evalDist (Option.some <$> firstExchangeFailureExp p χ) := by
  by_cases hj : j % 2 = 0
  · have hround := (evalDist_honestRounds_canonical p hp χ (j / 2)).1
    have hcount : 2 * (j / 2) + 1 = j + 1 := by omega
    rw [hcount] at hround
    have hmapped : evalDist ((fun out => out.map (fun z => z.2.2)) <$>
        honestRoundsSchemeExp p hp χ (j + 1)) =
        evalDist ((fun out => out.map (fun z => z.2.2)) <$> oddRoundCanonical p χ) :=
      evalDist_map_eq_of_evalDist_eq hround (fun out => out.map (fun z => z.2.2))
    exact hmapped.trans (evalDist_oddCanonical_last p χ)
  · have hj' : j % 2 = 1 := by omega
    have hround := (evalDist_honestRounds_canonical p hp χ (j / 2)).2
    have hcount : 2 * (j / 2) + 2 = j + 1 := by omega
    rw [hcount] at hround
    have hmapped : evalDist ((fun out => out.map (fun z => z.2.2)) <$>
        honestRoundsSchemeExp p hp χ (j + 1)) =
        evalDist ((fun out => out.map (fun z => z.2.2)) <$> evenRoundCanonical p χ) :=
      evalDist_map_eq_of_evalDist_eq hround (fun out => out.map (fun z => z.2.2))
    exact hmapped.trans (evalDist_evenCanonical_last p χ)

/-- The final round through the scheme has the same mismatch distribution as the corresponding
tape round. -/
theorem evalDist_honestRoundsSchemeExp_last_eq_tape
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (j : ℕ) :
    𝒟[(fun out => out.map (fun z => z.2.2)) <$>
      honestRoundsSchemeExp p hp χ (j + 1)] =
      𝒟[(fun t => some (tapeRoundMismatch p t.1 t.2 j)) <$>
        sampleHonestTape p χ (j + 1)] := by
  have hmapped := evalDist_map_eq_of_evalDist_eq
    (evalDist_tapeRoundMismatch_eq_first p χ (j + 1) j (by omega)) Option.some
  exact (evalDist_honestRounds_last_eq_first p hp χ j).trans (by
    simpa [Functor.map_map, Function.comp_def] using hmapped.symm)

/-- The final round has the same mismatch distribution as the first exchange. -/
theorem evalDist_honestRoundsSchemeExp_last_eq_first
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (j : ℕ) :
    𝒟[(fun out => out.map (fun z => z.2.2)) <$>
      honestRoundsSchemeExp p hp χ (j + 1)] =
      𝒟[Option.some <$> firstExchangeFailureExp p χ] := by
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
              | .aSend base pub =>
                  let a := coins.1
                  let nextPub := a.secret * base + a.error
                  let value := a.secret * pub + a.extra
                  some (extract p value, .fromA nextPub (makeHint p value),
                    .aRecv base a.secret)
              | _ => none
            sendB := fun st => pure <| match st with
              | .bSend base pub =>
                  let b := coins.2
                  let nextPub := base * b.secret + b.error
                  let value := pub * b.secret + b.extra
                  some (extract p value, .fromB nextPub (makeHint p value),
                    .bRecv base b.secret)
              | _ => none }
        let (out, s') ← liftM ((CKAScheme.ckaCorrectnessImpl fixed q).run s)
        set (s', if max s.tA s.tB < max s'.tA s'.tB then rest else coins :: rest)
        return out

private def TapeProgress
    (p : Params)
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (z : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Range q ×
      (CKAScheme.GameState (State p) (Key p) (Message p) ×
        List (SendACoins p × SendBCoins p))) : Prop :=
  honestPhase p z.2.1 ∧ s.tA ≤ z.2.1.tA ∧ s.tB ≤ z.2.1.tB ∧
    min z.2.1.tA z.2.1.tB = min s.tA s.tB +
      (if (q = CKAScheme.ckaCorrectnessSpec.ORecvA ∧
            CKAScheme.validStep s.lastAction .recvA = true) ∨
          (q = CKAScheme.ckaCorrectnessSpec.ORecvB ∧
            CKAScheme.validStep s.lastAction .recvB = true) then 1 else 0) ∧
    max z.2.1.tA z.2.1.tB = max s.tA s.tB +
      (if (q = CKAScheme.ckaCorrectnessSpec.OSendA ∧
            CKAScheme.validStep s.lastAction .sendA = true) ∨
          (q = CKAScheme.ckaCorrectnessSpec.OSendB ∧
            CKAScheme.validStep s.lastAction .sendB = true) then 1 else 0) ∧
    z.2.2 = (if max s.tA s.tB < max z.2.1.tA z.2.1.tB
      then tape.drop 1 else tape) ∧
    (min z.2.1.tA z.2.1.tB = min s.tA s.tB → z.2.1.correct = s.correct)

private theorem correctnessImpl_sendA_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendA).run s =
      (CKAScheme.oracleSendA cka ()).run s := by
  rfl

private theorem correctnessImpl_unif_run
    {p : Params} (n : ℕ)
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka (CKAScheme.ckaCorrectnessSpec.OUnif n)).run s =
      (CKAScheme.oracleUnif (State p) (Key p) (Message p) n).run s := by
  rfl

private theorem correctnessImpl_recvA_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvA).run s =
      (CKAScheme.oracleRecvA cka ()).run s := by
  rfl

private theorem correctnessImpl_sendB_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendB).run s =
      (CKAScheme.oracleSendB cka ()).run s := by
  rfl

private theorem correctnessImpl_recvB_run
    {p : Params}
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvB).run s =
      (CKAScheme.oracleRecvB cka ()).run s := by
  rfl

private theorem mem_support_StateT_liftM_run_iff
    {A S : Type} (mx : ProbComp A) (s : S) (z : A × S) :
    z ∈ support ((liftM mx : StateT S ProbComp A).run s) ↔
      z.1 ∈ support mx ∧ z.2 = s := by
  rw [StateT.run_monadLift, monadLift_self]
  rw [mem_support_bind_iff]
  constructor
  · rintro ⟨x, hx, hz⟩
    have hz' := eq_of_mem_support_pure hz
    subst z
    exact ⟨hx, rfl⟩
  · rintro ⟨hz, hs⟩
    refine ⟨z.1, hz, ?_⟩
    rw [mem_support_pure_iff]
    exact Prod.ext rfl hs

private theorem eq_of_mem_image_support_StateT_liftM_pure
    {A S B : Type} (x : A) (s : S) (f : A × S → B) {z : B}
    (hz : z ∈ f '' support ((liftM (pure x : ProbComp A) :
      StateT S ProbComp A).run s)) :
    z = f (x, s) := by
  rcases hz with ⟨out, hout, rfl⟩
  have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
  exact congrArg f (Prod.ext (eq_of_mem_support_pure hout'.1) hout'.2)

private theorem tapeCorrectnessImpl_sendA_invalid
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hguard : CKAScheme.validStep s.lastAction .sendA = false) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendA).run (s, tape)),
      z = (none, (s, tape)) := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases tape with _ | ⟨coins, rest⟩
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendA_run,
      CKAScheme.oracleSendA, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    rcases hz with ⟨out, hout, rfl⟩
    have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
    rcases out with ⟨first, outer⟩
    rcases hout' with ⟨hfirst, houter⟩
    simp only at hfirst houter
    subst outer
    have hfirst' := eq_of_mem_support_pure hfirst
    subst first
    simp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendA_run,
      CKAScheme.oracleSendA, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    rcases hz with ⟨out, hout, rfl⟩
    have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
    rcases out with ⟨first, outer⟩
    rcases hout' with ⟨hfirst, houter⟩
    simp only at hfirst houter
    subst outer
    have hfirst' := eq_of_mem_support_pure hfirst
    subst first
    simp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]

private theorem tapeCorrectnessImpl_sendA_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendA).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.OSendA s tape z := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases last with _ | action
  · rcases stA <;> rcases stB <;> simp [honestPhase] at hs
    rcases tape with _ | ⟨coins, rest⟩
    · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
        correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
        liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
        pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte,
        Option.map_some, StateT.run_monadLift, monadLift_self, StateT.run_map,
        StateT.run_set, map_pure, Functor.map_map, support_map] at hz
      rcases hz with ⟨out, hout, rfl⟩
      have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
      rcases out with ⟨first, outer⟩
      change Option (Message p × Key p) ×
        CKAScheme.GameState (State p) (Key p) (Message p) at first
      rcases hout' with ⟨hfirst, houter⟩
      simp only at hfirst houter
      subst outer
      dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA] at hfirst
      rw [support_map] at hfirst
      rcases hfirst with ⟨a, ha, rfl⟩
      simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
    · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
        correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
        liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
        pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
        StateT.run_set, map_pure, support_map] at hz
      rcases hz with ⟨out, hout, rfl⟩
      have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
      rcases out with ⟨first, outer⟩
      change Option (Message p × Key p) ×
        CKAScheme.GameState (State p) (Key p) (Message p) at first
      rcases hout' with ⟨hfirst, houter⟩
      simp only at hfirst houter
      subst outer
      have hfirst' := eq_of_mem_support_pure hfirst
      subst first
      simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
  · cases action
    case recvA =>
      rcases stA <;> rcases stB <;> simp [honestPhase] at hs
      rcases tape with _ | ⟨coins, rest⟩
      · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
          correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
          liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
          pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte,
          Option.map_some, StateT.run_monadLift, monadLift_self, StateT.run_map,
          StateT.run_set, map_pure, Functor.map_map, support_map] at hz
        rcases hz with ⟨out, hout, rfl⟩
        have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
        rcases out with ⟨first, outer⟩
        change Option (Message p × Key p) ×
          CKAScheme.GameState (State p) (Key p) (Message p) at first
        rcases hout' with ⟨hfirst, houter⟩
        simp only at hfirst houter
        subst outer
        dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA] at hfirst
        rw [support_map] at hfirst
        rcases hfirst with ⟨a, ha, rfl⟩
        simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
        omega
      · simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
          correctnessImpl_sendA_run, CKAScheme.oracleSendA, CKAScheme.validStep,
          liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
          pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
          StateT.run_set, map_pure, support_map] at hz
        rcases hz with ⟨out, hout, rfl⟩
        have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
        rcases out with ⟨first, outer⟩
        change Option (Message p × Key p) ×
          CKAScheme.GameState (State p) (Key p) (Message p) at first
        rcases hout' with ⟨hfirst, houter⟩
        simp only at hfirst houter
        subst outer
        have hfirst' := eq_of_mem_support_pure hfirst
        subst first
        simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
        omega
    case sendA =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .sendA) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case sendB =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .sendB) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case recvB =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .recvB) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case challA =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .challA) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs
    case challB =>
      have hz' := tapeCorrectnessImpl_sendA_invalid p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct
          (some .challB) tA tB) tape rfl z hz
      subst z
      simpa [TapeProgress, CKAScheme.validStep] using hs

private theorem tapeCorrectnessImpl_recvA_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.ORecvA).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.ORecvA s tape z := by
  intro z hz
  change Unit × (CKAScheme.GameState (State p) (Key p) (Message p) ×
    List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  cases hguard : CKAScheme.validStep last .recvA
  case false =>
    rcases tape with _ | ⟨coins, rest⟩
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvA_run,
        CKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvA_run,
        CKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case sendB =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase, exists_and_left, exists_and_right] at hs
        rcases hs with ⟨ht, hmod, ⟨pub, hint, key, hrho, hkey⟩,
          hrhoA, hkeyA⟩
        rcases pub with ⟨pub, hintValue, hrho⟩
        subst rhoB
        subst rhoA
        subst keyA
        rcases tape with _ | ⟨coins, rest⟩
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvA_run,
            CKAScheme.oracleRecvA, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvA, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvA_run,
            CKAScheme.oracleRecvA, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvA, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
      case challB => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

private theorem tapeCorrectnessImpl_sendB_invalid
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hguard : CKAScheme.validStep s.lastAction .sendB = false) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendB).run (s, tape)),
      z = (none, (s, tape)) := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases tape with _ | ⟨coins, rest⟩
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendB_run,
      CKAScheme.oracleSendB, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
    simpa [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendB] using hz'
  · simp only [tapeCorrectnessImpl, correctnessImpl_sendB_run,
      CKAScheme.oracleSendB, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
      support_map] at hz
    have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
    simpa [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendB] using hz'

private theorem tapeCorrectnessImpl_sendB_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.OSendB).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.OSendB s tape z := by
  intro z hz
  change Option (Message p × Key p) ×
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  cases hguard : CKAScheme.validStep last .sendB
  case false =>
    have hz' := tapeCorrectnessImpl_sendB_invalid p hp χ
      (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
      tape hguard z hz
    subst z
    simpa [TapeProgress, hguard] using hs
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case recvB =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase] at hs
        rcases tape with _ | ⟨coins, rest⟩
        · simp only [tapeCorrectnessImpl, scheme, sendBrleak, bind_pure_comp,
            correctnessImpl_sendB_run, CKAScheme.oracleSendB, CKAScheme.validStep,
            reduceCtorEq, imp_self, implies_true, liftM_map, bind_map_left,
            eraseCoins, StateT.run_bind, StateT.run_get, pure_bind, liftM_pure,
            lt_sup_iff, sup_lt_iff, ↓reduceIte, Option.map_some,
            StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_set,
            map_pure, Functor.map_map, support_map] at hz
          rcases hz with ⟨out, hout, rfl⟩
          have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
          rcases out with ⟨first, outer⟩
          change Option (Message p × Key p) ×
            CKAScheme.GameState (State p) (Key p) (Message p) at first
          rcases hout' with ⟨hfirst, houter⟩
          simp only at hfirst houter
          subst outer
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.OSendB] at hfirst
          rw [support_map] at hfirst
          rcases hfirst with ⟨b, hb, rfl⟩
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
        · simp only [tapeCorrectnessImpl, scheme, sendBrleak, bind_pure_comp,
            correctnessImpl_sendB_run, CKAScheme.oracleSendB, CKAScheme.validStep,
            reduceCtorEq, imp_self, implies_true, liftM_map, bind_map_left,
            eraseCoins, StateT.run_bind, StateT.run_get, pure_bind, liftM_pure,
            lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map, StateT.run_set,
            map_pure, support_map] at hz
          rcases hz with ⟨out, hout, rfl⟩
          have hout' := (mem_support_StateT_liftM_run_iff _ _ _).mp hout
          rcases out with ⟨first, outer⟩
          change Option (Message p × Key p) ×
            CKAScheme.GameState (State p) (Key p) (Message p) at first
          rcases hout' with ⟨hfirst, houter⟩
          simp only at hfirst houter
          subst outer
          have hfirst' := eq_of_mem_support_pure hfirst
          subst first
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
      all_goals simp [CKAScheme.validStep] at hguard

private theorem tapeCorrectnessImpl_recvB_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      CKAScheme.ckaCorrectnessSpec.ORecvB).run (s, tape)),
      TapeProgress p CKAScheme.ckaCorrectnessSpec.ORecvB s tape z := by
  intro z hz
  change Unit × (CKAScheme.GameState (State p) (Key p) (Message p) ×
    List (SendACoins p × SendBCoins p)) at z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  cases hguard : CKAScheme.validStep last .recvB
  case false =>
    rcases tape with _ | ⟨coins, rest⟩
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvB_run,
        CKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
    · simp only [tapeCorrectnessImpl, correctnessImpl_recvB_run,
        CKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind,
        bind_pure_comp, lt_sup_iff, sup_lt_iff, hguard, Bool.false_eq_true,
        ↓reduceIte, StateT.run_pure, StateT.run_map, StateT.run_set, map_pure,
        support_map] at hz
      have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
      subst z
      simpa [TapeProgress, hguard] using hs
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case sendA =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase, exists_and_left, exists_and_right] at hs
        rcases hs with ⟨ht, hmod, ⟨pub, hint, key, hrho, hkey⟩,
          hrhoB, hkeyB⟩
        rcases pub with ⟨pub, hintValue, hrho⟩
        subst rhoA
        subst rhoB
        subst keyB
        rcases tape with _ | ⟨coins, rest⟩
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvB_run,
            CKAScheme.oracleRecvB, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvB, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
        · simp only [tapeCorrectnessImpl, scheme, correctnessImpl_recvB_run,
            CKAScheme.oracleRecvB, CKAScheme.validStep, reduceCtorEq, imp_self,
            implies_true, recvB, StateT.run_bind, StateT.run_get, pure_bind,
            bind_pure_comp, lt_sup_iff, sup_lt_iff, ↓reduceIte,
            Option.some_beq_some, StateT.run_set, StateT.run_map, map_pure,
            support_map] at hz
          have hz' := eq_of_mem_image_support_StateT_liftM_pure _ _ _ hz
          subst z
          simp_all [TapeProgress, honestPhase, CKAScheme.validStep]
          omega
      case challA => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

/-- Each query preserves `honestPhase` and updates the counters according to its send or receive
result. -/
theorem tapeCorrectnessImpl_progress
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hs : honestPhase p s) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ q).run (s, tape)),
      honestPhase p z.2.1 ∧ s.tA ≤ z.2.1.tA ∧ s.tB ≤ z.2.1.tB ∧
      min z.2.1.tA z.2.1.tB = min s.tA s.tB +
        (if (q = CKAScheme.ckaCorrectnessSpec.ORecvA ∧
              CKAScheme.validStep s.lastAction .recvA = true) ∨
            (q = CKAScheme.ckaCorrectnessSpec.ORecvB ∧
              CKAScheme.validStep s.lastAction .recvB = true) then 1 else 0) ∧
      max z.2.1.tA z.2.1.tB = max s.tA s.tB +
        (if (q = CKAScheme.ckaCorrectnessSpec.OSendA ∧
              CKAScheme.validStep s.lastAction .sendA = true) ∨
            (q = CKAScheme.ckaCorrectnessSpec.OSendB ∧
              CKAScheme.validStep s.lastAction .sendB = true) then 1 else 0) ∧
      z.2.2 = (if max s.tA s.tB < max z.2.1.tA z.2.1.tB
        then tape.drop 1 else tape) ∧
      (min z.2.1.tA z.2.1.tB = min s.tA s.tB → z.2.1.correct = s.correct) := by
  intro z hz
  change TapeProgress p q s tape z
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  match q with
  | CKAScheme.ckaCorrectnessSpec.OUnif n =>
      rcases tape with _ | ⟨coins, rest⟩
      · simp only [tapeCorrectnessImpl, bind_pure_comp, lt_sup_iff, sup_lt_iff,
          StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_map, StateT.run_set, map_pure,
          Functor.map_map, support_map, Set.mem_image, Prod.exists] at hz
        rcases hz with ⟨a, b, hab, rfl⟩
        have hb : b = CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB := by
          rw [correctnessImpl_unif_run] at hab
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.OUnif] at a hab
          simp only [CKAScheme.oracleUnif, PFunctor.Handler.liftTarget_apply,
            PFunctor.selfMonomial_B, QueryImpl.ofLift_apply, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, support_map, support_liftM,
            OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
            Set.image_univ] at hab
          rcases hab with ⟨_, h⟩
          exact (congrArg Prod.snd h).symm
        subst b
        simpa [TapeProgress] using hs
      · simp only [tapeCorrectnessImpl, bind_pure_comp, lt_sup_iff, sup_lt_iff,
          StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_map, StateT.run_set, map_pure,
          Functor.map_map, support_map, Set.mem_image, Prod.exists] at hz
        rcases hz with ⟨a, b, hab, rfl⟩
        have hb : b = CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB := by
          rw [correctnessImpl_unif_run] at hab
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.OUnif] at a hab
          simp only [CKAScheme.oracleUnif, PFunctor.Handler.liftTarget_apply,
            PFunctor.selfMonomial_B, QueryImpl.ofLift_apply, StateT.run_monadLift,
            monadLift_self, bind_pure_comp, support_map, support_liftM,
            OracleQuery.input_query, OracleQuery.cont_query, Set.range_id,
            Set.image_univ] at hab
          rcases hab with ⟨_, h⟩
          exact (congrArg Prod.snd h).symm
        subst b
        simpa [TapeProgress] using hs
  | CKAScheme.ckaCorrectnessSpec.OSendA =>
      exact tapeCorrectnessImpl_sendA_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz
  | CKAScheme.ckaCorrectnessSpec.ORecvA =>
      exact tapeCorrectnessImpl_recvA_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz
  | CKAScheme.ckaCorrectnessSpec.OSendB =>
      exact tapeCorrectnessImpl_sendB_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz
  | CKAScheme.ckaCorrectnessSpec.ORecvB =>
      exact tapeCorrectnessImpl_recvB_progress p hp χ
        (CKAScheme.GameState.mk stA stB rhoA rhoB keyA keyB correct last tA tB)
        tape hs z hz

private theorem correctnessImpl_preserves_honestPhase
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) :
    QueryImpl.PreservesInv
      (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)) (honestPhase p) := by
  intro q s hs z hz
  have hz' : (z.1, (z.2, ([] : List (SendACoins p × SendBCoins p)))) ∈
      support ((tapeCorrectnessImpl p hp χ q).run
        (s, ([] : List (SendACoins p × SendBCoins p)))) := by
    simpa [tapeCorrectnessImpl] using hz
  exact (tapeCorrectnessImpl_progress p hp χ q s [] hs _ hz').1

private theorem tapeCorrectnessImpl_unif_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p)) (n : ℕ)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) :
    (tapeCorrectnessImpl p hp χ
      (CKAScheme.ckaCorrectnessSpec.OUnif n)).run (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          (CKAScheme.ckaCorrectnessSpec.OUnif n)).run s := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_unif_run,
      CKAScheme.oracleUnif] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OUnif] <;>
    simp

private theorem tapeCorrectnessImpl_sendA_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendA = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (s, tape) = pure (none, (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_sendA_run,
      CKAScheme.oracleSendA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendA] <;>
    simp

private theorem tapeCorrectnessImpl_sendB_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendB = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (s, tape) = pure (none, (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_sendB_run,
      CKAScheme.oracleSendB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.OSendB] <;>
    simp

private theorem tapeCorrectnessImpl_recvA_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvA = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (s, tape) = pure ((), (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_recvA_run,
      CKAScheme.oracleRecvA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.ORecvA] <;>
    simp

private theorem tapeCorrectnessImpl_recvB_invalid_run
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvB = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (s, tape) = pure ((), (s, tape)) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, correctnessImpl_recvB_run,
      CKAScheme.oracleRecvB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec,
      CKAScheme.ckaCorrectnessSpec.ORecvB] <;>
    simp

private theorem tapeCorrectnessImpl_recvA_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.ORecvA).run s := by
  cases hguard : CKAScheme.validStep s.lastAction .recvA
  case false =>
    rw [tapeCorrectnessImpl_recvA_invalid_run p hp χ s tape hguard]
    simp [correctnessImpl_recvA_run, CKAScheme.oracleRecvA, hguard]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA]
    simp
  case true =>
    rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case sendB =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase, exists_and_left, exists_and_right] at hs
        rcases hs with ⟨ht, hmod, ⟨pub, hint, key, hrho, hkey⟩,
          hrhoA, hkeyA⟩
        rcases pub with ⟨pub, hintValue, hrho⟩
        subst rhoB
        subst rhoA
        subst keyA
        cases tape <;>
          simp [tapeCorrectnessImpl, correctnessImpl_recvA_run,
            CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recvA] <;>
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.ORecvA] <;>
          simp
        all_goals omega
      case challB => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

private theorem tapeCorrectnessImpl_recvB_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.ORecvB).run s := by
  cases hguard : CKAScheme.validStep s.lastAction .recvB
  case false =>
    rw [tapeCorrectnessImpl_recvB_invalid_run p hp χ s tape hguard]
    simp [correctnessImpl_recvB_run, CKAScheme.oracleRecvB, hguard]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB]
    simp
  case true =>
    rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hguard
    · cases action
      case sendA =>
        rcases stA <;> rcases stB <;>
          simp only [honestPhase, exists_and_left, exists_and_right] at hs
        rcases hs with ⟨ht, hmod, ⟨pub, hint, key, hrho, hkey⟩,
          hrhoB, hkeyB⟩
        rcases pub with ⟨pub, hintValue, hrho⟩
        subst rhoA
        subst rhoB
        subst keyB
        cases tape <;>
          simp [tapeCorrectnessImpl, correctnessImpl_recvB_run,
            CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recvB] <;>
          dsimp [CKAScheme.ckaCorrectnessSpec,
            CKAScheme.ckaCorrectnessSpec.ORecvB] <;>
          simp
        all_goals omega
      case challA => simp [honestPhase] at hs
      all_goals simp [CKAScheme.validStep] at hguard

private theorem evalDist_sample_tape_query_bind_passthrough
    {ι : Type} {spec : OracleSpec ι} {σ θ α : Type}
    (sample : ProbComp θ)
    (impl : QueryImpl spec (StateT (σ × θ) ProbComp))
    (base : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (himpl : ∀ param ∈ support sample, (impl t).run (s, param) =
      (fun z => (z.1, (z.2, param))) <$> (base t).run s)
    (hpres : ∀ z, z ∈ support ((base t).run s) → Inv z.2)
    (hih : ∀ (u : spec.Range t) (s' : σ), Inv s' →
      𝒟[do
        let param ← sample
        let (out, s'', _) ← (simulateQ impl (k u)).run (s', param)
        return (out, s'')] =
      𝒟[(simulateQ base (k u)).run s']) :
    𝒟[do
      let param ← sample
      let (out, s', _) ←
        (simulateQ impl (OracleSpec.query t >>= k)).run (s, param)
      return (out, s')] =
      𝒟[(simulateQ base (OracleSpec.query t >>= k)).run s] := by
  apply evalDist_ext
  intro y
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
    OracleQuery.input_query, StateT.run_bind, bind_assoc]
  have halign : Pr[= y | do
        let param ← sample
        let step ← (impl t).run (s, param)
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1)] =
      Pr[= y | do
        let param ← sample
        let step ← (base t).run s
        let out ← (simulateQ impl (k step.1)).run (step.2, param)
        pure (out.1, out.2.1)] := by
    refine probOutput_bind_congr ?_
    intro param hparam
    rw [himpl param hparam, bind_map_left]
  rw [halign]
  rw [probOutput_bind_bind_swap (mx := sample) (my := (base t).run s)
    (f := fun param step => do
      let out ← (simulateQ impl (k step.1)).run (step.2, param)
      pure (out.1, out.2.1)) (z := y)]
  refine probOutput_bind_congr ?_
  intro step hstep
  exact evalDist_ext_iff.mp (hih step.1 step.2 (hpres step hstep)) y

private theorem evalDist_bind_of_evalDist_eq
    {A B : Type} {mx my : ProbComp A} (h : 𝒟[mx] = 𝒟[my])
    (f : A → ProbComp B) : 𝒟[mx >>= f] = 𝒟[my >>= f] := by
  rw [evalDist_bind, evalDist_bind, h]

private theorem evalDist_head_tail_query_bind_consume
    {ι : Type} {spec : OracleSpec ι} {σ η θ α : Type}
    (head : ProbComp η) (tail : ProbComp θ) (combine : η → θ → θ)
    (impl : QueryImpl spec (StateT (σ × θ) ProbComp))
    (base : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (hstep : ∀ rest, 𝒟[do
        let h ← head
        (impl t).run (s, combine h rest)] =
      𝒟[(fun z => (z.1, (z.2, rest))) <$> (base t).run s])
    (hpres : ∀ z, z ∈ support ((base t).run s) → Inv z.2)
    (hih : ∀ (u : spec.Range t) (s' : σ), Inv s' →
      𝒟[do
        let rest ← tail
        let (out, s'', _) ← (simulateQ impl (k u)).run (s', rest)
        return (out, s'')] =
      𝒟[(simulateQ base (k u)).run s']) :
    𝒟[do
      let h ← head
      let rest ← tail
      let (out, s', _) ←
        (simulateQ impl (OracleSpec.query t >>= k)).run (s, combine h rest)
      return (out, s')] =
      𝒟[(simulateQ base (OracleSpec.query t >>= k)).run s] := by
  apply evalDist_ext
  intro y
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
    OracleQuery.input_query, StateT.run_bind, bind_assoc]
  rw [probOutput_bind_bind_swap (mx := head) (my := tail)
    (f := fun h rest => do
      let step ← (impl t).run (s, combine h rest)
      let out ← (simulateQ impl (k step.1)).run step.2
      pure (out.1, out.2.1)) (z := y)]
  have halign : Pr[= y | do
        let rest ← tail
        let h ← head
        let step ← (impl t).run (s, combine h rest)
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1)] =
      Pr[= y | do
        let rest ← tail
        let step ← (fun z : spec.Range t × σ => (z.1, (z.2, rest))) <$> (base t).run s
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1)] := by
    refine probOutput_bind_congr' tail y fun rest => ?_
    simpa only [bind_assoc] using evalDist_ext_iff.mp
      (evalDist_bind_of_evalDist_eq (hstep rest)
      (fun step => do
        let out ← (simulateQ impl (k step.1)).run step.2
        pure (out.1, out.2.1))) y
  rw [halign]
  simp only [bind_map_left]
  rw [probOutput_bind_bind_swap (mx := tail) (my := (base t).run s)
    (f := fun rest step => do
      let out ← (simulateQ impl (k step.1)).run (step.2, rest)
      pure (out.1, out.2.1)) (z := y)]
  refine probOutput_bind_congr ?_
  intro step hstep'
  exact evalDist_ext_iff.mp (hih step.1 step.2 (hpres step hstep')) y

private theorem correctnessImpl_sendA_run_for_head (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendA).run s =
      (CKAScheme.oracleSendA cka ()).run s := by
  rfl

private theorem evalDist_tapeCorrectnessImpl_sendA_head
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (rest : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s)
    (hg : CKAScheme.validStep s.lastAction .sendA = true) :
    𝒟[do
      let a ← sampleSendACoins p χ
      let b ← sampleSendBCoins p χ
      (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
        (s, (a, b) :: rest)] =
    𝒟[do
      let z ← (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
        CKAScheme.ckaCorrectnessSpec.OSendA).run s
      pure (z.1, (z.2, rest))] := by
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases last with _ | (_ | _ | _ | _ | _ | _) <;>
    simp [CKAScheme.validStep] at hg
  all_goals
    rcases stA <;> rcases stB <;> simp [honestPhase] at hs
  all_goals
    simp only [tapeCorrectnessImpl, scheme, sendArleak, bind_pure_comp,
      correctnessImpl_sendA_run_for_head p, CKAScheme.oracleSendA,
      CKAScheme.validStep,
      liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
      StateT.run_set, map_pure, liftM_bind, Option.map_some, StateT.run_monadLift,
      monadLift_self, Functor.map_map]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
    simp only [pure_bind, bind_map_left]
    simp only [liftM_pure, map_pure]
    have hab : tA = tB := by omega
    subst tB
    simp only [lt_add_iff_pos_right, Order.lt_one_iff, and_self, lt_self_iff_false,
      or_false, ↓reduceIte, bind_pure_comp, liftM_map]
    simp only [← liftM_bind, ← liftM_map]
    simp only [map_eq_bind_pure_comp]
    apply evalDist_bind_congr'
    intro a
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (sampleSendBCoins p χ) (probFailure_eq_zero) _

private theorem correctnessImpl_sendB_run_for_head (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendB).run s =
      (CKAScheme.oracleSendB cka ()).run s := by
  rfl

private theorem evalDist_tapeCorrectnessImpl_sendB_head
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (rest : List (SendACoins p × SendBCoins p)) (hs : honestPhase p s)
    (hg : CKAScheme.validStep s.lastAction .sendB = true) :
    𝒟[do
      let a ← sampleSendACoins p χ
      let b ← sampleSendBCoins p χ
      (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
        (s, (a, b) :: rest)] =
    𝒟[do
      let z ← (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
        CKAScheme.ckaCorrectnessSpec.OSendB).run s
      pure (z.1, (z.2, rest))] := by
  rcases s with ⟨stA, stB, rhoA, rhoB, keyA, keyB, correct, last, tA, tB⟩
  rcases last with _ | (_ | _ | _ | _ | _ | _) <;>
    simp [CKAScheme.validStep] at hg
  all_goals
    rcases stA <;> rcases stB <;> simp [honestPhase] at hs
  all_goals
    simp only [tapeCorrectnessImpl, scheme, sendBrleak, bind_pure_comp,
      correctnessImpl_sendB_run_for_head p, CKAScheme.oracleSendB,
      CKAScheme.validStep,
      liftM_map, bind_map_left, eraseCoins, StateT.run_bind, StateT.run_get,
      pure_bind, liftM_pure, lt_sup_iff, sup_lt_iff, ↓reduceIte, StateT.run_map,
      StateT.run_set, map_pure, liftM_bind, Option.map_some, StateT.run_monadLift,
      monadLift_self, Functor.map_map]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB]
    simp only [pure_bind, bind_map_left]
    simp only [liftM_pure, map_pure]
    have hab : tA = tB := by omega
    subst tB
    simp only [lt_self_iff_false, and_self, lt_add_iff_pos_right, Order.lt_one_iff,
      or_true, ↓reduceIte, bind_pure_comp, liftM_map]
    simp only [← liftM_bind, ← liftM_map]
    simp only [map_eq_bind_pure_comp]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (sampleSendACoins p χ) (probFailure_eq_zero) _

private theorem tapeCorrectnessImpl_sendA_invalid_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendA = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.OSendA).run s := by
  rw [tapeCorrectnessImpl_sendA_invalid_run p hp χ s tape hg]
  simp [correctnessImpl_sendA_run, CKAScheme.oracleSendA, hg]
  dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
  simp

private theorem tapeCorrectnessImpl_sendB_invalid_run_eq_map
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendB = false) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (s, tape) =
      (fun z => (z.1, (z.2, tape))) <$>
        (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)
          CKAScheme.ckaCorrectnessSpec.OSendB).run s := by
  rw [tapeCorrectnessImpl_sendB_invalid_run p hp χ s tape hg]
  simp [correctnessImpl_sendB_run, CKAScheme.oracleSendB, hg]
  dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB]
  simp

/-- Sampling the send tape in advance preserves the joint distribution of the adversary result and
final game state. -/
theorem evalDist_tapeCorrectnessRun
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    {α : Type}
    (oa : OracleComp (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)) α)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (hs : honestPhase p s) (N : ℕ) :
    𝒟[do
      let tape ← OracleComp.drawList (do
        let a ← sampleSendACoins p χ
        let b ← sampleSendBCoins p χ
        return (a, b)) N
      let (out, s', _) ← (simulateQ (tapeCorrectnessImpl p hp χ) oa).run (s, tape)
      return (out, s')] =
      𝒟[(simulateQ (CKAScheme.ckaCorrectnessImpl (scheme p hp χ)) oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s N with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (OracleComp.drawList (do
          let a ← sampleSendACoins p χ
          let b ← sampleSendBCoins p χ
          return (a, b)) N)
        (OracleComp.probFailure_drawList _ _) _
  | query_bind t k ih =>
      match t with
      | CKAScheme.ckaCorrectnessSpec.OUnif n =>
          apply evalDist_sample_tape_query_bind_passthrough
            (Inv := honestPhase p)
          · intro tape _
            exact tapeCorrectnessImpl_unif_run_eq_map p hp χ n s tape
          · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
          · intro u s' hs'
            exact ih u s' hs' N
      | CKAScheme.ckaCorrectnessSpec.OSendA =>
          cases hg : CKAScheme.validStep s.lastAction .sendA
          case false =>
            apply evalDist_sample_tape_query_bind_passthrough
              (Inv := honestPhase p)
            · intro tape _
              exact tapeCorrectnessImpl_sendA_invalid_run_eq_map p hp χ s tape hg
            · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
            · intro u s' hs'
              exact ih u s' hs' N
          case true =>
            cases N with
            | zero =>
                apply evalDist_sample_tape_query_bind_passthrough
                  (Inv := honestPhase p)
                · intro tape htape
                  have hlen := length_of_mem_support_drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) 0 tape htape
                  cases tape with
                  | nil => simp [tapeCorrectnessImpl]
                  | cons _ _ => simp at hlen
                · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
                · intro u s' hs'
                  exact ih u s' hs' 0
            | succ N =>
                rw [OracleComp.drawList]
                simp only [bind_assoc, pure_bind]
                have hrun := evalDist_head_tail_query_bind_consume
                  (head := do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b))
                  (tail := OracleComp.drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) N)
                  (combine := List.cons) (impl := tapeCorrectnessImpl p hp χ)
                  (base := CKAScheme.ckaCorrectnessImpl (scheme p hp χ))
                  (Inv := honestPhase p) (s := s)
                  (t := CKAScheme.ckaCorrectnessSpec.OSendA) (k := k)
                  (hstep := fun rest => by
                    simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp,
                      Function.comp_def] using
                      evalDist_tapeCorrectnessImpl_sendA_head p hp χ s rest hs hg)
                  (hpres := correctnessImpl_preserves_honestPhase p hp χ _ s hs)
                  (hih := fun u s' hs' => ih u s' hs' N)
                simpa only [bind_assoc, pure_bind] using hrun
      | CKAScheme.ckaCorrectnessSpec.ORecvA =>
          apply evalDist_sample_tape_query_bind_passthrough
            (Inv := honestPhase p)
          · intro tape _
            exact tapeCorrectnessImpl_recvA_run_eq_map p hp χ s tape hs
          · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
          · intro u s' hs'
            exact ih u s' hs' N
      | CKAScheme.ckaCorrectnessSpec.OSendB =>
          cases hg : CKAScheme.validStep s.lastAction .sendB
          case false =>
            apply evalDist_sample_tape_query_bind_passthrough
              (Inv := honestPhase p)
            · intro tape _
              exact tapeCorrectnessImpl_sendB_invalid_run_eq_map p hp χ s tape hg
            · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
            · intro u s' hs'
              exact ih u s' hs' N
          case true =>
            cases N with
            | zero =>
                apply evalDist_sample_tape_query_bind_passthrough
                  (Inv := honestPhase p)
                · intro tape htape
                  have hlen := length_of_mem_support_drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) 0 tape htape
                  cases tape with
                  | nil => simp [tapeCorrectnessImpl]
                  | cons _ _ => simp at hlen
                · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
                · intro u s' hs'
                  exact ih u s' hs' 0
            | succ N =>
                rw [OracleComp.drawList]
                simp only [bind_assoc, pure_bind]
                have hrun := evalDist_head_tail_query_bind_consume
                  (head := do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b))
                  (tail := OracleComp.drawList (do
                    let a ← sampleSendACoins p χ
                    let b ← sampleSendBCoins p χ
                    return (a, b)) N)
                  (combine := List.cons) (impl := tapeCorrectnessImpl p hp χ)
                  (base := CKAScheme.ckaCorrectnessImpl (scheme p hp χ))
                  (Inv := honestPhase p) (s := s)
                  (t := CKAScheme.ckaCorrectnessSpec.OSendB) (k := k)
                  (hstep := fun rest => by
                    simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp,
                      Function.comp_def] using
                      evalDist_tapeCorrectnessImpl_sendB_head p hp χ s rest hs hg)
                  (hpres := correctnessImpl_preserves_honestPhase p hp χ _ s hs)
                  (hih := fun u s' hs' => ih u s' hs' N)
                simpa only [bind_assoc, pure_bind] using hrun
      | CKAScheme.ckaCorrectnessSpec.ORecvB =>
          apply evalDist_sample_tape_query_bind_passthrough
            (Inv := honestPhase p)
          · intro tape _
            exact tapeCorrectnessImpl_recvB_run_eq_map p hp χ s tape hs
          · exact correctnessImpl_preserves_honestPhase p hp χ _ s hs
          · intro u s' hs'
            exact ih u s' hs' N

namespace TapePrefix

private def coin (p : Params) (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    SendACoins p × SendBCoins p :=
  (tape[n]?).getD (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)

private def prefixOK (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) : Bool :=
  decide (∀ j : Fin n, tapeRoundMismatch p ik tape j.val = false)

private def complete (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    CKAScheme.GameState (State p) (Key p) (Message p) :=
  if n = 0 then CKAScheme.initGameState (initA ik) (initB ik)
  else
    let previous := coin p tape (n - 1)
    { stA := if n % 2 = 0 then
        .aSend ik.base (ik.base * previous.2.secret + previous.2.error)
      else .aRecv ik.base previous.1.secret
      stB := if n % 2 = 0 then .bRecv ik.base previous.2.secret
        else .bSend ik.base (previous.1.secret * ik.base + previous.1.error)
      rhoA := none, rhoB := none, keyA := none, keyB := none
      correct := prefixOK p ik tape n
      lastAction := if n % 2 = 0 then some .recvA else some .recvB
      tA := n, tB := n }

private def pending (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    CKAScheme.GameState (State p) (Key p) (Message p) :=
  let current := coin p tape n
  let previous := coin p tape (n - 1)
  if n % 2 = 0 then
    let secret := if n = 0 then ik.secret else previous.2.secret
    let error := if n = 0 then ik.error else previous.2.error
    let value := current.1.secret * (ik.base * secret + error) + current.1.extra
    { stA := .aRecv ik.base current.1.secret
      stB := .bRecv ik.base secret
      rhoA := some (.fromA (current.1.secret * ik.base + current.1.error) (makeHint p value))
      rhoB := none, keyA := some (extract p value), keyB := none
      correct := prefixOK p ik tape n, lastAction := some .sendA
      tA := n + 1, tB := n }
  else
    let value := (previous.1.secret * ik.base + previous.1.error) *
      current.2.secret + current.2.extra
    { stA := .aRecv ik.base previous.1.secret
      stB := .bRecv ik.base current.2.secret
      rhoA := none
      rhoB := some (.fromB (ik.base * current.2.secret + current.2.error) (makeHint p value))
      keyA := none, keyB := some (extract p value)
      correct := prefixOK p ik tape n, lastAction := some .sendB
      tA := n, tB := n + 1 }

private theorem complete_phase (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    honestPhase p (complete p ik tape n) := by
  by_cases hn : n = 0
  · simp [complete, hn, honestPhase_init]
  · by_cases he : n % 2 = 0
    · simp [complete, hn, he, honestPhase]
    · have ho : n % 2 = 1 := by omega
      simp [complete, hn, ho, honestPhase]

private theorem pending_phase (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    honestPhase p (pending p ik tape n) := by
  by_cases he : n % 2 = 0
  · simp [pending, he, honestPhase]
  · have ho : n % 2 = 1 := by omega
    simp [pending, ho, honestPhase]

private theorem complete_count (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    (complete p ik tape n).tA = n ∧ (complete p ik tape n).tB = n := by
  by_cases hn : n = 0 <;> simp [complete, hn, CKAScheme.initGameState]

private theorem pending_count (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    min (pending p ik tape n).tA (pending p ik tape n).tB = n ∧
    max (pending p ik tape n).tA (pending p ik tape n).tB = n + 1 := by
  by_cases he : n % 2 = 0 <;> simp [pending, he]

private theorem complete_correct (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    (complete p ik tape n).correct = prefixOK p ik tape n := by
  cases n <;> simp [complete, prefixOK, CKAScheme.initGameState]

private theorem pending_correct (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    (pending p ik tape n).correct = prefixOK p ik tape n := by
  by_cases he : n % 2 = 0 <;> simp [pending, he]

private theorem prefixOK_succ (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    prefixOK p ik tape (n + 1) =
      (prefixOK p ik tape n && !tapeRoundMismatch p ik tape n) := by
  simp [prefixOK, Fin.forall_fin_succ', Bool.decide_eq_false]

private theorem coin_get (p : Params) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) : tape[n]? = some (coin p tape n) := by
  simp [coin, List.getElem?_eq_getElem hn]

private def senderValue (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) : Shared p :=
  let current := coin p tape n
  let previous := coin p tape (n - 1)
  if n % 2 = 0 then
    let secret := if n = 0 then ik.secret else previous.2.secret
    let error := if n = 0 then ik.error else previous.2.error
    current.1.secret * (ik.base * secret + error) + current.1.extra
  else
    (previous.1.secret * ik.base + previous.1.error) * current.2.secret + current.2.extra

private def receiverValue (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) : Shared p :=
  let current := coin p tape n
  let previous := coin p tape (n - 1)
  if n % 2 = 0 then
    let secret := if n = 0 then ik.secret else previous.2.secret
    (current.1.secret * ik.base + current.1.error) * secret
  else
    previous.1.secret * (ik.base * current.2.secret + current.2.error)

private theorem mismatch_values (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) (hn : n < tape.length) :
    tapeRoundMismatch p ik tape n = decide
      (reconcile p (receiverValue p ik tape n) (makeHint p (senderValue p ik tape n)) ≠
        extract p (senderValue p ik tape n)) := by
  cases n with
  | zero => simp [tapeRoundMismatch, coin_get p tape 0 hn, senderValue, receiverValue]
  | succ n =>
    have hprev := coin_get p tape n (by omega)
    have hcur := coin_get p tape (n + 1) hn
    by_cases he : (n + 1) % 2 = 0 <;>
      simp [tapeRoundMismatch, hprev, hcur, senderValue, receiverValue, he]

private theorem recvA_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvA).run s =
      (CKAScheme.oracleRecvA cka ()).run s := rfl

private theorem recvB_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvB).run s =
      (CKAScheme.oracleRecvB cka ()).run s := rfl

private theorem keyAgreement (p : Params) (a b : Key p) :
    (a == b) = !decide (b ≠ a) := by
  by_cases h : a = b
  · subst b
    simp
  · have h' : b ≠ a := Ne.symm h
    simp [h, h']

private theorem pending_recvA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape rest : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (ho : n % 2 = 1) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (pending p ik tape n, rest) = pure ((), complete p ik tape (n + 1), rest) := by
  have he : ¬ n % 2 = 0 := by omega
  have hs : (n + 1) % 2 = 0 := by omega
  have hm := mismatch_values p ik tape n hn
  simp only [senderValue, receiverValue, if_neg he] at hm
  cases rest with
  | nil =>
    simp [tapeCorrectnessImpl, recvA_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recvA,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not]
  | cons c rest =>
    simp [tapeCorrectnessImpl, recvA_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recvA,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not, Nat.lt_irrefl, and_false,
      or_self, ite_false]

private theorem pending_recvB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape rest : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (he : n % 2 = 0) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (pending p ik tape n, rest) = pure ((), complete p ik tape (n + 1), rest) := by
  have hs : ¬ (n + 1) % 2 = 0 := by omega
  have hm := mismatch_values p ik tape n hn
  simp only [senderValue, receiverValue, if_pos he] at hm
  cases rest with
  | nil =>
    simp [tapeCorrectnessImpl, recvB_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recvB,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not]
  | cons c rest =>
    simp [tapeCorrectnessImpl, recvB_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recvB,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not, Nat.lt_irrefl, false_and,
      or_self, ite_false]

private theorem sendA_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendA).run s =
      (CKAScheme.oracleSendA cka ()).run s := rfl

private theorem sendB_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendB).run s =
      (CKAScheme.oracleSendB cka ()).run s := rfl

private theorem drop_coin (p : Params) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) :
    tape.drop n = coin p tape n :: tape.drop (n + 1) := by
  rw [List.drop_eq_getElem_cons hn]
  simp [coin, List.getElem?_eq_getElem hn]

private theorem complete_sendA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (he : n % 2 = 0) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (complete p ik tape n, tape.drop n) =
      pure (pending p ik tape n, tape.drop (n + 1)) := by
  rw [drop_coin p tape n hn]
  by_cases hz : n = 0
  · subst n
    simp [tapeCorrectnessImpl, sendA_run p, complete, pending, initA, initB,
      CKAScheme.initGameState, CKAScheme.oracleSendA, CKAScheme.validStep, prefixOK]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
    simp only [pure_bind, map_pure, Nat.lt_irrefl]
    simp
  · simp [tapeCorrectnessImpl, sendA_run p, complete, pending, he, hz,
      CKAScheme.oracleSendA, CKAScheme.validStep]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
    simp only [pure_bind, map_pure]
    simp

private theorem complete_sendB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (he : n % 2 = 1) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (complete p ik tape n, tape.drop n) =
      pure (pending p ik tape n, tape.drop (n + 1)) := by
  have hz : n ≠ 0 := by omega
  have he' : ¬ n % 2 = 0 := by omega
  rw [drop_coin p tape n hn]
  simp [tapeCorrectnessImpl, sendB_run p, complete, pending, he', hz,
    CKAScheme.oracleSendB, CKAScheme.validStep]
  dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB]
  simp only [pure_bind, map_pure]
  simp

private theorem invalid_sendA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendA = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, sendA_run p, CKAScheme.oracleSendA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA] <;>
    simp

private theorem invalid_sendB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendB = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, sendB_run p, CKAScheme.oracleSendB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB] <;>
    simp

private theorem invalid_recvA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvA = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, recvA_run p, CKAScheme.oracleRecvA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA] <;>
    simp

private theorem invalid_recvB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvB = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, recvB_run p, CKAScheme.oracleRecvB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB] <;>
    simp

private theorem unif_run (p : Params) (n : ℕ)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka (CKAScheme.ckaCorrectnessSpec.OUnif n)).run s =
      (CKAScheme.oracleUnif (State p) (Key p) (Message p) n).run s := rfl

private theorem unif_state (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      (CKAScheme.ckaCorrectnessSpec.OUnif n)).run (s, tape)), z.2 = (s, tape) := by
  intro z hz
  cases tape <;>
    simp only [tapeCorrectnessImpl, bind_pure_comp, lt_sup_iff, sup_lt_iff,
      StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift, monadLift_self,
      StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
      support_map, Set.mem_image, Prod.exists] at hz
  all_goals
    rcases hz with ⟨a, b, hab, rfl⟩
    have hb : b = s := by
      rw [unif_run p] at hab
      dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OUnif] at a hab
      simp only [CKAScheme.oracleUnif, PFunctor.Handler.liftTarget_apply,
        PFunctor.selfMonomial_B, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, bind_pure_comp, support_map, support_liftM,
        OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hab
      rcases hab with ⟨_, h⟩
      exact (congrArg Prod.snd h).symm
    subst b
    simp

private theorem state_eq_of_map {A S : Type} (mx : ProbComp (A × S)) (s : S)
    (heq : Prod.snd <$> mx = pure s) (z : A × S) (hz : z ∈ support mx) : z.2 = s := by
  have hmem : z.2 ∈ support (Prod.snd <$> mx) := by
    rw [support_map]
    exact ⟨z, hz, rfl⟩
  rw [heq] at hmem
  exact eq_of_mem_support_pure hmem

private inductive Good (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) :
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) → Prop
  | complete (n : ℕ) (hn : n ≤ tape.length) :
      Good p ik tape (complete p ik tape n, tape.drop n)
  | pending (n : ℕ) (hn : n < tape.length) :
      Good p ik tape (pending p ik tape n, tape.drop (n + 1))
  | exhausted (s rest) (hmin : min s.tA s.tB = tape.length)
      (hc : s.correct = prefixOK p ik tape tape.length) : Good p ik tape (s, rest)
  | overflow (s rest) (hn : tape.length < min s.tA s.tB) : Good p ik tape (s, rest)

private theorem good_correct (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (s rest)
    (hg : Good p ik tape (s, rest)) (hn : min s.tA s.tB ≤ tape.length) :
    s.correct = prefixOK p ik tape (min s.tA s.tB) := by
  cases hg with
  | complete n h =>
      rw [(complete_count p ik tape n).1, (complete_count p ik tape n).2, min_self]
      exact complete_correct p ik tape n
  | pending n h =>
      rw [(pending_count p ik tape n).1]
      exact pending_correct p ik tape n
  | exhausted s rest hm hc => simpa [hm] using hc
  | overflow s rest h => omega

private theorem boundary_step (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (s rest) (hs : honestPhase p s)
    (hm : min s.tA s.tB = tape.length)
    (hc : s.correct = prefixOK p ik tape tape.length)
    (z) (hz : z ∈ support ((tapeCorrectnessImpl p hp χ q).run (s, rest))) :
    Good p ik tape z.2 := by
  have h := tapeCorrectnessImpl_progress p hp χ q s rest hs z hz
  have hmono : min s.tA s.tB ≤ min z.2.1.tA z.2.1.tB := min_le_min h.2.1 h.2.2.1
  by_cases he : min z.2.1.tA z.2.1.tB = tape.length
  · exact Good.exhausted z.2.1 z.2.2 he ((h.2.2.2.2.2.2 (he.trans hm.symm)).trans hc)
  · apply Good.overflow z.2.1 z.2.2
    exact lt_of_le_of_ne (hm ▸ hmono) (Ne.symm he)

private theorem complete_step (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length)
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (z) (hz : z ∈ support ((tapeCorrectnessImpl p hp χ q).run
      (complete p ik tape n, tape.drop n))) : Good p ik tape z.2 := by
  have hself := Good.complete (p := p) (ik := ik) (tape := tape) n (by omega)
  match q with
  | CKAScheme.ckaCorrectnessSpec.OUnif k =>
      rw [unif_state p hp χ _ _ k z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendA =>
      by_cases he : n % 2 = 0
      · rw [state_eq_of_map _ _ (complete_sendA p hp χ ik tape n hn he) z hz]
        exact Good.pending n hn
      · have hg : CKAScheme.validStep (complete p ik tape n).lastAction .sendA = false := by
          have hne : n ≠ 0 := by omega
          simp [complete, hne, he, CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_sendA p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendB =>
      by_cases he : n % 2 = 1
      · rw [state_eq_of_map _ _ (complete_sendB p hp χ ik tape n hn he) z hz]
        exact Good.pending n hn
      · have hg : CKAScheme.validStep (complete p ik tape n).lastAction .sendB = false := by
          have he' : n % 2 = 0 := by omega
          by_cases hzero : n = 0 <;> simp [complete, hzero, he',
            CKAScheme.initGameState, CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_sendB p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvA =>
      have hg : CKAScheme.validStep (complete p ik tape n).lastAction .recvA = false := by
        by_cases hz : n = 0 <;> by_cases he : n % 2 = 0 <;>
          simp [complete, hz, he, CKAScheme.initGameState, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_recvA p hp χ _ _ hg) z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvB =>
      have hg : CKAScheme.validStep (complete p ik tape n).lastAction .recvB = false := by
        by_cases hz : n = 0 <;> by_cases he : n % 2 = 0 <;>
          simp [complete, hz, he, CKAScheme.initGameState, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_recvB p hp χ _ _ hg) z hz]
      exact hself

private theorem pending_step (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length)
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (z) (hz : z ∈ support ((tapeCorrectnessImpl p hp χ q).run
      (pending p ik tape n, tape.drop (n + 1)))) : Good p ik tape z.2 := by
  have hself := Good.pending (p := p) (ik := ik) (tape := tape) n hn
  match q with
  | CKAScheme.ckaCorrectnessSpec.OUnif k =>
      rw [unif_state p hp χ _ _ k z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvA =>
      by_cases he : n % 2 = 1
      · have heq := pending_recvA p hp χ ik tape (tape.drop (n + 1)) n hn he
        have hz' := hz
        rw [heq] at hz'
        have hz'' := eq_of_mem_support_pure hz'
        rw [hz'']
        exact Good.complete (n + 1) (by omega)
      · have hg : CKAScheme.validStep (pending p ik tape n).lastAction .recvA = false := by
          have he' : n % 2 = 0 := by omega
          simp [pending, he', CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_recvA p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvB =>
      by_cases he : n % 2 = 0
      · have heq := pending_recvB p hp χ ik tape (tape.drop (n + 1)) n hn he
        have hz' := hz
        rw [heq] at hz'
        have hz'' := eq_of_mem_support_pure hz'
        rw [hz'']
        exact Good.complete (n + 1) (by omega)
      · have hg : CKAScheme.validStep (pending p ik tape n).lastAction .recvB = false := by
          have he' : n % 2 = 1 := by omega
          simp [pending, he', CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_recvB p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendA =>
      have hg : CKAScheme.validStep (pending p ik tape n).lastAction .sendA = false := by
        by_cases he : n % 2 = 0 <;> simp [pending, he, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_sendA p hp χ _ _ hg) z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendB =>
      have hg : CKAScheme.validStep (pending p ik tape n).lastAction .sendB = false := by
        by_cases he : n % 2 = 0 <;> simp [pending, he, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_sendB p hp χ _ _ hg) z hz]
      exact hself

private theorem good_preserved (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p)) :
    QueryImpl.PreservesInv (tapeCorrectnessImpl p hp χ)
      (fun z => honestPhase p z.1 ∧ Good p ik tape z) := by
  intro q initial hin z hz
  rcases initial with ⟨s, rest⟩
  rcases hin with ⟨hs, hg⟩
  have hprogress := tapeCorrectnessImpl_progress p hp χ q s rest hs z hz
  refine ⟨hprogress.1, ?_⟩
  cases hg with
  | complete n hn =>
      by_cases hlt : n < tape.length
      · exact complete_step p hp χ ik tape n hlt q z hz
      · have heq : n = tape.length := by omega
        apply boundary_step p hp χ ik tape q _ _ hs _ _ z hz
        · rw [(complete_count p ik tape n).1, (complete_count p ik tape n).2,
            min_self, heq]
        · rw [complete_correct, heq]
  | pending n hn => exact pending_step p hp χ ik tape n hn q z hz
  | exhausted s rest hm hc =>
      exact boundary_step p hp χ ik tape q s rest hs hm hc z hz
  | overflow s rest hn =>
      exact Good.overflow z.2.1 z.2.2
        (lt_of_lt_of_le hn (min_le_min hprogress.2.1 hprogress.2.2.1))

private theorem prefix_correct (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    {α : Type}
    (oa : OracleComp (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)) α) :
    ∀ z ∈ support ((simulateQ (tapeCorrectnessImpl p hp χ) oa).run
      (CKAScheme.initGameState (initA ik) (initB ik), tape)),
      min z.2.1.tA z.2.1.tB ≤ tape.length →
      z.2.1.correct = decide (∀ j : Fin (min z.2.1.tA z.2.1.tB),
        tapeRoundMismatch p ik tape j.val = false) := by
  intro z hz hn
  have hinit : honestPhase p (CKAScheme.initGameState (initA ik) (initB ik)) ∧
      Good p ik tape (CKAScheme.initGameState (initA ik) (initB ik), tape) := by
    refine ⟨honestPhase_init p ik, ?_⟩
    simpa [complete] using
      Good.complete (p := p) (ik := ik) (tape := tape) 0 (by omega)
  have hfinal := simulateQ_run_preservesInv (tapeCorrectnessImpl p hp χ)
    (fun z => honestPhase p z.1 ∧ Good p ik tape z)
    (good_preserved p hp χ ik tape) oa _ hinit z hz
  exact good_correct p ik tape z.2.1 z.2.2 hfinal.2 hn

end TapePrefix

/-- Assume that the number of completed exchanges is at most the tape length.
The final correctness flag is true exactly when all completed exchanges agree. -/
theorem tapeCorrectnessRun_correct
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    {α : Type}
    (oa : OracleComp (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)) α) :
    ∀ z ∈ support
      ((simulateQ (tapeCorrectnessImpl p hp χ) oa).run
        (CKAScheme.initGameState (initA ik) (initB ik), tape)),
      min z.2.1.tA z.2.1.tB ≤ tape.length →
      z.2.1.correct =
        decide (∀ j : Fin (min z.2.1.tA z.2.1.tB),
          tapeRoundMismatch p ik tape j.val = false) := by
  exact TapePrefix.prefix_correct p hp χ ik tape oa

/-- Run the correctness experiment and return the adversary result together with the final game
state. -/
def correctnessStateExp
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p)) :
    ProbComp (Bool × CKAScheme.GameState (State p) (Key p) (Message p)) := do
  let cka := scheme p hp χ
  let ik ← cka.initKeyGen
  let stateA ← cka.initA ik
  let stateB ← cka.initB ik
  (simulateQ (CKAScheme.ckaCorrectnessImpl cka) adv).run
    (CKAScheme.initGameState stateA stateB)

/-- Every possible final state of the correctness experiment satisfies `honestPhase`. -/
theorem correctnessStateExp_honestPhase
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p)) :
    ∀ z ∈ support (correctnessStateExp p hp χ adv), honestPhase p z.2 := by
  intro z hz
  simp only [correctnessStateExp, scheme, pure_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨ik, hik, hz⟩ := hz
  exact simulateQ_run_preservesInv _ (honestPhase p)
    (correctnessImpl_preserves_honestPhase p hp χ) adv _
    (honestPhase_init p ik) z hz

/-- The public correctness experiment returns the correctness flag from the final game state. -/
theorem correctnessExp_eq_map_state
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p)) :
    CKAScheme.correctnessExp (scheme p hp χ) adv =
      (fun z => z.2.correct) <$> correctnessStateExp p hp χ adv := by
  simp [CKAScheme.correctnessExp, correctnessStateExp, map_eq_bind_pure_comp]

/-- Require at most `T` completed exchanges in every possible outcome of the correctness experiment.
The count is `min tA tB`, so a send without its matching receive does not count. -/
def HasExchangeBound
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p))
    (T : ℕ) : Prop :=
  ∀ z ∈ support (correctnessStateExp p hp χ adv), min z.2.tA z.2.tB ≤ T

/-- If every run completes at most `T` exchanges, its failure probability is at most `min 1 (T *
firstExchangeFailureProb)`. -/
theorem correctness_failure_le
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p))
    (T : ℕ) (hT : HasExchangeBound p hp χ adv T) :
    Pr[= false | CKAScheme.correctnessExp (scheme p hp χ) adv] ≤
      min 1 ((T : ℝ≥0∞) * firstExchangeFailureProb p χ) := by
  have hReplay := fun (ik : InitKey p) (N : ℕ) =>
    evalDist_tapeCorrectnessRun p hp χ adv
      (CKAScheme.initGameState (initA ik) (initB ik))
      (honestPhase_init p ik) N
  have hPrefix := fun ik tape =>
    tapeCorrectnessRun_correct p hp χ ik tape adv
  classical
  let runTape := fun t : InitKey p × List (SendACoins p × SendBCoins p) =>
    (simulateQ (tapeCorrectnessImpl p hp χ) adv).run
      (CKAScheme.initGameState (initA t.1) (initB t.1), t.2)
  let replay : ProbComp (Bool × CKAScheme.GameState (State p) (Key p) (Message p)) := do
    let t ← sampleHonestTape p χ (T + 1)
    let z ← runTape t
    return (z.1, z.2.1)
  have hdist : 𝒟[replay] = 𝒟[correctnessStateExp p hp χ adv] := by
    simp only [replay, sampleHonestTape, correctnessStateExp, scheme, bind_assoc,
      pure_bind]
    exact evalDist_bind_congr' (initKeyGen p χ) fun ik => hReplay ik (T + 1)
  have hcount : ∀ t ∈ support (sampleHonestTape p χ (T + 1)),
      ∀ z ∈ support (runTape t), min z.2.1.tA z.2.1.tB ≤ T := by
    intro t ht z hz
    apply hT (z.1, z.2.1)
    apply (mem_support_iff_of_evalDist_eq hdist _).1
    simp only [replay, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨t, ht, z, hz, rfl⟩
  have hevent : Pr[fun z => z.2.correct = false | replay] ≤
      (T : ℝ≥0∞) * firstExchangeFailureProb p χ := by
    calc
      Pr[fun z => z.2.correct = false | replay] =
          Pr[fun z => z.2.1.correct = false |
            sampleHonestTape p χ (T + 1) >>= runTape] := by
        simp [replay, probEvent_bind_eq_tsum, Function.comp_def]
      _ ≤ Pr[fun t => ∃ j : Fin T, tapeRoundMismatch p t.1 t.2 j.val = true |
          sampleHonestTape p χ (T + 1)] := by
        apply probEvent_bind_le_probEvent
        intro t ht hgood
        apply probEvent_eq_zero_iff.mpr
        intro z hz hfalse
        have hc := hcount t ht z hz
        have hl := sampleHonestTape_length p χ (T + 1) t ht
        have hpref := hPrefix t.1 t.2 z hz (by omega)
        have hall : ∀ j : Fin (min z.2.1.tA z.2.1.tB),
            tapeRoundMismatch p t.1 t.2 j.val = false := by
          intro j
          have hnot : tapeRoundMismatch p t.1 t.2 j.val ≠ true := by
            intro h
            exact hgood ⟨⟨j.val, by omega⟩, h⟩
          exact Bool.eq_false_iff.mpr hnot
        simp [hall, hfalse] at hpref
      _ ≤ (T : ℝ≥0∞) * firstExchangeFailureProb p χ :=
        probEvent_tapePrefixFailure_le p χ T
  apply le_min probOutput_le_one
  rw [correctnessExp_eq_map_state, probOutput_map]
  have heq : Pr[fun z => z.2.correct = false | replay] =
      Pr[fun z => z.2.correct = false | correctnessStateExp p hp χ adv] := by
    rw [probEvent_def, probEvent_def, hdist]
  exact heq ▸ hevent

/-- If every run completes at most `T` exchanges and the first exchange has zero failure
probability, correctness holds with probability one. -/
theorem correctness_of_zero
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p))
    (T : ℕ) (hT : HasExchangeBound p hp χ adv T)
    (hzero : firstExchangeFailureProb p χ = 0) :
    Pr[= true | CKAScheme.correctnessExp (scheme p hp χ) adv] = 1 := by
  have hz : Pr[= false | CKAScheme.correctnessExp (scheme p hp χ) adv] = 0 :=
    le_antisymm
      (by simpa [hzero] using correctness_failure_le p hp χ adv T hT)
      bot_le
  apply (probOutput_eq_one_iff_forall _ true).2
  refine ⟨probFailure_eq_zero, ?_⟩
  intro y hy
  cases y
  · exact False.elim ((probOutput_eq_zero_iff _ false).1 hz hy)
  · rfl

end lweCKA
