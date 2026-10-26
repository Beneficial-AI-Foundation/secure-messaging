/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Construction
import VCVio.EvalDist.IndepProduct
import VCVio.EvalDist.Option

/-!
# First and second honest-exchange laws

This module defines the first two honest-exchange experiments and proves their mismatch
distributions agree.
The sender performs the first send. The receiver uses the initial secret to recover its key from
the message.
Reconciliation recovers key bits using a public hint.
It returns `true` when the complete extracted and reconciled keys disagree, so a
failure in any matrix entry counts. The experiment keeps the joint distribution of both parties'
values.
It does not assume that those values are independent.

The definitions accept arbitrary scalar noise `χ`. Their intended cryptographic
use is with `Params.WellFormed`. The later `Correctness` modules relate these exchange laws to
sampled tapes and the adversarial correctness game. The final bound assumes at most `T` completed
exchanges in every possible run.

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
The endpoint theorem `correctness_failure_le` bounds the game failure probability by
`min 1 (T * firstExchangeFailureProb)`.
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
  -- ik.baseMatrix is the shared public n × n matrix, sampled uniformly over ZMod p.q.
  -- It is the matrix conventionally written A in the mathematical construction.
  let ik ← initKeyGen p χ
  -- Sample the first sender's fresh secret, error, and extra-error matrices.
  let r ← sampleSendACoins p χ
  -- The receiver's initial public matrix P₀ = baseMatrix · S₀ + E₀ (n × nbar).
  -- The sender initially holds P₀; the receiver retains S₀ = ik.secret.
  let receiverPublicMatrix := ik.baseMatrix * ik.secret + ik.error
  -- The sender's outgoing public matrix P₁ = S₁ · baseMatrix + E₁ (nbar × n).
  -- It accompanies the hint; S₁ = r.secret is the sender's fresh secret.
  let senderPublicMatrix := r.secret * ik.baseMatrix + r.error
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
    (p : Params) (receiverValue senderValue : SharedMatrix p) :
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
  let firstPublicMatrix := a.secret * ik.baseMatrix + a.error
  let secondPublicMatrix := ik.baseMatrix * b.secret + b.error
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
         ({ baseMatrix := ik.baseMatrix.transpose
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
      𝒟[(fun m : BaseMatrix p => m.transpose) <$> ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))] =
        𝒟[($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))] := by
    apply evalDist_map_bijective_uniform_cross
    exact ⟨Matrix.transpose_injective,
      fun y => ⟨y.transpose, Matrix.transpose_transpose y⟩⟩
  simp only [initKeyGen, sampleSendACoins, sampleSendBCoins, bind_assoc, pure_bind]
  let mid : ProbComp (InitKey p × SendACoins p) := do
    let baseMatrix ←
      (fun m : BaseMatrix p => m.transpose) <$> ($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))
    let initSecret ← (fun m => m.transpose) <$> sampleMatrix χ p.nbar p.n
    let initError ← (fun m => m.transpose) <$> sampleMatrix χ p.nbar p.n
    let sendSecret ← (fun m => m.transpose) <$> sampleMatrix χ p.n p.nbar
    let sendError ← (fun m => m.transpose) <$> sampleMatrix χ p.n p.nbar
    let sendExtra ← (fun m => m.transpose) <$> sampleMatrix χ p.nbar p.nbar
    pure (InitKey.mk baseMatrix initSecret initError,
      SendACoins.mk sendSecret sendError sendExtra)
  refine Eq.trans (b := 𝒟[mid]) ?_ ?_
  · simp only [mid, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    refine evalDist_bind_congr' (($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))) fun _ => ?_
    refine (hDrop (sampleMatrix χ p.n p.nbar) _).trans ?_
    refine (hDrop (sampleMatrix χ p.n p.nbar) _).trans ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
    refine evalDist_bind_congr' (sampleMatrix χ p.nbar p.n) fun _ => ?_
    exact hDrop (sampleMatrix χ p.nbar p.nbar) _
  · simp only [mid]
    refine (hHead _ _ hBase _).trans ?_
    refine evalDist_bind_congr' (($ᵗ (BaseMatrix p) : ProbComp (BaseMatrix p))) fun _ => ?_
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
    let receiverPublicMatrix := ik.baseMatrix * ik.secret + ik.error
    let senderPublicMatrix := a.secret * ik.baseMatrix + a.error
    let senderValue := a.secret * receiverPublicMatrix + a.extra
    let receiverValue := senderPublicMatrix * ik.secret
    decide (reconcile p receiverValue (makeHint p senderValue) ≠ extract p senderValue)
  have hSecond : secondExchangeFailureExp p χ = firstMismatch <$> (do
      let ik ← initKeyGen p χ
      let a ← sampleSendACoins p χ
      let b ← sampleSendBCoins p χ
      return (
        ({ baseMatrix := ik.baseMatrix.transpose
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
        (a.secret * (ik.baseMatrix * b.secret + b.error))
        ((a.secret * ik.baseMatrix + a.error) * b.secret + b.extra)).symm
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

end lweCKA
