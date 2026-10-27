/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.PairBound.Moments
import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.Experiment

/-!
# Integer coins and block moments for the Frodo Challenge pair bound

This module converts the Challenge sampler to centered integer coins, proves the matrix projection
laws needed downstream, and computes the shared and disjoint block moments.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA

open PairBoundInternal

namespace PairBoundInternal

private theorem evalDist_sampleIID_two_coords
    {α : Type} (mx : ProbComp α) (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    finiteLaw ((fun v : Fin n → α => (v i, v j)) <$> ProbComp.sampleIID n mx) =
      finiteLaw (Prod.mk <$> mx <*> mx) := by
  apply evalDist_ext
  intro z
  rw [prEvent_map]
  change Pr{let v ← Fin.mOfFn n fun _ => mx}[(v i, v j) = z] = Pr{let x ← Prod.mk <$> mx <*> mx}[x = z]
  have hevent :
      (fun v : Fin n → α => (v i, v j) = z) =
        fun v => ∀ k,
          (fun x => if k = i then x = z.1 else if k = j then x = z.2 else True)
            (v k) := by
    funext v
    apply propext
    constructor
    · intro hv k
      have hi : v i = z.1 := congrArg Prod.fst hv
      have hj : v j = z.2 := congrArg Prod.snd hv
      by_cases hki : k = i
      · simpa [hki] using hi
      · by_cases hkj : k = j
        · simpa [hki, hkj, Ne.symm hij] using hj
        · simp [hki, hkj]
    · intro hv
      apply Prod.ext
      · simpa using hv i
      · simpa [Ne.symm hij] using hv j
  rw [hevent]
  calc
    Pr{let v ← Fin.mOfFn n fun _ => mx}[∀ k,
          (fun x => if k = i then x = z.1 else if k = j then x = z.2 else True)
            (v k)] =
        ∏ k, Pr{let x ← mx}[if k = i then x = z.1 else if k = j then x = z.2 else True] :=
      prEvent_forall_coord_mOfFn n (fun _ => mx)
        (fun k x => if k = i then x = z.1 else if k = j then x = z.2 else True)
    _ = Pr{let x ← Prod.mk <$> mx <*> mx}[x = z] := by
      rw [probOutput_seq_map_prod_mk_eq_mul]
      classical
      rw [Finset.prod_eq_mul_of_mem i j (by simp) (by simp) hij]
      · simp [Ne.symm hij]
      · intro k _ hk
        simp [hk.1, hk.2]

private theorem evalDist_sampleIID_map_local
    {α β : Type} (n : ℕ) (mx : ProbComp α) (f : α → β) :
    finiteLaw
        ((fun xs : Fin n → α => fun i => f (xs i)) <$>
          ProbComp.sampleIID n mx) =
      finiteLaw (ProbComp.sampleIID n (f <$> mx)) := by
  induction n with
  | zero =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_pure]
      congr 2
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
      refine evalDist_bind_congr' mx fun a => ?_
      have htail := finiteLaw_map_congr ih
        (fun rest : Fin n → β => @Fin.cons n (fun _ => β) (f a) rest)
      convert htail using 1
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => mx) fun rest => ?_
        congr 2
        funext i
        exact Fin.cases (by simp) (fun j => by simp) i
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, Function.comp_def]

theorem evalDist_sampleIID_congr_local
    {α : Type} (n : ℕ) (mx my : ProbComp α) (h : finiteLaw mx = finiteLaw my) :
    finiteLaw (ProbComp.sampleIID n mx) = finiteLaw (ProbComp.sampleIID n my) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn]
      rw [evalDist_bind, evalDist_bind, h]
      apply congrArg
      funext a
      have ih' : finiteLaw (Fin.mOfFn n fun _ => mx) =
          finiteLaw (Fin.mOfFn n fun _ => my) := by
        simpa only [ProbComp.sampleIID] using ih
      rw [evalDist_bind, evalDist_bind, ih']

/-- A matrix whose entries are independent exact integer-valued Challenge `D₁` samples. -/
def challengeIntMatrix (rows cols : ℕ) :
    ProbComp (Matrix (Fin rows) (Fin cols) ℤ) :=
  ProbComp.sampleIID rows (ProbComp.sampleIID cols d1IntSampler)

private theorem evalDist_sampleMatrix_valMinAbs (rows cols : ℕ) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
            fun i j => (m i j).valMinAbs) <$>
          sampleMatrix d1Sampler rows cols) =
      finiteLaw (challengeIntMatrix rows cols) := by
  have hinner := (evalDist_sampleIID_map_local cols d1Sampler
    (fun x : Scalar challengeParams => x.valMinAbs)).trans
      (evalDist_sampleIID_congr_local cols
        ((fun x : Scalar challengeParams => x.valMinAbs) <$> d1Sampler)
        d1IntSampler evalDist_valMinAbs_d1Sampler)
  have houter := (evalDist_sampleIID_map_local rows
    (ProbComp.sampleIID cols d1Sampler)
    (fun row : Fin cols → Scalar challengeParams =>
      fun j => (row j).valMinAbs)).trans
        (evalDist_sampleIID_congr_local rows _ _ hinner)
  unfold sampleMatrix challengeIntMatrix
  have hfun :
      (fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
        fun i j => (m i j).valMinAbs) =
      (fun xs : Fin rows → Fin cols → Scalar challengeParams =>
        fun i j => (xs i j).valMinAbs) := by
    funext m i j
    rfl
  rw [hfun]
  exact houter

/-- The five centered integer noise matrices used by the first Challenge exchange. -/
structure ChallengeIntCoins where
  /-- The key-generation secret matrix. -/
  s0 : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ
  /-- The key-generation error matrix. -/
  e0 : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ
  /-- The sender's ephemeral secret matrix. -/
  s1 : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ
  /-- The sender's ephemeral error matrix. -/
  e1 : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ
  /-- The sender's additional output-error matrix. -/
  extra : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ

private def challengeCenteredCoinsExp : ProbComp ChallengeIntCoins := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
  return ⟨s0, e0, s1, e1, extra⟩

/-- Samples all five first-exchange noise matrices directly from the integer `D₁` sampler. -/
def challengeIntCoinsExp : ProbComp ChallengeIntCoins := do
  let s0 ← challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ← challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ← challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ← challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ← challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return ⟨s0, e0, s1, e1, extra⟩

/-- Converts scalar first-exchange coins to their centered integer representatives. -/
def centerChallengeCoins
    (t : InitKey challengeParams × SendACoins challengeParams) : ChallengeIntCoins :=
  ⟨(fun i j => (t.1.secret i j).valMinAbs),
    (fun i j => (t.1.error i j).valMinAbs),
    (fun i j => (t.2.secret i j).valMinAbs),
    (fun i j => (t.2.error i j).valMinAbs),
    (fun i j => (t.2.extra i j).valMinAbs)⟩

/-- Computes one centered entry-noise value from the integer first-exchange coins. -/
def challengeEntryNoiseAux
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : ChallengeIntCoins) : ℤ :=
  (∑ k : Fin challengeParams.n, t.s1 c.1 k * t.e0 k c.2) -
    (∑ k : Fin challengeParams.n, t.e1 c.1 k * t.s0 k c.2) +
    t.extra c.1 c.2

theorem challengeEntryNoiseAux_center
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    challengeEntryNoiseAux c (centerChallengeCoins t) = challengeEntryNoiseInt c t := rfl

theorem evalDist_centerChallengeCoins :
    finiteLaw (centerChallengeCoins <$> challengeCoinsExp) =
      finiteLaw challengeIntCoinsExp := by
  have hcentered :
      finiteLaw (centerChallengeCoins <$> challengeCoinsExp) =
        finiteLaw challengeCenteredCoinsExp := by
    simp only [challengeCoinsExp, challengeCenteredCoinsExp, centerChallengeCoins,
      initKeyGen, sampleSendACoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    exact lweCKA.evalDist_bind_const_neverFails
      (($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams)))
      (probFailure_eq_zero
        (mx := ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))))
      _
  have hHead {α β : Type} {mx my : ProbComp α}
      (h : finiteLaw mx = finiteLaw my) (f : α → ProbComp β) :
      finiteLaw (mx >>= f) = finiteLaw (my >>= f) := by
    simp only [evalDist_bind, h]
  apply hcentered.trans
  simp only [challengeCenteredCoinsExp, challengeIntCoinsExp]
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  exact hHead (evalDist_sampleMatrix_valMinAbs _ _) _

/-- Samples the signed product exponent `σ * (x * y)` from two independent `D₁` values. -/
def challengeProductExponent (σ : ℤ) : ProbComp ℤ := do
  let x ← d1IntSampler
  let y ← d1IntSampler
  return σ * (x * y)

/-- Samples the shared-coordinate exponent `x * (σ * y + τ * z)`. -/
def challengeSharedExponent (σ τ : ℤ) : ProbComp ℤ := do
  let x ← d1IntSampler
  let y ← d1IntSampler
  let z ← d1IntSampler
  return x * (σ * y + τ * z)

/-- Independently samples two exponent experiments and adds their results. -/
def challengeAddExponents (mx my : ProbComp ℤ) : ProbComp ℤ := do
  let x ← mx
  let y ← my
  return x + y

/-- One inner-coordinate exponent block for a pair sharing a row or column. -/
def challengeSharedBlock (σ τ : ℤ) : ProbComp ℤ :=
  challengeAddExponents (challengeSharedExponent σ τ)
    (challengeSharedExponent (-σ) (-τ))

/-- One inner-coordinate exponent block for a pair with disjoint rows and columns. -/
def challengeDisjointBlock (σ τ : ℤ) : ProbComp ℤ :=
  challengeAddExponents
    (challengeAddExponents (challengeProductExponent σ) (challengeProductExponent τ))
    (challengeAddExponents (challengeProductExponent (-σ))
      (challengeProductExponent (-τ)))

/-- Sums `challengeParams.n` independent copies of an exponent block. -/
def challengeBlockSum (block : ProbComp ℤ) : ProbComp ℤ :=
  (fun v : Fin challengeParams.n → ℤ => ∑ i, v i) <$>
    ProbComp.sampleIID challengeParams.n block

/-- The full signed pair exponent, including its block sum and two additional errors. -/
def challengePairExponentExp (shared : Bool) (σ τ : ℤ) : ProbComp ℤ :=
  let block := if shared then challengeSharedBlock σ τ else challengeDisjointBlock σ τ
  challengeAddExponents (challengeAddExponents (challengeBlockSum block)
    ((fun z => σ * z) <$> d1IntSampler)) ((fun z => τ * z) <$> d1IntSampler)

private theorem expectedValue_add_exponents (mx my : ProbComp ℤ) :
    expectedValue (challengeAddExponents mx my)
        (fun z => challengeChernoffBase ^ z) =
      expectedValue mx (fun z => challengeChernoffBase ^ z) *
        expectedValue my (fun z => challengeChernoffBase ^ z) := by
  have hbase_zero : challengeChernoffBase ≠ 0 := by
    norm_num [challengeChernoffBase]
  have hbase_top : challengeChernoffBase ≠ ∞ := by
    unfold challengeChernoffBase
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  simp only [challengeAddExponents, expectedValue_bind, expectedValue_pure]
  calc
    expectedValue mx (fun x =>
        expectedValue my (fun y => challengeChernoffBase ^ (x + y))) =
        expectedValue mx (fun x =>
          expectedValue my (fun y =>
            challengeChernoffBase ^ x * challengeChernoffBase ^ y)) := by
      congr 1
      funext x
      congr 1
      funext y
      rw [ENNReal.zpow_add hbase_zero hbase_top]
    _ = expectedValue mx (fun x =>
          challengeChernoffBase ^ x *
            expectedValue my (fun y => challengeChernoffBase ^ y)) := by
      congr 1
      funext x
      exact expectedValue_const_mul_left _ _ _
    _ = expectedValue mx (fun x => challengeChernoffBase ^ x) *
          expectedValue my (fun y => challengeChernoffBase ^ y) :=
      expectedValue_const_mul_right _ _ _

private theorem expectedValue_product_exponent
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    expectedValue (challengeProductExponent σ)
        (fun z => challengeChernoffBase ^ z) = challengeProductMoment := by
  simp only [challengeProductExponent, expectedValue_bind, expectedValue_pure]
  exact challenge_product_moment σ hσ

private theorem expectedValue_shared_exponent
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengeSharedExponent σ τ)
        (fun z => challengeChernoffBase ^ z) = challengeSharedMoment := by
  simp only [challengeSharedExponent, expectedValue_bind, expectedValue_pure]
  exact challenge_shared_moment σ τ hσ hτ

private theorem expectedValue_shared_block
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengeSharedBlock σ τ)
        (fun z => challengeChernoffBase ^ z) = challengeSharedMoment ^ 2 := by
  rw [challengeSharedBlock, expectedValue_add_exponents,
    expectedValue_shared_exponent σ τ hσ hτ,
    expectedValue_shared_exponent (-σ) (-τ)]
  · ring
  · rcases hσ with rfl | rfl <;> simp
  · rcases hτ with rfl | rfl <;> simp

private theorem expectedValue_disjoint_block
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengeDisjointBlock σ τ)
        (fun z => challengeChernoffBase ^ z) = challengeProductMoment ^ 4 := by
  have hnσ : -σ = 1 ∨ -σ = -1 := by
    rcases hσ with rfl | rfl <;> simp
  have hnτ : -τ = 1 ∨ -τ = -1 := by
    rcases hτ with rfl | rfl <;> simp
  simp only [challengeDisjointBlock, expectedValue_add_exponents]
  rw [expectedValue_product_exponent σ hσ, expectedValue_product_exponent τ hτ,
    expectedValue_product_exponent (-σ) hnσ,
    expectedValue_product_exponent (-τ) hnτ]
  ring

private theorem expectedValue_block_sum (block : ProbComp ℤ) :
    expectedValue (challengeBlockSum block)
        (fun z => challengeChernoffBase ^ z) =
      expectedValue block (fun z => challengeChernoffBase ^ z) ^ challengeParams.n := by
  rw [challengeBlockSum, expectedValue_map]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    expectedValue_sampleIID_zpow_sum block challengeParams.n
      (fun _ z => z)

theorem expectedValue_pair_exponent
    (shared : Bool) (σ τ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengePairExponentExp shared σ τ)
        (fun z => challengeChernoffBase ^ z) =
      if shared then
        challengeSharedMoment ^ 704 * challengeOneMoment ^ 2
      else
        challengeProductMoment ^ 1408 * challengeOneMoment ^ 2 := by
  simp only [challengePairExponentExp, expectedValue_add_exponents,
    expectedValue_map, expectedValue_block_sum]
  rw [challenge_one_moment σ hσ, challenge_one_moment τ hτ]
  cases shared
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [expectedValue_disjoint_block σ τ hσ hτ]
    simp only [challengeParams]
    ring
  · simp only [↓reduceIte]
    rw [expectedValue_shared_block σ τ hσ hτ]
    simp only [challengeParams]
    ring

private theorem evalDist_sampleIID_coord
    {α : Type} (mx : ProbComp α) (hfail : prFail mx = 0)
    (n : ℕ) (i : Fin n) :
    finiteLaw ((fun v : Fin n → α => v i) <$> ProbComp.sampleIID n mx) =
      finiteLaw mx := by
  apply evalDist_ext
  intro x
  rw [prEvent_map]
  exact (probEvent_coord_mOfFn n (fun _ => mx) (fun _ => hfail) i (· = x)).trans
    (rfl)

theorem evalDist_challengeIntMatrix_row
    (rows cols : ℕ) (i : Fin rows) :
    finiteLaw ((fun m : Matrix (Fin rows) (Fin cols) ℤ => m i) <$>
      challengeIntMatrix rows cols) =
      finiteLaw (ProbComp.sampleIID cols d1IntSampler) := by
  unfold challengeIntMatrix
  exact evalDist_sampleIID_coord _
    (probFailure_mOfFn cols (fun _ => d1IntSampler) fun _ => probFailure_eq_zero)
    rows i

theorem evalDist_challengeIntMatrix_col
    (rows cols : ℕ) (j : Fin cols) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ => fun i => m i j) <$>
          challengeIntMatrix rows cols) =
      finiteLaw (ProbComp.sampleIID rows d1IntSampler) := by
  unfold challengeIntMatrix
  calc
    finiteLaw
          ((fun m : Matrix (Fin rows) (Fin cols) ℤ => fun i => m i j) <$>
            ProbComp.sampleIID rows (ProbComp.sampleIID cols d1IntSampler)) =
        finiteLaw
          (ProbComp.sampleIID rows
            ((fun row : Fin cols → ℤ => row j) <$>
              ProbComp.sampleIID cols d1IntSampler)) :=
      evalDist_sampleIID_map_local rows _ (fun row : Fin cols → ℤ => row j)
    _ = finiteLaw (ProbComp.sampleIID rows d1IntSampler) := by
      apply evalDist_sampleIID_congr_local
      exact evalDist_sampleIID_coord d1IntSampler probFailure_eq_zero cols j

theorem evalDist_challengeIntMatrix_two_cols
    (rows cols : ℕ) (j l : Fin cols) (hjl : j ≠ l) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
            fun i => (m i j, m i l)) <$>
          challengeIntMatrix rows cols) =
      finiteLaw (ProbComp.sampleIID rows
        (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
  unfold challengeIntMatrix
  calc
    finiteLaw
          ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
              fun i => (m i j, m i l)) <$>
            ProbComp.sampleIID rows (ProbComp.sampleIID cols d1IntSampler)) =
        finiteLaw
          (ProbComp.sampleIID rows
            ((fun row : Fin cols → ℤ => (row j, row l)) <$>
              ProbComp.sampleIID cols d1IntSampler)) :=
      evalDist_sampleIID_map_local rows _
        (fun row : Fin cols → ℤ => (row j, row l))
    _ = finiteLaw (ProbComp.sampleIID rows
          (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
      apply evalDist_sampleIID_congr_local
      exact evalDist_sampleIID_two_coords d1IntSampler cols j l hjl

private theorem evalDist_sampleIID_zip
    {α β : Type} (mx : ProbComp α) (my : ProbComp β) (n : ℕ) :
    finiteLaw
        (do
          let xs ← ProbComp.sampleIID n mx
          let ys ← ProbComp.sampleIID n my
          return fun i => (xs i, ys i)) =
      finiteLaw (ProbComp.sampleIID n (Prod.mk <$> mx <*> my)) := by
  induction n with
  | zero =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, pure_bind]
      congr 2
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, bind_assoc, pure_bind,
        seq_eq_bind_map, map_eq_bind_pure_comp, Function.comp_apply]
      refine evalDist_bind_congr' mx fun x => ?_
      rw [evalDist_bind_bind_swap]
      refine evalDist_bind_congr' my fun y => ?_
      have htail := finiteLaw_map_congr ih
        (fun rest : Fin n → α × β => @Fin.cons n (fun _ => α × β) (x, y) rest)
      convert htail using 1
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, bind_assoc,
          pure_bind, Function.comp_apply]
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => mx) fun xs => ?_
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => my) fun ys => ?_
        congr 2
        funext i
        exact Fin.cases (by simp) (fun j => by simp) i
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp]
        simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc,
          pure_bind, Function.comp_apply]
        congr 1

theorem evalDist_challengeIntMatrix_two_rows
    (rows cols : ℕ) (i k : Fin rows) (hik : i ≠ k) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
            fun j => (m i j, m k j)) <$>
          challengeIntMatrix rows cols) =
      finiteLaw (ProbComp.sampleIID cols
        (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
  calc
    finiteLaw
          ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
              fun j => (m i j, m k j)) <$>
            challengeIntMatrix rows cols) =
        finiteLaw
          ((fun rows : (Fin cols → ℤ) × (Fin cols → ℤ) =>
              fun j => (rows.1 j, rows.2 j)) <$>
            ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i, m k)) <$>
              challengeIntMatrix rows cols)) := by
      rw [Functor.map_map]
    _ = finiteLaw
          ((fun rows : (Fin cols → ℤ) × (Fin cols → ℤ) =>
              fun j => (rows.1 j, rows.2 j)) <$>
            (Prod.mk <$>
              ProbComp.sampleIID cols d1IntSampler <*>
              ProbComp.sampleIID cols d1IntSampler)) :=
      finiteLaw_map_congr
        (by
          unfold challengeIntMatrix
          exact evalDist_sampleIID_two_coords _ rows i k hik)
        _
    _ = finiteLaw (ProbComp.sampleIID cols
          (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
      simpa only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
        using evalDist_sampleIID_zip d1IntSampler d1IntSampler cols

theorem evalDist_challengeIntMatrix_two_entries
    (rows cols : ℕ) (i k : Fin rows) (j l : Fin cols)
    (hentry : (i, j) ≠ (k, l)) :
    finiteLaw
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i j, m k l)) <$>
          challengeIntMatrix rows cols) =
      finiteLaw (Prod.mk <$> d1IntSampler <*> d1IntSampler) := by
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by
      intro h
      exact hentry (Prod.ext rfl h)
    calc
      finiteLaw
            ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i j, m i l)) <$>
              challengeIntMatrix rows cols) =
          finiteLaw
            ((fun v : Fin rows → ℤ × ℤ => v i) <$>
              ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
                  fun r => (m r j, m r l)) <$>
                challengeIntMatrix rows cols)) := by
        rw [Functor.map_map]
      _ = finiteLaw
            ((fun v : Fin rows → ℤ × ℤ => v i) <$>
              ProbComp.sampleIID rows
                (Prod.mk <$> d1IntSampler <*> d1IntSampler)) :=
        finiteLaw_map_congr
          (evalDist_challengeIntMatrix_two_cols rows cols j l hjl) _
      _ = finiteLaw (Prod.mk <$> d1IntSampler <*> d1IntSampler) :=
        evalDist_sampleIID_coord _ (by simp) rows i
  · calc
      finiteLaw
            ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i j, m k l)) <$>
              challengeIntMatrix rows cols) =
          finiteLaw
            ((fun rs : (Fin cols → ℤ) × (Fin cols → ℤ) =>
                (rs.1 j, rs.2 l)) <$>
              ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i, m k)) <$>
                challengeIntMatrix rows cols)) := by
        rw [Functor.map_map]
      _ = finiteLaw
            ((fun rs : (Fin cols → ℤ) × (Fin cols → ℤ) =>
                (rs.1 j, rs.2 l)) <$>
              (Prod.mk <$>
                ProbComp.sampleIID cols d1IntSampler <*>
                ProbComp.sampleIID cols d1IntSampler)) :=
        finiteLaw_map_congr
          (by
            unfold challengeIntMatrix
            exact evalDist_sampleIID_two_coords _ rows i k hik) _
      _ = finiteLaw
            (Prod.mk <$>
              ((fun row : Fin cols → ℤ => row j) <$>
                ProbComp.sampleIID cols d1IntSampler) <*>
              ((fun row : Fin cols → ℤ => row l) <$>
                ProbComp.sampleIID cols d1IntSampler)) := by
        simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
      _ = finiteLaw (Prod.mk <$> d1IntSampler <*> d1IntSampler) := by
        apply evalDist_ext
        intro z
        simp only [probOutput_seq_map_prod_mk_eq_mul]
        rw [evalDist_ext_iff.mp
          (evalDist_sampleIID_coord d1IntSampler probFailure_eq_zero cols j) z.1,
          evalDist_ext_iff.mp
          (evalDist_sampleIID_coord d1IntSampler probFailure_eq_zero cols l) z.2]

theorem evalDist_sampleIID_map_four
    {α β γ δ ε : Type}
    (mx : ProbComp α) (my : ProbComp β) (mz : ProbComp γ) (mw : ProbComp δ)
    (n : ℕ) (f : α → β → γ → δ → ε) :
    finiteLaw
        (do
          let xs ← ProbComp.sampleIID n mx
          let ys ← ProbComp.sampleIID n my
          let zs ← ProbComp.sampleIID n mz
          let ws ← ProbComp.sampleIID n mw
          return fun i => f (xs i) (ys i) (zs i) (ws i)) =
      finiteLaw
        (ProbComp.sampleIID n (do
          let x ← mx
          let y ← my
          let z ← mz
          let w ← mw
          return f x y z w)) := by
  let mxy : ProbComp (α × β) := Prod.mk <$> mx <*> my
  let mxyz : ProbComp ((α × β) × γ) := Prod.mk <$> mxy <*> mz
  let mxyzw : ProbComp (((α × β) × γ) × δ) := Prod.mk <$> mxyz <*> mw
  have hHead {κ ρ : Type} {ma mb : ProbComp κ}
      (h : finiteLaw ma = finiteLaw mb) (g : κ → ProbComp ρ) :
      finiteLaw (ma >>= g) = finiteLaw (mb >>= g) := by
    simp only [evalDist_bind, h]
  have hxy := evalDist_sampleIID_zip mx my n
  have hxyz := evalDist_sampleIID_zip mxy mz n
  have hxyzw := evalDist_sampleIID_zip mxyz mw n
  calc
    finiteLaw
          (do
            let xs ← ProbComp.sampleIID n mx
            let ys ← ProbComp.sampleIID n my
            let zs ← ProbComp.sampleIID n mz
            let ws ← ProbComp.sampleIID n mw
            return fun i => f (xs i) (ys i) (zs i) (ws i)) =
        finiteLaw
          (do
            let xys ← ProbComp.sampleIID n mxy
            let zs ← ProbComp.sampleIID n mz
            let ws ← ProbComp.sampleIID n mw
            return fun i => f (xys i).1 (xys i).2 (zs i) (ws i)) := by
      simpa only [mxy, bind_assoc, pure_bind, seq_eq_bind_map,
        map_eq_bind_pure_comp, Function.comp_apply] using
        hHead hxy (fun xys => do
          let zs ← ProbComp.sampleIID n mz
          let ws ← ProbComp.sampleIID n mw
          return fun i => f (xys i).1 (xys i).2 (zs i) (ws i))
    _ = finiteLaw
          (do
            let xyzs ← ProbComp.sampleIID n mxyz
            let ws ← ProbComp.sampleIID n mw
            return fun i => f (xyzs i).1.1 (xyzs i).1.2 (xyzs i).2 (ws i)) := by
      simpa only [mxyz, bind_assoc, pure_bind, seq_eq_bind_map,
        map_eq_bind_pure_comp, Function.comp_apply] using
        hHead hxyz (fun xyzs => do
          let ws ← ProbComp.sampleIID n mw
          return fun i => f (xyzs i).1.1 (xyzs i).1.2 (xyzs i).2 (ws i))
    _ = finiteLaw
          ((fun xyzw : Fin n → (((α × β) × γ) × δ) =>
              fun i => f (xyzw i).1.1.1 (xyzw i).1.1.2
                (xyzw i).1.2 (xyzw i).2) <$>
            ProbComp.sampleIID n mxyzw) := by
      simpa only [mxyzw, bind_assoc, pure_bind, seq_eq_bind_map,
        map_eq_bind_pure_comp, Function.comp_apply] using
        finiteLaw_map_congr hxyzw
          (fun xyzw : Fin n → (((α × β) × γ) × δ) =>
            fun i => f (xyzw i).1.1.1 (xyzw i).1.1.2
              (xyzw i).1.2 (xyzw i).2)
    _ = finiteLaw
          (ProbComp.sampleIID n (do
            let x ← mx
            let y ← my
            let z ← mz
            let w ← mw
            return f x y z w)) := by
      calc
        finiteLaw
              ((fun xyzw : Fin n → (((α × β) × γ) × δ) =>
                  fun i => f (xyzw i).1.1.1 (xyzw i).1.1.2
                    (xyzw i).1.2 (xyzw i).2) <$>
                ProbComp.sampleIID n mxyzw) =
            finiteLaw
              (ProbComp.sampleIID n
                ((fun xyzw : (((α × β) × γ) × δ) =>
                    f xyzw.1.1.1 xyzw.1.1.2 xyzw.1.2 xyzw.2) <$> mxyzw)) :=
          evalDist_sampleIID_map_local n mxyzw
            (fun xyzw : (((α × β) × γ) × δ) =>
              f xyzw.1.1.1 xyzw.1.1.2 xyzw.1.2 xyzw.2)
        _ = finiteLaw
              (ProbComp.sampleIID n (do
                let x ← mx
                let y ← my
                let z ← mz
                let w ← mw
                return f x y z w)) := by
          apply evalDist_sampleIID_congr_local
          simp only [mxyzw, mxyz, mxy, seq_eq_bind_map,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

end PairBoundInternal

end lweCKA
