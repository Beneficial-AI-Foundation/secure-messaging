/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.PairBound.Coins

/-!
# Pair projection laws for the Frodo Challenge pair bound

This module rewrites shared-row, shared-column, and disjoint coordinate projections into the block
experiments whose moments were computed in the preceding layer.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA

open PairBoundInternal

namespace PairBoundInternal

/-- Two independent integer-valued Challenge `D₁` samples. -/
def challengePairSampler : ProbComp (ℤ × ℤ) :=
  Prod.mk <$> d1IntSampler <*> d1IntSampler

private def challengeProjectedRowExponentExp
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ => m c.1) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ => m c.1) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ =>
      (m c.1 c.2, m d.1 d.2)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return Finset.univ.sum (fun k =>
      s1 k * (σ * (e0 k).1 + τ * (e0 k).2) +
        e1 k * ((-σ) * (s0 k).1 + (-τ) * (s0 k).2)) +
    σ * extra.1 + τ * extra.2

private def challengeProjectedColExponentExp
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => m k c.2) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => m k c.2) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ =>
      (m c.1 c.2, m d.1 d.2)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return Finset.univ.sum (fun k =>
      e0 k * (σ * (s1 k).1 + τ * (s1 k).2) +
        s0 k * ((-σ) * (e1 k).1 + (-τ) * (e1 k).2)) +
    σ * extra.1 + τ * extra.2

/-- Projects disjoint matrix coordinates into their combined signed-noise exponent. -/
def challengeProjectedDisjointExponentExp
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ =>
      (m c.1 c.2, m d.1 d.2)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return Finset.univ.sum (fun k =>
      σ * (s1 k).1 * (e0 k).1 + τ * (s1 k).2 * (e0 k).2 +
        (-σ) * (e1 k).1 * (s0 k).1 + (-τ) * (e1 k).2 * (s0 k).2) +
    σ * extra.1 + τ * extra.2

private theorem evalDist_bind_five_output_congr
    {α₁ α₂ α₃ α₄ α₅ ρ : Type}
    (m₁ : ProbComp α₁) (m₂ : ProbComp α₂) (m₃ : ProbComp α₃)
    (m₄ : ProbComp α₄) (m₅ : ProbComp α₅)
    (f g : α₁ → α₂ → α₃ → α₄ → α₅ → ProbComp ρ)
    (h : ∀ a₁ a₂ a₃ a₄ a₅, f a₁ a₂ a₃ a₄ a₅ = g a₁ a₂ a₃ a₄ a₅) :
    finiteLaw (do
      let a₁ ← m₁
      let a₂ ← m₂
      let a₃ ← m₃
      let a₄ ← m₄
      let a₅ ← m₅
      f a₁ a₂ a₃ a₄ a₅) =
    finiteLaw (do
      let a₁ ← m₁
      let a₂ ← m₂
      let a₃ ← m₃
      let a₄ ← m₄
      let a₅ ← m₅
      g a₁ a₂ a₃ a₄ a₅) := by
  simp only [evalDist_bind, h]

theorem evalDist_challengeInt_to_row_projected
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hrow : c.1 = d.1) (σ τ : ℤ) :
    finiteLaw
        ((fun t => σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t) <$>
          challengeIntCoinsExp) =
      finiteLaw (challengeProjectedRowExponentExp c d σ τ) := by
  simp only [challengeIntCoinsExp, challengeProjectedRowExponentExp,
    challengeEntryNoiseAux, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_five_output_congr
  intro s0 e0 s1 e1 extra
  congr 1
  simp only [← hrow]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf

theorem evalDist_challengeInt_to_col_projected
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcol : c.2 = d.2) (σ τ : ℤ) :
    finiteLaw
        ((fun t => σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t) <$>
          challengeIntCoinsExp) =
      finiteLaw (challengeProjectedColExponentExp c d σ τ) := by
  simp only [challengeIntCoinsExp, challengeProjectedColExponentExp,
    challengeEntryNoiseAux, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_five_output_congr
  intro s0 e0 s1 e1 extra
  congr 1
  simp only [← hcol]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hswap (r : ℤ) (a b : Fin challengeParams.n → ℤ) :
      (∑ k, r * a k * b k) = ∑ k, r * b k * a k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hswap σ (fun k => e0 k c.2) (fun k => s1 c.1 k),
    hswap σ (fun k => s0 k c.2) (fun k => e1 c.1 k),
    hswap τ (fun k => e0 k c.2) (fun k => s1 d.1 k),
    hswap τ (fun k => s0 k c.2) (fun k => e1 d.1 k)]
  ring_nf

theorem evalDist_challengeInt_to_disjoint_projected
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) :
    finiteLaw
        ((fun t => σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t) <$>
          challengeIntCoinsExp) =
      finiteLaw (challengeProjectedDisjointExponentExp c d σ τ) := by
  simp only [challengeIntCoinsExp, challengeProjectedDisjointExponentExp,
    challengeEntryNoiseAux, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_five_output_congr
  intro s0 e0 s1 e1 extra
  congr 1
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf

private def challengeRowBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let s1 ← d1IntSampler
  let e1 ← d1IntSampler
  return s1 * (σ * e0.1 + τ * e0.2) +
    e1 * ((-σ) * s0.1 + (-τ) * s0.2)

private def challengeColBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← d1IntSampler
  let e0 ← d1IntSampler
  let s1 ← challengePairSampler
  let e1 ← challengePairSampler
  return e0 * (σ * s1.1 + τ * s1.2) +
    s0 * ((-σ) * e1.1 + (-τ) * e1.2)

/-- One disjoint-coordinate exponent block expressed through four independent sample pairs. -/
def challengeDisjointProjectedBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let s1 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def challengeSharedPairBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← d1IntSampler
  let e0 ← challengePairSampler
  let e1 ← d1IntSampler
  let s0 ← challengePairSampler
  return s1 * (σ * e0.1 + τ * e0.2) +
    e1 * ((-σ) * s0.1 + (-τ) * s0.2)

private theorem evalDist_sharedPairBlock_eq
    (σ τ : ℤ) :
    finiteLaw (challengeSharedPairBlock σ τ) =
      finiteLaw (challengeSharedBlock σ τ) := by
  simp only [challengeSharedPairBlock, challengeSharedBlock, challengeSharedExponent,
    challengeAddExponents, challengePairSampler, seq_eq_bind_map,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

private theorem evalDist_rowBlock_eq_sharedBlock (σ τ : ℤ) :
    finiteLaw (challengeRowBlock σ τ) = finiteLaw (challengeSharedBlock σ τ) := by
  apply (show finiteLaw (challengeRowBlock σ τ) =
      finiteLaw (challengeSharedPairBlock σ τ) by
    simp only [challengeRowBlock, challengeSharedPairBlock]
    calc
      finiteLaw
            (challengePairSampler >>= fun s0 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun s1 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) =
          finiteLaw
            (challengePairSampler >>= fun s0 =>
              d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        apply evalDist_bind_congr'
        intro s0
        rw [evalDist_bind_bind_swap]
      _ = finiteLaw
            (d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun s0 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        exact evalDist_bind_bind_swap challengePairSampler d1IntSampler
          (fun s0 s1 =>
            challengePairSampler >>= fun e0 =>
            d1IntSampler >>= fun e1 =>
            pure (s1 * (σ * e0.1 + τ * e0.2) +
              e1 * (-σ * s0.1 + -τ * s0.2)))
      _ = finiteLaw
            (d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun e0 =>
              challengePairSampler >>= fun s0 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        apply evalDist_bind_congr'
        intro s1
        rw [evalDist_bind_bind_swap]
      _ = finiteLaw
            (d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun e1 =>
              challengePairSampler >>= fun s0 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        apply evalDist_bind_congr'
        intro s1
        apply evalDist_bind_congr'
        intro e0
        rw [evalDist_bind_bind_swap])

private theorem evalDist_colBlock_eq_sharedBlock (σ τ : ℤ) :
    finiteLaw (challengeColBlock σ τ) = finiteLaw (challengeSharedBlock σ τ) := by
  have hreorder : finiteLaw (challengeColBlock σ τ) =
      finiteLaw (challengeSharedPairBlock σ τ) := by
    simp only [challengeColBlock, challengeSharedPairBlock]
    calc
      finiteLaw
            (d1IntSampler >>= fun s0 =>
              d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun s1 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) =
          finiteLaw
            (d1IntSampler >>= fun s0 =>
              challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        apply evalDist_bind_congr'
        intro s0
        rw [evalDist_bind_bind_swap]
      _ = finiteLaw
            (challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun s0 =>
              d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        exact evalDist_bind_bind_swap d1IntSampler challengePairSampler
          (fun s0 s1 =>
            d1IntSampler >>= fun e0 =>
            challengePairSampler >>= fun e1 =>
            pure (e0 * (σ * s1.1 + τ * s1.2) +
              s0 * (-σ * e1.1 + -τ * e1.2)))
      _ = finiteLaw
            (challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun e0 =>
              d1IntSampler >>= fun s0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        apply evalDist_bind_congr'
        intro s1
        rw [evalDist_bind_bind_swap]
      _ = finiteLaw
            (d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun s0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        exact evalDist_bind_bind_swap challengePairSampler d1IntSampler
          (fun s1 e0 =>
            d1IntSampler >>= fun s0 =>
            challengePairSampler >>= fun e1 =>
            pure (e0 * (σ * s1.1 + τ * s1.2) +
              s0 * (-σ * e1.1 + -τ * e1.2)))
      _ = finiteLaw (challengeSharedPairBlock σ τ) := by
        simp only [challengeSharedPairBlock]
  exact hreorder.trans (evalDist_sharedPairBlock_eq σ τ)

private def challengeDoubleProductBlock (σ τ : ℤ) : ProbComp ℤ := do
  let x ← challengePairSampler
  let y ← challengePairSampler
  return σ * x.1 * y.1 + τ * x.2 * y.2

private def challengeDisjointPairBlock (σ τ : ℤ) : ProbComp ℤ :=
  challengeAddExponents (challengeDoubleProductBlock σ τ)
    (challengeDoubleProductBlock (-σ) (-τ))

private theorem evalDist_doubleProductBlock_eq (σ τ : ℤ) :
    finiteLaw (challengeDoubleProductBlock σ τ) =
      finiteLaw (challengeAddExponents (challengeProductExponent σ)
        (challengeProductExponent τ)) := by
  simp only [challengeDoubleProductBlock, challengePairSampler,
    challengeAddExponents, challengeProductExponent, seq_eq_bind_map,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply evalDist_bind_congr'
  intro x₁
  rw [evalDist_bind_bind_swap]
  apply evalDist_bind_congr'
  intro y₁
  apply evalDist_bind_congr'
  intro x₂
  apply evalDist_bind_congr'
  intro y₂
  congr 2
  ring

private theorem evalDist_disjointPairBlock_eq (σ τ : ℤ) :
    finiteLaw (challengeDisjointPairBlock σ τ) =
      finiteLaw (challengeDisjointBlock σ τ) := by
  have hHead {α β : Type} {mx my : ProbComp α}
      (h : finiteLaw mx = finiteLaw my) (f : α → ProbComp β) :
      finiteLaw (mx >>= f) = finiteLaw (my >>= f) := by
    simp only [evalDist_bind, h]
  simp only [challengeDisjointPairBlock, challengeDisjointBlock,
    challengeAddExponents]
  refine (hHead (evalDist_doubleProductBlock_eq σ τ) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  exact hHead (evalDist_doubleProductBlock_eq (-σ) (-τ)) _

private def disjointOrder0 (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let s1 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder1 (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let s1 ← challengePairSampler
  let e0 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder2 (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← challengePairSampler
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder3 (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← challengePairSampler
  let e0 ← challengePairSampler
  let s0 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder4 (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← challengePairSampler
  let e0 ← challengePairSampler
  let e1 ← challengePairSampler
  let s0 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private theorem evalDist_disjointOrder01 (σ τ : ℤ) :
    finiteLaw (disjointOrder0 σ τ) = finiteLaw (disjointOrder1 σ τ) := by
  simp only [disjointOrder0, disjointOrder1]
  apply evalDist_bind_congr'
  intro s0
  rw [evalDist_bind_bind_swap]

private theorem evalDist_disjointOrder12 (σ τ : ℤ) :
    finiteLaw (disjointOrder1 σ τ) = finiteLaw (disjointOrder2 σ τ) := by
  simp only [disjointOrder1, disjointOrder2]
  exact evalDist_bind_bind_swap challengePairSampler challengePairSampler
    (fun s0 s1 =>
      challengePairSampler >>= fun e0 =>
      challengePairSampler >>= fun e1 =>
      pure (σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
        -σ * e1.1 * s0.1 + -τ * e1.2 * s0.2))

private theorem evalDist_disjointOrder23 (σ τ : ℤ) :
    finiteLaw (disjointOrder2 σ τ) = finiteLaw (disjointOrder3 σ τ) := by
  simp only [disjointOrder2, disjointOrder3]
  apply evalDist_bind_congr'
  intro s1
  rw [evalDist_bind_bind_swap]

private theorem evalDist_disjointOrder34 (σ τ : ℤ) :
    finiteLaw (disjointOrder3 σ τ) = finiteLaw (disjointOrder4 σ τ) := by
  simp only [disjointOrder3, disjointOrder4]
  apply evalDist_bind_congr'
  intro s1
  apply evalDist_bind_congr'
  intro e0
  rw [evalDist_bind_bind_swap]

private theorem evalDist_disjointOrder4_pair (σ τ : ℤ) :
    finiteLaw (disjointOrder4 σ τ) =
      finiteLaw (challengeDisjointPairBlock σ τ) := by
  have hout (s1 e0 e1 s0 : ℤ × ℤ) :
      σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
          -σ * e1.1 * s0.1 + -τ * e1.2 * s0.2 =
        (σ * s1.1 * e0.1 + τ * s1.2 * e0.2) +
          ((-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2) := by
    ring
  simp only [disjointOrder4, challengeDisjointPairBlock,
    challengeDoubleProductBlock, challengeAddExponents, bind_assoc, pure_bind]
  simp_rw [hout]

theorem evalDist_disjointProjectedBlock_eq (σ τ : ℤ) :
    finiteLaw (challengeDisjointProjectedBlock σ τ) =
      finiteLaw (challengeDisjointBlock σ τ) := by
  change finiteLaw (disjointOrder0 σ τ) = _
  exact (evalDist_disjointOrder01 σ τ).trans
    ((evalDist_disjointOrder12 σ τ).trans
      ((evalDist_disjointOrder23 σ τ).trans
        ((evalDist_disjointOrder34 σ τ).trans
          ((evalDist_disjointOrder4_pair σ τ).trans
            (evalDist_disjointPairBlock_eq σ τ)))))

theorem evalDist_bind_five_congr
    {α₁ α₂ α₃ α₄ α₅ ρ : Type}
    {ma₁ mb₁ : ProbComp α₁} {ma₂ mb₂ : ProbComp α₂}
    {ma₃ mb₃ : ProbComp α₃} {ma₄ mb₄ : ProbComp α₄}
    {ma₅ mb₅ : ProbComp α₅}
    (h₁ : finiteLaw ma₁ = finiteLaw mb₁)
    (h₂ : finiteLaw ma₂ = finiteLaw mb₂)
    (h₃ : finiteLaw ma₃ = finiteLaw mb₃)
    (h₄ : finiteLaw ma₄ = finiteLaw mb₄)
    (h₅ : finiteLaw ma₅ = finiteLaw mb₅)
    (f : α₁ → α₂ → α₃ → α₄ → α₅ → ProbComp ρ) :
    finiteLaw (do
      let a₁ ← ma₁
      let a₂ ← ma₂
      let a₃ ← ma₃
      let a₄ ← ma₄
      let a₅ ← ma₅
      f a₁ a₂ a₃ a₄ a₅) =
    finiteLaw (do
      let b₁ ← mb₁
      let b₂ ← mb₂
      let b₃ ← mb₃
      let b₄ ← mb₄
      let b₅ ← mb₅
      f b₁ b₂ b₃ b₄ b₅) := by
  simp only [evalDist_bind, h₁, h₂, h₃, h₄, h₅]

theorem evalDist_bind_head_congr
    {α β : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (f : α → ProbComp β) :
    finiteLaw (mx >>= f) = finiteLaw (my >>= f) := by
  simp only [evalDist_bind, h]

theorem evalDist_projected_row_pairExponent
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcol : c.2 ≠ d.2) (σ τ : ℤ) :
    finiteLaw (challengeProjectedRowExponentExp c d σ τ) =
      finiteLaw (challengePairExponentExp true σ τ) := by
  let vectorExp : ProbComp (Fin challengeParams.n → ℤ) := do
    let s0 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let e0 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let s1 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    let e1 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    return fun k => s1 k * (σ * (e0 k).1 + τ * (e0 k).2) +
      e1 k * ((-σ) * (s0 k).1 + (-τ) * (s0 k).2)
  have hprojected : finiteLaw (challengeProjectedRowExponentExp c d σ τ) =
      finiteLaw (do
        let blocks ← vectorExp
        let extra ← challengePairSampler
        return (∑ k, blocks k) + σ * extra.1 + τ * extra.2) := by
    simp only [challengeProjectedRowExponentExp, vectorExp, bind_assoc, pure_bind]
    apply evalDist_bind_five_congr
    · exact evalDist_challengeIntMatrix_two_cols _ _ _ _ hcol
    · exact evalDist_challengeIntMatrix_two_cols _ _ _ _ hcol
    · exact evalDist_challengeIntMatrix_row _ _ c.1
    · exact evalDist_challengeIntMatrix_row _ _ c.1
    · exact evalDist_challengeIntMatrix_two_entries _ _ _ _ _ _
        (fun h => hcol (congrArg Prod.snd h))
  have hvector : finiteLaw vectorExp =
      finiteLaw (ProbComp.sampleIID challengeParams.n (challengeRowBlock σ τ)) := by
    simpa only [vectorExp, challengeRowBlock] using
      evalDist_sampleIID_map_four challengePairSampler challengePairSampler
        d1IntSampler d1IntSampler challengeParams.n
        (fun s0 e0 s1 e1 => s1 * (σ * e0.1 + τ * e0.2) +
          e1 * ((-σ) * s0.1 + (-τ) * s0.2))
  apply hprojected.trans
  refine (evalDist_bind_head_congr hvector _).trans ?_
  have hblocks := evalDist_sampleIID_congr_local challengeParams.n
    (challengeRowBlock σ τ) (challengeSharedBlock σ τ)
    (evalDist_rowBlock_eq_sharedBlock σ τ)
  refine (evalDist_bind_head_congr hblocks _).trans ?_
  simp only [challengePairExponentExp, challengeBlockSum, challengeAddExponents,
    challengePairSampler, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  apply evalDist_bind_congr'
  intro blocks
  apply evalDist_bind_congr'
  intro x
  apply evalDist_bind_congr'
  intro y
  congr 2

theorem evalDist_projected_col_pairExponent
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hrow : c.1 ≠ d.1) (σ τ : ℤ) :
    finiteLaw (challengeProjectedColExponentExp c d σ τ) =
      finiteLaw (challengePairExponentExp true σ τ) := by
  let vectorExp : ProbComp (Fin challengeParams.n → ℤ) := do
    let s0 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    let e0 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    let s1 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let e1 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    return fun k => e0 k * (σ * (s1 k).1 + τ * (s1 k).2) +
      s0 k * ((-σ) * (e1 k).1 + (-τ) * (e1 k).2)
  have hprojected : finiteLaw (challengeProjectedColExponentExp c d σ τ) =
      finiteLaw (do
        let blocks ← vectorExp
        let extra ← challengePairSampler
        return (∑ k, blocks k) + σ * extra.1 + τ * extra.2) := by
    simp only [challengeProjectedColExponentExp, vectorExp, bind_assoc, pure_bind]
    apply evalDist_bind_five_congr
    · exact evalDist_challengeIntMatrix_col _ _ c.2
    · exact evalDist_challengeIntMatrix_col _ _ c.2
    · exact evalDist_challengeIntMatrix_two_rows _ _ _ _ hrow
    · exact evalDist_challengeIntMatrix_two_rows _ _ _ _ hrow
    · exact evalDist_challengeIntMatrix_two_entries _ _ _ _ _ _
        (fun h => hrow (congrArg Prod.fst h))
  have hvector : finiteLaw vectorExp =
      finiteLaw (ProbComp.sampleIID challengeParams.n (challengeColBlock σ τ)) := by
    simpa only [vectorExp, challengeColBlock] using
      evalDist_sampleIID_map_four d1IntSampler d1IntSampler
        challengePairSampler challengePairSampler challengeParams.n
        (fun s0 e0 s1 e1 => e0 * (σ * s1.1 + τ * s1.2) +
          s0 * ((-σ) * e1.1 + (-τ) * e1.2))
  apply hprojected.trans
  refine (evalDist_bind_head_congr hvector _).trans ?_
  have hblocks := evalDist_sampleIID_congr_local challengeParams.n
    (challengeColBlock σ τ) (challengeSharedBlock σ τ)
    (evalDist_colBlock_eq_sharedBlock σ τ)
  refine (evalDist_bind_head_congr hblocks _).trans ?_
  simp only [challengePairExponentExp, challengeBlockSum, challengeAddExponents,
    challengePairSampler, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  apply evalDist_bind_congr'
  intro blocks
  apply evalDist_bind_congr'
  intro x
  apply evalDist_bind_congr'
  intro y
  congr 2

end PairBoundInternal

end lweCKA
