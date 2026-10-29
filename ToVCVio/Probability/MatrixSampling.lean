/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
module

public import VCVio.EvalDist.IndepProduct
public import VCVio.OracleComp.ProbComp
public import Mathlib.Data.Matrix.Basic

/-!
# Independent matrix sampling

This file samples a matrix as independent rows of independent entries and records the finite laws
of entrywise maps and coordinate projections.
-/

@[expose] public section

namespace ToVCVio

open OracleComp MeasureTheory

/-- The complete discrete output measure of a finite probabilistic computation. -/
noncomputable abbrev finiteLaw {α : Type} (mx : ProbComp α) :
    @Measure α ⊤ := @evalDist _ _ _ ⊤ mx

theorem finiteLaw_ext_iff {α : Type} {mx my : ProbComp α} :
    finiteLaw mx = finiteLaw my ↔
      ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x] := by
  let : MeasurableSpace α := ⊤
  constructor
  · intro h x
    exact (EvalDistEq.of_evalDist_eq h).prEvent_eq (· = x)
  · intro h
    exact (OracleComp.evalDistEq_of_forall_prEvent_eq_output h).evalDist_eq

theorem finiteLaw_bind_congr {α β : Type} (mx : ProbComp α)
    {ob₁ ob₂ : α → ProbComp β} (h : ∀ x, finiteLaw (ob₁ x) = finiteLaw (ob₂ x)) :
    finiteLaw (mx >>= ob₁) = finiteLaw (mx >>= ob₂) := by
  let : MeasurableSpace β := ⊤
  exact OracleComp.evalDist_bind_congr_of_support mx ob₁ ob₂ fun x _ => h x

theorem finiteLaw_map_congr {α β : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (f : α → β) :
    finiteLaw (f <$> mx) = finiteLaw (f <$> my) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact ((EvalDistEq.of_evalDist_eq h).map f).evalDist_eq

/-- Replacing the head of a bind by one with the same finite law preserves the law. -/
theorem finiteLaw_bind_head {α β : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (k : α → ProbComp β) :
    finiteLaw (mx >>= k) = finiteLaw (my >>= k) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact ((EvalDistEq.of_evalDist_eq h).bind (fun _ => EvalDistEq.refl _)).evalDist_eq

/-- A discarded first computation does not change the finite law. -/
theorem finiteLaw_bind_const {α β : Type}
    (mx : ProbComp α) (my : ProbComp β) :
    finiteLaw (mx >>= fun _ => my) = finiteLaw my := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact (EvalDistEq.bind_const mx my).evalDist_eq

private theorem probEvent_coord {α : Type} (n : ℕ) (g : Fin n → ProbComp α)
    (i : Fin n) (p : α → Prop) :
    Pr{let v ← Fin.mOfFn n g}[p (v i)] = Pr{let x ← g i}[p x] :=
  prEvent_coord_mOfFn n g i p fun j _ => (prFail_eq_zero_iff (g j)).mp (prFail_eq_zero _)

/-- Sample a matrix whose entries are independent draws from `χ`. -/
def sampleMatrix {α : Type} (rows cols : ℕ)
    (χ : ProbComp α) : ProbComp (Matrix (Fin rows) (Fin cols) α) :=
  ProbComp.sampleIID rows (ProbComp.sampleIID cols χ)

private theorem finiteLaw_sampleIID_map
    {α β : Type} (n : ℕ) (χ : ProbComp α) (f : α → β) :
    finiteLaw
        ((fun xs : Fin n → α => fun k => f (xs k)) <$>
          ProbComp.sampleIID n χ) =
      finiteLaw (ProbComp.sampleIID n (f <$> χ)) := by
  induction n with
  | zero =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_pure]
      congr 2
      funext k
      exact k.elim0
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
      refine finiteLaw_bind_congr χ fun a => ?_
      have htail := finiteLaw_map_congr ih
        (fun rest : Fin n → β => @Fin.cons n (fun _ => β) (f a) rest)
      convert htail using 1
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        refine finiteLaw_bind_congr (Fin.mOfFn n fun _ => χ) fun rest => ?_
        congr 2
        funext k
        exact Fin.cases (by simp) (fun l => by simp) k
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, Function.comp_def]

private theorem finiteLaw_sampleIID_congr
    {α : Type} (n : ℕ) (χ ψ : ProbComp α)
    (hχψ : finiteLaw χ = finiteLaw ψ) :
    finiteLaw (ProbComp.sampleIID n χ) =
      finiteLaw (ProbComp.sampleIID n ψ) := by
  apply finiteLaw_ext_iff.mpr
  intro v
  simp only [ProbComp.sampleIID, prEvent_eq_mOfFn]
  apply Finset.prod_congr rfl
  intro i _
  exact finiteLaw_ext_iff.mp hχψ (v i)

/-- Mapping every sampled matrix entry equals sampling from the mapped entry law. -/
theorem finiteLaw_sampleMatrix_map
    {α β : Type} (rows cols : ℕ) (χ : ProbComp α) (f : α → β) :
    finiteLaw ((fun M => M.map f) <$> sampleMatrix rows cols χ) =
      finiteLaw (sampleMatrix rows cols (f <$> χ)) := by
  unfold sampleMatrix
  change finiteLaw
      ((fun M : Matrix (Fin rows) (Fin cols) α => fun i j => f (M i j)) <$>
        ProbComp.sampleIID rows (ProbComp.sampleIID cols χ)) =
    finiteLaw (ProbComp.sampleIID rows (ProbComp.sampleIID cols (f <$> χ)))
  exact (finiteLaw_sampleIID_map rows (ProbComp.sampleIID cols χ)
    (fun row : Fin cols → α => fun j => f (row j))).trans
      (finiteLaw_sampleIID_congr rows _ _ (finiteLaw_sampleIID_map cols χ f))

/-- A selected row of an independently sampled matrix has the row sampling law. -/
theorem finiteLaw_sampleMatrix_row
    {α : Type} (rows cols : ℕ) (χ : ProbComp α)
    (i : Fin rows) :
    finiteLaw ((fun M => M i) <$> sampleMatrix rows cols χ) =
      finiteLaw (ProbComp.sampleIID cols χ) := by
  apply finiteLaw_ext_iff.mpr
  intro y
  rw [prEvent_map]
  unfold sampleMatrix ProbComp.sampleIID
  change
    Pr{let M ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[M i = y] =
      Pr{let x ← Fin.mOfFn cols fun _ => χ}[x = y]
  exact probEvent_coord rows (fun _ => Fin.mOfFn cols fun _ => χ)
    i (· = y)

/-- A selected column of an independently sampled matrix has the column sampling law. -/
theorem finiteLaw_sampleMatrix_col
    {α : Type} (rows cols : ℕ) (χ : ProbComp α)
    (j : Fin cols) :
    finiteLaw ((fun M => fun i => M i j) <$> sampleMatrix rows cols χ) =
      finiteLaw (ProbComp.sampleIID rows χ) := by
  apply finiteLaw_ext_iff.mpr
  intro y
  rw [prEvent_map]
  unfold sampleMatrix ProbComp.sampleIID
  change
    Pr{let M ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[
        (fun i => M i j) = y] =
      Pr{let x ← Fin.mOfFn rows fun _ => χ}[x = y]
  calc
    Pr{let M ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[
          (fun i => M i j) = y] =
        Pr{let M ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[
          ∀ i, M i j = y i] :=
      prEvent_congr _ _ _ fun _ => funext_iff
    _ = ∏ i, Pr{let row ← Fin.mOfFn cols fun _ => χ}[row j = y i] :=
      prEvent_forall_coord_mOfFn rows
        (fun _ => Fin.mOfFn cols fun _ => χ) (fun i row => row j = y i)
    _ = ∏ i, Pr{let x ← χ}[x = y i] := by
      apply Finset.prod_congr rfl
      intro i _
      exact probEvent_coord cols (fun _ => χ) j (· = y i)
    _ = Pr{let x ← Fin.mOfFn rows fun _ => χ}[x = y] :=
      (prEvent_eq_mOfFn rows (fun _ => χ) y).symm

/-- A selected entry of an independently sampled matrix has the entry sampling law. -/
theorem finiteLaw_sampleMatrix_entry
    {α : Type} (rows cols : ℕ) (χ : ProbComp α)
    (i : Fin rows) (j : Fin cols) :
    finiteLaw ((fun M => M i j) <$> sampleMatrix rows cols χ) =
      finiteLaw χ := by
  apply finiteLaw_ext_iff.mpr
  intro y
  rw [prEvent_map]
  unfold sampleMatrix ProbComp.sampleIID
  change
    Pr{let M ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[M i j = y] =
      Pr{let x ← χ}[x = y]
  calc
    Pr{let M ← Fin.mOfFn rows fun _ => Fin.mOfFn cols fun _ => χ}[M i j = y] =
        Pr{let row ← Fin.mOfFn cols fun _ => χ}[row j = y] :=
      probEvent_coord rows (fun _ => Fin.mOfFn cols fun _ => χ)
        i
        (fun row : Fin cols → α => row j = y)
    _ = Pr{let x ← χ}[x = y] :=
      probEvent_coord cols (fun _ => χ) j (· = y)

end ToVCVio
