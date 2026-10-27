/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Sum
import VCVio.EvalDist.IndepProduct
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps
import VCVio.OracleComp.Constructions.UniformSelectMeasure
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Discrete output laws for the LWE correctness experiments

The experiments have finite support, including when their outputs are matrices or protocol
states. Their full output law uses the discrete measurable structure explicitly, so distribution
equalities do not depend on a choice of measurable structure for those output types.
These laws are the current VCVio measure semantics, not a separate probability model.
-/

open OracleComp ENNReal MeasureTheory

namespace lweCKA

/-- The complete discrete output measure of a finite probabilistic computation. -/
noncomputable abbrev finiteLaw {α : Type} (mx : ProbComp α) :
    @Measure α ⊤ := @evalDist _ _ _ ⊤ mx

theorem evalDist_ext_iff {α : Type} {mx my : ProbComp α} :
    finiteLaw mx = finiteLaw my ↔
      ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x] := by
  let : MeasurableSpace α := ⊤
  constructor
  · intro h x
    exact (EvalDistEq.of_evalDist_eq h).prEvent_eq (· = x)
  · intro h
    exact (OracleComp.evalDistEq_of_forall_prEvent_eq_output h).evalDist_eq

theorem evalDist_ext {α : Type} {mx my : ProbComp α}
    (h : ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x]) :
    finiteLaw mx = finiteLaw my := evalDist_ext_iff.mpr h

theorem evalDist_bind_congr' {α β : Type} (mx : ProbComp α)
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

theorem evalDist_bind_bind_swap {α β γ : Type} (mx : ProbComp α)
    (my : ProbComp β) (f : α → β → ProbComp γ) :
    finiteLaw (mx >>= fun a => my >>= fun b => f a b) =
      finiteLaw (my >>= fun b => mx >>= fun a => f a b) := by
  let : MeasurableSpace γ := ⊤
  exact OracleComp.evalDist_bind_bind_swap mx my f

theorem evalDist_bind_const_neverFails {α β : Type} (mx : ProbComp α)
    (_h : prFail mx = 0) (my : ProbComp β) :
    finiteLaw (mx >>= fun _ => my) = finiteLaw my := by
  apply evalDist_ext
  intro x
  simpa only [map_bind] using OracleComp.prEvent_bind_const mx ((· = x) <$> my)

/-- Expected payoff in the current VCVio weakest-precondition semantics. -/
noncomputable abbrev expectedValue {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) :=
  OracleComp.ProgramLogic.wp mx f

theorem expectedValue_def {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) :
    expectedValue mx f = ∑' x, Pr{let y ← mx}[y = x] * f x :=
  OracleComp.ProgramLogic.wp_eq_tsum mx f

theorem expectedValue_pure {α : Type} (x : α) (f : α → ℝ≥0∞) :
    expectedValue (pure x) f = f x := OracleComp.ProgramLogic.wp_pure x f

theorem expectedValue_bind {α β : Type} (mx : ProbComp α) (my : α → ProbComp β)
    (f : β → ℝ≥0∞) :
    expectedValue (mx >>= my) f = expectedValue mx (fun x => expectedValue (my x) f) :=
  OracleComp.ProgramLogic.wp_bind mx my f

theorem expectedValue_map {α β : Type} (mx : ProbComp α) (f : α → β) (g : β → ℝ≥0∞) :
    expectedValue (f <$> mx) g = expectedValue mx (fun x => g (f x)) :=
  OracleComp.ProgramLogic.wp_map f mx g

theorem expectedValue_mono {α : Type} (mx : ProbComp α) {f g : α → ℝ≥0∞}
    (h : ∀ x, f x ≤ g x) : expectedValue mx f ≤ expectedValue mx g :=
  OracleComp.ProgramLogic.wp_mono mx h

theorem expectedValue_const {α : Type} {mx : ProbComp α} (_h : prFail mx = 0)
    (c : ℝ≥0∞) : expectedValue mx (fun _ => c) = c :=
  OracleComp.ProgramLogic.wp_const mx c

theorem expectedValue_add {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞) :
    expectedValue mx (fun x => f x + g x) = expectedValue mx f + expectedValue mx g :=
  OracleComp.ProgramLogic.wp_add mx f g

theorem expectedValue_finsetSum {α : Type} {ι : Type*} (mx : ProbComp α)
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    expectedValue mx (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, expectedValue mx (f i) :=
  OracleComp.ProgramLogic.wp_finsetSum mx s f

theorem expectedValue_congr {α : Type} {mx my : ProbComp α}
    (h : ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x]) (f : α → ℝ≥0∞) :
    expectedValue mx f = expectedValue my f := by
  simp only [expectedValue_def, h]

theorem probOutput_some_map_none {α : Type} (mx : ProbComp α) :
    Pr{let x ← Option.some <$> mx}[x = none] = 0 := by
  simp

theorem probOutput_some_map_some {α : Type} (mx : ProbComp α) (x : α) :
    Pr{let y ← Option.some <$> mx}[y = some x] = Pr{let y ← mx}[y = x] := by
  simp

theorem probOutput_map_eq_probOutput_inverse {α β : Type} (mx : ProbComp α)
    {f : α → β} {g : β → α} (hgf : Function.LeftInverse g f) {y : β} (hfg : f (g y) = y) :
    Pr{let x ← f <$> mx}[x = y] = Pr{let x ← mx}[x = g y] := by
  rw [prEvent_map]
  exact prEvent_congr mx _ _ fun x => ⟨fun h => by rw [← h, hgf], fun h => by rw [h, hfg]⟩

theorem uniformSelectListVector_mass {α : Type} [DecidableEq α] {n : ℕ}
    (xs : List.Vector α (n + 1)) (x : α) :
    Pr{let y ← $! xs}[y = x] = (xs.toList.count x : ℝ≥0∞) / (n + 1) := by
  rw [ProbComp.prEvent_uniformSelectListVector]
  rfl

theorem probFailure_eq_zero {α : Type} {mx : ProbComp α} : prFail mx = 0 :=
  OracleComp.prFail_eq_zero mx

theorem probFailure_mOfFn {α : Type} (n : ℕ) (f : Fin n → ProbComp α)
    (_h : ∀ i, prFail (f i) = 0) : prFail (Fin.mOfFn n f) = 0 :=
  OracleComp.prFail_eq_zero _

theorem evalDist_map_bijective_uniform_cross {α β : Type}
    [SampleableType α] [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) :
    finiteLaw (f <$> ($ᵗ α)) = finiteLaw ($ᵗ β) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : Finite β := Finite.of_surjective f hf.surjective
  change evalDist (f <$> ($ᵗ α)) = evalDist ($ᵗ β)
  rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample,
    SampleableType.evalDist_uniformSample]
  exact ProbabilityTheory.map_uniformOn_univ_of_bijective Measurable.of_discrete hf

theorem probEvent_def {α : Type} (mx : ProbComp α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = finiteLaw mx {x | p x} := by
  let : MeasurableSpace α := ⊤
  exact prEvent_eq_evalDist_of_discrete mx p

theorem probOutput_bind_congr {α β : Type} {mx : ProbComp α}
    {ob₁ ob₂ : α → ProbComp β} {y : β}
    (h : ∀ x ∈ support mx, Pr{let z ← ob₁ x}[z = y] = Pr{let z ← ob₂ x}[z = y]) :
    Pr{let z ← mx >>= ob₁}[z = y] = Pr{let z ← mx >>= ob₂}[z = y] := by
  simpa only [map_bind] using OracleComp.prEvent_bind_congr_of_support mx
    (fun x => (· = y) <$> ob₁ x) (fun x => (· = y) <$> ob₂ x) h

theorem probOutput_bind_congr' {α β : Type} (mx : ProbComp α)
    {ob₁ ob₂ : α → ProbComp β} (y : β)
    (h : ∀ x, Pr{let z ← ob₁ x}[z = y] = Pr{let z ← ob₂ x}[z = y]) :
    Pr{let z ← mx >>= ob₁}[z = y] = Pr{let z ← mx >>= ob₂}[z = y] :=
  probOutput_bind_congr fun x _ => h x

theorem evalDist_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) :
    finiteLaw (mx >>= f) = (finiteLaw mx).bind (fun x => finiteLaw (f x)) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact evalDist_bind_of_discrete mx f

theorem evalDist_bind_congr {α β : Type} {mx : ProbComp α}
    {ob₁ ob₂ : α → ProbComp β}
    (h : ∀ x ∈ support mx, finiteLaw (ob₁ x) = finiteLaw (ob₂ x)) :
    finiteLaw (mx >>= ob₁) = finiteLaw (mx >>= ob₂) := by
  let : MeasurableSpace β := ⊤
  exact OracleComp.evalDist_bind_congr_of_support mx ob₁ ob₂ h

theorem probEvent_coord_mOfFn {α : Type} (n : ℕ) (g : Fin n → ProbComp α)
    (_h : ∀ i, prFail (g i) = 0) (i : Fin n) (p : α → Prop) :
    Pr{let v ← Fin.mOfFn n g}[p (v i)] = Pr{let x ← g i}[p x] :=
  prEvent_coord_mOfFn n g i p fun j _ => OracleComp.prEvent_true_eq_one (g j)

theorem probFailure_drawList {α : Type} (mx : ProbComp α) (n : ℕ) :
    prFail (OracleComp.drawList mx n) = 0 := OracleComp.prFail_eq_zero _

theorem probEvent_congr' {α : Type} {p q : α → Prop} {oa oa' : ProbComp α}
    (h₁ : ∀ x ∈ support oa, p x ↔ q x) (h₂ : finiteLaw oa = finiteLaw oa') :
    Pr{let x ← oa}[p x] = Pr{let x ← oa'}[q x] := by
  rw [prEvent_congr_of_support oa p q h₁, probEvent_def, probEvent_def, h₂]

theorem probOutput_eq_zero' {α : Type} [DecidableEq α] (mx : ProbComp α) (x : α)
    (h : x ∉ finSupport mx) : Pr{let y ← mx}[y = x] = 0 := by
  apply prEvent_eq_zero_of_not_mem_support
  simpa only [mem_finSupport_iff_mem_support] using h

theorem probOutput_bind_eq_sum_finSupport {α β : Type} [DecidableEq α]
    (mx : ProbComp α) (f : α → ProbComp β) (y : β) :
    Pr{let z ← mx >>= f}[z = y] =
      ∑ x ∈ finSupport mx, Pr{let z ← mx}[z = x] * Pr{let z ← f x}[z = y] := by
  rw [OracleComp.prEvent_bind_eq_tsum]
  apply tsum_eq_sum
  intro x hx
  rw [probOutput_eq_zero' mx x hx, zero_mul]

theorem mem_support_iff {α : Type} (mx : ProbComp α) (x : α) :
    x ∈ support mx ↔ Pr{let y ← mx}[y = x] ≠ 0 :=
  OracleComp.mem_support_iff_prEvent_ne_zero mx x

theorem probOutput_pos_iff {α : Type} {mx : ProbComp α} {x : α} :
    0 < Pr{let y ← mx}[y = x] ↔ x ∈ support mx := by
  rw [mem_support_iff, pos_iff_ne_zero]

theorem probOutput_pos {α : Type} (mx : ProbComp α) (x : α) (h : x ∈ support mx) :
    0 < Pr{let y ← mx}[y = x] := probOutput_pos_iff.mpr h

theorem mem_support_of_probOutput_pos {α : Type} {mx : ProbComp α} {x : α}
    (h : 0 < Pr{let y ← mx}[y = x]) : x ∈ support mx := probOutput_pos_iff.mp h

theorem sum_finSupport_probOutput_of_liftM_PMF {α : Type} [DecidableEq α]
    (mx : ProbComp α) : ∑ x ∈ finSupport mx, Pr{let y ← mx}[y = x] = 1 := by
  rw [← OracleComp.tsum_prEvent_eq_one mx]
  symm
  exact tsum_eq_sum fun x hx => probOutput_eq_zero' mx x hx

theorem probOutput_seq_map_eq_tsum_ite {α β γ : Type} [DecidableEq γ]
    (mx : ProbComp α) (my : ProbComp β) (f : α → β → γ) (z : γ) :
    Pr{let w ← f <$> mx <*> my}[w = z] =
      ∑' x, ∑' y, if z = f x y then
        Pr{let w ← mx}[w = x] * Pr{let w ← my}[w = y] else 0 := by
  classical
  simp only [seq_eq_bind_map, bind_map_left, OracleComp.prEvent_bind_eq_tsum, prEvent_map]
  apply tsum_congr
  intro x
  rw [OracleComp.prEvent_eq_tsum_ite my (fun y => f x y = z), ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  split_ifs <;> simp_all [eq_comm]

theorem probOutput_seq_map_prod_mk_eq_mul {α β : Type}
    (mx : ProbComp α) (my : ProbComp β) (z : α × β) :
    Pr{let w ← Prod.mk <$> mx <*> my}[w = z] =
      Pr{let x ← mx}[x = z.1] * Pr{let y ← my}[y = z.2] := by
  rcases z with ⟨a, b⟩
  simp only [seq_eq_bind_map, bind_map_left]
  simpa only [map_bind, Functor.map_map, Function.comp_def, Prod.mk.injEq] using
    prEvent_bind_bind_and mx my (fun x => x = a) (fun y => y = b)

theorem probOutput_bind_bind_swap {α β γ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → ProbComp γ) (z : γ) :
    Pr{let w ← mx >>= fun x => my >>= fun y => f x y}[w = z] =
      Pr{let w ← my >>= fun y => mx >>= fun x => f x y}[w = z] :=
  evalDist_ext_iff.mp (evalDist_bind_bind_swap mx my f) z

theorem probEvent_mono'' {α : Type} {mx : ProbComp α} {p q : α → Prop}
    (h : ∀ x, p x → q x) : Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] :=
  prEvent_mono mx p q h

theorem evalDist_map_fst_uniformSample_prod {α β : Type}
    [SampleableType α] [SampleableType β] :
    finiteLaw (Prod.fst <$> ($ᵗ (α × β) : ProbComp _)) = finiteLaw ($ᵗ α) := by
  apply evalDist_ext
  intro x
  simpa only [prEvent_map] using SampleableType.prEvent_uniformSample_fst (β := β) (· = x)

theorem mem_support_iff_of_evalDist_eq {α : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (x : α) : x ∈ support mx ↔ x ∈ support my := by
  rw [mem_support_iff, mem_support_iff, evalDist_ext_iff.mp h x]

end lweCKA
