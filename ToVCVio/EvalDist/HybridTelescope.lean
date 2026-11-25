/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Hybrid telescope over an exposure index

A hybrid argument over games `H 0, H 1, …, H L` usually bounds `Pr_{H 0}[X] - Pr_{H L}[X]` by
the sum of the gaps between neighbouring games. Some proofs can bound a gap only on the runs
where an index `f` is large, for example where the adversary learns no state below position
`j`. `prEvent_hybrid_telescope` splits `X` along the value `v = f(x) ∈ {0, …, L}`:
```text
Pr_{H 0}[X] = Σ_{v ≤ L} Pr_{H v}[X ∧ f = v]
            + Σ_{j < L} (Pr_{H j}[X ∧ j + 1 ≤ f] - Pr_{H (j+1)}[X ∧ j + 1 ≤ f])
```
The run with `f = v` is moved to game `H v`, and the gap between `H j` and `H (j + 1)` only
counts runs with `f ≥ j + 1`. The games need not share a probability space.

This is the bookkeeping behind the Bellare-Yee proof of forward-secure PRGs with an
adaptive break-in, with the break-in position as `f`.

- [BY03] Bellare, Yee. *Forward-Security in Private-Key Cryptography.* CT-RSA 2003.
-/

@[expose] public section

open OracleComp ENNReal

namespace ToVCVio

/-- Let `p j v` be reals for `j, v ≤ L`. Then
```text
Σ_{v ≤ L} p 0 v = Σ_{v ≤ L} p v v + Σ_{j < L} Σ_{j < v ≤ L} (p j v - p (j + 1) v)
``` -/
theorem sum_range_eq_sum_diag_add_sum_sub (p : ℕ → ℕ → ℝ) (L : ℕ) :
    ∑ v ∈ Finset.range (L + 1), p 0 v =
      ∑ v ∈ Finset.range (L + 1), p v v +
        ∑ j ∈ Finset.range L, ∑ v ∈ Finset.Ico (j + 1) (L + 1), (p j v - p (j + 1) v) := by
  have h : ∀ v, p 0 v = p v v + ∑ j ∈ Finset.range v, (p j v - p (j + 1) v) := by
    intro v
    rw [Finset.sum_range_sub' (fun j => p j v)]
    ring
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm' fun v j => by
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

variable {α : Type}

/-- Let `f ≤ L` on every outcome. Then for `j ≤ L + 1`, the probability of `X ∧ j ≤ f` is the
sum over `j ≤ v ≤ L` of the probabilities of `X ∧ f = v`. -/
theorem prEvent_and_le_eq_sum (mx : ProbComp α) (X : α → Prop) (f : α → ℕ) (L : ℕ)
    (hf : ∀ x, f x ≤ L) (j : ℕ) (hj : j ≤ L + 1) :
    Pr{let x ← mx}[X x ∧ j ≤ f x] =
      ∑ v ∈ Finset.Ico j (L + 1), Pr{let x ← mx}[X x ∧ f x = v] := by
  induction h : L + 1 - j generalizing j with
  | zero =>
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact prEvent_eq_zero_of_forall_not _ _ fun x hx => by have := hf x; have := hx.2; omega
  | succ n ih =>
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), ← ih (j + 1) (by omega) (by omega),
      prEvent_eq_prEvent_and_add_prEvent_and_not mx _ fun x => f x = j]
    congr 1
    · exact prEvent_congr_of_support mx _ _ fun x _ =>
        ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.ge⟩, h.2⟩⟩
    · exact prEvent_congr_of_support mx _ _ fun x _ =>
        ⟨fun h => ⟨h.1.1, by have := h.1.2; have := h.2; omega⟩,
          fun h => ⟨⟨h.1, by have := h.2; omega⟩, by have := h.2; omega⟩⟩

/-- **Hybrid telescope over an exposure index.** Let `H 0, …, H L` be games with outcomes in
`α`, let `X` be an event, and let `f ≤ L` on every outcome. Then
```text
Pr_{H 0}[X] = Σ_{v ≤ L} Pr_{H v}[X ∧ f = v]
            + Σ_{j < L} (Pr_{H j}[X ∧ j + 1 ≤ f] - Pr_{H (j+1)}[X ∧ j + 1 ≤ f])
``` -/
theorem prEvent_hybrid_telescope (H : ℕ → ProbComp α) (X : α → Prop) (f : α → ℕ) (L : ℕ)
    (hf : ∀ x, f x ≤ L) :
    (Pr{let x ← H 0}[X x]).toReal =
      ∑ v ∈ Finset.range (L + 1), (Pr{let x ← H v}[X x ∧ f x = v]).toReal +
        ∑ j ∈ Finset.range L, ((Pr{let x ← H j}[X x ∧ j + 1 ≤ f x]).toReal -
          (Pr{let x ← H (j + 1)}[X x ∧ j + 1 ≤ f x]).toReal) := by
  have hsplit : ∀ i j, j ≤ L + 1 → (Pr{let x ← H i}[X x ∧ j ≤ f x]).toReal =
      ∑ v ∈ Finset.Ico j (L + 1), (Pr{let x ← H i}[X x ∧ f x = v]).toReal := by
    intro i j hj
    rw [prEvent_and_le_eq_sum _ X f L hf j hj,
      ENNReal.toReal_sum fun _ _ => prEvent_ne_top _]
  have h0 : (Pr{let x ← H 0}[X x]).toReal =
      ∑ v ∈ Finset.range (L + 1), (Pr{let x ← H 0}[X x ∧ f x = v]).toReal := by
    rw [Finset.range_eq_Ico, ← hsplit 0 0 (by omega)]
    congr 1
    exact prEvent_congr_of_support _ _ _ fun x _ => ⟨fun h => ⟨h, Nat.zero_le _⟩, And.left⟩
  rw [h0, sum_range_eq_sum_diag_add_sum_sub
    (fun j v => (Pr{let x ← H j}[X x ∧ f x = v]).toReal) L]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [hsplit j (j + 1) (by omega), hsplit (j + 1) (j + 1) (by omega), Finset.sum_sub_distrib]

end ToVCVio
