/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.Probability.FiniteLaw
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import ToVCVio.Data.Vector.Split

/-!
# Finite tables for extendable-output functions

This file models an extendable-output function, such as SHAKE, as a finite table. The table gives
each allowed input a fixed string of `outBits` random bits. A request for `n` bits returns the
first `n` of them. Inputs whose length is not in the allowed set get zeros.
-/

@[expose] public section

namespace ToVCVio.FiniteXOF

open OracleComp

/-- Bit strings whose length belongs to the finite set of modeled input lengths. -/
abbrev Input (lengths : Finset ℕ) := (l : lengths) × Vector Bool l.val

/-- A finite table with one bounded output stream for every modeled input. -/
abbrev Table (lengths : Finset ℕ) (outBits : ℕ) :=
  Input lengths → Vector Bool outBits

/-- Package a list whose length is modeled as a finite-XOF input. -/
def encode (lengths : Finset ℕ) (x : List Bool)
    (hx : x.length ∈ lengths) : Input lengths :=
  ⟨⟨x.length, hx⟩, Vector.ofFn (fun i : Fin x.length => x[i.val])⟩

/-- Read the first `n` bits, extending with zeroes when `n` exceeds the stored stream length. -/
def «prefix» {O : ℕ} (v : Vector Bool O) (n : ℕ) : Vector Bool n :=
  Vector.ofFn fun i => if h : i.val < O then v[i.val]'h else false

/-- Answer a modeled input with its table prefix and every other input with zeroes. -/
def answer {lengths : Finset ℕ} {O : ℕ} (H : Table lengths O)
    (x : List Bool) (n : ℕ) : Vector Bool n :=
  if h : x.length ∈ lengths then «prefix» (H (encode lengths x h)) n
  else Vector.replicate n false

private noncomputable instance inputFintype (lengths : Finset ℕ) :
    Fintype (Input lengths) := Fintype.ofFinite _

private noncomputable instance tableFintype (lengths : Finset ℕ) (O : ℕ) :
    Fintype (Table lengths O) := Fintype.ofFinite _

private instance tableNonempty (lengths : Finset ℕ) (O : ℕ) :
    Nonempty (Table lengths O) :=
  ⟨fun _ => Vector.replicate O false⟩

/-- Uniformly sample the complete finite table. -/
noncomputable def sampleTable (lengths : Finset ℕ) (O : ℕ) :
    ProbComp (Table lengths O) :=
  @uniformSample _ (SampleableType.ofFintype _)

/-- Encoding preserves and reflects equality of the underlying input lists. -/
theorem encode_eq_iff (lengths : Finset ℕ) (x y : List Bool)
    (hx : x.length ∈ lengths) (hy : y.length ∈ lengths) :
    encode lengths x hx = encode lengths y hy ↔ x = y := by
  constructor
  · intro h
    have hlist := congrArg (fun z : Input lengths => z.2.toList) h
    simpa only [encode, Vector.toList_ofFn, List.ofFn_getElem] using hlist
  · intro h
    subst y
    rfl

private theorem splitAt_fst_eq_prefix (a b : ℕ) (v : Vector Bool (a + b)) :
    (Vector.splitAt v).1 = «prefix» v a := by
  apply Vector.ext
  intro i hi
  have hi' : i < a + b := by omega
  simp [«prefix», hi']

/-- A bounded prefix of a uniform stored stream is itself uniform. -/
theorem finiteLaw_prefix_uniform (O n : ℕ) (h : n ≤ O) :
    ToVCVio.finiteLaw ((fun v => «prefix» v n) <$> ($ᵗ (Vector Bool O))) =
      ToVCVio.finiteLaw ($ᵗ (Vector Bool n)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  let : MeasurableSpace (Vector Bool (n + k)) := ⊤
  let : MeasurableSpace (Vector Bool n) := ⊤
  let : MeasurableSpace (Vector Bool k) := ⊤
  let : MeasurableSpace (Vector Bool n × Vector Bool k) := ⊤
  have hsplit := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (Vector.splitAtEquiv (α := Bool) n k).bijective
  have hfst := hsplit.map (fun p : Vector Bool n × Vector Bool k => p.1)
  calc
    ToVCVio.finiteLaw
        ((fun v => «prefix» v n) <$> ($ᵗ (Vector Bool (n + k)))) =
      ToVCVio.finiteLaw
        ((fun p : Vector Bool n × Vector Bool k => p.1) <$>
          ((Vector.splitAtEquiv n k) <$> ($ᵗ (Vector Bool (n + k))))) := by
        apply congrArg ToVCVio.finiteLaw
        rw [Functor.map_map]
        apply congrArg (fun f : Vector Bool (n + k) → Vector Bool n =>
          f <$> ($ᵗ (Vector Bool (n + k))))
        funext v
        exact (splitAt_fst_eq_prefix n k v).symm
    _ = ToVCVio.finiteLaw
        ((fun p : Vector Bool n × Vector Bool k => p.1) <$>
          ($ᵗ (Vector Bool n × Vector Bool k))) := hfst.evalDist_eq
    _ = ToVCVio.finiteLaw ($ᵗ (Vector Bool n)) := by
      change 𝒟[(fun p : Vector Bool n × Vector Bool k => p.1) <$>
          ($ᵗ (Vector Bool n × Vector Bool k))] =
        𝒟[$ᵗ (Vector Bool n)]
      simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_pure] using
        (SampleableType.evalDist_uniformSample_prod_bind_fst
          (α := Vector Bool n) (β := Vector Bool k)
          (f := fun v => pure v))

end ToVCVio.FiniteXOF
