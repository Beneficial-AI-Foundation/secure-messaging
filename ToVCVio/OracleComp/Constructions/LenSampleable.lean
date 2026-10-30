/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Uniform sampling by length

`LenSampleable C` gives each element of `C` a length and samples uniformly among the elements
of a given length. The ideal branch of an ind$ game uses it to return a random ciphertext of the
same length as the real one, as the `$` oracle of [NRS14] Figure 4 does ("`|C|` random bits").

Instances:

* `LenSampleable.const`: one length for the whole type, so `unifOfLen` is `$ᵗ C`. Not an
  instance, because it would overlap with the instances below. `BitVec n` uses it.
* `C × T`: the length of `(c, t)` is the length of `c`, and `T` is sampled uniformly. This is
  the shape of a ciphertext with a fixed-size tag.
* `(n : ℕ) × BitVec n`: bit strings of every length, with `len = Sigma.fst`.

[NRS14] Namprempre, Rogaway, Shrimpton. *Reconsidering Generic Composition.* EUROCRYPT 2014.
-/

@[expose] public section

open OracleComp ENNReal

/-- A type whose elements have a length, with a uniform sampler for each length that occurs.

`unifOfLen (len c)` is uniform on `{c' | len c' = len c}`: its outputs have length `len c`, and
any two elements of that length have the same probability.

`len` is the leakage that an ind$ game allows. The laws make the sample uniform within each
length class. They do not restrict the choice of `len`: if `len` is injective, every class has
one element, and the sample is that element. -/
class LenSampleable (C : Type) where
  /-- The length of an element. -/
  len : C → ℕ
  /-- A uniform sample among the elements of length `n`. Only lengths that occur matter. -/
  unifOfLen : ℕ → ProbComp C
  /-- Every output of `unifOfLen (len c)` has length `len c`. -/
  len_eq_of_mem_support : ∀ c c', c' ∈ support (unifOfLen (len c)) → len c' = len c
  /-- Elements of the same length have the same probability. -/
  prEvent_eq : ∀ c c', len c' = len c →
    Pr{let x ← unifOfLen (len c)}[x = c'] = Pr{let x ← unifOfLen (len c)}[x = c]

namespace LenSampleable

/-- A uniform sample among the elements with the same length as `c`. -/
abbrev unifSameLen {C : Type} [LenSampleable C] (c : C) : ProbComp C := unifOfLen (len c)

/-- The constant grading: every element has length `0`, and `unifOfLen` is `$ᵗ C`. With this
grading, an ind$ game samples from the whole type. -/
@[reducible] def const (C : Type) [SampleableType C] : LenSampleable C where
  len _ := 0
  unifOfLen _ := $ᵗ C
  len_eq_of_mem_support _ _ _ := rfl
  prEvent_eq c c' _ := by
    let : Fintype C := Fintype.ofFinite C
    rw [SampleableType.prEvent_uniformSample_eq_singleton,
      SampleableType.prEvent_uniformSample_eq_singleton]

/-- With the constant grading, the sampler is `$ᵗ C`. -/
@[simp] lemma unifSameLen_const {C : Type} [SampleableType C] (c : C) :
    @unifSameLen C (const C) c = $ᵗ C := rfl

/-- `BitVec n` has one length, so its sampler is `$ᵗ BitVec n`. -/
instance instBitVec (n : ℕ) : LenSampleable (BitVec n) := const (BitVec n)

/-- A pair `(c, t)` with a fixed-size second component has the length of `c`. The sampler draws
`c` by length and `t` uniformly. -/
instance instProd (C T : Type) [LenSampleable C] [SampleableType T] :
    LenSampleable (C × T) where
  len p := len p.1
  unifOfLen n := do
    let c ← unifOfLen n
    let t ← $ᵗ T
    pure (c, t)
  len_eq_of_mem_support p p' h := by
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
    obtain ⟨c, hc, t, -, rfl⟩ := h
    exact len_eq_of_mem_support p.1 c hc
  prEvent_eq p p' h := by
    let : Fintype T := Fintype.ofFinite T
    have key : ∀ q : C × T, len q.1 = len p.1 →
        Pr{let x ← (do let c ← unifOfLen (len p.1); let t ← $ᵗ T; pure (c, t))}[x = q] =
          (Fintype.card T : ℝ≥0∞)⁻¹ * Pr{let x ← unifOfLen (len p.1)}[x = q.1] := by
      intro q _
      have := prEvent_bind_and_eq_mul (unifOfLen (len p.1)) (fun _ => ($ᵗ T : ProbComp T))
        (· = q.2) (· = q.1) (c := (Fintype.card T : ℝ≥0∞)⁻¹)
        (fun _ => SampleableType.prEvent_uniformSample_eq_singleton q.2)
      simpa only [prEvent_norm, bind_assoc, pure_bind, Prod.ext_iff, and_comm] using this
    rw [key p' h, key p rfl, prEvent_eq p.1 p'.1 h]

/-- The sampler for a pair draws the first component by length and the second uniformly. -/
@[simp] lemma unifSameLen_prod {C T : Type} [LenSampleable C] [SampleableType T] (c : C) (t : T) :
    unifSameLen (c, t) = (do
      let c' ← unifSameLen c
      let t' ← $ᵗ T
      pure (c', t')) := rfl

/-- `BitVec n` has one length, so the sampler is `$ᵗ BitVec n`. -/
@[simp] lemma unifSameLen_bitVec {n : ℕ} (x : BitVec n) : unifSameLen x = $ᵗ BitVec n := rfl

/-- With the constant grading on the first component, the sampler for a pair is `$ᵗ (C × T)`. -/
lemma unifSameLen_const_prod {C T : Type} [SampleableType C] [SampleableType T] (p : C × T) :
    @unifSameLen (C × T) (@instProd C T (const C) _) p = $ᵗ (C × T) :=
  (SampleableType.uniformSample_prod_eq_bind C T).symm

/-- A pair with a `BitVec n` first component has one length, so the sampler is `$ᵗ`. -/
lemma unifSameLen_bitVec_prod {n : ℕ} {T : Type} [SampleableType T] (p : BitVec n × T) :
    unifSameLen p = $ᵗ (BitVec n × T) :=
  unifSameLen_const_prod p

/-- Bit strings of every length: the length of `⟨n, x⟩` is `n`, and the sampler for length `n`
draws `x ← $ᵗ BitVec n`. -/
instance instSigmaBitVec : LenSampleable ((n : ℕ) × BitVec n) where
  len := Sigma.fst
  unifOfLen n := (⟨n, ·⟩) <$> ($ᵗ BitVec n)
  len_eq_of_mem_support c c' h := by
    simp only [support_map, Set.mem_image] at h
    obtain ⟨x, -, rfl⟩ := h
    rfl
  prEvent_eq c c' h := by
    obtain ⟨n, x⟩ := c
    obtain ⟨n', x'⟩ := c'
    obtain rfl : n' = n := h
    dsimp only
    have hinj (k : ℕ) : Function.Injective (fun y : BitVec k => (⟨k, y⟩ : (j : ℕ) × BitVec j)) :=
      fun _ _ hy => eq_of_heq (Sigma.mk.inj hy).2
    rw [prEvent_map_injective _ (hinj _), prEvent_map_injective _ (hinj _)]
    exact (const (BitVec _)).prEvent_eq x x' rfl

end LenSampleable
