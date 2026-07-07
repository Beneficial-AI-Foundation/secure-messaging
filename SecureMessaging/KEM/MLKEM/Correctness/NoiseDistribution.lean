/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Support
import LatticeCrypto.MLKEM.Concrete.Encoding
import SecureMessaging.KEM.MLKEM.Correctness.Noise

/-!
# Exact coefficient-noise laws for the ML-KEM failure certificate

This file defines finite integer-valued mass laws on `ℤ` and composes the
per-coefficient decryption-noise law that the failure certificate evaluates.
The composition follows the decryption-noise identity
`w − μ = eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u` (`kpkeDecryptDifference_eq_noise`):
`k·n` coefficient products for each transposed-vector product, and one additive
term for the `v` component.

The laws are exact counting measures. `cbdLaw η` counts the `4^η` bit samples
of `CBD_η` by centered binomial value. `compressionErrorLaw d` counts the `q`
residues by their `Compress_d` round-trip error. `coefficientNoiseLaw` composes
them with convolution (`*`, the law of an independent sum) and `prodLaw` (the
law of an independent product). `foldedNoiseLaw` reduces the integer law into
`ZMod q`, and `decodeFailureMass` sums the folded masses against the exact
per-bit `Compress₁` decode-failure weights.

Every law here is a definition. No statement in this file relates these laws to
the honest sampler.
-/

open LatticeCrypto

namespace MLKEM

/-- An integer-valued mass law on `ℤ`: finitely many integers carrying natural
masses. Multiplication is additive convolution: `F * G` assigns to `v` the sums of
`F a * G b` over `a + b = v`, the mass law of a sum of independent draws, and
`F ^ n` is the law of an `n`-fold sum of independent draws. -/
abbrev IntLaw := AddMonoidAlgebra ℕ ℤ

/-- The law `F` has all its mass inside `[lo, hi]`. -/
def LawWindow (F : IntLaw) (lo hi : ℤ) : Prop :=
  ∀ v : ℤ, F v ≠ 0 → lo ≤ v ∧ v ≤ hi

/-- A window may be widened. -/
theorem LawWindow.mono {F : IntLaw} {lo hi lo' hi' : ℤ} (h : LawWindow F lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : LawWindow F lo' hi' := fun v hv =>
  ⟨hlo.trans (h v hv).1, (h v hv).2.trans hhi⟩

/-- A windowed law vanishes outside its window. -/
theorem LawWindow.apply_eq_zero {F : IntLaw} {lo hi : ℤ} (h : LawWindow F lo hi)
    {v : ℤ} (hv : v < lo ∨ hi < v) : F v = 0 := by
  by_contra hne
  rcases h v hne with ⟨h1, h2⟩
  omega

/-! ## Counting laws -/

/-- The mass law of the value map `g` under counting over `range N`: the mass of
`v` is the number of `x < N` with `g x = v`. -/
noncomputable def enumLaw (N : ℕ) (g : ℕ → ℤ) : IntLaw :=
  ∑ x ∈ Finset.range N, AddMonoidAlgebra.single (g x) 1

/-- The mass of `v` under `enumLaw N g` counts the preimages of `v`. -/
theorem enumLaw_apply (N : ℕ) (g : ℕ → ℤ) (v : ℤ) :
    enumLaw N g v = ((Finset.range N).filter fun x => g x = v).card := by
  rw [Finset.card_filter]
  refine (Finsupp.finsetSum_apply _ _ _).trans (Finset.sum_congr rfl fun x _ => ?_)
  exact Finsupp.single_apply

/-- A law of enumerated values is windowed by pointwise bounds on the values. -/
theorem lawWindow_enumLaw {N : ℕ} {g : ℕ → ℤ} {lo hi : ℤ}
    (h : ∀ x < N, lo ≤ g x ∧ g x ≤ hi) : LawWindow (enumLaw N g) lo hi := by
  intro v hv
  rw [enumLaw_apply] at hv
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hv
  rw [Finset.mem_filter, Finset.mem_range] at hx
  exact hx.2 ▸ h x hx.1

/-! ## Total mass -/

/-- The total mass of a law. -/
def totalMass (F : IntLaw) : ℕ :=
  Finsupp.sum F fun _ m => m

theorem totalMass_single (v : ℤ) (m : ℕ) :
    totalMass (AddMonoidAlgebra.single v m) = m :=
  Finsupp.sum_single_index rfl

/-- Total mass, as an additive monoid homomorphism. -/
def totalMassHom : IntLaw →+ ℕ where
  toFun := totalMass
  map_zero' := rfl
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

theorem totalMass_mul (F G : IntLaw) :
    totalMass (F * G) = totalMass F * totalMass G := by
  rw [AddMonoidAlgebra.mul_def]
  refine (map_finsuppSum totalMassHom _ _).trans ?_
  have hinner : ∀ (a : ℤ) (m : ℕ),
      (Finsupp.sum G fun b k => totalMass (AddMonoidAlgebra.single (a + b) (m * k))) =
        m * totalMass G := by
    intro a m
    refine (Finsupp.sum_congr fun b _ => totalMass_single _ _).trans ?_
    exact (Finsupp.mul_sum _ _).symm
  calc (Finsupp.sum F fun a m =>
          totalMassHom (Finsupp.sum G fun b k => AddMonoidAlgebra.single (a + b) (m * k)))
      = Finsupp.sum F fun a m => m * totalMass G := by
        refine Finsupp.sum_congr fun a _ => ?_
        refine (map_finsuppSum totalMassHom _ _).trans ?_
        exact hinner a _
    _ = totalMass F * totalMass G := (Finsupp.sum_mul _ _).symm

theorem totalMass_one : totalMass (1 : IntLaw) = 1 := by
  rw [AddMonoidAlgebra.one_def]
  exact totalMass_single 0 1

theorem totalMass_pow (F : IntLaw) (n : ℕ) :
    totalMass (F ^ n) = totalMass F ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, totalMass_one]
  | succ n ih => rw [pow_succ, pow_succ, totalMass_mul, ih]

theorem totalMass_enumLaw (N : ℕ) (g : ℕ → ℤ) : totalMass (enumLaw N g) = N := by
  rw [enumLaw]
  refine (map_sum totalMassHom _ _).trans ?_
  have : ∀ x ∈ Finset.range N, totalMassHom (AddMonoidAlgebra.single (g x) 1) = 1 :=
    fun x _ => totalMass_single _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-! ## Windows of convolutions, powers, and products -/

theorem lawWindow_mul {F G : IntLaw} {lo₁ hi₁ lo₂ hi₂ : ℤ}
    (hF : LawWindow F lo₁ hi₁) (hG : LawWindow G lo₂ hi₂) :
    LawWindow (F * G) (lo₁ + lo₂) (hi₁ + hi₂) := by
  intro v hv
  have hmem := AddMonoidAlgebra.support_mul F G (Finsupp.mem_support_iff.mpr hv)
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hmem
  have h₁ := hF a (Finsupp.mem_support_iff.mp ha)
  have h₂ := hG b (Finsupp.mem_support_iff.mp hb)
  exact ⟨add_le_add h₁.1 h₂.1, add_le_add h₁.2 h₂.2⟩

theorem lawWindow_pow {F : IntLaw} {lo hi : ℤ} (hF : LawWindow F lo hi) (n : ℕ) :
    LawWindow (F ^ n) (n * lo) (n * hi) := by
  induction n with
  | zero =>
    intro v hv
    rw [pow_zero, AddMonoidAlgebra.one_def] at hv
    have : v = 0 := by
      by_contra hne
      exact hv (Finsupp.single_eq_of_ne fun h => hne h)
    simp [this]
  | succ n ih =>
    have h := lawWindow_mul ih hF
    have hlo : (n : ℤ) * lo + lo = ((n + 1 : ℕ) : ℤ) * lo := by push_cast; ring
    have hhi : (n : ℤ) * hi + hi = ((n + 1 : ℕ) : ℤ) * hi := by push_cast; ring
    rw [hlo, hhi] at h
    exact fun v hv => h v (by rwa [pow_succ] at hv)

/-! ## Windowed convolution values -/

/-- The value of a convolution over a window of the left factor: with `F` inside
`[lo, lo + n - 1]`, the mass of `F * G` at `v` is the window sum of
`F (lo + i) * G (v - (lo + i))`. -/
theorem mul_apply_window {F G : IntLaw} {lo : ℤ} {n : ℕ}
    (hF : LawWindow F lo (lo + n - 1)) (v : ℤ) :
    (F * G) v = ∑ i ∈ Finset.range n, F (lo + i) * G (v - (lo + i)) := by
  rw [AddMonoidAlgebra.mul_apply]
  have hinner : ∀ (a : ℤ) (m : ℕ),
      (Finsupp.sum G fun b k => if a + b = v then m * k else 0) = m * G (v - a) := by
    intro a m
    have hcong : (fun (b : ℤ) (k : ℕ) => if a + b = v then m * k else 0) =
        fun b k => if b = v - a then m * k else 0 := by
      funext b k
      exact if_congr (by omega) rfl rfl
    rw [hcong, Finsupp.sum_ite_eq' G (v - a) fun _ k => m * k]
    by_cases hmem : v - a ∈ G.support
    · rw [if_pos hmem]
    · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem, mul_zero]
  rw [Finsupp.sum_congr (g2 := fun a m => m * G (v - a)) fun a _ => hinner a (F a)]
  rw [Finsupp.sum_of_support_subset F (s := (Finset.range n).image fun i : ℕ => lo + (i : ℤ))
    ?_ (fun a m => m * G (v - a)) fun i _ => zero_mul _]
  · rw [Finset.sum_image fun i _ j _ h => by omega]
  · intro a ha
    have hw := hF a (Finsupp.mem_support_iff.mp ha)
    rw [Finset.mem_image]
    exact ⟨(a - lo).toNat, Finset.mem_range.mpr (by omega), by omega⟩

/-! ## Product laws -/

/-- The product law of two mass laws: `prodLaw F G` assigns to `v` the sums of
`F a * G b` over `a * b = v`, the mass law of a product of independent draws. -/
noncomputable def prodLaw (F G : IntLaw) : IntLaw :=
  Finsupp.sum F fun a m => Finsupp.sum G fun b k => AddMonoidAlgebra.single (a * b) (m * k)

theorem totalMass_prodLaw (F G : IntLaw) :
    totalMass (prodLaw F G) = totalMass F * totalMass G := by
  rw [prodLaw]
  refine (map_finsuppSum totalMassHom _ _).trans ?_
  calc (Finsupp.sum F fun a m =>
          totalMassHom (Finsupp.sum G fun b k => AddMonoidAlgebra.single (a * b) (m * k)))
      = Finsupp.sum F fun a m => m * totalMass G := by
        refine Finsupp.sum_congr fun a _ => ?_
        refine (map_finsuppSum totalMassHom _ _).trans ?_
        refine (Finsupp.sum_congr fun b _ => totalMass_single _ _).trans ?_
        exact (Finsupp.mul_sum _ _).symm
    _ = totalMass F * totalMass G := (Finsupp.sum_mul _ _).symm

/-- The mass of `v` under a product law, as a double sum over the factors. -/
theorem prodLaw_apply (F G : IntLaw) (v : ℤ) :
    prodLaw F G v =
      Finsupp.sum F fun a m => Finsupp.sum G fun b k =>
        if a * b = v then m * k else 0 := by
  rw [prodLaw]
  refine (Finsupp.sum_apply).trans (Finsupp.sum_congr fun a _ => ?_)
  refine (Finsupp.sum_apply).trans (Finsupp.sum_congr fun b _ => ?_)
  exact Finsupp.single_apply

/-- Any nonzero mass of a product law decomposes as a product of masses. -/
theorem exists_of_prodLaw_apply_ne_zero {F G : IntLaw} {v : ℤ}
    (hv : prodLaw F G v ≠ 0) : ∃ a b, F a ≠ 0 ∧ G b ≠ 0 ∧ a * b = v := by
  rw [prodLaw_apply, Finsupp.sum] at hv
  obtain ⟨a, ha, hane⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  rw [Finsupp.sum] at hane
  obtain ⟨b, hb, hbne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hane
  refine ⟨a, b, Finsupp.mem_support_iff.mp ha, Finsupp.mem_support_iff.mp hb, ?_⟩
  by_contra hne
  exact hbne (if_neg hne)

/-- A product of symmetrically windowed laws is windowed by the product bound. -/
theorem lawWindow_prodLaw {F G : IntLaw} {a b : ℤ}
    (hF : LawWindow F (-a) a) (hG : LawWindow G (-b) b) :
    LawWindow (prodLaw F G) (-(a * b)) (a * b) := by
  intro v hv
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_of_prodLaw_apply_ne_zero hv
  have h₁ := hF x hx
  have h₂ := hG y hy
  have habs : |x * y| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨h₁.1, h₁.2⟩) (abs_le.mpr ⟨h₂.1, h₂.2⟩) (abs_nonneg y)
      ((abs_nonneg x).trans (abs_le.mpr ⟨h₁.1, h₁.2⟩))
  exact abs_le.mp habs

/-! ## Component laws -/

/-- The centered binomial value of a `2η`-bit sample `x`: the number of set bits
among the low `η` bits minus the number among the next `η` bits (FIPS 203,
Algorithm 8). -/
def cbdValue (η x : ℕ) : ℤ :=
  ((∑ j ∈ Finset.range η, (x >>> j) % 2 : ℕ) : ℤ) -
    ((∑ j ∈ Finset.range η, (x >>> (η + j)) % 2 : ℕ) : ℤ)

/-- The centered binomial law `CBD_η`, counting the `4^η` equally likely bit
samples by their centered binomial value. -/
noncomputable def cbdLaw (η : ℕ) : IntLaw := enumLaw (4 ^ η) (cbdValue η)

theorem lawWindow_cbdLaw_two : LawWindow (cbdLaw 2) (-2) 2 :=
  lawWindow_enumLaw (by decide)

theorem lawWindow_cbdLaw_three : LawWindow (cbdLaw 3) (-3) 3 :=
  lawWindow_enumLaw (by decide)

/-- The `Compress_d` round-trip error of the residue `x`: the centered
representative of `Decompress_d (Compress_d x) - x`. -/
def compressionError (d x : ℕ) : ℤ :=
  centeredRepr (Concrete.decompress d (Concrete.compress d (x : Coeff)) - (x : Coeff))

/-- The compression-error law: the `Compress_d` round-trip error under counting
over the `q` residues. -/
noncomputable def compressionErrorLaw (d : ℕ) : IntLaw :=
  enumLaw modulus (compressionError d)

theorem lawWindow_compressionErrorLaw_four :
    LawWindow (compressionErrorLaw 4) (-104) 104 :=
  lawWindow_enumLaw (by decide +kernel)

theorem lawWindow_compressionErrorLaw_five :
    LawWindow (compressionErrorLaw 5) (-52) 52 :=
  lawWindow_enumLaw (by decide +kernel)

theorem lawWindow_compressionErrorLaw_ten :
    LawWindow (compressionErrorLaw 10) (-2) 2 :=
  lawWindow_enumLaw (by decide +kernel)

theorem lawWindow_compressionErrorLaw_eleven :
    LawWindow (compressionErrorLaw 11) (-1) 1 :=
  lawWindow_enumLaw (by decide +kernel)

/-! ## The certificate coefficient-noise law -/

/-- The law of one coefficient product in `eᵀy`, as composed here: a product of
two independent `CBD_{η₁}` draws. -/
noncomputable def keyNoiseProductLaw (p : ParameterSet) : IntLaw :=
  prodLaw (cbdLaw p.params.eta1) (cbdLaw p.params.eta1)

/-- The law of one coefficient product in `sᵀ(e₁ + ε_u)`, as composed here: a
product of an independent `CBD_{η₁}` draw with an independent sum of a
`CBD_{η₂}` draw and a `Compress_{d_u}` round-trip error. -/
noncomputable def ciphertextNoiseProductLaw (p : ParameterSet) : IntLaw :=
  prodLaw (cbdLaw p.params.eta1)
    (cbdLaw p.params.eta2 * compressionErrorLaw p.params.du)

/-- The law of the additive noise `e₂ + ε_v`, as composed here: an independent
sum of a `CBD_{η₂}` draw and a `Compress_{d_v}` round-trip error. -/
noncomputable def additiveNoiseLaw (p : ParameterSet) : IntLaw :=
  cbdLaw p.params.eta2 * compressionErrorLaw p.params.dv

/-- The certificate law of one coefficient of the decryption noise: `k·n`
independent products for each of the two transposed-vector products, and one
additive noise term. Whether the honest per-coordinate noise law equals this
law is not stated here. -/
noncomputable def coefficientNoiseLaw (p : ParameterSet) : IntLaw :=
  keyNoiseProductLaw p ^ (p.params.k * ringDegree) *
    ciphertextNoiseProductLaw p ^ (p.params.k * ringDegree) *
    additiveNoiseLaw p

/-- The coefficient-noise law folded into `ZMod q`, matching reduction of the
integer noise into the coefficient ring. -/
noncomputable def foldedNoiseLaw (p : ParameterSet) : ZMod modulus →₀ ℕ :=
  Finsupp.mapDomain (fun v : ℤ => (v : ZMod modulus)) (coefficientNoiseLaw p)

/-- The number of message bits (0, 1, or 2 of them) whose encoded coefficient is
decoded wrongly by `Compress₁` after adding the noise residue `r`. -/
def decodeFailureWeight (r : Coeff) : ℕ :=
  (if Concrete.compress 1 (Concrete.decompress 1 0 + r) ≠ 0 then 1 else 0) +
    (if Concrete.compress 1 (Concrete.decompress 1 1 + r) ≠ 1 then 1 else 0)

theorem decodeFailureWeight_le_two (r : Coeff) : decodeFailureWeight r ≤ 2 := by
  rw [decodeFailureWeight]
  split <;> split <;> omega

/-- The bit-summed decode-failure mass of the folded coefficient-noise law. Over
a uniform message bit, the decode-failure probability of the law defined here is
this mass divided by twice the total mass. -/
noncomputable def decodeFailureMass (p : ParameterSet) : ℕ :=
  ∑ r : Coeff, foldedNoiseLaw p r * decodeFailureWeight r

/-- The total mass of the certificate coefficient-noise law. -/
noncomputable def noiseDenominator (p : ParameterSet) : ℕ :=
  totalMass (coefficientNoiseLaw p)

/-! ## Per-parameter-set windows and totals -/

theorem noiseDenominator_mlkem512 :
    noiseDenominator .MLKEM512 = 2 ^ 11268 * 3329 ^ 513 := by
  simp only [noiseDenominator, coefficientNoiseLaw, keyNoiseProductLaw,
    ciphertextNoiseProductLaw, additiveNoiseLaw, ParameterSet.params, cbdLaw,
    compressionErrorLaw, totalMass_mul, totalMass_pow, totalMass_prodLaw,
    totalMass_enumLaw, ringDegree, modulus]
  decide +kernel

theorem noiseDenominator_mlkem768 :
    noiseDenominator .MLKEM768 = 2 ^ 12292 * 3329 ^ 769 := by
  simp only [noiseDenominator, coefficientNoiseLaw, keyNoiseProductLaw,
    ciphertextNoiseProductLaw, additiveNoiseLaw, ParameterSet.params, cbdLaw,
    compressionErrorLaw, totalMass_mul, totalMass_pow, totalMass_prodLaw,
    totalMass_enumLaw, ringDegree, modulus]
  decide +kernel

theorem noiseDenominator_mlkem1024 :
    noiseDenominator .MLKEM1024 = 2 ^ 16388 * 3329 ^ 1025 := by
  simp only [noiseDenominator, coefficientNoiseLaw, keyNoiseProductLaw,
    ciphertextNoiseProductLaw, additiveNoiseLaw, ParameterSet.params, cbdLaw,
    compressionErrorLaw, totalMass_mul, totalMass_pow, totalMass_prodLaw,
    totalMass_enumLaw, ringDegree, modulus]
  decide +kernel

theorem lawWindow_coefficientNoiseLaw_mlkem512 :
    LawWindow (coefficientNoiseLaw .MLKEM512) (-10858) 10858 := by
  have h1 : LawWindow (keyNoiseProductLaw .MLKEM512) (-9) 9 := by
    have := lawWindow_prodLaw lawWindow_cbdLaw_three lawWindow_cbdLaw_three
    norm_num at this
    exact this
  have h2 : LawWindow (ciphertextNoiseProductLaw .MLKEM512) (-12) 12 := by
    have hin := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_ten
    norm_num at hin
    have hin' : LawWindow (cbdLaw 2 * compressionErrorLaw 10) (-4) 4 := hin
    have := lawWindow_prodLaw lawWindow_cbdLaw_three hin'
    norm_num at this
    exact this
  have h3 : LawWindow (additiveNoiseLaw .MLKEM512) (-106) 106 := by
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_four
    norm_num at this
    exact this
  have hc1 := lawWindow_pow h1 (2 * 256)
  have hc2 := lawWindow_pow h2 (2 * 256)
  norm_num at hc1 hc2
  have := lawWindow_mul (lawWindow_mul hc1 hc2) h3
  norm_num at this
  exact this

theorem lawWindow_coefficientNoiseLaw_mlkem768 :
    LawWindow (coefficientNoiseLaw .MLKEM768) (-9322) 9322 := by
  have h1 : LawWindow (keyNoiseProductLaw .MLKEM768) (-4) 4 := by
    have := lawWindow_prodLaw lawWindow_cbdLaw_two lawWindow_cbdLaw_two
    norm_num at this
    exact this
  have h2 : LawWindow (ciphertextNoiseProductLaw .MLKEM768) (-8) 8 := by
    have hin := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_ten
    norm_num at hin
    have hin' : LawWindow (cbdLaw 2 * compressionErrorLaw 10) (-4) 4 := hin
    have := lawWindow_prodLaw lawWindow_cbdLaw_two hin'
    norm_num at this
    exact this
  have h3 : LawWindow (additiveNoiseLaw .MLKEM768) (-106) 106 := by
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_four
    norm_num at this
    exact this
  have hc1 := lawWindow_pow h1 (3 * 256)
  have hc2 := lawWindow_pow h2 (3 * 256)
  norm_num at hc1 hc2
  have := lawWindow_mul (lawWindow_mul hc1 hc2) h3
  norm_num at this
  exact this

theorem lawWindow_coefficientNoiseLaw_mlkem1024 :
    LawWindow (coefficientNoiseLaw .MLKEM1024) (-10294) 10294 := by
  have h1 : LawWindow (keyNoiseProductLaw .MLKEM1024) (-4) 4 := by
    have := lawWindow_prodLaw lawWindow_cbdLaw_two lawWindow_cbdLaw_two
    norm_num at this
    exact this
  have h2 : LawWindow (ciphertextNoiseProductLaw .MLKEM1024) (-6) 6 := by
    have hin := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_eleven
    norm_num at hin
    have hin' : LawWindow (cbdLaw 2 * compressionErrorLaw 11) (-3) 3 := hin
    have := lawWindow_prodLaw lawWindow_cbdLaw_two hin'
    norm_num at this
    exact this
  have h3 : LawWindow (additiveNoiseLaw .MLKEM1024) (-54) 54 := by
    have := lawWindow_mul lawWindow_cbdLaw_two lawWindow_compressionErrorLaw_five
    norm_num at this
    exact this
  have hc1 := lawWindow_pow h1 (4 * 256)
  have hc2 := lawWindow_pow h2 (4 * 256)
  norm_num at hc1 hc2
  have := lawWindow_mul (lawWindow_mul hc1 hc2) h3
  norm_num at this
  exact this

end MLKEM
