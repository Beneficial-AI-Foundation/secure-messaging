/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.UniversalHash
import ToVCVio.OracleComp.Constructions.BitVec

/-!
# Wegman-Carter authenticity: the probability core

The abstract probability statements behind `probEvent_wcInst_forge_le` (`WegmanCarter.lean`).
They are stated over an arbitrary run distribution, so that they depend on nothing but the
almost-XOR-universal (AXU) predicate of `UniversalHash.lean`.

A forgery attempt is a decryption query `(X', T')` made either before or after the adversary
sees the challenge `(X*, T*)`. The two kinds are bounded using different randomness:

* `probEvent_post_axu_le`: a post-challenge query accepts only if
  `hash H X' ⊕ hash H X* = T' ⊕ T*`, which AXU over the hash key `H` bounds by `ε`;
* `probEvent_pre_fresh_le`: a pre-challenge query is a blind guess at the not-yet-drawn
  128-bit tag mask, which succeeds with probability `2⁻¹²⁸`;
* `combine_pre_post_le`: the two are added under a single budget `q` on the number of
  decryption queries, which is what gives `q · ε` rather than `2 · q · ε`.
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace OracleComp.WegmanCarter

/-- Fix a challenge `c = (X*, T*)` and a list `l` of pairs `(X', T')` none of which equals `c`.
For a uniform key `H`, the probability that some entry of `l` satisfies
`hash H X' ⊕ hash H X* = T' ⊕ T*` is at most `|l| · ε`.

An entry with `X' = X*` contributes `0`: it would need `T' = T*`, i.e. `(X', T') = c`. Such
entries can occur, because the decryption guard compares ciphertexts rather than digest points,
which is why the hypothesis is `(X', T') ≠ c` and not `X' ≠ X*`. -/
private theorem probEvent_post_axu_le_run {K D : Type} [SampleableType K] {ε : ℝ≥0∞}
    {hash : K → D → BitVec 128} (haxu : IsAlmostXorUniversal hash ε)
    (c : D × BitVec 128) (l : List (D × BitVec 128)) (hne : ∀ x ∈ l, x ≠ c) :
    Pr[fun H : K => ∃ x ∈ l, hash H x.1 ^^^ hash H c.1 = x.2 ^^^ c.2
       | ($ᵗ K : ProbComp K)]
      ≤ (l.length : ℝ≥0∞) * ε := by
  -- Reindex the existential over the fixed list by `Fin l.length`.
  refine le_trans (probEvent_mono'' (q := fun H : K => ∃ i ∈ (Finset.univ : Finset (Fin l.length)),
      hash H (l.get i).1 ^^^ hash H c.1 = (l.get i).2 ^^^ c.2) ?_) ?_
  · rintro H ⟨x, hx, hxe⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hx
    exact ⟨i, Finset.mem_univ i, hxe⟩
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  calc ∑ i : Fin l.length,
        Pr[fun H : K => hash H (l.get i).1 ^^^ hash H c.1 = (l.get i).2 ^^^ c.2
           | ($ᵗ K : ProbComp K)]
      ≤ ∑ _i : Fin l.length, ε := by
        refine Finset.sum_le_sum fun i _ => ?_
        rcases eq_or_ne (l.get i).1 c.1 with hd | hd
        · -- Degenerate case: equal digest points contribute exactly `0`.
          have hx2 : (l.get i).2 ≠ c.2 := fun h =>
            hne (l.get i) (List.get_mem l i) (Prod.ext hd h)
          refine le_of_eq_of_le (probEvent_eq_zero fun H _ hev => hx2 ?_) zero_le
          rw [hd, BitVec.xor_self] at hev
          simpa [BitVec.xor_assoc] using congrArg (· ^^^ c.2) hev.symm
        · -- Distinct digest points: this is exactly the AXU predicate.
          have hconv :
              Pr[fun H : K => hash H (l.get i).1 ^^^ hash H c.1 = (l.get i).2 ^^^ c.2
                 | ($ᵗ K : ProbComp K)]
                = Pr[= (l.get i).2 ^^^ c.2
                    | (fun k => hash k (l.get i).1 ^^^ hash k c.1) <$> ($ᵗ K)] := by
            rw [← probEvent_eq_eq_probOutput, probEvent_map]
            rfl
          rw [hconv]
          exact haxu (l.get i).1 c.1 hd _
    _ = (l.length : ℝ≥0∞) * ε := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Post-challenge half. Let `z` be drawn from `μ` and then `H` uniformly and independently.
Write `chal z = (X*, T*)` and suppose no entry of `post z` equals `chal z` for `z` in the support
of `μ`. Then the probability that some `(X', T') ∈ post z` satisfies
`hash H X' ⊕ hash H X* = T' ⊕ T*` is at most `𝔼[|post z|] · ε`. -/
theorem probEvent_post_axu_le {Z K D : Type} [SampleableType K] {ε : ℝ≥0∞}
    {hash : K → D → BitVec 128} (haxu : IsAlmostXorUniversal hash ε)
    (μ : ProbComp Z) (chal : Z → D × BitVec 128) (post : Z → List (D × BitVec 128))
    (hne : ∀ z ∈ support μ, ∀ x ∈ post z, x ≠ chal z) :
    Pr[fun p : Z × K => ∃ x ∈ post p.1,
         hash p.2 x.1 ^^^ hash p.2 (chal p.1).1 = x.2 ^^^ (chal p.1).2
       | (do let z ← μ; let H ← ($ᵗ K : ProbComp K); pure (z, H))]
      ≤ ∑' z, Pr[= z | μ] * ((post z).length : ℝ≥0∞) * ε := by
  rw [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun z => ?_
  rcases Classical.em (z ∈ support μ) with hz | hz
  · rw [mul_assoc]
    gcongr
    have hmap : (do let H ← ($ᵗ K : ProbComp K); (pure (z, H) : ProbComp (Z × K)))
        = (fun H => (z, H)) <$> ($ᵗ K : ProbComp K) := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [hmap, probEvent_map]
    exact probEvent_post_axu_le_run haxu (chal z) (post z) (hne z hz)
  · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul, zero_mul]

/-- Pre-challenge half. Let `w` be drawn from `ν` and then `m` uniformly from `{0,1}¹²⁸`, and
let the continuation `k w m` end in the event `E` exactly when `m ∈ pre w`. Then `E` holds with
probability at most `𝔼[|pre w|] · 2⁻¹²⁸`. Same mathematics as VCVio's
`probEvent_hiddenReadMany_le` (`RandomOracle/ProbeEps.lean`), stated for an arbitrary
continuation instead of the `readMany` game shape. -/
theorem probEvent_pre_fresh_le {W β : Type} (ν : ProbComp W)
    (pre : W → List (BitVec 128)) (k : W → BitVec 128 → ProbComp β)
    (E : β → Prop)
    (hk : ∀ w m, ∀ y ∈ support (k w m), (E y ↔ m ∈ pre w)) :
    Pr[E | (do let w ← ν; let m ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128)); k w m)]
      ≤ ∑' w, Pr[= w | ν] * ((pre w).length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := by
  have hunif : ∀ m : BitVec 128,
      Pr[= m | ($ᵗ (BitVec 128) : ProbComp (BitVec 128))] = ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := by
    intro m; rw [probOutput_uniformSample, ToVCVio.natCast_card_bitVec]
  rw [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun w => ?_
  rw [mul_assoc]
  gcongr
  rw [probEvent_bind_eq_tsum]
  calc ∑' m : BitVec 128,
        Pr[= m | ($ᵗ (BitVec 128) : ProbComp (BitVec 128))] * Pr[E | k w m]
      -- Off the fixed locus list the event is impossible on the whole support of `k w m`.
      ≤ ∑' m : BitVec 128,
        ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ * (if m ∈ pre w then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        rw [hunif m]
        gcongr
        by_cases hm : m ∈ pre w
        · simp [hm]
        · simp only [hm, if_false]
          exact le_of_eq (probEvent_eq_zero fun y hy hE => hm ((hk w m y hy).1 hE))
    _ = ∑ m : BitVec 128, ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ * (if m ∈ pre w then 1 else 0) :=
        tsum_fintype _
      -- The locus has at most `(pre w).length` distinct points (duplicates only help).
    _ ≤ ((pre w).length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := by
        rw [← Finset.mul_sum, mul_comm]
        gcongr
        rw [Finset.sum_boole]
        have hsub : Finset.univ.filter (fun m : BitVec 128 => m ∈ pre w)
            ⊆ (pre w).toFinset := by
          intro m hm
          rw [Finset.mem_filter] at hm
          exact List.mem_toFinset.2 hm.2
        exact Nat.cast_le.2 ((Finset.card_le_card hsub).trans (List.toFinset_card_le (pre w)))

/-- Adds the two halves under one budget. `hfloor` lets the pre-challenge term be charged at
rate `ε` like the post-challenge one, and `hcount` bounds the two counts together, so the sum is
`q · ε`. Bounding each half by `q` on its own would give `2 · q · ε`. -/
theorem combine_pre_post_le (q npre npost : ℕ) (ε : ℝ≥0∞) (P Q : ℝ≥0∞)
    (hP : P ≤ (npre : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹)
    (hQ : Q ≤ (npost : ℝ≥0∞) * ε)
    (hcount : npre + npost ≤ q)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε) :
    P + Q ≤ (q : ℝ≥0∞) * ε :=
  calc P + Q
      ≤ (npre : ℝ≥0∞) * ε + (npost : ℝ≥0∞) * ε :=
        add_le_add (hP.trans (mul_le_mul' le_rfl hfloor)) hQ
    _ = ((npre + npost : ℕ) : ℝ≥0∞) * ε := by push_cast; ring
    _ ≤ (q : ℝ≥0∞) * ε := mul_le_mul' (Nat.cast_le.2 hcount) le_rfl

end OracleComp.WegmanCarter
