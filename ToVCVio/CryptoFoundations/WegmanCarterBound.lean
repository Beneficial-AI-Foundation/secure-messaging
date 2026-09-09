/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.CryptoFoundations.UniversalHash

/-!
# Wegman–Carter authenticity: the abstract probability core

The three abstract probability statements behind `probEvent_wcInst_forge_le`
(`ToVCVio/CryptoFoundations/WegmanCarter.lean`): the two halves of the pre/post split and
their combination. They are stated over an abstract run distribution and an abstract fresh
sample point, so they depend on nothing but the AXU predicate.

## Why the pre/post split is mandatory

It is tempting to treat all guard-passing decrypt queries uniformly: after the local
bijection at the encryption query, query `i` accepts exactly when
`hash H X'ᵢ ^^^ hash H X* = T'ᵢ ^^^ T*`, which looks like a single AXU application
regardless of when the query was made. That is unsound. After hoisting `H` to the end the
whole run is `H`-free, so for a log index with `X'ᵢ = X*` the acceptance event degenerates
to `T'ᵢ = T*`, a statement about values already fixed by the run: its probability over `H`
is `0` or `1`, never `2⁻¹²⁸`. The `2⁻¹²⁸` lives in `T*`, which is drawn INSIDE the run. So
per index one can only charge `Pr ≤ ε + 2⁻¹²⁸ ≤ 2 · ε`, giving `2 · q · ε` — a factor two
off the target.

The sound structure charges the two randomness sources to DISJOINT index sets. A
post-challenge entry differs from the challenge as a DIGEST-POINT/TAG PAIR — not as a
digest point alone. The guard compares the full ciphertext `(C, T)`, so `(ad*, (C*, T))`
with `T ≠ T*` clears it and is logged post-challenge at the very digest point `X*`
(ROADMAP criterion 5 makes the same distinction). Hence the two sub-cases: at a distinct
digest point AXU over the hoisted `H` gives `≤ ε`, and at an equal digest point acceptance
forces `T'ᵢ = T*`, contradicting pair-distinctness, so the entry contributes exactly `0`.
Either way `≤ ε` — that is `probEvent_post_axu_le`, whose hypothesis `hne` is accordingly
pair-inequality and NOT distinctness of digest points. A
pre-challenge entry is a blind guess at the not-yet-drawn 128-bit mask, of probability
exactly `2⁻¹²⁸` — that is `probEvent_pre_fresh_le`.

## The combination rule

`combine_pre_post_le` combines the two halves at a SHARED support count: the hypothesis is
`npre z + npost z ≤ q` per run, NOT `npre z ≤ q` and `npost z ≤ q` separately. Bounding the
two terms by `q` independently is exactly where the factor two reappears.

## Main statements

- `probEvent_post_axu_le` — post-challenge half: union bound + AXU over the hoisted key.
- `probEvent_pre_fresh_le` — pre-challenge half: blind guesses against a fresh uniform
  128-bit draw.
- `combine_pre_post_le` — the combination at a shared support count.

All three were staged as typed `sorry`-bodied lemmas by plan 04-01 and are PROVED here by
plan 04-04; this module is sorry-free.

## Composition note for callers

`probEvent_pre_fresh_le` expresses its expectation over the PREFIX distribution `ν` (the
run up to the mask draw), while `combine_pre_post_le` requires both expectations over the
SAME distribution `μ`. A caller must therefore transport the frozen pre-count through the
continuation onto `μ` before invoking the combination. Bounding the two expectations
separately by `q` and adding is not a legal shortcut — it is the factor-two leak again.
-/

open OracleSpec OracleComp ENNReal

namespace OracleComp.WegmanCarter

/-- Per-run conditional core of `probEvent_post_axu_le`, kept as its own top-level lemma so
the union bound and the AXU application never share an elaboration with the outer `tsum`
(heartbeat discipline).

At a FIXED challenge `c` and a FIXED target list `l` the length `l.length` is no longer
random, so `Finset.univ : Finset (Fin l.length)` is a legal index set for the union bound.
Per index there are exactly two sub-cases:

* distinct digest points — `IsAlmostXorUniversal` at offset `Δ := x.2 ^^^ c.2` (the offset
  is allowed to be `0`, and the predicate admits it, so no further split);
* EQUAL digest points — acceptance would read `0 = x.2 ^^^ c.2`, i.e. `x.2 = c.2`, which
  together with `x.1 = c.1` contradicts the PAIR-inequality `hne`. The entry therefore
  contributes exactly `0`, not `2⁻¹²⁸`. This is ROADMAP criterion 5's degenerate case: it
  is reachable (the challenge guard compares the full ciphertext, so `(ad*, (C*, T))` with
  `T ≠ T*` clears it and is logged post-challenge at the very digest point `X*`), and it is
  free. -/
private theorem probEvent_post_axu_le_run {K D : Type} [SampleableType K] {ε : ℝ≥0∞}
    {hash : K → D → BitVec 128} (haxu : IsAlmostXorUniversal hash ε)
    (c : D × BitVec 128) (l : List (D × BitVec 128)) (hne : ∀ x ∈ l, x ≠ c) :
    Pr[fun H : K => ∃ x ∈ l, hash H x.1 ^^^ hash H c.1 = x.2 ^^^ c.2
       | ($ᵗ K : ProbComp K)]
      ≤ (l.length : ℝ≥0∞) * ε := by
  classical
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

/-- **Obligation WC4** (staged here, discharged by plan 04-04). Post-challenge half of the
bound: over a uniformly random hash key drawn AFTER the run, the probability that some
post-challenge target `x` collides with the challenge `chal z` in the Wegman–Carter sense
is at most the expected number of targets times `ε`.

Route: condition on `z` FIRST (`probEvent_bind_eq_tsum`, VCVio `EvalDist/Monad/Basic.lean`),
THEN apply `probEvent_exists_finset_le_sum` (ibid.) at the index set of the now-fixed list
`post z` — legal only after conditioning, since `(post z).length` is random beforehand.
The index set is spelled `(Finset.univ : Finset (Fin (post z).length))` rather than
`Finset.range (post z).length`, so that `(post z).get i` is total and needs no in-bounds
side goal; the two are the same index set. Per index: when `x.1 ≠ (chal z).1`,
`IsAlmostXorUniversal` applies at offset `Δ := x.2 ^^^ (chal z).2`; when
`x.1 = (chal z).1`, `hne` forces `x.2 ≠ (chal z).2`, so the event reads
`0 = x.2 ^^^ (chal z).2`, is impossible, and contributes `0`.

The per-`z` conditional bound is the private `probEvent_post_axu_le_run`; off the support
of `μ` the summand vanishes because `Pr[= z | μ] = 0`. -/
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

/-- **Obligation WC5** (staged here, discharged by plan 04-04). Pre-challenge half of the
bound: blind guesses against a fresh uniform 128-bit draw, under an arbitrary continuation
`k` that faithfully reports both the target list and the drawn value — `hk` says that on
every run of `k w m`, the observed event `E` holds exactly when the drawn `m` was one of
the pre-challenge targets `pre w`.

Route: the same conditioning shape as WC4 (`probEvent_bind_eq_tsum` on `ν` first), then
`probOutput` of a uniform `BitVec 128` at each of the at most `(pre w).length` target
points.

**Why there is no degenerate sub-split here.** Unlike the post-challenge half, this half
never case-splits on the digest point. A pre-challenge entry accepts exactly when
`mask = T'ᵢ ^^^ hash H X'ᵢ` for *whatever* `X'ᵢ` it carries: the whole right-hand side is
frozen before `mask` is drawn, so the event is a blind guess at a fresh uniform 128-bit
value and has probability exactly `2⁻¹²⁸` — for every entry, degenerate or not. The
reparameterization used in the post-challenge half is neither used nor needed, and no
`ε` appears. This is a LOCAL argument at the one-shot encrypt query, not EtM's per-query
interleaved induction: `pre` is a functional of the prefix output `w` alone, and `hk`
propagates the frozen verdict through the whole continuation `k`. -/
theorem probEvent_pre_fresh_le {W β : Type} (ν : ProbComp W)
    (pre : W → List (BitVec 128)) (k : W → BitVec 128 → ProbComp β)
    (E : β → Prop)
    (hk : ∀ w m, ∀ y ∈ support (k w m), (E y ↔ m ∈ pre w)) :
    Pr[E | (do let w ← ν; let m ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128)); k w m)]
      ≤ ∑' w, Pr[= w | ν] * ((pre w).length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := by
  classical
  have hunif : ∀ m : BitVec 128,
      Pr[= m | ($ᵗ (BitVec 128) : ProbComp (BitVec 128))] = ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ := by
    intro m; rw [probOutput_uniformSample]; norm_num
  rw [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun w => ?_
  rw [mul_assoc]
  gcongr
  rw [probEvent_bind_eq_tsum]
  calc ∑' m : BitVec 128,
        Pr[= m | ($ᵗ (BitVec 128) : ProbComp (BitVec 128))] * Pr[E | k w m]
      -- Off the frozen locus list the event is impossible on the whole support of `k w m`.
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
      -- The locus has at most `(pre w).length` DISTINCT points (duplicates only help).
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

/-- **Obligation WC6** (staged here, discharged by plan 04-04). The combination of the two
halves at a SHARED support count.

`hcount` bounds the SUM of the two per-run counts by `q`; the two halves must NOT be
bounded by `q` separately, which is exactly where the factor two reappears. `hfloor`
(`2⁻¹²⁸ ≤ ε`) is what lets the pre-challenge term be re-charged at the AXU rate.

Route: `ENNReal.tsum_add`, then per-`z` arithmetic
`npre z * 2⁻¹²⁸ + npost z * ε ≤ (npre z + npost z) * ε ≤ q * ε` from `hfloor` and
`hcount`, then `∑' z, Pr[= z | μ] ≤ 1`.

**WARNING TO FUTURE READERS — do NOT bound the two terms by `q` separately.** The
temptation is to read off `P ≤ q * 2⁻¹²⁸` and `Q ≤ q * ε` and add them, giving
`q * 2⁻¹²⁸ + q * ε ≤ 2 * q * ε`. That is the factor-two leak: it double-spends the query
budget, once on each half. The two counts are combined FIRST — inside a single expectation
over one distribution `μ`, at a single `z` — and only the combined count `npre z + npost z`
is charged against `q`. This is why `hcount` is a hypothesis about the SUM and why both
`hP` and `hQ` must already be expectations over the SAME `μ`; a caller holding WC5 over a
prefix distribution `ν` must transport it to `μ` before invoking this lemma, not bound it
separately. -/
theorem combine_pre_post_le {Z : Type} (μ : ProbComp Z) (q : ℕ) (ε : ℝ≥0∞)
    (npre npost : Z → ℕ) (P Q : ℝ≥0∞)
    (hP : P ≤ ∑' z, Pr[= z | μ] * (npre z : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹)
    (hQ : Q ≤ ∑' z, Pr[= z | μ] * (npost z : ℝ≥0∞) * ε)
    (hcount : ∀ z ∈ support μ, npre z + npost z ≤ q)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε) :
    P + Q ≤ (q : ℝ≥0∞) * ε := by
  calc P + Q
      ≤ (∑' z, Pr[= z | μ] * (npre z : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹)
          + ∑' z, Pr[= z | μ] * (npost z : ℝ≥0∞) * ε := add_le_add hP hQ
      -- Merge the two expectations into ONE sum over ONE distribution.
    _ = ∑' z, (Pr[= z | μ] * (npre z : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹
          + Pr[= z | μ] * (npost z : ℝ≥0∞) * ε) := (ENNReal.tsum_add).symm
      -- Only now is the COMBINED count charged against the budget `q`.
    _ ≤ ∑' _z : Z, Pr[= _z | μ] * ((q : ℝ≥0∞) * ε) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        rcases Classical.em (z ∈ support μ) with hz | hz
        · calc Pr[= z | μ] * (npre z : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹
                + Pr[= z | μ] * (npost z : ℝ≥0∞) * ε
              ≤ Pr[= z | μ] * (npre z : ℝ≥0∞) * ε + Pr[= z | μ] * (npost z : ℝ≥0∞) * ε := by
                gcongr
            _ = Pr[= z | μ] * ((npre z : ℝ≥0∞) + (npost z : ℝ≥0∞)) * ε := by ring
            _ ≤ Pr[= z | μ] * (q : ℝ≥0∞) * ε := by
                gcongr
                exact_mod_cast hcount z hz
            _ = Pr[= z | μ] * ((q : ℝ≥0∞) * ε) := mul_assoc _ _ _
        · rw [probOutput_eq_zero_of_not_mem_support hz]
          simp
    _ = (∑' z, Pr[= z | μ]) * ((q : ℝ≥0∞) * ε) := ENNReal.tsum_mul_right
    _ ≤ 1 * ((q : ℝ≥0∞) * ε) := by gcongr; exact tsum_probOutput_le_one
    _ = (q : ℝ≥0∞) * ε := one_mul _

end OracleComp.WegmanCarter
