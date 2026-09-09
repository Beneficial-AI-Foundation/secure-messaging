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

All three are typed `sorry`-bodied lemmas staged by plan 04-01 and discharged by plan
04-04.
-/

open OracleSpec OracleComp ENNReal

namespace OracleComp.WegmanCarter

/-- **Obligation WC4** (staged here, discharged by plan 04-04). Post-challenge half of the
bound: over a uniformly random hash key drawn AFTER the run, the probability that some
post-challenge target `x` collides with the challenge `chal z` in the Wegman–Carter sense
is at most the expected number of targets times `ε`.

Route: condition on `z` FIRST (`probEvent_bind_eq_tsum`, VCVio `EvalDist/Monad/Basic.lean`),
THEN apply `probEvent_exists_finset_le_sum` (ibid.) at `Finset.range (post z).length` —
legal only after conditioning, since `(post z).length` is random beforehand. Per index:
when `x.1 ≠ (chal z).1`, `IsAlmostXorUniversal` applies at offset `Δ := x.2 ^^^ (chal z).2`;
when `x.1 = (chal z).1`, `hne` forces `x.2 ≠ (chal z).2`, so the event reads
`0 = x.2 ^^^ (chal z).2`, is impossible, and contributes `0`. -/
theorem probEvent_post_axu_le {Z K D : Type} [SampleableType K] {ε : ℝ≥0∞}
    {hash : K → D → BitVec 128} (haxu : IsAlmostXorUniversal hash ε)
    (μ : ProbComp Z) (chal : Z → D × BitVec 128) (post : Z → List (D × BitVec 128))
    (hne : ∀ z ∈ support μ, ∀ x ∈ post z, x ≠ chal z) :
    Pr[fun p : Z × K => ∃ x ∈ post p.1,
         hash p.2 x.1 ^^^ hash p.2 (chal p.1).1 = x.2 ^^^ (chal p.1).2
       | (do let z ← μ; let H ← ($ᵗ K : ProbComp K); pure (z, H))]
      ≤ ∑' z, Pr[= z | μ] * ((post z).length : ℝ≥0∞) * ε :=
  sorry

/-- **Obligation WC5** (staged here, discharged by plan 04-04). Pre-challenge half of the
bound: blind guesses against a fresh uniform 128-bit draw, under an arbitrary continuation
`k` that faithfully reports both the target list and the drawn value — `hk` says that on
every run of `k w m`, the observed event `E` holds exactly when the drawn `m` was one of
the pre-challenge targets `pre w`.

Route: the same conditioning shape as WC4 (`probEvent_bind_eq_tsum` on `ν` first), then
`probOutput` of a uniform `BitVec 128` at each of the at most `(pre w).length` target
points. -/
theorem probEvent_pre_fresh_le {W β : Type} (ν : ProbComp W)
    (pre : W → List (BitVec 128)) (k : W → BitVec 128 → ProbComp β)
    (E : β → Prop)
    (hk : ∀ w m, ∀ y ∈ support (k w m), (E y ↔ m ∈ pre w)) :
    Pr[E | (do let w ← ν; let m ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128)); k w m)]
      ≤ ∑' w, Pr[= w | ν] * ((pre w).length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ :=
  sorry

/-- **Obligation WC6** (staged here, discharged by plan 04-04). The combination of the two
halves at a SHARED support count.

`hcount` bounds the SUM of the two per-run counts by `q`; the two halves must NOT be
bounded by `q` separately, which is exactly where the factor two reappears. `hfloor`
(`2⁻¹²⁸ ≤ ε`) is what lets the pre-challenge term be re-charged at the AXU rate.

Route: `ENNReal.tsum_add`, then per-`z` arithmetic
`npre z * 2⁻¹²⁸ + npost z * ε ≤ (npre z + npost z) * ε ≤ q * ε` from `hfloor` and
`hcount`, then `∑' z, Pr[= z | μ] ≤ 1`. -/
theorem combine_pre_post_le {Z : Type} (μ : ProbComp Z) (q : ℕ) (ε : ℝ≥0∞)
    (npre npost : Z → ℕ) (P Q : ℝ≥0∞)
    (hP : P ≤ ∑' z, Pr[= z | μ] * (npre z : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹)
    (hQ : Q ≤ ∑' z, Pr[= z | μ] * (npost z : ℝ≥0∞) * ε)
    (hcount : ∀ z ∈ support μ, npre z + npost z ≤ q)
    (hfloor : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε) :
    P + Q ≤ (q : ℝ≥0∞) * ε :=
  sorry

end OracleComp.WegmanCarter
