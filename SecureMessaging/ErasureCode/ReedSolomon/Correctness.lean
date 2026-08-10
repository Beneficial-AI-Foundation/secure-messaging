/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.ReedSolomon.Construction

/-!
# Correctness of the Reed–Solomon Erasure Code

In the notation of `SecureMessaging.ErasureCode.ReedSolomon.Construction`, writing

`L_I := {(j, Encode(m, j)) | j ∈ I}`

for the honest chunks of a message `m` at a set of positions `I`, we prove:

* `Encode(m, i) = mᵢ` for `i < k` — the code is systematic (`encode_source`);
* `Decode(L_I) = m` when `k ≤ |I|` (`decode_encodeChunks_of_k_le_card`);
* `Decode(L_I) = ⊥` when `|I| < k` (`decode_encodeChunks_of_card_lt`).

Together these give the erasure-code correctness predicate `ErasureCode.Correct`
for `toErasureCode` (`correct`).
-/

namespace ErasureCode.ReedSolomon

noncomputable section

open Polynomial

variable {F : Type} [Field F]

namespace Code

/-- The interpolation property of the message polynomial: `Pₘ(xᵢ) = mᵢ` for `i < k`. -/
theorem eval_messagePolynomial_source (rs : Code F) (message : Fin rs.k → F)
    (i : Fin rs.k) :
    (rs.messagePolynomial message).eval (rs.sourcePoint i) = message i := by
  apply Lagrange.eval_interpolate_at_node
  · exact rs.sourcePoint_injective.injOn
  · simp

/-- The degree bound of the message polynomial: `deg Pₘ < k`. -/
theorem degree_messagePolynomial_lt (rs : Code F) (message : Fin rs.k → F) :
    (rs.messagePolynomial message).degree < rs.k := by
  simpa [messagePolynomial] using
    (Lagrange.degree_interpolate_lt (s := Finset.univ) message rs.sourcePoint_injective.injOn)

/-- The systematic property: `Encode(m, i) = Pₘ(xᵢ) = mᵢ` for message indices `i < k`. -/
@[simp]
-- ANCHOR: reedSolomon_systematic
theorem encode_source (rs : Code F) (message : Fin rs.k → F) (i : Fin rs.k) :
    rs.encode message (rs.sourceIndex i) = message i := by
  exact rs.eval_messagePolynomial_source message i
-- ANCHOR_END: reedSolomon_systematic

/-- The honest chunk set `L_I` is decodable when `k ≤ |I|`: it has one chunk per
position of `I`, so its evaluation points are pairwise distinct. -/
theorem decodable_encodeChunks_of_k_le_card (rs : Code F)
    (message : Fin rs.k → F) (I : Finset (Fin rs.N)) (hcard : rs.k ≤ I.card) :
    rs.Decodable (rs.toErasureCode.encodeChunks message I) := by
  constructor
  · calc
      rs.k ≤ I.card := hcard
      _ = (rs.toErasureCode.encodeChunks message I).card :=
        (rs.toErasureCode.card_encodeChunks message I).symm
  · intro a ha b hb hab
    have ha' := (rs.toErasureCode.mem_encodeChunks message I a).mp ha
    have hb' := (rs.toErasureCode.mem_encodeChunks message I b).mp hb
    have hindex : a.1 = b.1 := rs.point_injective hab
    apply Prod.ext hindex
    rw [ha'.2, hb'.2, hindex]

/-- Uniqueness of interpolation: for `k ≤ |I|`, the interpolant `Q` through the
honest chunks `L_I` equals `Pₘ` — both have degree `< |I|` and agree at the `|I|`
distinct points `{xⱼ | j ∈ I}`. -/
private theorem messagePolynomial_eq_receivedInterpolation (rs : Code F)
    (message : Fin rs.k → F) (I : Finset (Fin rs.N)) (hcard : rs.k ≤ I.card) :
    rs.messagePolynomial message =
      rs.receivedPolynomial (rs.toErasureCode.encodeChunks message I) := by
  classical
  let chunks := rs.toErasureCode.encodeChunks message I
  have hdec : rs.Decodable chunks := rs.decodable_encodeChunks_of_k_le_card message I hcard
  rw [receivedPolynomial]
  apply Lagrange.eq_interpolate_of_eval_eq _ hdec.2
  · have hcard' : rs.k ≤ chunks.card := hdec.1
    exact lt_of_lt_of_le (rs.degree_messagePolynomial_lt message) (by exact_mod_cast hcard')
  · intro chunk hchunk
    have hmem := (rs.toErasureCode.mem_encodeChunks message I chunk).mp hchunk
    exact hmem.2.symm

/-- Reconstruction above the threshold: `Decode(L_I) = m` when `k ≤ |I|`, by
`Q = Pₘ` and `Pₘ(xᵢ) = mᵢ`. -/
theorem decode_encodeChunks_of_k_le_card (rs : Code F)
    (message : Fin rs.k → F) (I : Finset (Fin rs.N)) (hcard : rs.k ≤ I.card) :
    rs.toErasureCode.decode (rs.toErasureCode.encodeChunks message I) = some message := by
  have hdec := rs.decodable_encodeChunks_of_k_le_card message I hcard
  have hpoly := rs.messagePolynomial_eq_receivedInterpolation message I hcard
  change rs.decode (rs.toErasureCode.encodeChunks message I) = some message
  rw [decode, dif_pos hdec]
  congr 1
  funext i
  exact (congrArg (fun poly : F[X] => poly.eval (rs.sourcePoint i)) hpoly.symm).trans
    (rs.eval_messagePolynomial_source message i)

/-- Failure below the threshold: `Decode(L_I) = ⊥` when `|I| < k`. -/
theorem decode_encodeChunks_of_card_lt (rs : Code F)
    (message : Fin rs.k → F) (I : Finset (Fin rs.N)) (hcard : I.card < rs.k) :
    rs.toErasureCode.decode (rs.toErasureCode.encodeChunks message I) = none := by
  change rs.decode (rs.toErasureCode.encodeChunks message I) = none
  rw [decode, dif_neg]
  intro hdec
  apply Nat.not_le_of_lt hcard
  have hk := hdec.1
  calc
    rs.k ≤ (rs.toErasureCode.encodeChunks message I).card := hk
    _ = I.card := rs.toErasureCode.card_encodeChunks message I

/-- Rejection of conflicts: `Decode(L) = ⊥` when the chunks of `L` do not have
pairwise distinct evaluation points — in particular when `L` contains
`(j, y₁), (j, y₂)` with `y₁ ≠ y₂`. -/
theorem decode_eq_none_of_not_injective (rs : Code F)
    (chunks : Finset (Fin rs.N × F))
    (hconflict : ¬Set.InjOn (fun ((j, _) : Fin rs.N × F) => rs.point j) chunks) :
    rs.decode chunks = none := by
  simp [decode, Decodable, hconflict]

/-- The Reed–Solomon erasure code is correct (`ErasureCode.Correct`, [SCKA] Def.
A.6): for every message `m` and position set `I`, `Decode(L_I) = m` if `k ≤ |I|`,
and `Decode(L_I) = ⊥` if `|I| < k`. -/
-- ANCHOR: reedSolomon_correct
theorem correct (rs : Code F) : rs.toErasureCode.Correct
-- ANCHOR_END: reedSolomon_correct
    := by
  intro message I
  constructor
  · exact rs.decode_encodeChunks_of_k_le_card message I
  · exact rs.decode_encodeChunks_of_card_lt message I

end Code

end

end ErasureCode.ReedSolomon
