/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.ReedSolomon.Correctness
import SecureMessaging.ErasureCode.SPQRReedSolomon.Construction

/-!
# Correctness of the Parallel Reed–Solomon Erasure Code

Let `rs` be a scalar Reed–Solomon code, `m ∈ (F^16)^k`, and
`I ⊆ {0, …, N-1}`. Denote by

`L_I := {(j, Encode(m, j)) | j ∈ I}`

the set of chunks at positions `I`. Each of the 16 coordinates forms an ordinary
scalar Reed–Solomon codeword. We prove:

* `Encode(m, i) = mᵢ` for `i < k` — the parallel code is systematic (`encode_source`);
* `Decode(L_I) = m` when `k ≤ |I|` (`decode_encodeChunks_of_k_le_card`);
* `Decode(L_I) = ⊥` when `|I| < k` (`decode_encodeChunks_of_card_lt`);
* `ErasureCode.Correct` for `parallelCode rs` (`parallelCode_correct`) and its
  specialization `spqrCode k` (`correct`).
-/

namespace ErasureCode.SPQRReedSolomon

noncomputable section

open Polynomial

variable {F : Type} [Field F]

/-- Systematic encoding: at each source index `i < k`, parallel encoding returns the
source chunk itself, `Encode(message, i) = message i`. -/
@[simp]
theorem encode_source (rs : ReedSolomon.Code F) (message : Fin rs.k → Chunk F)
    (i : Fin rs.k) : encode rs message (rs.sourceIndex i) = message i := by
  funext coordinate
  exact rs.encode_source (fun j => message j coordinate) i

/-- If `I` contains at least `k` positions, then the chunk set
`(parallelCode rs).encodeChunks message I` is decodable: it has at least `k` elements
and pairwise distinct evaluation points. -/
theorem decodable_encodeChunks_of_k_le_card (rs : ReedSolomon.Code F)
    (message : Fin rs.k → Chunk F) (I : Finset (Fin rs.N)) (hcard : rs.k ≤ I.card) :
    Decodable rs ((parallelCode rs).encodeChunks message I) := by
  constructor
  · calc
      rs.k ≤ I.card := hcard
      _ = ((parallelCode rs).encodeChunks message I).card :=
        ((parallelCode rs).card_encodeChunks message I).symm
  · intro a ha b hb hab
    have ha' := ((parallelCode rs).mem_encodeChunks message I a).mp ha
    have hb' := ((parallelCode rs).mem_encodeChunks message I b).mp hb
    have hindex : a.1 = b.1 := rs.point_injective hab
    apply Prod.ext hindex
    rw [ha'.2, hb'.2, hindex]

/-- Projection commutes with encoding: selecting coordinate `c` from every parallel
encoded chunk over `I` gives exactly the scalar encoded chunk set for the coordinate
message `i ↦ message i c`. -/
@[simp]
theorem coordinateChunks_encodeChunks (rs : ReedSolomon.Code F)
    (message : Fin rs.k → Chunk F) (I : Finset (Fin rs.N)) (coordinate : Fin 16) :
    coordinateChunks rs ((parallelCode rs).encodeChunks message I) coordinate =
      rs.toErasureCode.encodeChunks (fun i => message i coordinate) I := by
  classical
  ext chunk
  constructor
  · intro hchunk
    rcases Finset.mem_image.mp hchunk with ⟨fullChunk, hfull, rfl⟩
    have hmem := ((parallelCode rs).mem_encodeChunks message I fullChunk).mp hfull
    apply (rs.toErasureCode.mem_encodeChunks (fun i => message i coordinate) I _).mpr
    refine ⟨hmem.1, ?_⟩
    exact congrFun hmem.2 coordinate
  · intro hchunk
    have hmem :=
      (rs.toErasureCode.mem_encodeChunks (fun i => message i coordinate) I chunk).mp hchunk
    rcases chunk with ⟨index, value⟩
    let fullChunk := (index, (parallelCode rs).encode message index)
    apply Finset.mem_image.mpr
    refine ⟨fullChunk, ?_, ?_⟩
    · exact ((parallelCode rs).mem_encodeChunks message I fullChunk).mpr ⟨hmem.1, rfl⟩
    · change (index, ((parallelCode rs).encode message index) coordinate) = (index, value)
      congr
      change rs.encode (fun i => message i coordinate) index = value
      exact hmem.2.symm

/-- Coordinatewise interpolation of honest chunks: when `k ≤ |I|`, the received
polynomial for coordinate `c` equals the scalar message polynomial of
`i ↦ message i c`. -/
private theorem messagePolynomial_eq_receivedPolynomial (rs : ReedSolomon.Code F)
    (message : Fin rs.k → Chunk F) (I : Finset (Fin rs.N)) (hcard : rs.k ≤ I.card)
    (coordinate : Fin 16) :
    rs.messagePolynomial (fun i => message i coordinate) =
      receivedPolynomial rs ((parallelCode rs).encodeChunks message I) coordinate := by
  classical
  let scalarMessage := fun i => message i coordinate
  let chunks := rs.toErasureCode.encodeChunks scalarMessage I
  have hdec : rs.Decodable chunks :=
    rs.decodable_encodeChunks_of_k_le_card scalarMessage I hcard
  rw [receivedPolynomial, coordinateChunks_encodeChunks,
    ReedSolomon.Code.receivedPolynomial]
  apply Lagrange.eq_interpolate_of_eval_eq _ hdec.2
  · have hdegree := rs.degree_messagePolynomial_lt scalarMessage
    have hcard' : rs.k ≤ chunks.card := hdec.1
    exact lt_of_lt_of_le hdegree (by exact_mod_cast hcard')
  · intro chunk hchunk
    have hmem := (rs.toErasureCode.mem_encodeChunks scalarMessage I chunk).mp hchunk
    exact hmem.2.symm

/-- Reconstruction at or above the threshold: encoding a message at every position in
`I` and decoding those chunks returns the message whenever `k ≤ |I|`. -/
theorem decode_encodeChunks_of_k_le_card (rs : ReedSolomon.Code F)
    (message : Fin rs.k → Chunk F) (I : Finset (Fin rs.N)) (hcard : rs.k ≤ I.card) :
    (parallelCode rs).decode ((parallelCode rs).encodeChunks message I) = some message := by
  have hdec := decodable_encodeChunks_of_k_le_card rs message I hcard
  change decode rs ((parallelCode rs).encodeChunks message I) = some message
  rw [decode, dif_pos hdec]
  congr 1
  funext i coordinate
  have hpoly := messagePolynomial_eq_receivedPolynomial rs message I hcard coordinate
  exact (congrArg (fun poly : F[X] => poly.eval (rs.sourcePoint i)) hpoly.symm).trans
    (rs.eval_messagePolynomial_source (fun j => message j coordinate) i)

/-- Failure below the threshold: decoding
`(parallelCode rs).encodeChunks message I` returns `none` whenever `|I| < k`. -/
theorem decode_encodeChunks_of_card_lt (rs : ReedSolomon.Code F)
    (message : Fin rs.k → Chunk F) (I : Finset (Fin rs.N)) (hcard : I.card < rs.k) :
    (parallelCode rs).decode ((parallelCode rs).encodeChunks message I) = none := by
  change decode rs ((parallelCode rs).encodeChunks message I) = none
  rw [decode, dif_neg]
  intro hdec
  apply Nat.not_le_of_lt hcard
  have hk := hdec.1
  calc
    rs.k ≤ ((parallelCode rs).encodeChunks message I).card := hk
    _ = I.card := (parallelCode rs).card_encodeChunks message I

/-- Rejection of conflicting chunks: decoding returns `none` if two distinct received
entries determine the same evaluation point, equivalently if the evaluation-point map
is not injective on the received chunk set. -/
theorem decode_eq_none_of_not_injective (rs : ReedSolomon.Code F)
    (chunks : Finset (Fin rs.N × Chunk F))
    (hconflict : ¬Set.InjOn
      (fun ((j, _) : Fin rs.N × Chunk F) => rs.point j) chunks) :
    decode rs chunks = none := by
  simp [decode, Decodable, hconflict]

/-- Correctness of the generic parallel construction: for every message and position
set `I`, decoding honest chunks returns the message when `|I| = k` and returns `none`
when `|I| < k`. -/
-- ANCHOR: parallelReedSolomon_correct
theorem parallelCode_correct (rs : ReedSolomon.Code F) :
    (parallelCode rs).Correct
-- ANCHOR_END: parallelReedSolomon_correct
    := by
  intro message I
  constructor
  · intro hcard
    exact decode_encodeChunks_of_k_le_card rs message I hcard.ge
  · exact decode_encodeChunks_of_card_lt rs message I

/-- Correctness of the abstract SPQR specialization for every threshold `k ≤ 2^16`. -/
-- ANCHOR: spqrReedSolomon_correct
theorem correct (k : ℕ) (hk : k ≤ 2 ^ 16) : (spqrCode k hk).Correct
-- ANCHOR_END: spqrReedSolomon_correct
    := by
  exact parallelCode_correct (scalarCode k hk)

end

end ErasureCode.SPQRReedSolomon
