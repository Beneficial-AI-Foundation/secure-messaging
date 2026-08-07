/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.Defs

/-!
# Erasure-Code Payload Lemmas

Protocol-independent helpers for natural-number-indexed payload chunks.

`ErasureCode` uses bounded positions `Fin N`, while protocol messages carry natural
number indices. This module relates those representations and lifts
`ErasureCode.Correct` to serialized payloads. Its incremental result,
`ErasureCodePayload.decode_insert_honest`, describes adding one honest chunk to an
honest sub-threshold chunk set.
-/

namespace ErasureCode

variable {Sym : Type} [DecidableEq Sym]

/-- Convert a bounded chunk index to a natural number, forgetting the bound. -/
def chunkToNat {ec : ErasureCode Sym} :
    (Fin ec.N × Sym) ↪ (ℕ × Sym) where
  toFun chunk := (chunk.1.val, chunk.2)
  inj' := by
    intro a b h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h))
      (congrArg (fun chunk : ℕ × Sym => chunk.2) h)

/-- Encoding chunks at `insert i I` adds the chunk at `i` to the chunk set at `I`. -/
theorem encodeChunks_insert (ec : ErasureCode Sym)
    (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)) (i : Fin ec.N) :
    ec.encodeChunks M (insert i I) = insert (i, ec.encode M i) (ec.encodeChunks M I) := by
  ext chunk
  simp [ErasureCode.encodeChunks, eq_comm]

end ErasureCode

namespace ErasureCodePayload

variable {Sym : Type} [DecidableEq Sym]

/-- The natural-index representation of an honest subset of a payload's codeword. -/
noncomputable def payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) : Finset (ℕ × Sym) :=
  (ecp.ec.encodeChunks (ecp.serialize payload) I).map ErasureCode.chunkToNat

omit [DecidableEq Sym] in
/-- All chunk indices in `payloadChunks` satisfy the bound `< ecp.ec.N`. -/
theorem payloadChunks_valid {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    ∀ chunk ∈ payloadChunks ecp payload I, chunk.1 < ecp.ec.N := by
  classical
  intro chunk hchunk
  rw [payloadChunks, Finset.mem_map] at hchunk
  obtain ⟨bounded, _, rfl⟩ := hchunk
  exact bounded.1.isLt

/-- Convert a natural chunk index back to a bounded index using `payloadChunks_valid`. -/
def chunkToFin {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    {chunk // chunk ∈ payloadChunks ecp payload I} ↪ (Fin ecp.ec.N × Sym) where
  toFun chunk :=
    (⟨chunk.1.1, payloadChunks_valid ecp payload I chunk.1 chunk.2⟩, chunk.1.2)
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact Prod.ext
      (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.1.val) hab)
      (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.2) hab)

omit [DecidableEq Sym] in
/-- Mapping `payloadChunks` back to bounded indices recovers the original chunk set. -/
theorem payloadChunks_roundtrip {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    (payloadChunks ecp payload I).attach.map (chunkToFin ecp payload I) =
      ecp.ec.encodeChunks (ecp.serialize payload) I := by
  classical
  apply Finset.ext
  intro chunk
  constructor
  · intro hchunk
    rw [Finset.mem_map] at hchunk
    obtain ⟨natChunk, _, hnatChunk⟩ := hchunk
    have hmem := natChunk.property
    change natChunk.1 ∈
      (ecp.ec.encodeChunks (ecp.serialize payload) I).map ErasureCode.chunkToNat at hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨bounded, hbounded, hboundedEq⟩ := hmem
    have hback : chunkToFin ecp payload I natChunk = bounded := by
      apply Prod.ext
      · apply Fin.ext
        exact (congrArg Prod.fst hboundedEq).symm
      · exact (congrArg Prod.snd hboundedEq).symm
    rw [← hnatChunk, hback]
    exact hbounded
  · intro hchunk
    have hnat : ErasureCode.chunkToNat chunk ∈ payloadChunks ecp payload I := by
      rw [payloadChunks, Finset.mem_map]
      exact ⟨chunk, hchunk, rfl⟩
    let natChunk : {chunk // chunk ∈ payloadChunks ecp payload I} :=
      ⟨ErasureCode.chunkToNat chunk, hnat⟩
    rw [Finset.mem_map]
    refine ⟨natChunk, by simp, ?_⟩
    exact Prod.ext (Fin.ext rfl) rfl

omit [DecidableEq Sym] in
/-- Mapping `payloadChunks` to bounded indices with any validity proof recovers the
original bounded chunk set. This form matches the bounds check inside `decode`. -/
theorem payloadChunks_boundedMap {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N))
    (hvalid : ∀ chunk ∈ payloadChunks ecp payload I, chunk.1 < ecp.ec.N) :
    let toBounded : {chunk // chunk ∈ payloadChunks ecp payload I} ↪
        (Fin ecp.ec.N × Sym) :=
      { toFun := fun chunk =>
          (⟨chunk.1.1, hvalid chunk.1 chunk.2⟩, chunk.1.2)
        inj' := by
          intro a b hab
          apply Subtype.ext
          exact Prod.ext
            (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.1.val) hab)
            (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.2) hab) }
    (payloadChunks ecp payload I).attach.map toBounded =
      ecp.ec.encodeChunks (ecp.serialize payload) I := by
  classical
  dsimp only
  apply Finset.ext
  intro chunk
  constructor
  · intro hchunk
    rw [Finset.mem_map] at hchunk
    obtain ⟨natChunk, _, hnatChunk⟩ := hchunk
    have hmem := natChunk.property
    change natChunk.1 ∈
      (ecp.ec.encodeChunks (ecp.serialize payload) I).map ErasureCode.chunkToNat at hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨bounded, hbounded, hboundedEq⟩ := hmem
    rw [← hnatChunk]
    have : (⟨natChunk.1.1, hvalid natChunk.1 natChunk.2⟩, natChunk.1.2) = bounded := by
      apply Prod.ext
      · apply Fin.ext
        exact (congrArg Prod.fst hboundedEq).symm
      · exact (congrArg Prod.snd hboundedEq).symm
    change (⟨natChunk.1.1, hvalid natChunk.1 natChunk.2⟩, natChunk.1.2) ∈
      ecp.ec.encodeChunks (ecp.serialize payload) I
    rw [this]
    exact hbounded
  · intro hchunk
    have hnat : ErasureCode.chunkToNat chunk ∈ payloadChunks ecp payload I := by
      rw [payloadChunks, Finset.mem_map]
      exact ⟨chunk, hchunk, rfl⟩
    let natChunk : {chunk // chunk ∈ payloadChunks ecp payload I} :=
      ⟨ErasureCode.chunkToNat chunk, hnat⟩
    rw [Finset.mem_map]
    refine ⟨natChunk, by simp, ?_⟩
    exact Prod.ext (Fin.ext rfl) rfl

omit [DecidableEq Sym] in
/-- Decoding an honest chunk set at the reconstruction threshold recovers its payload. -/
theorem decode_payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : I.card = ecp.ec.nchunk) :
    ecp.decode (payloadChunks ecp payload I) = some payload := by
  classical
  rw [ErasureCodePayload.decode]
  split
  next hvalid =>
    dsimp only
    rw [payloadChunks_boundedMap ecp payload I hvalid]
    rw [(hcorrect (ecp.serialize payload) I).1 hcard]
    exact ecp.parse_serialize payload
  next hvalid => exact False.elim (hvalid (payloadChunks_valid ecp payload I))

omit [DecidableEq Sym] in
/-- Decoding an honest chunk set below the reconstruction threshold fails. -/
theorem decode_payloadChunks_none {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : I.card < ecp.ec.nchunk) :
    ecp.decode (payloadChunks ecp payload I) = none := by
  classical
  rw [ErasureCodePayload.decode]
  split
  next hvalid =>
    dsimp only
    rw [payloadChunks_boundedMap ecp payload I hvalid]
    simp [(hcorrect (ecp.serialize payload) I).2 hcard]
  next hvalid => exact False.elim (hvalid (payloadChunks_valid ecp payload I))

/-- Map a natural counter index to a bounded chunk position modulo `N`. -/
def counterIndex {M : Type} (ecp : ErasureCodePayload M Sym) (i : ℕ) :
    Fin ecp.ec.N :=
  ⟨i % ecp.ec.N, Nat.mod_lt i ecp.ec.N_pos⟩

omit [DecidableEq Sym] in
/-- Encoding at counter `i` produces the natural representation of the bounded chunk. -/
theorem encode_eq_chunkToNat {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M) (i : ℕ) :
    ecp.encode payload i =
      ErasureCode.chunkToNat
        (counterIndex ecp i, ecp.ec.encode (ecp.serialize payload) (counterIndex ecp i)) :=
  rfl

/-- Inserting an encoded chunk into `payloadChunks` inserts its bounded position. -/
theorem insert_payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    insert (ecp.encode payload i) (payloadChunks ecp payload I) =
      payloadChunks ecp payload (insert (counterIndex ecp i) I) := by
  rw [payloadChunks, payloadChunks, ErasureCode.encodeChunks_insert, Finset.map_insert,
    encode_eq_chunkToNat]

/-- Inserting one honest chunk into an honest sub-threshold set either remains below
the threshold or reaches it and decodes the original payload. -/
theorem decode_insert_honest {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N)) (i : ℕ)
    (hcard : I.card < ecp.ec.nchunk) :
    let I' := insert (counterIndex ecp i) I
    (I'.card < ecp.ec.nchunk ∧
        ecp.decode (insert (ecp.encode payload i) (payloadChunks ecp payload I)) = none) ∨
      (I'.card = ecp.ec.nchunk ∧
        ecp.decode (insert (ecp.encode payload i) (payloadChunks ecp payload I)) =
          some payload) := by
  dsimp only
  have hle : (insert (counterIndex ecp i) I).card ≤ ecp.ec.nchunk := by
    calc
      (insert (counterIndex ecp i) I).card ≤ I.card + 1 :=
        Finset.card_insert_le (counterIndex ecp i) I
      _ ≤ ecp.ec.nchunk := hcard
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · left
    exact ⟨hlt, by
      rw [insert_payloadChunks]
      exact decode_payloadChunks_none ecp hcorrect payload _ hlt⟩
  · right
    exact ⟨heq, by
      rw [insert_payloadChunks]
      exact decode_payloadChunks ecp hcorrect payload _ heq⟩

end ErasureCodePayload
