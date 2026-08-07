/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.Defs

/-!
# Erasure Code Helpers for Perfect Correctness

Helper functions and lemmas for working with honest chunk sets and erasure code
decoding in the Opp-UniKEM SCKA perfect correctness game.

The key results link the natural-index chunk representation used in Opp-UniKEM
messages (`payloadChunks`) with the bounded-index operations of the abstract
erasure code (`ErasureCode.encodeChunks`, `ErasureCode.decode`):

* `decode_payloadChunks`: an honest chunk set at exactly the reconstruction
  threshold decodes to the original payload;
* `decode_payloadChunks_none`: an honest chunk set strictly below the threshold
  fails to decode;
* `decode_insert_honest`: inserting one honest chunk into a sub-threshold set
  either stays below the threshold or reaches it and decodes correctly.

These helpers are used throughout the Opp-UniKEM correctness invariant to track
honest chunk buffers (`ChunksAConsistent`, `ChunksBConsistent`) and guarantee
that all decoded values match their recorded transcripts.
-/

namespace oppUniKemCKA.Perfect.Internal

variable {Sym : Type} [DecidableEq Sym]

/-- Convert a bounded chunk index to a natural number, forgetting the bound. -/
def chunkToNat {ec : ErasureCode Sym} :
    (Fin ec.N × Sym) ↪ (ℕ × Sym) where
  toFun chunk := (chunk.1.val, chunk.2)
  inj' := by
    intro a b h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h))
      (congrArg (fun chunk : ℕ × Sym => chunk.2) h)

/-- The natural-index representation used by the Opp-UniKEM message format for
an honest subset of a payload's codeword. Maps bounded chunk indices to natural
numbers via `chunkToNat`. -/
noncomputable def payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) : Finset (ℕ × Sym) :=
  (ecp.ec.encodeChunks (ecp.serialize payload) I).map chunkToNat

/-- All chunk indices in `payloadChunks` satisfy the bound `< ecp.ec.N`. -/
lemma payloadChunks_valid {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    ∀ chunk ∈ payloadChunks ecp payload I, chunk.1 < ecp.ec.N := by
  intro chunk hchunk
  rw [payloadChunks, Finset.mem_map] at hchunk
  obtain ⟨bounded, _, rfl⟩ := hchunk
  exact bounded.1.isLt

/-- Convert a natural chunk index back to a bounded index using `payloadChunks_valid`.
Used to establish bijections between the natural and bounded representations. -/
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

/-- The roundtrip identity: mapping `payloadChunks` to bounded indices via
`chunkToFin` recovers the original bounded chunk set. -/
lemma payloadChunks_roundtrip {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    (payloadChunks ecp payload I).attach.map (chunkToFin ecp payload I) =
      ecp.ec.encodeChunks (ecp.serialize payload) I := by
  apply Finset.ext
  intro chunk
  constructor
  · intro hchunk
    rw [Finset.mem_map] at hchunk
    obtain ⟨natChunk, _, hnatChunk⟩ := hchunk
    have hmem := natChunk.property
    change natChunk.1 ∈
      (ecp.ec.encodeChunks (ecp.serialize payload) I).map chunkToNat at hmem
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
    have hnat : chunkToNat chunk ∈ payloadChunks ecp payload I := by
      rw [payloadChunks, Finset.mem_map]
      exact ⟨chunk, hchunk, rfl⟩
    let natChunk : {chunk // chunk ∈ payloadChunks ecp payload I} :=
      ⟨chunkToNat chunk, hnat⟩
    rw [Finset.mem_map]
    refine ⟨natChunk, by simp, ?_⟩
    exact Prod.ext (Fin.ext rfl) rfl

/-- Casting every chunk of `payloadChunks ecp payload I` back to a bounded
index recovers `ecp.ec.encodeChunks (ecp.serialize payload) I`.  The same
identity as `payloadChunks_roundtrip`, but the in-bounds hypothesis `hvalid`
is a parameter, so the statement matches the bounds check performed inside
`ErasureCodePayload.decode`. -/
lemma payloadChunks_boundedMap {M : Type}
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
  dsimp only
  apply Finset.ext
  intro chunk
  constructor
  · intro hchunk
    rw [Finset.mem_map] at hchunk
    obtain ⟨natChunk, _, hnatChunk⟩ := hchunk
    have hmem := natChunk.property
    change natChunk.1 ∈
      (ecp.ec.encodeChunks (ecp.serialize payload) I).map chunkToNat at hmem
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
    have hnat : chunkToNat chunk ∈ payloadChunks ecp payload I := by
      rw [payloadChunks, Finset.mem_map]
      exact ⟨chunk, hchunk, rfl⟩
    let natChunk : {chunk // chunk ∈ payloadChunks ecp payload I} :=
      ⟨chunkToNat chunk, hnat⟩
    rw [Finset.mem_map]
    refine ⟨natChunk, by simp, ?_⟩
    exact Prod.ext (Fin.ext rfl) rfl

/-- Decoding an honest chunk set at exactly the reconstruction threshold recovers
the original payload. Used in the correctness invariant to show that decoded values
match their transcripts. -/
lemma decode_payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : I.card = ecp.ec.nchunk) :
    ecp.decode (payloadChunks ecp payload I) = some payload := by
  rw [ErasureCodePayload.decode]
  split
  next hvalid =>
    dsimp only
    rw [payloadChunks_boundedMap ecp payload I hvalid]
    rw [(hcorrect (ecp.serialize payload) I).1 hcard]
    exact ecp.parse_serialize payload
  next hvalid => exact False.elim (hvalid (payloadChunks_valid ecp payload I))

/-- Decoding an honest chunk set strictly below the reconstruction threshold fails.
Used to show that chunk buffers remain `none` until the threshold is reached. -/
lemma decode_payloadChunks_none {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : I.card < ecp.ec.nchunk) :
    ecp.decode (payloadChunks ecp payload I) = none := by
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
lemma encode_eq_chunkToNat {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M) (i : ℕ) :
    ecp.encode payload i =
      chunkToNat (counterIndex ecp i, ecp.ec.encode (ecp.serialize payload) (counterIndex ecp i)) :=
  rfl

/-- Encoding chunks at `insert i I` adds the chunk at `i` to the chunk set at `I`. -/
lemma encodeChunks_insert (ec : ErasureCode Sym)
    (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)) (i : Fin ec.N) :
    ec.encodeChunks M (insert i I) = insert (i, ec.encode M i) (ec.encodeChunks M I) := by
  ext chunk
  simp [ErasureCode.encodeChunks, eq_comm]

/-- Inserting an encoded chunk into `payloadChunks` corresponds to inserting the
bounded index into the position set. -/
lemma insert_payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    insert (ecp.encode payload i) (payloadChunks ecp payload I) =
      payloadChunks ecp payload (insert (counterIndex ecp i) I) := by
  rw [payloadChunks, payloadChunks, encodeChunks_insert, Finset.map_insert,
    encode_eq_chunkToNat]

/-- Inserting one honest chunk into an honest sub-threshold set either leaves a
strictly sub-threshold honest set, or reaches the threshold and decodes the
original payload.

This is the key lemma for tracking chunk buffers in the invariant: each received
chunk either keeps the buffer below threshold (decoded value remains `none`) or
completes the set (decoded value becomes `some payload`). -/
lemma decode_insert_honest {M : Type}
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

end oppUniKemCKA.Perfect.Internal
