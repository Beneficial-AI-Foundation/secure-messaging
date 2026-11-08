/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.ErasureCode.Payload

/-!
# Stateful Erasure-Code Streaming

Protocol-independent stateful wrappers over `ErasureCodePayload`. The encoder emits
successive natural-number-indexed chunks. An `EncoderState` stores its `ErasureCodePayload`
scheme, so a stream cannot be encoded under a different scheme.

A `StreamDecoder` is a structure defined by a state type, an initial state, an operation that
adds one indexed chunk to a state, and a partial decoding function. `StreamDecoder.Sound` states
that a decoder that received only chunks of `p`, at least one, decodes to `none` or `some p`.
`StreamDecoder.Received` is the matching invariant, and `StreamDecoder.Sound.of_inv` proves
soundness from an instance's own invariant.

`setDecoder ecp` is the set-based instance. Its state is a finite set of indexed chunks that stores
at most one symbol per index and keeps the first symbol received at a repeated index. It is sound
when the erasure code is correct (`setDecoder_sound`).

The encoder and `setDecoder` abstract away the byte representation, polynomial caches, bounded
storage, and serialization of an implementation such as Signal's. Other `StreamDecoder` instances
can model these.

## References

- [Signal ML-KEM Braid, §2.2: Encode/Decode](https://signal.org/docs/specifications/mlkembraid/)
- [SparsePostQuantumRatchet encoder and decoder interfaces](https://github.com/signalapp/SparsePostQuantumRatchet/blob/fd320484dcec89004021e6fdc7481825f5f261fa/src/encoding.rs#L24-L47)
- [SparsePostQuantumRatchet polynomial streaming implementation](https://github.com/signalapp/SparsePostQuantumRatchet/blob/fd320484dcec89004021e6fdc7481825f5f261fa/src/encoding/polynomial.rs#L751-L976)
-/

@[expose] public section

namespace ErasureCodePayload.Streaming

variable {M Sym : Type}

/-- Encoder state for one erasure-coded payload stream. It stores the erasure-code
payload scheme, the payload being encoded, and the counter for the next chunk. -/
-- ANCHOR: ErasureCodePayload_Streaming_EncoderState
structure EncoderState (M Sym : Type) where
  /-- The erasure-code payload scheme used to encode this stream. -/
  ecp : ErasureCodePayload M Sym
  /-- The fixed payload encoded by this stream. -/
  payload : M
  /-- The natural-number counter used for the next emitted chunk. -/
  nextIndex : ℕ
-- ANCHOR_END: ErasureCodePayload_Streaming_EncoderState


namespace EncoderState

/-- Initialize an encoder before emitting its first chunk. -/
-- ANCHOR: ErasureCodePayload_Streaming_init
def init (ecp : ErasureCodePayload M Sym) (payload : M) : EncoderState M Sym :=
  { ecp, payload, nextIndex := 0 }
-- ANCHOR_END: ErasureCodePayload_Streaming_init

/-- Emit the chunk at the current counter and advance the counter by one. -/
-- ANCHOR: ErasureCodePayload_Streaming_nextChunk
def nextChunk (state : EncoderState M Sym) :
    (ℕ × Sym) × EncoderState M Sym :=
  (state.ecp.encode state.payload state.nextIndex,
    { state with nextIndex := state.nextIndex + 1 })
-- ANCHOR_END: ErasureCodePayload_Streaming_nextChunk

/-- The emitted chunk index is the encoder counter reduced modulo the codeword size. -/
theorem nextChunk_index (state : EncoderState M Sym) :
    state.nextChunk.1.1 = state.nextIndex % state.ecp.ec.N := rfl

end EncoderState


/-- A streaming decoder for payloads in `M` from indexed symbols in `Sym`. -/
-- ANCHOR: StreamDecoder
structure StreamDecoder (M Sym : Type) where
  /-- Decoder state. -/
  D : Type
  /-- Initial state. -/
  empty : D
  /-- Adds one indexed chunk. -/
  addChunk : D → ℕ × Sym → D
  /-- The decoded payload, if any. -/
  decodedPayload : D → Option M
-- ANCHOR_END: StreamDecoder

namespace StreamDecoder

/-- The state of `dec` after it receives the chunks `ecp.encode p i` for `i` in `is`, in order. -/
-- ANCHOR: StreamDecoder_run
def run (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) (is : List ℕ) :
    dec.D :=
  is.foldl (fun d i => dec.addChunk d (ecp.encode p i)) dec.empty
-- ANCHOR_END: StreamDecoder_run

/-- `dec` is sound for `ecp` if a decoder that received only chunks of `p`, at least one, decodes
to `none` or `some p`. Soundness does not imply that `dec` ever decodes, and it does not constrain
`decodedPayload` of the initial state. -/
-- ANCHOR: StreamDecoder_Sound
def Sound (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) : Prop :=
  ∀ (p : M) (is : List ℕ), is ≠ [] →
    dec.decodedPayload (dec.run ecp p is) = none ∨
      dec.decodedPayload (dec.run ecp p is) = some p
-- ANCHOR_END: StreamDecoder_Sound

/-- The state `d` of `dec` received only chunks of `p`, possibly none. -/
-- ANCHOR: StreamDecoder_Received
def Received (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) (d : dec.D) :
    Prop :=
  ∃ is : List ℕ, d = dec.run ecp p is
-- ANCHOR_END: StreamDecoder_Received

variable {dec : StreamDecoder M Sym} {ecp : ErasureCodePayload M Sym} {p : M}

/-- Running one more chunk adds it to the previous state. -/
theorem run_append_singleton (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym)
    (p : M) (is : List ℕ) (i : ℕ) :
    dec.run ecp p (is ++ [i]) = dec.addChunk (dec.run ecp p is) (ecp.encode p i) := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The initial state received only chunks of every payload. -/
theorem received_empty (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) :
    dec.Received ecp p dec.empty :=
  ⟨[], rfl⟩

/-- Adding a chunk of `p` to a state that received only chunks of `p` keeps that property. -/
theorem Received.addChunk {d : dec.D} (hd : dec.Received ecp p d) (i : ℕ) :
    dec.Received ecp p (dec.addChunk d (ecp.encode p i)) := by
  obtain ⟨is, rfl⟩ := hd
  exact ⟨is ++ [i], (run_append_singleton dec ecp p is i).symm⟩

/-- Let `I` hold for the initial state and be preserved by adding a chunk of `p`. Then `I` holds
for every state that received only chunks of `p`. -/
theorem Received.induction {I : dec.D → Prop} (h0 : I dec.empty)
    (hstep : ∀ d i, I d → I (dec.addChunk d (ecp.encode p i)))
    {d : dec.D} (hd : dec.Received ecp p d) : I d := by
  obtain ⟨is, rfl⟩ := hd
  induction is using List.reverseRecOn with
  | nil => exact h0
  | append_singleton is i ih =>
      rw [run_append_singleton]
      exact hstep _ i ih

/-- Let `dec` be sound for `ecp`, and let `d` have received only chunks of `p`. Then adding a chunk
of `p` gives a state that received only chunks of `p` and decodes to `none` or `some p`. -/
theorem Sound.received_addChunk (hsound : dec.Sound ecp) {d : dec.D}
    (hd : dec.Received ecp p d) (i : ℕ) :
    dec.Received ecp p (dec.addChunk d (ecp.encode p i)) ∧
      (dec.decodedPayload (dec.addChunk d (ecp.encode p i)) = none ∨
        dec.decodedPayload (dec.addChunk d (ecp.encode p i)) = some p) := by
  refine ⟨hd.addChunk i, ?_⟩
  obtain ⟨is, rfl⟩ := hd
  rw [← run_append_singleton]
  exact hsound p (is ++ [i]) (by simp)

/-- Let `I p` hold for the initial state for every `p`. Let adding a chunk of `p` to a state that
satisfies `I p` give a state that satisfies `I p` and decodes to `none` or `some p`. Then `dec` is
sound for `ecp`. -/
theorem Sound.of_inv (I : M → dec.D → Prop) (h0 : ∀ p, I p dec.empty)
    (hstep : ∀ d p i, I p d →
      I p (dec.addChunk d (ecp.encode p i)) ∧
        (dec.decodedPayload (dec.addChunk d (ecp.encode p i)) = none ∨
          dec.decodedPayload (dec.addChunk d (ecp.encode p i)) = some p)) :
    dec.Sound ecp := by
  intro p is hne
  obtain ⟨is, i, rfl⟩ := (List.eq_nil_or_concat is).resolve_left hne
  rw [List.concat_eq_append, run_append_singleton]
  exact (hstep _ p i
    (Received.induction (I := I p) (h0 p) (fun d i h => (hstep d p i h).1) ⟨is, rfl⟩)).2

end StreamDecoder

namespace SetDecoder

/-- The chunk set already contains a chunk at `index`. -/
-- ANCHOR: SetDecoder_HasIndex
def HasIndex (chunks : Finset (ℕ × Sym)) (index : ℕ) : Prop :=
  ∃ chunk ∈ chunks, chunk.1 = index
-- ANCHOR_END: SetDecoder_HasIndex

/-- Whether a chunk set contains a chunk at a given index is decidable. -/
instance (chunks : Finset (ℕ × Sym)) (index : ℕ) : Decidable (HasIndex chunks index) := by
  unfold HasIndex
  infer_instance

/-- Stored chunks have pairwise distinct indices. -/
def IndexUnique (chunks : Finset (ℕ × Sym)) : Prop :=
  Set.InjOn Prod.fst (chunks : Set (ℕ × Sym))

/-- Add a chunk unless its index is already present. The first symbol received at an
index is retained, so exact duplicates are harmless and later conflicts are ignored.
The soundness and recovery results below cover only chunks encoded from one payload. Their
indices are in range by construction. -/
-- ANCHOR: SetDecoder_addChunk
def addChunk [DecidableEq Sym] (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) :
    Finset (ℕ × Sym) :=
  if HasIndex chunks chunk.1 then chunks else insert chunk chunks
-- ANCHOR_END: SetDecoder_addChunk

end SetDecoder

/-- The set-based decoder of `ecp`. It keeps the first symbol received at each index and decodes
the stored chunk set with `ecp.decode`. -/
-- ANCHOR: setDecoder
def setDecoder [DecidableEq Sym] (ecp : ErasureCodePayload M Sym) : StreamDecoder M Sym where
  D := Finset (ℕ × Sym)
  empty := ∅
  addChunk := SetDecoder.addChunk
  decodedPayload := ecp.decode
-- ANCHOR_END: setDecoder

namespace SetDecoder

/-- The empty chunk set has pairwise distinct stored indices. -/
@[simp]
theorem indexUnique_empty : IndexUnique (∅ : Finset (ℕ × Sym)) := by
  simp [IndexUnique]

/-- A chunk whose index is already present leaves the chunk set unchanged. -/
theorem addChunk_eq_self_of_hasIndex [DecidableEq Sym]
    (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) (h : HasIndex chunks chunk.1) :
    addChunk chunks chunk = chunks := by
  simp [addChunk, h]

/-- After adding a chunk, its index is present in the chunk set. -/
private theorem hasIndex_addChunk_self [DecidableEq Sym]
    (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) :
    HasIndex (addChunk chunks chunk) chunk.1 := by
  by_cases h : HasIndex chunks chunk.1
  · simp [addChunk, h]
  · refine ⟨chunk, ?_, rfl⟩
    simp [addChunk, h]

/-- Adding the same chunk twice is idempotent. -/
@[simp]
theorem addChunk_idempotent [DecidableEq Sym]
    (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) :
    addChunk (addChunk chunks chunk) chunk = addChunk chunks chunk :=
  addChunk_eq_self_of_hasIndex _ _ (hasIndex_addChunk_self chunks chunk)

/-- First-received-value behavior for two chunks with the same index. -/
theorem addChunk_sameIndex [DecidableEq Sym]
    (chunks : Finset (ℕ × Sym)) (first second : ℕ × Sym)
    (hindex : first.1 = second.1) :
    addChunk (addChunk chunks first) second = addChunk chunks first := by
  apply addChunk_eq_self_of_hasIndex
  obtain ⟨stored, hstored, hstoredIndex⟩ := hasIndex_addChunk_self chunks first
  exact ⟨stored, hstored, hstoredIndex.trans hindex⟩

/-- First-wins insertion preserves pairwise uniqueness of stored indices. -/
theorem indexUnique_addChunk [DecidableEq Sym]
    (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) (hunique : IndexUnique chunks) :
    IndexUnique (addChunk chunks chunk) := by
  by_cases h : HasIndex chunks chunk.1
  · simpa [addChunk, h] using hunique
  · rw [IndexUnique]
    simp only [addChunk, h, ↓reduceIte]
    intro a ha b hb hab
    have ha' : a = chunk ∨ a ∈ chunks := by simpa using ha
    have hb' : b = chunk ∨ b ∈ chunks := by simpa using hb
    rcases ha' with haeq | haState
    · rcases hb' with hbeq | hbState
      · exact haeq.trans hbeq.symm
      · subst a
        exact False.elim (h ⟨b, hbState, hab.symm⟩)
    · rcases hb' with hbeq | hbState
      · subst b
        exact False.elim (h ⟨a, haState, hab⟩)
      · exact hunique haState hbState hab

/-- Chunk sets reachable from `∅` by repeatedly applying `addChunk` to arbitrary chunks. -/
inductive Reachable [DecidableEq Sym] : Finset (ℕ × Sym) → Prop
  | empty : Reachable ∅
  | addChunk {chunks : Finset (ℕ × Sym)} {chunk : ℕ × Sym} :
      Reachable chunks → Reachable (addChunk chunks chunk)

/-- Every chunk set reachable from `∅` has pairwise distinct stored indices. -/
theorem indexUnique_of_reachable [DecidableEq Sym]
    {chunks : Finset (ℕ × Sym)} (hreach : Reachable chunks) :
    IndexUnique chunks := by
  induction hreach with
  | empty => simp
  | addChunk hreach ih => exact indexUnique_addChunk _ _ ih

/-- If any stored chunk index is out of range, decoding returns `none`. -/
theorem decode_eq_none_of_invalid (ecp : ErasureCodePayload M Sym)
    (chunks : Finset (ℕ × Sym)) (hinvalid : ∃ chunk ∈ chunks, ecp.ec.N ≤ chunk.1) :
    ecp.decode chunks = none := by
  rw [ErasureCodePayload.decode]
  split
  next hvalid =>
    obtain ⟨chunk, hchunk, hindex⟩ := hinvalid
    exact False.elim (Nat.not_lt_of_ge hindex (hvalid chunk hchunk))
  next => rfl

/-- In a chunk set built from correctly encoded chunks, an emitted chunk's index is
present exactly when its codeword position has already been received. -/
private theorem hasIndex_payloadChunks_iff
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    HasIndex (ErasureCodePayload.payloadChunks ecp payload I) (ecp.encode payload i).1 ↔
      ErasureCodePayload.counterIndex ecp i ∈ I := by
  classical
  constructor
  · rintro ⟨natChunk, hnatChunk, hindex⟩
    rw [ErasureCodePayload.payloadChunks, Finset.mem_map] at hnatChunk
    obtain ⟨bounded, hbounded, hboundedEq⟩ := hnatChunk
    have hboundedMem :=
      (ecp.ec.mem_encodeChunks (ecp.serialize payload) I bounded).mp hbounded
    have hvalue : bounded.1.val = (ecp.encode payload i).1 := by
      calc
        bounded.1.val = (ErasureCode.chunkToNat bounded).1 := rfl
        _ = natChunk.1 := congrArg Prod.fst hboundedEq
        _ = (ecp.encode payload i).1 := hindex
    have hboundedIndex : bounded.1 = ErasureCodePayload.counterIndex ecp i := by
      apply Fin.ext
      exact hvalue
    simpa [hboundedIndex] using hboundedMem.1
  · intro hmem
    refine ⟨ecp.encode payload i, ?_, rfl⟩
    rw [ErasureCodePayload.payloadChunks, Finset.mem_map]
    let bounded : Fin ecp.ec.N × Sym :=
      (ErasureCodePayload.counterIndex ecp i,
        ecp.ec.encode (ecp.serialize payload) (ErasureCodePayload.counterIndex ecp i))
    refine ⟨bounded, ?_, ?_⟩
    · exact (ecp.ec.mem_encodeChunks (ecp.serialize payload) I bounded).2 ⟨hmem, rfl⟩
    · exact (ErasureCodePayload.encode_eq_chunkToNat ecp payload i).symm

/-- Adding a correctly encoded chunk to a chunk set built from chunks of the same payload
preserves that representation and records the chunk's codeword position. -/
-- ANCHOR: addChunk_payloadChunks
theorem addChunk_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    addChunk (ErasureCodePayload.payloadChunks ecp payload I) (ecp.encode payload i) =
      ErasureCodePayload.payloadChunks ecp payload
        (insert (ErasureCodePayload.counterIndex ecp i) I)
-- ANCHOR_END: addChunk_payloadChunks
    := by
  by_cases hmem : ErasureCodePayload.counterIndex ecp i ∈ I
  · have hhas := (hasIndex_payloadChunks_iff ecp payload I i).2 hmem
    rw [addChunk_eq_self_of_hasIndex _ _ hhas]
    simp [Finset.insert_eq_of_mem hmem]
  · have hhas :
        ¬HasIndex (ErasureCodePayload.payloadChunks ecp payload I) (ecp.encode payload i).1 := by
      simpa [hasIndex_payloadChunks_iff ecp payload I i] using hmem
    simp only [addChunk, hhas, ↓reduceIte]
    exact ErasureCodePayload.insert_payloadChunks ecp payload I i

/-- Adding one honest chunk to an honest sub-threshold chunk set either remains below
the threshold with no payload, or reaches the threshold and decodes the payload. -/
theorem addChunk_honest [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N)) (i : ℕ)
    (hcard : I.card < ecp.ec.nchunk) :
    let I' := insert (ErasureCodePayload.counterIndex ecp i) I
    (I'.card < ecp.ec.nchunk ∧
        ecp.decode (addChunk (ErasureCodePayload.payloadChunks ecp payload I)
          (ecp.encode payload i)) = none) ∨
      (I'.card = ecp.ec.nchunk ∧
        ecp.decode (addChunk (ErasureCodePayload.payloadChunks ecp payload I)
          (ecp.encode payload i)) = some payload) := by
  rw [addChunk_payloadChunks]
  simpa [ErasureCodePayload.insert_payloadChunks] using
    (ErasureCodePayload.decode_insert_honest ecp hcorrect payload I i hcard)

/-- Adding a correctly encoded chunk to a chunk set that holds chunks of the same payload gives a
chunk set that again holds chunks of that payload, and that decodes to nothing or the payload. -/
theorem addChunk_encode_of_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (chunks : Finset (ℕ × Sym))
    (hchunks : ∃ I : Finset (Fin ecp.ec.N),
      chunks = ErasureCodePayload.payloadChunks ecp payload I)
    (i : ℕ) :
    (∃ I' : Finset (Fin ecp.ec.N),
        addChunk chunks (ecp.encode payload i) =
          ErasureCodePayload.payloadChunks ecp payload I') ∧
      (ecp.decode (addChunk chunks (ecp.encode payload i)) = none ∨
        ecp.decode (addChunk chunks (ecp.encode payload i)) = some payload) := by
  obtain ⟨I, rfl⟩ := hchunks
  let I' := insert (ErasureCodePayload.counterIndex ecp i) I
  rw [addChunk_payloadChunks]
  refine ⟨⟨I', rfl⟩, ?_⟩
  by_cases hcard : ecp.ec.nchunk ≤ I'.card
  · exact Or.inr (ErasureCodePayload.decode_payloadChunks ecp hcorrect payload I' hcard)
  · exact Or.inl (ErasureCodePayload.decode_payloadChunks_none
      ecp hcorrect payload I' (Nat.lt_of_not_ge hcard))

/-- Codeword positions delivered from the first `t` encoder counters. A counter absent
from `delivered` models a lost chunk. -/
def honestPrefixPositions (ecp : ErasureCodePayload M Sym)
    (delivered : Finset ℕ) : ℕ → Finset (Fin ecp.ec.N)
  | 0 => ∅
  | t + 1 =>
      if t ∈ delivered then
        insert (ErasureCodePayload.counterIndex ecp t)
          (honestPrefixPositions ecp delivered t)
      else
        honestPrefixPositions ecp delivered t

/-- Chunk set after processing the first `t` encoder emissions, adding exactly
the counters selected by `delivered` and dropping the others. -/
def honestPrefixDecoder [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (delivered : Finset ℕ) : ℕ → Finset (ℕ × Sym)
  | 0 => ∅
  | t + 1 =>
      if t ∈ delivered then
        addChunk (honestPrefixDecoder ecp payload delivered t) (ecp.encode payload t)
      else
        honestPrefixDecoder ecp payload delivered t

/-- Every lossy honest prefix run is reachable from `∅` by repeated `addChunk` steps. -/
theorem honestPrefixDecoder_reachable [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M) (delivered : Finset ℕ) :
    ∀ t, Reachable (honestPrefixDecoder ecp payload delivered t)
  | 0 => Reachable.empty
  | t + 1 => by
      by_cases h : t ∈ delivered
      · rw [honestPrefixDecoder, ite_eq_left h]
        exact Reachable.addChunk (honestPrefixDecoder_reachable ecp payload delivered t)
      · rw [honestPrefixDecoder, ite_eq_right h]
        exact honestPrefixDecoder_reachable ecp payload delivered t

/-- Lossy honest prefix runs retain at most one stored symbol per index. -/
theorem indexUnique_honestPrefix [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (delivered : Finset ℕ) (t : ℕ) :
    IndexUnique (honestPrefixDecoder ecp payload delivered t) :=
  indexUnique_of_reachable (honestPrefixDecoder_reachable ecp payload delivered t)

/-- One streaming step: the chunk emitted by `nextChunk` at counter `t` is either
delivered to the decoder or lost according to `delivered`. -/
theorem honestPrefixDecoder_succ [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (delivered : Finset ℕ) (t : ℕ) :
    honestPrefixDecoder ecp payload delivered (t + 1) =
      if t ∈ delivered then
        addChunk (honestPrefixDecoder ecp payload delivered t)
          ((EncoderState.nextChunk { ecp := ecp, payload := payload, nextIndex := t }).1)
      else
        honestPrefixDecoder ecp payload delivered t := by
  rfl

/-- A lossy run over the first `t` emissions yields exactly the honest chunk-set
representation at the positions that were delivered. -/
theorem honestPrefixDecoder_eq_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M) (delivered : Finset ℕ) :
    ∀ t,
      honestPrefixDecoder ecp payload delivered t =
        ErasureCodePayload.payloadChunks ecp payload (honestPrefixPositions ecp delivered t)
  | 0 => by
      simp [honestPrefixDecoder, honestPrefixPositions]
  | t + 1 => by
      by_cases h : t ∈ delivered
      · simp [honestPrefixDecoder, honestPrefixPositions, h,
          honestPrefixDecoder_eq_payloadChunks, addChunk_payloadChunks]
      · simp [honestPrefixDecoder, honestPrefixPositions, h,
          honestPrefixDecoder_eq_payloadChunks]

/-- End-to-end recovery from an arbitrary lossy subset of the first `t` emissions,
provided the delivered positions meet the reconstruction threshold. -/
theorem decode_honestPrefix [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (delivered : Finset ℕ) (t : ℕ)
    (hcard : ecp.ec.nchunk ≤ (honestPrefixPositions ecp delivered t).card) :
    ecp.decode (honestPrefixDecoder ecp payload delivered t) = some payload := by
  rw [honestPrefixDecoder_eq_payloadChunks]
  exact ErasureCodePayload.decode_payloadChunks ecp hcorrect payload
    (honestPrefixPositions ecp delivered t) hcard

end SetDecoder

/-- Let the erasure code of `ecp` be correct. Then `setDecoder ecp` is sound for `ecp`. -/
-- ANCHOR: setDecoder_sound
theorem setDecoder_sound [DecidableEq Sym] (ecp : ErasureCodePayload M Sym)
    (hcorrect : ecp.ec.Correct) : (setDecoder ecp).Sound ecp
-- ANCHOR_END: setDecoder_sound
    :=
  StreamDecoder.Sound.of_inv
    (fun p (chunks : Finset (ℕ × Sym)) =>
      ∃ I : Finset (Fin ecp.ec.N), chunks = ErasureCodePayload.payloadChunks ecp p I)
    (fun p => ⟨∅, (ErasureCodePayload.payloadChunks_empty ecp p).symm⟩)
    (fun chunks p i hchunks =>
      SetDecoder.addChunk_encode_of_payloadChunks ecp hcorrect p chunks hchunks i)

end ErasureCodePayload.Streaming
