/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.Payload

/-!
# Stateful Erasure-Code Streaming

Protocol-independent stateful wrappers over `ErasureCodePayload`. The encoder emits
successive natural-number-indexed chunks. An `EncoderState` stores its `ErasureCodePayload`
scheme, so a stream cannot be encoded under a different scheme.

A `StreamDecoder` is a decoder given by its operations: a state type, an initial state, an
operation that adds one indexed chunk, and a partial decoding function. `StreamDecoder.Sound` is
the law that the ML-KEM Braid correctness proofs use: a decoder that received only chunks of `p`,
at least one, decodes to `none` or `some p`. SPQR uses the same decoder interface.
`StreamDecoder.Received` is the matching invariant, and `StreamDecoder.Sound.of_inv` proves
soundness from an instance's own invariant.

`setDecoder ecp` is the set-based instance. Its state is a finite set of indexed chunks that stores
at most one symbol per index and keeps the first symbol received at a repeated index. It is sound
when the erasure code is correct (`setDecoder_sound`).

The encoder and `setDecoder` model the observable streaming behavior of ML-KEM Braid and SPQR.
They abstract away the byte representation, polynomial caches, bounded storage, and
serialization of Signal's implementation. Other `StreamDecoder` instances can model these.

## References

- [Signal ML-KEM Braid, §2.2: Encode/Decode](https://signal.org/docs/specifications/mlkembraid/)
- [SparsePostQuantumRatchet encoder and decoder interfaces](https://github.com/signalapp/SparsePostQuantumRatchet/blob/fd320484dcec89004021e6fdc7481825f5f261fa/src/encoding.rs#L24-L47)
- [SparsePostQuantumRatchet polynomial streaming implementation](https://github.com/signalapp/SparsePostQuantumRatchet/blob/fd320484dcec89004021e6fdc7481825f5f261fa/src/encoding/polynomial.rs#L751-L976)
-/

namespace ErasureCodePayload.Streaming

variable {M Sym : Type}

-- ANCHOR: ErasureCodePayload_Streaming_States
/-- Encoder state for one erasure-coded payload stream. It stores the erasure-code
payload scheme, the payload being encoded, and the counter for the next chunk. -/
structure EncoderState (M Sym : Type) where
  /-- The erasure-code payload scheme used to encode this stream. -/
  ecp : ErasureCodePayload M Sym
  /-- The fixed payload encoded by this stream. -/
  payload : M
  /-- The natural-number counter used for the next emitted chunk. -/
  nextIndex : ℕ

/-- Decoder state for one erasure-coded payload stream. It stores the erasure-code
payload scheme and the indexed chunks received so far. -/
structure DecoderState (M Sym : Type) where
  /-- The erasure-code payload scheme used to decode this stream. -/
  ecp : ErasureCodePayload M Sym
  /-- Indexed chunks retained by the decoder, with at most one symbol per index for
  states reachable from `empty` through `addChunk`. -/
  chunks : Finset (ℕ × Sym)
-- ANCHOR_END: ErasureCodePayload_Streaming_States

namespace EncoderState
-- ANCHOR: ErasureCodePayload_Streaming_Encoder

/-- Initialize an encoder before emitting its first chunk. -/
def init (ecp : ErasureCodePayload M Sym) (payload : M) : EncoderState M Sym :=
  { ecp, payload, nextIndex := 0 }

/-- Emit the chunk at the current counter and advance the counter by one. -/
def nextChunk (state : EncoderState M Sym) :
    (ℕ × Sym) × EncoderState M Sym :=
  (state.ecp.encode state.payload state.nextIndex,
    { state with nextIndex := state.nextIndex + 1 })
-- ANCHOR_END: ErasureCodePayload_Streaming_Encoder

/-- The emitted chunk index is the encoder counter reduced modulo the codeword size. -/
theorem nextChunk_index (state : EncoderState M Sym) :
    state.nextChunk.1.1 = state.nextIndex % state.ecp.ec.N := rfl

end EncoderState

namespace DecoderState
-- ANCHOR: ErasureCodePayload_Streaming_Decoder

/-- The decoder already contains a chunk at `index`. -/
def HasIndex (state : DecoderState M Sym) (index : ℕ) : Prop :=
  ∃ chunk ∈ state.chunks, chunk.1 = index

/-- Whether the decoder contains a chunk at a given index is decidable. -/
instance (state : DecoderState M Sym) (index : ℕ) :
    Decidable (state.HasIndex index) := by
  unfold HasIndex
  infer_instance

/-- Stored chunks have pairwise distinct indices. -/
def IndexUnique (state : DecoderState M Sym) : Prop :=
  Set.InjOn Prod.fst (state.chunks : Set (ℕ × Sym))

/-- Initialize a decoder with no received chunks. -/
def empty (ecp : ErasureCodePayload M Sym) : DecoderState M Sym :=
  { ecp, chunks := ∅ }

/-- Add a chunk unless its index is already present. The first symbol received at an
index is retained, so exact duplicates are harmless and later conflicts are ignored.
Streaming guarantees here are erasure-only and assume honest, in-range chunk indices. -/
def addChunk [DecidableEq Sym] (state : DecoderState M Sym) (chunk : ℕ × Sym) :
    DecoderState M Sym :=
  if state.HasIndex chunk.1 then state
  else { state with chunks := insert chunk state.chunks }

/-- Attempt to decode the chunks accumulated by the decoder. -/
def decodedPayload (state : DecoderState M Sym) : Option M :=
  state.ecp.decode state.chunks

/-- Whether the accumulated chunks currently decode to a payload. -/
def hasMessage (state : DecoderState M Sym) : Bool :=
  state.decodedPayload.isSome
-- ANCHOR_END: ErasureCodePayload_Streaming_Decoder

/-- The empty decoder has pairwise distinct stored indices. -/
@[simp]
theorem indexUnique_empty (ecp : ErasureCodePayload M Sym) :
    (empty ecp).IndexUnique := by
  simp [IndexUnique, empty]

/-- A chunk whose index is already present leaves the decoder state unchanged. -/
theorem addChunk_eq_self_of_hasIndex [DecidableEq Sym]
    (state : DecoderState M Sym) (chunk : ℕ × Sym) (h : state.HasIndex chunk.1) :
    state.addChunk chunk = state := by
  simp [addChunk, h]

/-- After adding a chunk, its index is present in the decoder state. -/
private theorem hasIndex_addChunk_self [DecidableEq Sym]
    (state : DecoderState M Sym) (chunk : ℕ × Sym) :
    (state.addChunk chunk).HasIndex chunk.1 := by
  by_cases h : state.HasIndex chunk.1
  · simp [addChunk, h]
  · refine ⟨chunk, ?_, rfl⟩
    simp [addChunk, h]

/-- Adding the same chunk twice is idempotent. -/
@[simp]
theorem addChunk_idempotent [DecidableEq Sym]
    (state : DecoderState M Sym) (chunk : ℕ × Sym) :
    (state.addChunk chunk).addChunk chunk = state.addChunk chunk := by
  exact addChunk_eq_self_of_hasIndex _ _ (hasIndex_addChunk_self state chunk)

/-- First-received-value behavior for two chunks with the same index. -/
theorem addChunk_sameIndex [DecidableEq Sym]
    (state : DecoderState M Sym) (first second : ℕ × Sym)
    (hindex : first.1 = second.1) :
    (state.addChunk first).addChunk second = state.addChunk first := by
  apply addChunk_eq_self_of_hasIndex
  obtain ⟨stored, hstored, hstoredIndex⟩ := hasIndex_addChunk_self state first
  exact ⟨stored, hstored, hstoredIndex.trans hindex⟩

/-- First-wins insertion preserves pairwise uniqueness of stored indices. -/
theorem indexUnique_addChunk [DecidableEq Sym]
    (state : DecoderState M Sym) (chunk : ℕ × Sym) (hunique : state.IndexUnique) :
    (state.addChunk chunk).IndexUnique := by
  by_cases h : state.HasIndex chunk.1
  · simpa [addChunk, h] using hunique
  · rw [IndexUnique]
    simp only [addChunk, h, ↓reduceIte]
    intro a ha b hb hab
    have ha' : a = chunk ∨ a ∈ state.chunks := by simpa using ha
    have hb' : b = chunk ∨ b ∈ state.chunks := by simpa using hb
    rcases ha' with haeq | haState
    · rcases hb' with hbeq | hbState
      · exact haeq.trans hbeq.symm
      · subst a
        exact False.elim (h ⟨b, hbState, hab.symm⟩)
    · rcases hb' with hbeq | hbState
      · subst b
        exact False.elim (h ⟨a, haState, hab⟩)
      · exact hunique haState hbState hab

/-- Decoder states reachable from `empty ecp` by repeatedly applying `addChunk`. -/
inductive Reachable [DecidableEq Sym] (ecp : ErasureCodePayload M Sym) :
    DecoderState M Sym → Prop
  | empty : Reachable ecp (DecoderState.empty ecp)
  | addChunk {state : DecoderState M Sym} {chunk : ℕ × Sym} :
      Reachable ecp state → Reachable ecp (state.addChunk chunk)

/-- Every decoder state reachable from `empty` has pairwise distinct stored indices. -/
theorem indexUnique_of_reachable [DecidableEq Sym]
    {ecp : ErasureCodePayload M Sym} {state : DecoderState M Sym}
    (hreach : Reachable ecp state) :
    state.IndexUnique := by
  induction hreach with
  | empty => simp
  | addChunk hreach ih => exact indexUnique_addChunk _ _ ih

/-- The decoder reports a message exactly when decoding returns a payload. -/
theorem hasMessage_eq_true_iff (state : DecoderState M Sym) :
    state.hasMessage = true ↔ ∃ payload, state.decodedPayload = some payload := by
  simpa [hasMessage] using
    (Option.isSome_iff_exists (x := state.decodedPayload))

/-- If any stored chunk index is out of range, decoding returns `none`. -/
theorem decodedPayload_eq_none_of_invalid (state : DecoderState M Sym)
    (hinvalid : ∃ chunk ∈ state.chunks, state.ecp.ec.N ≤ chunk.1) :
    state.decodedPayload = none := by
  rw [decodedPayload, ErasureCodePayload.decode]
  split
  next hvalid =>
    obtain ⟨chunk, hchunk, hindex⟩ := hinvalid
    exact False.elim (Nat.not_lt_of_ge hindex (hvalid chunk hchunk))
  next => rfl

/-- In a decoder built from correctly encoded chunks, an emitted chunk's index is
present exactly when its codeword position has already been received. -/
private theorem hasIndex_payloadChunks_iff
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    (DecoderState.mk ecp (ErasureCodePayload.payloadChunks ecp payload I)).HasIndex
        (ecp.encode payload i).1 ↔
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

/-- Adding a correctly encoded chunk to a decoder built from chunks of the same
payload preserves that representation and records the chunk's codeword position. -/
theorem addChunk_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    (DecoderState.mk ecp (ErasureCodePayload.payloadChunks ecp payload I)).addChunk
        (ecp.encode payload i) =
      DecoderState.mk ecp
        (ErasureCodePayload.payloadChunks ecp payload
          (insert (ErasureCodePayload.counterIndex ecp i) I)) := by
  by_cases hmem : ErasureCodePayload.counterIndex ecp i ∈ I
  · have hhas := (hasIndex_payloadChunks_iff ecp payload I i).2 hmem
    rw [addChunk_eq_self_of_hasIndex _ _ hhas]
    simp [Finset.insert_eq_of_mem hmem]
  · have hhas :
        ¬(DecoderState.mk ecp (ErasureCodePayload.payloadChunks ecp payload I)).HasIndex
          (ecp.encode payload i).1 := by
      simpa [hasIndex_payloadChunks_iff ecp payload I i] using hmem
    simp only [addChunk, hhas, ↓reduceIte]
    exact congrArg (DecoderState.mk ecp)
      (ErasureCodePayload.insert_payloadChunks ecp payload I i)

/-- An honest decoder state at or above the threshold decodes its payload. -/
theorem decodedPayload_payloadChunks
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : ecp.ec.nchunk ≤ I.card) :
    (DecoderState.mk ecp (ErasureCodePayload.payloadChunks ecp payload I)).decodedPayload =
      some payload := by
  exact ErasureCodePayload.decode_payloadChunks ecp hcorrect payload I hcard

/-- Adding one honest chunk to an honest sub-threshold decoder either remains below
the threshold with no payload, or reaches the threshold and decodes the payload. -/
theorem addChunk_honest [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N)) (i : ℕ)
    (hcard : I.card < ecp.ec.nchunk) :
    let I' := insert (ErasureCodePayload.counterIndex ecp i) I
    (I'.card < ecp.ec.nchunk ∧
        ((DecoderState.mk ecp (ErasureCodePayload.payloadChunks ecp payload I)).addChunk
          (ecp.encode payload i)).decodedPayload = none) ∨
      (I'.card = ecp.ec.nchunk ∧
        ((DecoderState.mk ecp (ErasureCodePayload.payloadChunks ecp payload I)).addChunk
          (ecp.encode payload i)).decodedPayload = some payload) := by
  rw [addChunk_payloadChunks]
  simpa [decodedPayload, ErasureCodePayload.insert_payloadChunks] using
    (ErasureCodePayload.decode_insert_honest ecp hcorrect payload I i hcard)

/-- Adding a correctly encoded chunk to a decoder that holds chunks of the same payload gives a
decoder that again holds chunks of that payload, and that has decoded either nothing or the
payload. -/
theorem addChunk_encode_of_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (dec : DecoderState M Sym)
    (hdec : dec.ecp = ecp ∧
      ∃ I : Finset (Fin ecp.ec.N),
        dec.chunks = ErasureCodePayload.payloadChunks ecp payload I)
    (i : ℕ) :
    let dec' := dec.addChunk (ecp.encode payload i)
    dec'.ecp = ecp ∧
      (∃ I' : Finset (Fin ecp.ec.N),
        dec'.chunks = ErasureCodePayload.payloadChunks ecp payload I') ∧
      (dec'.decodedPayload = none ∨ dec'.decodedPayload = some payload) := by
  obtain ⟨actualEcp, chunks⟩ := dec
  obtain ⟨hecp, I, hchunks⟩ := hdec
  change actualEcp = ecp at hecp
  subst actualEcp
  change chunks = ErasureCodePayload.payloadChunks ecp payload I at hchunks
  subst chunks
  let I' := insert (ErasureCodePayload.counterIndex ecp i) I
  rw [addChunk_payloadChunks]
  refine ⟨rfl, ⟨I', rfl⟩, ?_⟩
  by_cases hcard : ecp.ec.nchunk ≤ I'.card
  · exact Or.inr (decodedPayload_payloadChunks ecp hcorrect payload I' hcard)
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

/-- Decoder state after processing the first `t` encoder emissions, adding exactly
the counters selected by `delivered` and dropping the others. -/
def honestPrefixDecoder [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (delivered : Finset ℕ) : ℕ → DecoderState M Sym
  | 0 => empty ecp
  | t + 1 =>
      if t ∈ delivered then
        (honestPrefixDecoder ecp payload delivered t).addChunk (ecp.encode payload t)
      else
        honestPrefixDecoder ecp payload delivered t

/-- Every lossy honest prefix run is reachable from `empty` by repeated `addChunk`
steps. -/
theorem honestPrefixDecoder_reachable [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M) (delivered : Finset ℕ) :
    ∀ t, Reachable ecp (honestPrefixDecoder ecp payload delivered t)
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
    (honestPrefixDecoder ecp payload delivered t).IndexUnique :=
  indexUnique_of_reachable (honestPrefixDecoder_reachable ecp payload delivered t)

/-- One streaming step: the chunk emitted by `nextChunk` at counter `t` is either
delivered to the decoder or lost according to `delivered`. -/
theorem honestPrefixDecoder_succ [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (delivered : Finset ℕ) (t : ℕ) :
    honestPrefixDecoder ecp payload delivered (t + 1) =
      if t ∈ delivered then
        (honestPrefixDecoder ecp payload delivered t).addChunk
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
        DecoderState.mk ecp
          (ErasureCodePayload.payloadChunks ecp payload
            (honestPrefixPositions ecp delivered t))
  | 0 => by
      simp [honestPrefixDecoder, honestPrefixPositions, DecoderState.empty,
        ErasureCodePayload.payloadChunks, ErasureCode.encodeChunks]
  | t + 1 => by
      by_cases h : t ∈ delivered
      · simp [honestPrefixDecoder, honestPrefixPositions, h,
          honestPrefixDecoder_eq_payloadChunks, addChunk_payloadChunks]
      · simp [honestPrefixDecoder, honestPrefixPositions, h,
          honestPrefixDecoder_eq_payloadChunks]

/-- End-to-end recovery from an arbitrary lossy subset of the first `t` emissions,
provided the delivered positions meet the reconstruction threshold. -/
theorem decodedPayload_honestPrefix [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (delivered : Finset ℕ) (t : ℕ)
    (hcard : ecp.ec.nchunk ≤ (honestPrefixPositions ecp delivered t).card) :
    (honestPrefixDecoder ecp payload delivered t).decodedPayload = some payload := by
  rw [honestPrefixDecoder_eq_payloadChunks]
  exact decodedPayload_payloadChunks ecp hcorrect payload
    (honestPrefixPositions ecp delivered t) hcard

end DecoderState

-- ANCHOR: StreamDecoder
/-- A streaming decoder for payloads in `M` from indexed symbols in `Sym`. -/
structure StreamDecoder (M Sym : Type) where
  /-- Decoder state. -/
  D : Type
  /-- Initial state. -/
  empty : D
  /-- Adds one indexed chunk. -/
  addChunk : D → ℕ × Sym → D
  /-- The decoded payload, if any. -/
  decodedPayload : D → Option M

namespace StreamDecoder

/-- The state of `dec` after it receives the chunks `ecp.encode p i` for `i` in `is`, in order. -/
def run (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) (is : List ℕ) :
    dec.D :=
  is.foldl (fun d i => dec.addChunk d (ecp.encode p i)) dec.empty

/-- `dec` is sound for `ecp` if a decoder that received only chunks of `p`, at least one, decodes
to `none` or `some p`. Soundness does not imply that `dec` ever decodes, and it does not constrain
`decodedPayload` of the initial state. -/
def Sound (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) : Prop :=
  ∀ (p : M) (is : List ℕ), is ≠ [] →
    dec.decodedPayload (dec.run ecp p is) = none ∨
      dec.decodedPayload (dec.run ecp p is) = some p
-- ANCHOR_END: StreamDecoder

-- ANCHOR: StreamDecoder_Received
/-- The state `d` of `dec` received only chunks of `p`, possibly none. -/
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
def HasIndex (chunks : Finset (ℕ × Sym)) (index : ℕ) : Prop :=
  ∃ chunk ∈ chunks, chunk.1 = index

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
def addChunk [DecidableEq Sym] (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) :
    Finset (ℕ × Sym) :=
  if HasIndex chunks chunk.1 then chunks else insert chunk chunks

end SetDecoder

-- ANCHOR: setDecoder
/-- The set-based decoder of `ecp`. It keeps the first symbol received at each index and decodes
the stored chunk set with `ecp.decode`. -/
def setDecoder [DecidableEq Sym] (ecp : ErasureCodePayload M Sym) : StreamDecoder M Sym where
  D := Finset (ℕ × Sym)
  empty := ∅
  addChunk := SetDecoder.addChunk
  decodedPayload := ecp.decode
-- ANCHOR_END: setDecoder

namespace SetDecoder

/-- A chunk whose index is already present leaves the chunk set unchanged. -/
theorem addChunk_eq_self_of_hasIndex [DecidableEq Sym]
    (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) (h : HasIndex chunks chunk.1) :
    addChunk chunks chunk = chunks := by
  simp [addChunk, h]

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
theorem addChunk_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    addChunk (ErasureCodePayload.payloadChunks ecp payload I) (ecp.encode payload i) =
      ErasureCodePayload.payloadChunks ecp payload
        (insert (ErasureCodePayload.counterIndex ecp i) I) := by
  by_cases hmem : ErasureCodePayload.counterIndex ecp i ∈ I
  · have hhas := (hasIndex_payloadChunks_iff ecp payload I i).2 hmem
    rw [addChunk_eq_self_of_hasIndex _ _ hhas]
    simp [Finset.insert_eq_of_mem hmem]
  · have hhas :
        ¬HasIndex (ErasureCodePayload.payloadChunks ecp payload I) (ecp.encode payload i).1 := by
      simpa [hasIndex_payloadChunks_iff ecp payload I i] using hmem
    simp only [addChunk, hhas, ↓reduceIte]
    exact ErasureCodePayload.insert_payloadChunks ecp payload I i

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

end SetDecoder

/-- Let the erasure code of `ecp` be correct. Then `setDecoder ecp` is sound for `ecp`. -/
theorem setDecoder_sound [DecidableEq Sym] (ecp : ErasureCodePayload M Sym)
    (hcorrect : ecp.ec.Correct) : (setDecoder ecp).Sound ecp :=
  StreamDecoder.Sound.of_inv
    (fun p (chunks : Finset (ℕ × Sym)) =>
      ∃ I : Finset (Fin ecp.ec.N), chunks = ErasureCodePayload.payloadChunks ecp p I)
    (fun p => ⟨∅, (ErasureCodePayload.payloadChunks_empty ecp p).symm⟩)
    (fun chunks p i hchunks =>
      SetDecoder.addChunk_encode_of_payloadChunks ecp hcorrect p chunks hchunks i)

end ErasureCodePayload.Streaming
