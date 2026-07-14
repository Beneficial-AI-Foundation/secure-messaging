/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

/-!
# Erasure Codes

Syntax and correctness of erasure codes following Definition A.6 from:

- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf

An *erasure code* over a set of symbols `Σ`, with block length `N` and message size
`nchunk`, consists of two algorithms:
- `Encode(M, i) → c`: encodes message `M ∈ Σ^nchunk` at chunk index `i : ℕ`
  to a symbol `c ∈ Σ`;
- `Decode(L) → M`: from a chunk set `L ⊆ ℕ × Σ`, recovers `M ∈ Σ^nchunk`
  or fails with `⊥`.

This model restricts `Encode` and `Decode` to deterministic functions, covering
deterministic codes such as Reed-Solomon.

Writing `L_I = {(i, Encode(M, i)) | i ∈ I}` for the chunks of `M` at indices `I ⊆ ℕ`,
correctness requires, for all `M` and all `I`:
- `Decode(L_I) = M, if |I| = nchunk`;
- `Decode(L_I) = ⊥, if |I| < nchunk`.
-/

/-- An erasure code over an alphabet `Sym` (Definition A.6 of [SCKA]).

- `Sym`: the alphabet Σ of symbols;
- `N`: the intended block length;
- `nchunk`: the message size; a message is an `nchunk`-tuple of symbols: `Fin nchunk → Sym`;
- `encode M i`: the chunk encoding of message `M` at index `i`;
- `decode L`: recovers a message from a chunk set `L`, or fails (`none`).
-/
-- ANCHOR: ErasureCode
structure ErasureCode (Sym : Type) where
  /-- Intended block length. -/
  N : ℕ
  /-- Message size; a message is `Fin nchunk → Sym`. -/
  nchunk : ℕ
  /-- `Encode(M, i)`: the chunk encoding of message `M` at index `i`. -/
  encode : (Fin nchunk → Sym) → ℕ → Sym
  /-- `Decode(L)`: recover the message from a chunk set, or fail (`none`). -/
  decode : Finset (ℕ × Sym) → Option (Fin nchunk → Sym)
-- ANCHOR_END: ErasureCode

/-- An erasure code over `Sym` equipped with serialization for payloads of type `M`. -/
structure ErasureCodePayload (M Sym : Type) where
  /-- The erasure code used for this payload type. -/
  ec : ErasureCode Sym
  /-- Serialize a payload as the `nchunk`-symbol message consumed by `ec.encode`. -/
  serialize : M → Fin ec.nchunk → Sym
  /-- Parse a decoded `nchunk`-symbol message as a payload, or fail. -/
  parse : (Fin ec.nchunk → Sym) → Option M

namespace ErasureCodePayload

variable {M Sym : Type}

/-- Encode a payload at a chunk index, including serialization. -/
def encode (ecp : ErasureCodePayload M Sym) (payload : M) (i : ℕ) : Sym :=
  ecp.ec.encode (ecp.serialize payload) i

/-- Decode a payload from chunks, including parsing. -/
def decode (ecp : ErasureCodePayload M Sym) (chunks : Finset (ℕ × Sym)) : Option M :=
  match ecp.ec.decode chunks with
  | none => none
  | some block => ecp.parse block

end ErasureCodePayload

namespace ErasureCode

variable {Sym : Type}

/-- Encode `M` at every index in `I`, collecting the chunk set
`{(i, Encode(M, i)) | i ∈ I}`. -/
-- ANCHOR: encodeChunks
noncomputable def encodeChunks [DecidableEq Sym] (ec : ErasureCode Sym)
    (M : Fin ec.nchunk → Sym) (I : Finset ℕ) :
    Finset (ℕ × Sym) :=
  (I.toList.map fun i => (i, ec.encode M i)).toFinset
-- ANCHOR_END: encodeChunks

/-- Correctness: decoding the chunk set `{(i, Encode(M, i)) | i ∈ I}` recovers
`M` when `|I| = nchunk` and fails when `|I| < nchunk`. -/
-- ANCHOR: Correct
def Correct [DecidableEq Sym] (ec : ErasureCode Sym) : Prop :=
  ∀ (M : Fin ec.nchunk → Sym) (I : Finset ℕ),
    (I.card = ec.nchunk → ec.decode (ec.encodeChunks M I) = some M) ∧
    (I.card < ec.nchunk → ec.decode (ec.encodeChunks M I) = none)
-- ANCHOR_END: Correct

end ErasureCode
