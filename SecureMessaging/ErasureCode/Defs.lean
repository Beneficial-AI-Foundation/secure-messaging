/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

/-!
# Erasure Codes

Syntex and correctness of erasure codes following Definition A.6 from:

- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf

An *erasure code* over a set of symbols `Σ`, with block length `N` and message size
`nchunk`, consists of two algorithms:
- `Encode(M, i) → c`: encodes message `M` ∈ `Σ^nchunk` at index `i` ∈ `ℤ_N` to symbol `c` ∈ `Σ`;
- `Decode(L) → M`: from a chunk set `L` ⊆ `ℤ_N × Σ`, recovers `M` ∈ `Σ^nchunk` or fails with `⊥`.

Writing `L_I = {(i, Encode(M, i)) | i ∈ I}` for the chunks of `M` at indices `I` ⊆ `ℤ_N`,
correctness requires, for all `M` and all `I`:
- Decode(L_I) = M, if |I| = nchunk;
- Decode(L_I) = ⊥, if |I| < nchunk.

The alphabet Σ is the type parameter `Sym`.
-/

universe u

/-- An erasure code over an alphabet `Sym` (Definition A.6 of [SCKA]).

- `m`: the ambient monad the algorithms run in;
- `Sym`: the alphabet Σ of symbols;
- `N`: the block length; chunk indices range over `Fin N`;
- `nchunk`: the message size; a message is an `nchunk`-tuple of symbols: `Fin nchunk → Sym`;
- `encode M i`: the chunk encoding of message `M` at index `i`;
- `decode L`: recovers a message from a chunk set `L`, or fails (`none`). -/
-- ANCHOR: ErasureCode
structure ErasureCode (m : Type → Type u) [Monad m] (Sym : Type) where
  /-- Block length; chunk indices range over `Fin N`. -/
  N : ℕ
  /-- Message size; a message is `Fin nchunk → Sym`. -/
  nchunk : ℕ
  /-- `Encode(M, i)`: the chunk encoding of message `M` at index `i`. -/
  encode : (Fin nchunk → Sym) → Fin N → m Sym
  /-- `Decode(L)`: recover the message from a chunk set, or fail (`none`). -/
  decode : Finset (Fin N × Sym) → m (Option (Fin nchunk → Sym))
-- ANCHOR_END: ErasureCode

namespace ErasureCode

variable {m : Type → Type u} [Monad m] {Sym : Type}

/-- Encode `M` at every index in `I`, collecting the chunk set
`{(i, Encode(M, i)) | i ∈ I}`. -/
-- ANCHOR: encodeChunks
noncomputable def encodeChunks [DecidableEq Sym] (ec : ErasureCode m Sym)
    (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)) :
    m (Finset (Fin ec.N × Sym)) := do
  let chunks ← I.toList.mapM fun i => (fun c => (i, c)) <$> ec.encode M i
  pure chunks.toFinset
-- ANCHOR_END: encodeChunks

/-- Correctness: decoding the chunk set `{(i, Encode(M, i)) | i ∈ I}` recovers
`M` when `|I| = nchunk` and fails when `|I| < nchunk`. -/
-- ANCHOR: Correct
def Correct [DecidableEq Sym] (ec : ErasureCode m Sym) : Prop :=
  ∀ (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)),
    (I.card = ec.nchunk → (ec.encodeChunks M I >>= ec.decode) = pure (some M)) ∧
    (I.card < ec.nchunk → (ec.encodeChunks M I >>= ec.decode) = pure none)
-- ANCHOR_END: Correct

end ErasureCode
