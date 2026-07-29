/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Finite.Card
import Mathlib.FieldTheory.Finite.GaloisField
import SecureMessaging.ErasureCode.ReedSolomon.Construction

/-!
# Parallel Reed–Solomon Erasure-Code Construction

This module lifts a scalar Reed–Solomon code over `F` to an erasure code over
16-coordinate chunks `F^16` by running 16 scalar codes in parallel. This models the
parallel structure of Signal's
[Sparse Post Quantum Ratchet polynomial encoder and decoder]
(https://github.com/signalapp/SparsePostQuantumRatchet/blob/main/src/encoding/polynomial.rs),
where a chunk is 16 `u16` values (32 bytes). The final section gives an abstract SPQR
specialization.

This is an algebraic abstraction, not an exact specification of Signal's
implementation. It does not model byte serialization, the concrete correspondence
between `u16` values and `GF(2^16)` elements, or protocol message encoding.

## Parallel 16-coordinate construction (`encode`, `decode`, `parallelCode`)

*Recall:* a scalar Reed–Solomon code with parameters `k ≤ N` and
pairwise distinct evaluation points `x₀, …, x_(N-1) ∈ F` is the linear code

`RS := { (P(x₀), …, P(x_(N-1))) | P ∈ F[X], deg P < k } ⊆ F^N`,

i.e. the set of evaluations of all polynomials of degree less than `k` over
the points `x₀, …, x_(N-1)`.

Fix a scalar Reed–Solomon code (`ReedSolomon.Code F`) with parameters `k ≤ N` and
evaluation points `x_0, …, x_(N-1)`.

A *16-coordinate erasure code* has symbol set `Σ = F^16` and message size `nchunk = k`.
A source message is `m = (m₀, …, m_(k-1))`, with each `mᵢ ∈ F^16`.
Encoding and decoding operations apply the underlying scalar Reed–Solomon code coordinatewise.
Writing `v[c]` for the `c`-th coordinate of a chunk `v`:
for each coordinate `c < 16`, the scalar message
`(m₀[c], …, m_(k-1)[c])` has its own message polynomial `P_c`.

We have:

* Encoding operation.
 `Encode(m, j) = (P₀(xⱼ), …, P₁₅(xⱼ)) ∈ F^16` — 16 independent scalar Reed–Solomon
  symbols evaluated at the common position `j`;
* Decodability predicate.
  A received chunk set `L ⊆ {0, …, N-1} × F^16` is decodable when
  `k ≤ |L|` and the map `(j, y) ↦ xⱼ` is injective on `L` (`Decodable`);
* `Decode(L)` interpolates each coordinate separately — `Q_c` through
  `{(xⱼ, y[c]) | (j, y) ∈ L}` (`receivedPolynomial`) — and returns the message chunks
  `mᵢ = (Q₀(xᵢ), …, Q₁₅(xᵢ))` for `i < k`; non-decodable `L` yields `⊥`.


The full codeword is an array with 16 rows and `N` columns:

```text
        position j :    0       ⋯      k-1    │     k      ⋯     N-1
        point xⱼ   :    x₀      ⋯    x_(k-1)  │    x_k     ⋯    x_(N-1)

        row c = 0  :  P₀(x₀)    ⋯  P₀(x_(k-1))│  P₀(x_k)   ⋯  P₀(x_(N-1))
        row c = 1  :  P₁(x₀)    ⋯  P₁(x_(k-1))│  P₁(x_k)   ⋯  P₁(x_(N-1))
            ⋮           ⋮             ⋮       │     ⋮             ⋮
        row c = 15 : P₁₅(x₀)    ⋯ P₁₅(x_(k-1))│ P₁₅(x_k)   ⋯ P₁₅(x_(N-1))

        column j   =    m₀      ⋯   m_(k-1)   │  Encode(m, j) for j ≥ k
                     └── message chunks ─────┘  └── redundancy chunks ──┘
```

* Each **row** `c` is one scalar Reed–Solomon codeword: the evaluations of `P_c`, the
  message polynomial of the scalar message `(m₀[c], …, m_(k-1)[c])`.
* Each **column** `j` is one chunk `Encode(m, j) ∈ F^16` — the unit that is
  transmitted, received, or lost. For `j < k` the column is the message chunk `mⱼ`
  itself (systematic, coordinatewise).

Erasures delete whole columns; decoding interpolates each surviving row and
re-evaluates it at `x₀, …, x_(k-1)`.

`parallelCode` packages this as an erasure code over the symbol set `Σ = F^16`: one
codeword position carries one whole chunk.

## Relation to Signal's SPQR instance

Signal treats each 32-byte chunk as 16 `u16` values and applies one Reed–Solomon code
to each coordinate. The model in this file, `spqrCode k`, specializes `parallelCode`
to an abstract `GF(2^16)`. It covers the fixed-size inputs used by ML-KEM Braid,
whose lengths are divisible by 32 bytes. It does not model Signal's more general
extension to arbitrary even-length byte strings, where the source field elements are
distributed unevenly among the 16 coordinate polynomials.
-/

namespace ErasureCode.SPQRReedSolomon

noncomputable section

open Polynomial

/-- A chunk of 16 field elements. For `F = GF(2^16)`, it represents 32 bytes after
choosing a two-byte representation of field elements. -/
abbrev Chunk (F : Type) := Fin 16 → F

variable {F : Type} [Field F]

/-- Encode a chunk message at position `j` by applying the scalar Reed–Solomon encoder
independently to each of its 16 coordinates:
`Encode(m, j) = (P₀(xⱼ), …, P₁₅(xⱼ))`. -/
-- ANCHOR: parallelReedSolomon_encode
def encode (rs : ReedSolomon.Code F) (message : Fin rs.k → Chunk F)
    (index : Fin rs.N) : Chunk F :=
  fun coordinate => rs.encode (fun i => message i coordinate) index
-- ANCHOR_END: parallelReedSolomon_encode

/-- A received chunk set is decodable when it contains at least `k` chunks at
pairwise distinct scalar evaluation points. -/
-- ANCHOR: parallelReedSolomon_decodable
def Decodable (rs : ReedSolomon.Code F)
    (chunks : Finset (Fin rs.N × Chunk F)) : Prop :=
  rs.k ≤ chunks.card ∧
    Set.InjOn (fun ((j, _) : Fin rs.N × Chunk F) => rs.point j) chunks
-- ANCHOR_END: parallelReedSolomon_decodable

/-- Project each received chunk `(j, y)` to its scalar coordinate `(j, y[c])`. -/
def coordinateChunks (rs : ReedSolomon.Code F)
    (chunks : Finset (Fin rs.N × Chunk F)) (coordinate : Fin 16) :
    Finset (Fin rs.N × F) := by
  classical
  exact chunks.image fun (j, y) => (j, y coordinate)

/-- The scalar received polynomial for coordinate `c`, obtained by applying the
scalar Reed–Solomon operation to `coordinateChunks`. -/
def receivedPolynomial (rs : ReedSolomon.Code F)
    (chunks : Finset (Fin rs.N × Chunk F)) (coordinate : Fin 16) : F[X] :=
  rs.receivedPolynomial (coordinateChunks rs chunks coordinate)

/-- Decode a received chunk set coordinatewise. For a decodable set, coordinate `c`
is reconstructed from `Q_c` at the `k` source points; otherwise decoding returns
`none`. -/
-- ANCHOR: parallelReedSolomon_decode
noncomputable def decode (rs : ReedSolomon.Code F)
    (chunks : Finset (Fin rs.N × Chunk F)) : Option (Fin rs.k → Chunk F) :=
  letI : Decidable (Decodable rs chunks) := Classical.propDecidable _
  if _h : Decodable rs chunks then
    some fun i coordinate =>
      (receivedPolynomial rs chunks coordinate).eval (rs.sourcePoint i)
  else
    none
-- ANCHOR_END: parallelReedSolomon_decode

/-- Lift a scalar Reed–Solomon code to an erasure code whose symbols are 16-coordinate
chunks. It retains block length `N` and threshold `k`. -/
-- ANCHOR: parallelReedSolomon_code
def parallelCode (rs : ReedSolomon.Code F) : ErasureCode (Chunk F) where
  N := rs.N
  N_pos := rs.N_pos
  nchunk := rs.k
  nchunk_le_N := rs.k_le_N
  encode := encode rs
  decode := decode rs
-- ANCHOR_END: parallelReedSolomon_code

/-! ## Abstract SPQR specialization

Set `N = 2^16` and `F = GF(2^16)`. Since `|{0, …, N-1}| = |F| = 2^16`, we can choose a
bijection

`x : {0, …, N-1} ≃ F,    j ↦ xⱼ`.

The field elements `xⱼ` are the evaluation points of the scalar Reed–Solomon code.
The Lean definition `evaluationEquiv` realizes this abstract choice, `scalarCode k`
forms the resulting scalar code, and
`spqrCode k := parallelCode (scalarCode k)`.
-/

/-- An abstract finite field with `2^16` elements for the SPQR specialization. -/
-- ANCHOR: spqrReedSolomon_GF16
abbrev GF16 := GaloisField 2 16
-- ANCHOR_END: spqrReedSolomon_GF16

/-- Classical decidable equality on the abstract field `GF16`. -/
noncomputable instance gf16DecidableEq : DecidableEq GF16 := Classical.decEq GF16

/-- The abstract field `GF16` has `2^16` elements. -/
theorem gf16_card : Nat.card GF16 = 2 ^ 16 := by
  exact GaloisField.card 2 16 (by decide)

/-- The chosen bijection `x : {0, …, 2^16-1} ≃ GF16`, whose values `xⱼ` are the
Reed–Solomon evaluation points. -/
-- ANCHOR: spqrReedSolomon_evaluationEquiv
def evaluationEquiv : Fin (2 ^ 16) ≃ GF16 :=
  (Finite.equivFinOfCardEq gf16_card).symm
-- ANCHOR_END: spqrReedSolomon_evaluationEquiv

/-- The scalar Reed–Solomon code with threshold `k`, block length `2^16`, and
evaluation points given by `evaluationEquiv`. -/
-- ANCHOR: spqrReedSolomon_scalarCode
def scalarCode (k : ℕ) (hk : k ≤ 2 ^ 16) : ReedSolomon.Code GF16
-- ANCHOR_END: spqrReedSolomon_scalarCode
    where
  N := 2 ^ 16
  N_pos := by norm_num
  k := k
  k_le_N := hk
  point := evaluationEquiv
  point_injective := evaluationEquiv.injective

/-- The abstract SPQR erasure code at threshold `k`: the 16-coordinate parallel code
specialized to `GF16`, with one chunk at each codeword position. -/
-- ANCHOR: spqrReedSolomon_code
def spqrCode (k : ℕ) (hk : k ≤ 2 ^ 16) : ErasureCode (Chunk GF16) :=
  parallelCode (scalarCode k hk)
-- ANCHOR_END: spqrReedSolomon_code

end

end ErasureCode.SPQRReedSolomon
