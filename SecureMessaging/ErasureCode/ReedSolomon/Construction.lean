/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.LinearAlgebra.Lagrange
import SecureMessaging.ErasureCode.Defs

/-!
# Reed–Solomon Erasure-Code Construction

## References

- [RS60] Reed, Solomon. *Polynomial Codes over Certain Finite Fields.*
  Journal of the SIAM 8(2), 1960, https://doi.org/10.1137/0108018
- [RFC5510] Lacan, Roca, Peltotalo, Peltotalo.
  *Reed-Solomon Forward Error Correction (FEC) Schemes.*
  RFC 5510, 2009, https://datatracker.ietf.org/doc/rfc5510/
- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf

## Scope

This file formalizes the algebraic evaluation/interpolation core of Reed–Solomon
codes and its instantiation as an erasure-code. It does not model the full details
of the packet-level FEC scheme of [RFC5510].

## Part 1: The Reed–Solomon code

### Definition (`Code`)

A Reed–Solomon code [RS60, RFC5510] with parameters `k ≤ N` and
pairwise distinct evaluation points `x₀, …, x_(N-1) ∈ F` is the linear code

`RS := { (P(x₀), …, P(x_(N-1))) | P ∈ F[X], deg P < k } ⊆ F^N`,

i.e. the set of evaluations of all polynomials of degree less than `k` over
the points `x₀, …, x_(N-1)`.

The structure `Code F` records these parameters: `N`, `k`, and the evaluation points
as an injective assignment `j ↦ xⱼ` of positions to field elements (field `point`).

### Lagrange interpolation

For any `n` pairwise distinct points `a₀, …, a_(n-1) ∈ F` and any values
`b₀, …, b_(n-1) ∈ F`, there is exactly one polynomial `Q ∈ F[X]` with
`deg Q < n` and `Q(aᵢ) = bᵢ` for all `i < n`.


### Systematic encoding (`messagePolynomial`, `encode`)

By Lagrange interpolation at the `k` distinct points `x₀, …, x_(k-1)` with values
`m₀, …, m_(k-1)`, a message `m = (m₀, …, m_(k-1)) ∈ F^k` determines its *message
polynomial*: the unique `Pₘ ∈ F[X]` with

* `deg Pₘ < k`, and
* `Pₘ(xᵢ) = mᵢ` for all `i < k`.

The *codeword* of `m` is the evaluation of `Pₘ` at all `N` points:

```text
position j     :    0        1     ⋯     k-1     │     k      ⋯     N-1
point xⱼ       :    x₀       x₁    ⋯    x_(k-1)  │    x_k     ⋯    x_(N-1)
symbol Pₘ(xⱼ)  :  Pₘ(x₀)  Pₘ(x₁)   ⋯  Pₘ(x_(k-1))│  Pₘ(x_k)   ⋯  Pₘ(x_(N-1))
               =    m₀      m₁     ⋯    m_(k-1)  │
                  └───── source symbols ───────┘   └── redundancy symbols ──┘
```

By the interpolation property, the message appears verbatim in the first `k`
coordinates: this means the code is *systematic*.

### Reconstruction from partial data (`receivedPolynomial`)

Suppose the values `yⱼ = Pₘ(xⱼ)` are known at `n ≥ k` distinct positions `j`. By
Lagrange interpolation at these `n` points, there is a unique polynomial `Q` with
`deg Q < n` and `Q(xⱼ) = yⱼ` for all of them. `Pₘ` satisfies both conditions (using
`deg Pₘ < k ≤ n`), so by uniqueness `Q = Pₘ`, and `(Q(x₀), …, Q(x_(k-1))) = m`
recovers the message.

## Part 2: Erasure Code Construction

### Recall: erasure codes ([SCKA] Def. A.6)

An erasure code over a set of symbols `Σ`, with block length `N > 0` and message size
`nchunk ≤ N`, consists of two algorithms:

* `Encode(M, j) → c` — the symbol of message `M ∈ Σ^nchunk` at position
  `j ∈ {0, …, N-1}`;
* `Decode(L) → M` — recovery of a message from a chunk set `L ⊆ {0, …, N-1} × Σ`,
  or failure `⊥`.

A *chunk* of `M` is a pair `(j, Encode(M, j))`. Correctness: any `nchunk` chunks of
`M` at distinct positions decode to `M`; fewer decode to `⊥`.

### Instantiation (`Decodable`, `decode`, `toErasureCode`)

Reed–Solomon Erasure Code instantiates this interface with `Σ = F` and `nchunk = k`, and:

* `Encode(m, j) = Pₘ(xⱼ)`;
* `Decode` takes a received chunk set `L ⊆ {0, …, N-1} × F` — a finite set of pairs
  `(j, y)` of a position `j` and the symbol `y` received for it.
* `Decode(L) = (Q(x₀), …, Q(x_(k-1)))` when `L` is *decodable* — `k ≤ |L|` and the
  chunks of `L` have pairwise distinct points `xⱼ` — where `Q` is the interpolant
  through the pairs `{(xⱼ, y) | (j, y) ∈ L}`.
* `Decode(L) = ⊥` otherwise.

In a sender-receiver protocol, with `n := |L|`, we have:

```text
send      :  (j, Pₘ(xⱼ))                    one chunk per position j < N
receive   :  L = {(j₁, y₁), …, (jₙ, yₙ)}    some chunks lost; need n ≥ k
                                            and x_(j₁), …, x_(jₙ) distinct
fit       :  Q := interpolant through       deg Q < n
             (x_(j₁), y₁), …, (x_(jₙ), yₙ)
output    :  (Q(x₀), …, Q(x_(k-1)))         = (m₀, …, m_(k-1)) when all received
                                            chunks are honest
```

`toErasureCode` assembles this into the erasure code `(N, nchunk = k, Encode, Decode)`
over `Σ = F`.
Correctness is proved in `SecureMessaging.ErasureCode.ReedSolomon.Correctness`
-/

namespace ErasureCode.ReedSolomon

noncomputable section

open Polynomial

/-- A Reed–Solomon code over `F`: positions `0, …, N-1`, message size `k ≤ N`, and
pairwise distinct evaluation points `xⱼ = point j`. -/
-- ANCHOR: reedSolomon_Code
structure Code (F : Type) [Field F] where
  /-- Number of codeword positions. -/
  N : ℕ
  /-- The codeword has at least one position. -/
  N_pos : 0 < N
  /-- Number of message symbols and reconstruction threshold. -/
  k : ℕ
  /-- At least one message symbol is required for reconstruction. -/
  k_pos : 0 < k
  /-- The message fits in the codeword. -/
  k_le_N : k ≤ N
  /-- Evaluation point `xⱼ` of each position `j`. -/
  point : Fin N → F
  /-- The evaluation points are pairwise distinct. -/
  point_injective : Function.Injective point
-- ANCHOR_END: reedSolomon_Code

variable {F : Type} [Field F]

namespace Code

/-- The inclusion `{0, …, k-1} ↪ {0, …, N-1}`, `i ↦ i`: a message index as a
codeword position. -/
-- ANCHOR: reedSolomon_sourceIndex
def sourceIndex (rs : Code F) (i : Fin rs.k) : Fin rs.N :=
  Fin.castLE rs.k_le_N i
-- ANCHOR_END: reedSolomon_sourceIndex

/-- The evaluation-point mapping `point : j ↦ xⱼ` restricted to the message
positions `{0, …, k-1}`: `i ↦ xᵢ`. -/
-- ANCHOR: reedSolomon_sourcePoint
def sourcePoint (rs : Code F) (i : Fin rs.k) : F :=
  rs.point (rs.sourceIndex i)
-- ANCHOR_END: reedSolomon_sourcePoint

/-- The points `x₀, …, x_(k-1)` are pairwise distinct: the restriction of an
injective mapping is itself injective. -/
theorem sourcePoint_injective (rs : Code F) : Function.Injective rs.sourcePoint :=
  rs.point_injective.comp (Fin.castLE_injective rs.k_le_N)

/-- The *message polynomial* `Pₘ` of a message `m`: the unique polynomial with
`deg Pₘ < k` and `Pₘ(xᵢ) = mᵢ` for `i < k`, by Lagrange interpolation at the points
`x₀, …, x_(k-1)`. -/
-- ANCHOR: reedSolomon_messagePolynomial
def messagePolynomial (rs : Code F) (message : Fin rs.k → F) : F[X] :=
  Lagrange.interpolate Finset.univ rs.sourcePoint message
-- ANCHOR_END: reedSolomon_messagePolynomial

/-- `Encode(m, j) = Pₘ(xⱼ)`: the codeword symbol of message `m` at position `j`. -/
-- ANCHOR: reedSolomon_encode
def encode (rs : Code F) (message : Fin rs.k → F) (i : Fin rs.N) : F :=
  (rs.messagePolynomial message).eval (rs.point i)
-- ANCHOR_END: reedSolomon_encode

/-- A chunk set `L` is *decodable* when `k ≤ |L|` and its chunks have pairwise
distinct evaluation points `xⱼ`. -/
-- ANCHOR: reedSolomon_decodable
def Decodable (rs : Code F) (chunks : Finset (Fin rs.N × F)) : Prop :=
  rs.k ≤ chunks.card ∧
    Set.InjOn (fun ((j, _) : Fin rs.N × F) => rs.point j) chunks
-- ANCHOR_END: reedSolomon_decodable

/-- The interpolant `Q` through the pairs `{(xⱼ, y) | (j, y) ∈ L}` of a received
chunk set `L`. For honest chunks `y = Pₘ(xⱼ)` at `n ≥ k` distinct positions,
`Q = Pₘ`. -/
-- ANCHOR: reedSolomon_receivedPolynomial
noncomputable def receivedPolynomial (rs : Code F)
    (chunks : Finset (Fin rs.N × F)) : F[X] :=
  letI : DecidableEq F := Classical.decEq F
  Lagrange.interpolate chunks (fun (j, _) => rs.point j) (fun (_, y) => y)
-- ANCHOR_END: reedSolomon_receivedPolynomial

/-- `Decode(L) = (Q(x₀), …, Q(x_(k-1)))` when `L` is decodable, and `⊥` (`none`)
otherwise.

Conflicting chunks `(j, y₁), (j, y₂)` with `y₁ ≠ y₂` are rejected because they share
the evaluation point `xⱼ`. Chunks with distinct positions but corrupted values are
outside the erasure-only correctness claim.
-/
-- ANCHOR: reedSolomon_decode
noncomputable def decode (rs : Code F)
    (chunks : Finset (Fin rs.N × F)) : Option (Fin rs.k → F) :=
  letI : Decidable (rs.Decodable chunks) := Classical.propDecidable _
  if _h : rs.Decodable chunks then
    some fun i => (rs.receivedPolynomial chunks).eval (rs.sourcePoint i)
  else
    none
-- ANCHOR_END: reedSolomon_decode

/-- The erasure code `(N, nchunk = k, Encode, Decode)` induced by a Reed–Solomon
code. -/
-- ANCHOR: reedSolomon_code
def toErasureCode (rs : Code F) : ErasureCode F where
  N := rs.N
  N_pos := rs.N_pos
  nchunk := rs.k
  nchunk_pos := rs.k_pos
  nchunk_le_N := rs.k_le_N
  encode := rs.encode
  decode := rs.decode
-- ANCHOR_END: reedSolomon_code

end Code

end

end ErasureCode.ReedSolomon
