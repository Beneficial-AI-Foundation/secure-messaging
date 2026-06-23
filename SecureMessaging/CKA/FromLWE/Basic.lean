/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.ProbComp

/-!
# Basic Frodo/LWE Matrix Model

This file is the concrete matrix layer of the construction
`MatrixParams → frodoScheme → frodoCorrectness`. It models the optimized
Frodo/LWE continuous key agreement of [ACD19, Section 4.1.2] over matrices
`Mat q r c = Matrix (Fin r) (Fin c) (ZMod q)` with nonzero modulus `q`.

A `Frodo.MatrixParams` fixes the dimensions `n` and `nbar`, the modulus `q`, the
error sampler `chi : ProbComp (ZMod q)`, and the reconciliation surface:
`RecInfo` is the type of the paper's `C'`, `recInfo V` is the paper's
`<V>_{2B}`, `key V` is the paper's key extraction from `V`, and `reconcile` is
the paper's `rec`. The laws `rec_sendA_correct` and `rec_sendB_correct` are
stated on the paper's matrix expressions: the public key `B = A * S + E`, the
fresh public key `B' = S' * A + E'`, and the shared value `V' = S' * B +
Etilde'`. They state that reconciliation recovers the sender's key and are taken
as assumptions, discharged by a concrete Frodo instance.

The matrix algorithms `init`, `sendA`, `sendB`, `recvA`, and `recvB` carry the
paper's dimensions:

* the common value is `Mat q n n`, the public matrix `A`;
* A's public keys and B's secrets are `Mat q n nbar`;
* B's public keys and A's secrets are `Mat q nbar n`;
* A's send randomness records `S'`, `E'`, `Etilde'` (paper `CKA-S-B`);
* B's send randomness records `S''`, `E''`, `Etilde''` (paper `CKA-S-A`).

The match relations `MatchAB` and `MatchBA` and the support lemmas `init_match`,
`sendA_correct`, `sendA_match_next`, `sendB_correct`, and `sendB_match_next`
package the agreement facts that `lweCKA.frodoScheme`'s correctness proof
consumes.

## Party convention

The repository CKA game starts from a `sendA` state. In ACD19's LWE
initialization, the first displayed half-round is paper-B sending from
`(A, B := A * S + E)` to paper-A, who receives using `(A, S)`. We align that
half-round with the repository's initial `sendA`/`recvB` transition: Lean
`sendA`/`recvB` implement paper `CKA-S-B`/`CKA-R-A`, and Lean `sendB`/`recvA`
implement paper `CKA-S-A`/`CKA-R-B`.
-/

open OracleSpec OracleComp

namespace Frodo

/-- Residue ring of integers modulo `q`. -/
abbrev Zq (q : ℕ) := ZMod q

/-- An `r × c` matrix over `ZMod q`. -/
abbrev Mat (q r c : ℕ) := Matrix (Fin r) (Fin c) (Zq q)

/-- Sample a length-`r` tuple by drawing each coordinate independently from `s`. -/
private def sampleFin {α : Type} (s : ProbComp α) : (r : ℕ) → ProbComp (Fin r → α)
  | 0 => pure Fin.elim0
  | r + 1 => do
      let head ← s
      let tail ← sampleFin s r
      pure (Fin.cons head tail)

/-- Parameters of the concrete Frodo/LWE matrix model.

The dimensions `n` and `nbar` and the modulus `q` (nonzero) fix the matrix
spaces. `chi` is the entrywise error sampler over `ZMod q`; `RecInfo`,
`recInfo`, `key`, and `reconcile` model the paper's reconciliation information
`C'`, map `<·>_{2B}`, key extraction, and `rec` function. The two
`rec_*_correct` fields state, on the paper's matrix expressions, that
reconciliation recovers the sender's key; they are the abstraction boundary
discharged by a concrete Frodo instance. -/
structure MatrixParams where
  /-- Lattice dimension. -/
  n : ℕ
  /-- Number of simultaneously agreed columns. -/
  nbar : ℕ
  /-- Modulus of the residue ring `ZMod q`. -/
  q : ℕ
  /-- The modulus is nonzero, so `ZMod q` is finite and sampleable. -/
  q_neZero : NeZero q
  /-- Epoch key space. -/
  Key : Type
  /-- Paper `C'`, the reconciliation information sent with the fresh public key. -/
  RecInfo : Type
  /-- Error sampler over `ZMod q`; matrix errors are sampled entrywise from this. -/
  chi : ProbComp (ZMod q)
  /-- Paper `<V>_{2B}`: compute reconciliation information from the sender's
  shared value. -/
  recInfo : Mat q nbar nbar → RecInfo
  /-- Paper key extraction from the sender's shared value. -/
  key : Mat q nbar nbar → Key
  /-- Reconciliation (paper `rec`): recover the key from the receiver's approximate
  value and the reconciliation information. -/
  reconcile : Mat q nbar nbar → RecInfo → Option Key
  /-- Reconciliation correctness for paper `CKA-S-B`: with `B = A * S + E`,
  `B' = S' * A + E'`, and `V' = S' * B + Etilde'`, the receiver recovers the
  sender's key from `B' * S` and paper `C' = recInfo V'`. -/
  rec_sendA_correct : ∀ (A : Mat q n n) (S E : Mat q n nbar)
      (S' E' : Mat q nbar n) (Etilde' : Mat q nbar nbar),
      reconcile ((S' * A + E') * S) (recInfo (S' * (A * S + E) + Etilde')) =
        some (key (S' * (A * S + E) + Etilde'))
  /-- Reconciliation correctness for paper `CKA-S-A`: with `B' = S' * A + E'`,
  `B'' = A * S'' + E''`, and `V = B' * S'' + Etilde''`, the receiver recovers the
  sender's key from `S' * B''` and paper `C = recInfo V`. -/
  rec_sendB_correct : ∀ (A : Mat q n n) (S' E' : Mat q nbar n)
      (S'' E'' : Mat q n nbar) (Etilde'' : Mat q nbar nbar),
      reconcile (S' * (A * S'' + E'')) (recInfo ((S' * A + E') * S'' + Etilde'')) =
        some (key ((S' * A + E') * S'' + Etilde''))

namespace MatrixParams

/-- Sample an `r × c` error matrix by drawing each entry independently from `chi`. -/
def chiMat (p : MatrixParams) (r c : ℕ) : ProbComp (Mat p.q r c) :=
  (fun f => Matrix.of f) <$> sampleFin (sampleFin p.chi c) r

/-- Sample an `r × c` matrix uniformly over `Z_q`. -/
def uniformMat (p : MatrixParams) (r c : ℕ) : ProbComp (Mat p.q r c) :=
  haveI := p.q_neZero
  $ᵗ (Mat p.q r c)

/-- Setup: sample the public matrix `A`, the secret `S`, and the error `E`, and
publish `B = A * S + E`. -/
def init (p : MatrixParams) :
    ProbComp (Mat p.q p.n p.n × Mat p.q p.n p.nbar × Mat p.q p.n p.nbar) := do
  let A ← p.uniformMat p.n p.n
  let S ← p.chiMat p.n p.nbar
  let E ← p.chiMat p.n p.nbar
  let B := A * S + E
  return (A, B, S)

/-- A's send. Sample `S'`, `E'`, `Etilde'`, form the fresh
public key `B' = S' * A + E'` and the shared value `V' = S' * B + Etilde'`, and
emit the key `key V'`, the public key `B'`, the reconciliation information
`recInfo V'`, the kept secret `S'`, and the randomness. -/
def sendA (p : MatrixParams) (A : Mat p.q p.n p.n) (B : Mat p.q p.n p.nbar) :
    ProbComp (p.Key × Mat p.q p.nbar p.n × p.RecInfo × Mat p.q p.nbar p.n ×
      (Mat p.q p.nbar p.n × Mat p.q p.nbar p.n × Mat p.q p.nbar p.nbar)) := do
  let S' ← p.chiMat p.nbar p.n
  let E' ← p.chiMat p.nbar p.n
  let Etilde' ← p.chiMat p.nbar p.nbar
  let B' := S' * A + E'
  let V' := S' * B + Etilde'
  return (p.key V', B', p.recInfo V', S', (S', E', Etilde'))

/-- B's send. Sample `S''`, `E''`, `Etilde''`, form the fresh
public key `B'' = A * S'' + E''` and the shared value `V = B' * S'' + Etilde''`,
and emit the key `key V`, the public key `B''`, the reconciliation information
`recInfo V`, the kept secret `S''`, and the randomness. -/
def sendB (p : MatrixParams) (A : Mat p.q p.n p.n) (B' : Mat p.q p.nbar p.n) :
    ProbComp (p.Key × Mat p.q p.n p.nbar × p.RecInfo × Mat p.q p.n p.nbar ×
      (Mat p.q p.n p.nbar × Mat p.q p.n p.nbar × Mat p.q p.nbar p.nbar)) := do
  let S'' ← p.chiMat p.n p.nbar
  let E'' ← p.chiMat p.n p.nbar
  let Etilde'' ← p.chiMat p.nbar p.nbar
  let B'' := A * S'' + E''
  let V := B' * S'' + Etilde''
  return (p.key V, B'', p.recInfo V, S'', (S'', E'', Etilde''))

/-- B's receive: reconcile `B' * S` against the reconciliation information. -/
def recvB (p : MatrixParams) (S : Mat p.q p.n p.nbar)
    (B' : Mat p.q p.nbar p.n) (h : p.RecInfo) : Option p.Key :=
  p.reconcile (B' * S) h

/-- A's receive: reconcile `S' * B''` against the reconciliation information. -/
def recvA (p : MatrixParams) (S' : Mat p.q p.nbar p.n)
    (B'' : Mat p.q p.n p.nbar) (h : p.RecInfo) : Option p.Key :=
  p.reconcile (S' * B'') h

/-- A public key and a secret are paired for the A-to-B direction when the key is
`A * S` up to an error term. -/
def MatchAB (p : MatrixParams) (A : Mat p.q p.n p.n) (B : Mat p.q p.n p.nbar)
    (S : Mat p.q p.n p.nbar) : Prop :=
  ∃ E : Mat p.q p.n p.nbar, B = A * S + E

/-- A public key and a secret are paired for the B-to-A direction when the key is
`S' * A` up to an error term. -/
def MatchBA (p : MatrixParams) (A : Mat p.q p.n p.n) (B' : Mat p.q p.nbar p.n)
    (S' : Mat p.q p.nbar p.n) : Prop :=
  ∃ E' : Mat p.q p.nbar p.n, B' = S' * A + E'

/-- Setup produces a paired public key and secret. -/
lemma init_match (p : MatrixParams) :
    ∀ (A : Mat p.q p.n p.n) (B S : Mat p.q p.n p.nbar),
      (A, B, S) ∈ support p.init → p.MatchAB A B S := by
  intro A B S hmem
  simp only [MatrixParams.init, MatrixParams.MatchAB, mem_support_bind_iff,
    mem_support_pure_iff, Prod.mk.injEq] at hmem ⊢
  obtain ⟨A', -, S', -, E', -, rfl, rfl, rfl⟩ := hmem
  exact ⟨E', rfl⟩

/-- When A's public key and B's secret are paired, B's receive recovers exactly
the epoch key produced by A's send. -/
lemma sendA_correct (p : MatrixParams) :
    ∀ (A : Mat p.q p.n p.n) (B S : Mat p.q p.n p.nbar),
      p.MatchAB A B S →
      ∀ (key : p.Key) (pubBA : Mat p.q p.nbar p.n) (recInfo : p.RecInfo)
        (secBA : Mat p.q p.nbar p.n)
        (randA : Mat p.q p.nbar p.n × Mat p.q p.nbar p.n × Mat p.q p.nbar p.nbar),
        (key, pubBA, recInfo, secBA, randA) ∈ support (p.sendA A B) →
        p.recvB S pubBA recInfo = some key := by
  intro A B S hM key pubBA recInfo secBA randA hmem
  obtain ⟨E, rfl⟩ : ∃ E, B = A * S + E := hM
  simp only [MatrixParams.sendA, mem_support_bind_iff, mem_support_pure_iff,
    Prod.mk.injEq] at hmem
  obtain ⟨S', -, E', -, Etilde', -, rfl, rfl, rfl, -, -⟩ := hmem
  simpa only [MatrixParams.recvB] using p.rec_sendA_correct A S E S' E' Etilde'

/-- A's send produces a public key and a secret paired for the next direction. -/
lemma sendA_match_next (p : MatrixParams) :
    ∀ (A : Mat p.q p.n p.n) (B : Mat p.q p.n p.nbar)
      (key : p.Key) (pubBA : Mat p.q p.nbar p.n) (recInfo : p.RecInfo)
      (secBA : Mat p.q p.nbar p.n)
      (randA : Mat p.q p.nbar p.n × Mat p.q p.nbar p.n × Mat p.q p.nbar p.nbar),
      (key, pubBA, recInfo, secBA, randA) ∈ support (p.sendA A B) →
      p.MatchBA A pubBA secBA := by
  intro A B key pubBA recInfo secBA randA hmem
  simp only [MatrixParams.sendA, MatrixParams.MatchBA, mem_support_bind_iff,
    mem_support_pure_iff, Prod.mk.injEq] at hmem ⊢
  obtain ⟨S', -, E', -, Etilde', -, -, rfl, -, rfl, -⟩ := hmem
  exact ⟨E', rfl⟩

/-- When B's public key and A's secret are paired, A's receive recovers exactly
the epoch key produced by B's send. -/
lemma sendB_correct (p : MatrixParams) :
    ∀ (A : Mat p.q p.n p.n) (B' S' : Mat p.q p.nbar p.n),
      p.MatchBA A B' S' →
      ∀ (key : p.Key) (pubAB : Mat p.q p.n p.nbar) (recInfo : p.RecInfo)
        (secAB : Mat p.q p.n p.nbar)
        (randB : Mat p.q p.n p.nbar × Mat p.q p.n p.nbar × Mat p.q p.nbar p.nbar),
        (key, pubAB, recInfo, secAB, randB) ∈ support (p.sendB A B') →
        p.recvA S' pubAB recInfo = some key := by
  intro A B' S' hM key pubAB recInfo secAB randB hmem
  obtain ⟨E', rfl⟩ : ∃ E', B' = S' * A + E' := hM
  simp only [MatrixParams.sendB, mem_support_bind_iff, mem_support_pure_iff,
    Prod.mk.injEq] at hmem
  obtain ⟨S'', -, E'', -, Etilde'', -, rfl, rfl, rfl, -, -⟩ := hmem
  simpa only [MatrixParams.recvA] using p.rec_sendB_correct A S' E' S'' E'' Etilde''

/-- B's send produces a public key and a secret paired for the next direction. -/
lemma sendB_match_next (p : MatrixParams) :
    ∀ (A : Mat p.q p.n p.n) (B' : Mat p.q p.nbar p.n)
      (key : p.Key) (pubAB : Mat p.q p.n p.nbar) (recInfo : p.RecInfo)
      (secAB : Mat p.q p.n p.nbar)
      (randB : Mat p.q p.n p.nbar × Mat p.q p.n p.nbar × Mat p.q p.nbar p.nbar),
      (key, pubAB, recInfo, secAB, randB) ∈ support (p.sendB A B') →
      p.MatchAB A pubAB secAB := by
  intro A B' key pubAB recInfo secAB randB hmem
  simp only [MatrixParams.sendB, MatrixParams.MatchAB, mem_support_bind_iff,
    mem_support_pure_iff, Prod.mk.injEq] at hmem ⊢
  obtain ⟨S'', -, E'', -, Etilde'', -, -, rfl, -, rfl, -⟩ := hmem
  exact ⟨E'', rfl⟩

end MatrixParams

end Frodo
