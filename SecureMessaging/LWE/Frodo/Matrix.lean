/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import VCVio.OracleComp.Constructions.SampleableType
import SecureMessaging.LWE.Frodo

/-!
# Concrete Frodo/LWE Matrix Model

This file gives the concrete matrix layer behind `Frodo.CKAParams`. It models the
optimized Frodo/LWE continuous key agreement of [ACD19, Section 4.1.2] over
matrices `Mat q r c = Matrix (Fin r) (Fin c) (ZMod q)` with nonzero modulus `q`.

A `Frodo.MatrixParams` fixes the dimensions `n` and `nbar`, the modulus `q`, the
error sampler `chi : ProbComp (ZMod q)`, and the reconciliation maps `hint`,
`key`, and `reconcile`. The laws `rec_sendA_correct` and `rec_sendB_correct` are
stated on the paper's matrix expressions: the public key `B = A * S + E`, the
fresh public key `B' = S' * A + E'`, and the shared value `V' = S' * B + Etilde'`.
They state that reconciliation recovers the sender's key and are taken as
assumptions, discharged by a concrete Frodo instance.

`concreteCKAParams` instantiates `Frodo.CKAParams` from a `MatrixParams`, so the
construction and correctness proved against the abstraction specialize to this
model. The dimensions follow the paper:

* `Common = Mat q n n` is the public matrix `A`;
* `PubAB = SecAB = Mat q n nbar`;
* `PubBA = SecBA = Mat q nbar n`;
* `RandA` records `S'`, `E'`, `Etilde'` (paper `CKA-S-B`);
* `RandB` records `S''`, `E''`, `Etilde''` (paper `CKA-S-A`).

## Party-label convention

As in `Frodo.CKAParams`, the field names follow the A-first repository game while
the paper is B-first: `sendA` is the paper's `CKA-S-B`, `recvB` is `CKA-R-A`,
`sendB` is `CKA-S-A`, and `recvA` is `CKA-R-B`.
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
spaces. `chi` is the entrywise error sampler over `ZMod q`; the maps `hint`,
`key`, and `reconcile` are the reconciliation surface. The two `rec_*_correct`
fields state, on the paper's matrix expressions, that reconciliation recovers the
sender's key; they are the abstraction boundary discharged by a concrete Frodo
instance. -/
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
  /-- Reconciliation hint space. -/
  Hint : Type
  /-- Error sampler over `ZMod q`; matrix errors are sampled entrywise from this. -/
  chi : ProbComp (ZMod q)
  /-- Reconciliation hint computed by the sender from the shared value. -/
  hint : Mat q nbar nbar → Hint
  /-- Epoch key extracted from the shared value. -/
  key : Mat q nbar nbar → Key
  /-- Reconciliation (paper `rec`): recover the key from the receiver's approximate
  value and the hint. -/
  reconcile : Mat q nbar nbar → Hint → Option Key
  /-- Reconciliation correctness for paper `CKA-S-B`: with `B = A * S + E`,
  `B' = S' * A + E'`, and `V' = S' * B + Etilde'`, the receiver recovers the
  sender's key from `B' * S` and `hint V'`. -/
  rec_sendA_correct : ∀ (A : Mat q n n) (S E : Mat q n nbar)
      (S' E' : Mat q nbar n) (Etilde' : Mat q nbar nbar),
      reconcile ((S' * A + E') * S) (hint (S' * (A * S + E) + Etilde')) =
        some (key (S' * (A * S + E) + Etilde'))
  /-- Reconciliation correctness for paper `CKA-S-A`: with `B' = S' * A + E'`,
  `B'' = A * S'' + E''`, and `V = B' * S'' + Etilde''`, the receiver recovers the
  sender's key from `S' * B''` and `hint V`. -/
  rec_sendB_correct : ∀ (A : Mat q n n) (S' E' : Mat q nbar n)
      (S'' E'' : Mat q n nbar) (Etilde'' : Mat q nbar nbar),
      reconcile (S' * (A * S'' + E'')) (hint ((S' * A + E') * S'' + Etilde'')) =
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
emit the key `key V'`, the public key `B'`, the hint `hint V'`, the kept secret
`S'`, and the randomness. -/
def sendA (p : MatrixParams) (A : Mat p.q p.n p.n) (B : Mat p.q p.n p.nbar) :
    ProbComp (p.Key × Mat p.q p.nbar p.n × p.Hint × Mat p.q p.nbar p.n ×
      (Mat p.q p.nbar p.n × Mat p.q p.nbar p.n × Mat p.q p.nbar p.nbar)) := do
  let S' ← p.chiMat p.nbar p.n
  let E' ← p.chiMat p.nbar p.n
  let Etilde' ← p.chiMat p.nbar p.nbar
  let B' := S' * A + E'
  let V' := S' * B + Etilde'
  return (p.key V', B', p.hint V', S', (S', E', Etilde'))

/-- B's send. Sample `S''`, `E''`, `Etilde''`, form the fresh
public key `B'' = A * S'' + E''` and the shared value `V = B' * S'' + Etilde''`,
and emit the key `key V`, the public key `B''`, the hint `hint V`, the kept
secret `S''`, and the randomness. -/
def sendB (p : MatrixParams) (A : Mat p.q p.n p.n) (B' : Mat p.q p.nbar p.n) :
    ProbComp (p.Key × Mat p.q p.n p.nbar × p.Hint × Mat p.q p.n p.nbar ×
      (Mat p.q p.n p.nbar × Mat p.q p.n p.nbar × Mat p.q p.nbar p.nbar)) := do
  let S'' ← p.chiMat p.n p.nbar
  let E'' ← p.chiMat p.n p.nbar
  let Etilde'' ← p.chiMat p.nbar p.nbar
  let B'' := A * S'' + E''
  let V := B' * S'' + Etilde''
  return (p.key V, B'', p.hint V, S'', (S'', E'', Etilde''))

/-- B's receive: reconcile `B' * S` against the hint. -/
def recvB (p : MatrixParams) (S : Mat p.q p.n p.nbar)
    (B' : Mat p.q p.nbar p.n) (h : p.Hint) : Option p.Key :=
  p.reconcile (B' * S) h

/-- A's receive: reconcile `S' * B''` against the hint. -/
def recvA (p : MatrixParams) (S' : Mat p.q p.nbar p.n)
    (B'' : Mat p.q p.n p.nbar) (h : p.Hint) : Option p.Key :=
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

end MatrixParams

/-- Instantiate the abstract `Frodo.CKAParams` from the concrete matrix model.

The data fields are the matrix algorithms; the match relations are `MatchAB` and
`MatchBA`; and the five support-level laws are discharged by unfolding the
algorithms and applying the reconciliation laws `rec_sendA_correct` and
`rec_sendB_correct`. -/
def concreteCKAParams (p : MatrixParams) : Frodo.CKAParams ProbComp where
  Common := Mat p.q p.n p.n
  PubAB := Mat p.q p.n p.nbar
  PubBA := Mat p.q p.nbar p.n
  SecAB := Mat p.q p.n p.nbar
  SecBA := Mat p.q p.nbar p.n
  Key := p.Key
  Hint := p.Hint
  RandA := Mat p.q p.nbar p.n × Mat p.q p.nbar p.n × Mat p.q p.nbar p.nbar
  RandB := Mat p.q p.n p.nbar × Mat p.q p.n p.nbar × Mat p.q p.nbar p.nbar
  init := p.init
  sendA := p.sendA
  sendB := p.sendB
  recvB := fun _ => p.recvB
  recvA := fun _ => p.recvA
  MatchAB := p.MatchAB
  MatchBA := p.MatchBA
  init_match := by
    intro A B S hmem
    simp only [MatrixParams.init, MatrixParams.MatchAB, mem_support_bind_iff,
      mem_support_pure_iff, Prod.mk.injEq] at hmem ⊢
    obtain ⟨A', -, S', -, E', -, rfl, rfl, rfl⟩ := hmem
    exact ⟨E', rfl⟩
  sendA_correct := by
    intro A B S hM key pubBA hint secBA randA hmem
    obtain ⟨E, rfl⟩ : ∃ E, B = A * S + E := hM
    simp only [MatrixParams.sendA, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨S', -, E', -, Etilde', -, rfl, rfl, rfl, -, -⟩ := hmem
    simpa only [MatrixParams.recvB] using p.rec_sendA_correct A S E S' E' Etilde'
  sendA_match_next := by
    intro A B key pubBA hint secBA randA hmem
    simp only [MatrixParams.sendA, MatrixParams.MatchBA, mem_support_bind_iff,
      mem_support_pure_iff, Prod.mk.injEq] at hmem ⊢
    obtain ⟨S', -, E', -, Etilde', -, -, rfl, -, rfl, -⟩ := hmem
    exact ⟨E', rfl⟩
  sendB_correct := by
    intro A B' S' hM key pubAB hint secAB randB hmem
    obtain ⟨E', rfl⟩ : ∃ E', B' = S' * A + E' := hM
    simp only [MatrixParams.sendB, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨S'', -, E'', -, Etilde'', -, rfl, rfl, rfl, -, -⟩ := hmem
    simpa only [MatrixParams.recvA] using p.rec_sendB_correct A S' E' S'' E'' Etilde''
  sendB_match_next := by
    intro A B' key pubAB hint secAB randB hmem
    simp only [MatrixParams.sendB, MatrixParams.MatchAB, mem_support_bind_iff,
      mem_support_pure_iff, Prod.mk.injEq] at hmem ⊢
    obtain ⟨S'', -, E'', -, Etilde'', -, -, rfl, -, rfl, -⟩ := hmem
    exact ⟨E'', rfl⟩

end Frodo
