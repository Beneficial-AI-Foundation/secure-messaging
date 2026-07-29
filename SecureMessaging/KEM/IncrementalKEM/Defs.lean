/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Incremental KEM

The incremental KEM interface of the
[ML-KEM Braid specification, Section 1.2](https://signal.org/docs/specifications/mlkembraid/),
modelled as a property of a plain `KEMScheme`.

Recall:

```
structure KEMScheme (m : Type → Type u) [Monad m] (K PK SK C : Type) where
  keygen : m (PK × SK)
  encaps : PK → m (C × K)
  decaps : SK → C → m (Option K)
```

`KEMScheme.IncrementalStructure kem` is a structure showing that for the given KEM:
- the public encapsulation key is equivalent to a valid header/vector pair `(hdr, vec)`,
- the ciphertext splits into two components `ct = (ct1, ct2)`,
- encapsulation splits into `encaps1` and `encaps2` stages, where
  - `encaps1 hdr` returns a state `st`, the first ciphertext component `ct1`, and the
    new shared key `k`,
  - `encaps2 st hdr vec` returns the second ciphertext component `ct2`,
- `validPK hdr vec` checks whether the received header/vector pair is consistent.

An incremental KEM is defined by a base KEM scheme `kem : KEMScheme m K PK SK C`
plus an incremental structure `inc : kem.IncrementalStructure`.

The example structure `KEMScheme.trivialIncremental` shows that any KEM scheme can be seen
as an incremental KEM taking the whole public key as the header.

-/

universe u

namespace KEMScheme

variable {m : Type → Type u} [Monad m] {K PK SK C : Type}

/-- An incremental KEM witness for a KEM `kem`, decomposing `kem.encaps`
into two stages using the two parts of the public encapsulation key.

- `PKheader`: the encapsulation key header;
- `PKvector`: the encapsulation key vector;
- `C₁`, `C₂`: the first and second ciphertext spaces;
- `St`: the encapsulation secret state carried between the two stages;
- `validPK hdr vec`: consistency check of a pair `(hdr,vec)`;
- `splitPK`: identifies public keys with valid header/vector pairs;
- `splitC`: identifies the ciphertext space `C` with `C₁ × C₂`;
- `encaps1 hdr`: the first stage, producing the state, `ct1`, and the shared key;
- `encaps2 st hdr vec`: the second stage, producing `ct2`;
- `factor`: `kem.encaps` agrees with `encaps1` then `encaps2` on `splitPK`. -/
-- ANCHOR: IncrementalStructure
structure IncrementalStructure (kem : KEMScheme m K PK SK C) where
  /-- Public-key header type. -/
  PKheader : Type
  /-- Public-key vector type. -/
  PKvector : Type
  /-- First ciphertext component. -/
  C₁ : Type
  /-- Second ciphertext component. -/
  C₂ : Type
  /-- Encapsulation state carried from the first stage to the second. -/
  St : Type
  /-- Consistency check of a vector part against a header. -/
  validPK : PKheader → PKvector → Bool
  /-- There is a bijection between public keys and header/vector pairs that pass `validPK`. -/
  splitPK : PK ≃ { parts : PKheader × PKvector // validPK parts.1 parts.2 = true }
  /-- The ciphertext splits as `ct = (ct1, ct2)`. -/
  splitC : C ≃ C₁ × C₂
  /-- First stage of encaps: from the header alone, returns the state, `ct1`, and the shared key. -/
  encaps1 : PKheader → m (St × C₁ × K)
  /-- Second stage of encaps: returns the second ciphertext component `ct2`. -/
  encaps2 : St → PKheader → PKvector → m C₂
  /-- For every public key, `kem.encaps` is equal to first running `encaps1`
  on the derived header, then running `encaps2` on the resulting state. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (hdr, vec) := (splitPK pk).1
    let (st, c1, k) ← encaps1 hdr
    let c2 ← encaps2 st hdr vec
    pure (splitC.symm (c1, c2), k))
-- ANCHOR_END: IncrementalStructure

/-- Incremental structure showing that any `kem` can be trivially made incremental by
taking the whole public key as the header. -/
def trivialIncremental [LawfulMonad m] (kem : KEMScheme m K PK SK C) :
    kem.IncrementalStructure where
  PKheader := PK
  PKvector := Unit
  C₁ := C
  C₂ := Unit
  St := Unit
  validPK _ _ := true
  splitPK :=
    { toFun := fun pk => ⟨(pk, ()), rfl⟩
      invFun := fun parts => parts.1.1
      left_inv := by
        intro pk
        rfl
      right_inv := by
        intro parts
        cases parts with
        | mk parts h =>
            cases parts with
            | mk pk vec =>
                cases vec
                rfl }
  splitC := (Equiv.prodPUnit C).symm
  encaps1 pk := do
    let (c, k) ← kem.encaps pk
    pure ((), c, k)
  encaps2 _ _ _ := pure ()
  factor pk := by simp

/-! ## Running the stages

The definitions below run an incremental KEM the way the braid protocol does: the sender
splits the public key, the receiver encapsulates in two stages, and the ciphertext is put back
together for decapsulation. `factor` says the staged run computes exactly `kem.encaps`, so
every correctness bound on the base KEM applies to the staged run as well.
-/

namespace IncrementalStructure

open ENNReal

variable {kem : KEMScheme m K PK SK C} (inc : kem.IncrementalStructure)

/-- The header of a public key. -/
def toHeader (pk : PK) : inc.PKheader := ((inc.splitPK pk).1).1

/-- The vector of a public key. -/
def toVector (pk : PK) : inc.PKvector := ((inc.splitPK pk).1).2

/-- The staged encapsulation: run `encaps1` on the header, complete with `encaps2`, and put
the ciphertext together. By `factor` this is exactly `kem.encaps`. -/
def stagedEncaps (pk : PK) : m (C × K) := do
  let (st, c1, k) ← inc.encaps1 (inc.toHeader pk)
  let c2 ← inc.encaps2 st (inc.toHeader pk) (inc.toVector pk)
  pure (inc.splitC.symm (c1, c2), k)

/-- The factorization law, phrased for the named staged run. -/
theorem encaps_eq_stagedEncaps (pk : PK) : kem.encaps pk = inc.stagedEncaps pk :=
  inc.factor pk

/-- The correctness experiment run the staged way: generate a key pair, encapsulate through
the two stages, decapsulate the result. Compare `KEMScheme.CorrectExp`. -/
def CorrectExp [DecidableEq K] : m Bool := do
  let (pk, sk) ← kem.keygen
  let (c, k) ← inc.stagedEncaps pk
  let k' ← kem.decaps sk c
  return decide (k' = some k)

/-- The staged experiment is the ordinary correctness experiment: the two programs are
equal. -/
theorem correctExp_eq [DecidableEq K] : inc.CorrectExp = kem.CorrectExp := by
  simp only [CorrectExp, KEMScheme.CorrectExp, inc.encaps_eq_stagedEncaps]

/-- A correctness bound for the KEM bounds the staged run in the same way. -/
theorem probFailure_correctExp_le [DecidableEq K] (runtime : ProbCompRuntime m)
    {delta : ℝ≥0∞} (h : kem.deltaCorrect runtime delta) :
    Pr[= false | runtime.evalDist inc.CorrectExp] ≤ delta := by
  rw [inc.correctExp_eq]
  refine le_trans ?_ h
  rw [kem.correctnessError_eq_probOutput_false_add_probFailure]
  exact le_self_add

end IncrementalStructure

end KEMScheme
