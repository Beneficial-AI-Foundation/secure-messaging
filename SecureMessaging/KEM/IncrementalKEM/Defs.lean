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
- the public encapsulation key splits into a header and a vector part `(hdr, vec)`,
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
- `pkParts pk`: derives the header/vector pair from the public key;
- `splitC`: identifies the ciphertext space `C` with `C₁ × C₂`;
- `validPK hdr vec`: consistency check of a pair `(hdr,vec)`;
- `validPK_iff_pkParts`: valid pairs are exactly those produced by `pkParts`;
- `encaps1 hdr`: the first stage, producing the state, `ct1`, and the shared key;
- `encaps2 st hdr vec`: the second stage, producing `ct2`;
- `factor`: `kem.encaps` agrees with `encaps1` then `encaps2` on `pkParts`. -/
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
  /-- Header/vector pair derived from the public encapsulation key. -/
  pkParts : PK → PKheader × PKvector
  /-- The ciphertext splits as `ct = (ct1, ct2)`. -/
  splitC : C ≃ C₁ × C₂
  /-- Consistency check of a vector part against a header. -/
  validPK : PKheader → PKvector → Bool
  /-- Header/vector pair is valid iff it is produced by some public key. -/
  validPK_iff_pkParts : ∀ hdr vec, validPK hdr vec = true ↔ ∃ pk, pkParts pk = (hdr, vec)
  /-- First stage of encaps: from the header alone, returns the state, `ct1`, and the shared key. -/
  encaps1 : PKheader → m (St × C₁ × K)
  /-- Second stage of encaps: returns the second ciphertext component. -/
  encaps2 : St → PKheader → PKvector → m C₂
  /-- Full `kem.encaps` agrees with `encaps1` then `encaps2` on `pkParts`. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (hdr, vec) := pkParts pk
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
  pkParts pk := (pk, ())
  splitC := (Equiv.prodPUnit C).symm
  validPK _ _ := true
  validPK_iff_pkParts hdr vec := by
    constructor
    · intro _
      exact ⟨hdr, by cases vec; rfl⟩
    · intro _
      rfl
  encaps1 pk := do
    let (c, k) ← kem.encaps pk
    pure ((), c, k)
  encaps2 _ _ _ := pure ()
  factor pk := by simp

end KEMScheme
