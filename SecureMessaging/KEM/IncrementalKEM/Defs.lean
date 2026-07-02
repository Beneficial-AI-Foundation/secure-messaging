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

`KEMScheme.IncrementalStructure kem` is a structure showing that the given KEM decomposes
incrementally: the public key splits into a small header and a larger vector part
(`pk = (hdr, vec)`), the ciphertext splits into two components (`ct = (ct1, ct2)`), and
encapsulation is staged so that `ct1` and the shared key are computed from the header alone
(`encaps1`), while `ct2` is computed later from the vector part (`encaps2`).

For ML-KEM the header is `ek_seed || SHA3-256(ek_seed || ek_vector)` and the vector part is
`ek_vector`; the predicate `validPK` is the prescribed consistency check of a received vector
against the hash carried in the header. Protocols must check `validPK` before running
`encaps2`; the check is deliberately a separate field so that protocol models can treat
vector reconstruction, validation, and second-stage encapsulation as distinct transitions.

An incremental KEM is therefore a `kem : KEMScheme m K PK SK C` together with
`inc : kem.IncrementalStructure`.

The example structure `KEMScheme.trivialIncremental` shows that any KEM scheme can have a
trivial incremental split where the header is the whole public key and the second ciphertext
component is empty.
-/

universe u

namespace KEMScheme

variable {m : Type → Type u} [Monad m] {K PK SK C : Type}

/-- An incremental KEM witness for a KEM `kem` (Section 1.2 of the
[ML-KEM Braid specification](https://signal.org/docs/specifications/mlkembraid/)),
decomposing `kem.encaps` into two stages driven by the two parts of the public key.

- `PKheader`: the public-key header space (`ek_header` for ML-KEM);
- `PKvector`: the remaining/vector part of the public key (`ek_vector` for ML-KEM);
- `C₁`, `C₂`: the first and second ciphertext component spaces;
- `St`: the encapsulation state space carried between the two stages;
- `splitPK`: identifies the public-key space `PK` with `PKheader × PKvector`;
- `splitC`: identifies the ciphertext space `C` with `C₁ × C₂`, i.e. `ct = (ct1, ct2)`;
- `validPK`: consistency check of a vector part against a header;
- `encaps1 hdr`: the first stage, producing the state, `ct1`, and the shared key;
- `encaps2 st hdr vec`: the second stage, producing `ct2`;
- `factor`: `kem.encaps` runs `encaps1` then `encaps2`, reassembled via `splitC`. -/
-- ANCHOR: IncrementalStructure
structure IncrementalStructure (kem : KEMScheme m K PK SK C) where
  /-- Public-key header space. For ML-KEM: `ek_seed || SHA3-256(ek_seed || ek_vector)`. -/
  PKheader : Type
  /-- Vector part of the public-key space. For ML-KEM: `ek_vector`. -/
  PKvector : Type
  /-- First ciphertext component space. -/
  C₁ : Type
  /-- Second ciphertext component space. -/
  C₂ : Type
  /-- Encapsulation state space carried from the first stage to the second. -/
  St : Type
  /-- The public key splits as `pk = (hdr, vec)`. -/
  splitPK : PK ≃ PKheader × PKvector
  /-- The ciphertext splits as `ct = (ct1, ct2)`. -/
  splitC : C ≃ C₁ × C₂
  /-- Consistency check of a vector part against a header. For ML-KEM this is the
  hash check `SHA3-256(ek_seed || ek_vector) = hek`. Protocols must check `validPK`
  before running `encaps2` on a received vector. -/
  validPK : PKheader → PKvector → Bool
  /-- First encapsulation stage `Encaps1`: from the public-key header alone, returns
  the encapsulation state, the first ciphertext component, and the shared key. -/
  encaps1 : PKheader → m (St × C₁ × K)
  /-- Second encapsulation stage `Encaps2`: from the state and the full public key,
  returns the second ciphertext component. -/
  encaps2 : St → PKheader → PKvector → m C₂
  /-- The KEM's encapsulation is the first stage followed by the second stage,
  with the two ciphertext components recombined via `splitC`. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (hdr, vec) := splitPK pk
    let (st, c1, k) ← encaps1 hdr
    let c2 ← encaps2 st hdr vec
    pure (splitC.symm (c1, c2), k))
-- ANCHOR_END: IncrementalStructure

/-- Incremental structure showing that any `kem` can be trivially split with the whole
public key as the header, an empty vector part, and an empty second ciphertext component,
so that the first stage performs the whole encapsulation. -/
def trivialIncremental [LawfulMonad m] (kem : KEMScheme m K PK SK C) :
    kem.IncrementalStructure where
  PKheader := PK
  PKvector := Unit
  C₁ := C
  C₂ := Unit
  St := Unit
  splitPK := (Equiv.prodPUnit PK).symm
  splitC := (Equiv.prodPUnit C).symm
  validPK _ _ := true
  encaps1 pk := do
    let (c, k) ← kem.encaps pk
    pure ((), c, k)
  encaps2 _ _ _ := pure ()
  factor pk := by simp

end KEMScheme
