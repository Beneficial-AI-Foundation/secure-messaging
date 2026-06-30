/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Online-Offline (On/Off) KEM

The online-offline KEM of [SCKA, Def. 2.1](https://eprint.iacr.org/2025/2267.pdf),
modelled as a property of a plain `KEMScheme`.

`KEMScheme.OnOffStructure kem` is a structure showing that the given KEM encapsulation algorithm
`kem.encaps` splits into an offline phase `Enc.Off` (key-independent, producing `ct0 : C₀`)
and an online phase `Enc.On` (producing `ct1 : C₁` and the encapsulation key), with the full
KEM ciphertext being `ct = (ct0, ct1)`.

An on/off KEM is therefore a `kem : KEMScheme m K PK SK C` together with
`oo : kem.OnOffStructure`.

The example structure `KEMScheme.trivialOnOff` shows that any KEM scheme can have a trivial
on/off split where the offline phase is empty.
-/

universe u

namespace KEMScheme

variable {m : Type → Type u} [Monad m] {K PK SK C : Type}

/-- An online-offline (on/off) KEM witness for a KEM `kem` (Definition 2.1 of
[SCKA]), decomposing `kem.encaps` into an offline and an online phase.

- `St`: the offline encapsulation state space;
- `C₀`: the offline ciphertext space;
- `C₁`: the online ciphertext space;
- `split`: identifies the ciphertext space `C` with `C₀ × C₁`, i.e. `ct = (ct0, ct1)`;
- `encapsOff`: the key-independent offline phase, producing a state and `ct0`;
- `encapsOn st ek`: the online phase, producing `ct1` and the shared key;
- `factor`: `kem.encaps` runs `encapsOff` then `encapsOn`, reassembled via `split`. -/
-- ANCHOR: OnOffStructure
structure OnOffStructure (kem : KEMScheme m K PK SK C) where
  /-- Offline encapsulation state space. -/
  St : Type
  /-- Offline ciphertext space. -/
  C₀ : Type
  /-- Online ciphertext space. -/
  C₁ : Type
  /-- The ciphertext space splits as `ct = (ct0, ct1)`. -/
  split : C ≃ C₀ × C₁
  /-- Offline encapsulation `Enc.Off`: returns a state and the offline
  ciphertext, independently of the encapsulation key. -/
  encapsOff : m (St × C₀)
  /-- Online encapsulation `Enc.On`: from the offline state and the
  encapsulation key, returns the online ciphertext and the shared key. -/
  encapsOn : St → PK → m (C₁ × K)
  /-- The KEM's encapsulation is the offline phase followed by the online phase,
  with the two ciphertext halves recombined via `split`. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (st, c0) ← encapsOff
    let (c1, k) ← encapsOn st pk
    pure (split.symm (c0, c1), k))
-- ANCHOR_END: OnOffStructure

/-- On/off structure showing that any `kem` can be trivially split into an offline
phase with an empty ciphertext, and an online phase that performs the whole encapsulation. -/
def trivialOnOff [LawfulMonad m] (kem : KEMScheme m K PK SK C) :
    kem.OnOffStructure where
  St := Unit
  C₀ := Unit
  C₁ := C
  split := (Equiv.punitProd C).symm
  encapsOff := pure ((), ())
  encapsOn _ pk := kem.encaps pk
  factor pk := by simp

end KEMScheme
