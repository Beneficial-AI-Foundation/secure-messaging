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

Recall:

```
structure KEMScheme (m : Type → Type u) [Monad m] (K PK SK C : Type) where
  keygen : m (PK × SK)
  encaps : PK → m (C × K)
  decaps : SK → C → m (Option K)
```

`KEMScheme.OnOffStructure kem` is a structure showing that for the given KEM:
- the ciphertext splits into two components `ct = (ct0, ct1)`,
- encapsulation splits into `encapsOff` and `encapsOn` phases, where
  - `ct0` is computed independently of the public key (`encapsOff`),
  - `ct1` and the shared key are computed from the public key (`encapsOn`).

An on/off KEM is defined by a base KEM scheme `kem : KEMScheme m K PK SK C`
plus an on/off structure `oo : kem.OnOffStructure`.

The example structure `KEMScheme.trivialOnOff` shows that any KEM scheme can be seen
as an on/off KEM with an empty offline phase.
-/

universe u

namespace KEMScheme

variable {m : Type → Type u} [Monad m] {K PK SK C : Type}

/-- An online-offline (on/off) KEM witness for a KEM `kem`
decomposing `kem.encaps` into an offline and an online phase.

- `St`: state produced by the offline encapsulation algorithm;
- `C₀`, `C₁`: the offline and online ciphertext spaces;
- `split`: identifies the ciphertext space `C` with `C₀ × C₁`, i.e. `ct = (ct0, ct1)`;
- `encapsOff`: the key-independent offline phase, producing a state and `ct0`;
- `encapsOn st pk`: the online phase, producing `ct1` and the shared key;
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
  /-- Offline encapsulation `Enc.Off`: key-independent, returns a state and `ct0`. -/
  encapsOff : m (St × C₀)
  /-- Online encapsulation `Enc.On`: from the state and `pk`, returns `ct1` and the shared key. -/
  encapsOn : St → PK → m (C₁ × K)
  /-- For every public key, `kem.encaps` is equal to first running `encapsOff`,
  then running `encapsOn st pk`. -/
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
