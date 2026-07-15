/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.KEM.OnOffKEM.Defs
import LatticeCrypto.MLKEM.KPKE
import LatticeCrypto.MLKEM.Concrete.Instance

/-!
# ML-KEM's K-PKE as an online-offline KEM

Online-offline KEM construction following [SCKA]:
Auerbach, Dodis, Jost, Katsumata, Schmidt,
*How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols*
(https://eprint.iacr.org/2025/2267.pdf).

The construction relies on the IND-CPA public-key encryption underlying ML-KEM (FIPS 203, §5),
specified by VCVio's K-PKE (`MLKEM.KPKE`). From this scheme, a basic KEM can be
constructed as follows:
- encapsulation: encrypt a uniformly random message;
- decapsulation:  decrypt the corresponding ciphertext.

The resulting shared secret key is the decrypted message.

This file provides this basic KEM instantiation from `MLKEM.KPKE` together with
a `KEMScheme.OnOffStructure` witnessing its online-offline split following the description
in [SCKA, Def. 2.1].

## Kyber PKE (`MLKEM.KPKE`)

All values are polynomials of the ML-KEM ring `R_q = ℤ_q[X] / (X^256 + 1)` with
`q = 3329`, and vectors/matrices are over `R_q` of dimension `k`. The `NTT` and
its inverse transform polynomial coefficients between two domains to make
multiplication efficient; a hat marks a value in the NTT domain, e.g. `ŷ = NTT y`.

The scheme fixes a `k × k` public matrix `Â`, expanded from a public seed `ρ`.

Key generation:

```
  keygen():
    sample s, e ∈ Rqᵏ       -- secret and error vectors
    ŝ, ê ← NTT s, NTT e
    t̂ ← Â ŝ + ê
    return (ek = t̂, dk = ŝ)
```

Encryption. Given a public key `ek = t̂` and a 32-byte message `m`:

```
  encrypt(t̂, m):
    sample y, e1 ∈ Rqᵏ and e2 ∈ Rq  -- ephemeral secret and noise vectors
    ŷ ← NTT y
    u ← invNTTVec (Âᵀ ŷ) + e1                                -- ct0
    v ← invNTT ⟨t̂, ŷ⟩ + e2 + decompress₁ (decode₁ m)         -- ct1
    return (u, v)
```

where `decompress₁ (decode₁ m)` is the polynomial that corresponds to message `m`.
The components `u`, `v` are compressed and byte-encoded into the ciphertext parts
`ct0`, `ct1`.

The noise `y`, `e1`, `e2` is not sampled independently but expanded from a single
32-byte seed `coins` (the encryption randomness) via PRFs. The online-offline
split below relies on this: the offline phase samples `coins`, and the online
phase re-derives `e2` from it.

Decryption. Given a secret key `dk = ŝ` and a ciphertext `(u, v)`:

```
  decrypt(ŝ, (u, v)):
    w ← v - invNTT ⟨ŝ, NTT u⟩        -- cancels the t̂-term, leaving ≈ decompress₁ (decode₁ m)
    return compress₁ w               -- ≈ m
```

## The KEM algorithms and their split

We build the KEM directly on `MLKEM.KPKE`, reusing the `keygen`, `encrypt`, and
`decrypt` above (with `Â` fixed, shared by all key pairs):

```
  keygen():                    -- as above
    return (ek = t̂, dk = ŝ)
  encaps(ek = t̂):
    sample coins, m            -- encryption randomness and message (the shared key)
    (ct0, ct1) ← encrypt(t̂, m; coins)
    return ((ct0, ct1), m)
  decaps(dk = ŝ, (ct0, ct1)):
    return decrypt(ŝ, (ct0, ct1))          -- = m
```

Here `encaps` and `decaps` are K-PKE encryption and decryption directly; only
`keygen` re-derives `KPKE.keygenFromSeed`, with `ρ` fixed rather than drawn per
key pair.

The on/off split is given by two phases that recompute the ciphertext components
separately (`u = ct0` offline, `v = ct1` online, as in `encrypt` above):

```
  encapsOff():                 -- offline; uses only Â, never ek
    sample coins               -- fixes y, e1, e2
    ŷ ← NTT y
    u ← invNTTVec (Âᵀ ŷ) + e1                                -- ct0
    return (u, st = (coins, ŷ))
  encapsOn(st = (coins, ŷ), ek = t̂):
    sample m                                                 -- the shared key
    v ← invNTT ⟨t̂, ŷ⟩ + e2 + decompress₁ (decode₁ m)         -- ct1
    return (v, m)
```

`onOff.factor` proves that running `encapsOff` then `encapsOn` equals `encaps`
(hence `KPKE.encrypt`), confirming the split is faithful; the ciphertext is
`ct = (ct0, ct1)` and the shared key is the encapsulated message `m`.

`schemeKyber768` / `onOffKyber768` fix the concrete Kyber-768 encoding, NTT, and
primitive bundles.
-/

open MLKEM

namespace KPKEOnOff

variable (params : Params) (encoding : Encoding params)
  (ring : NTTRingOps) (prims : Primitives params encoding)
  (rho : Seed32)

/-- Offline encapsulation `Enc.Off`: sample the encapsulation randomness `y` and
noise `e1` from fresh coins, and output the offline ciphertext
`ct0 = invNTTVec (Âᵀ ŷ) + e1` together with the state `(coins, ŷ)` needed by the
online phase. Independent of the encapsulation key. -/
-- ANCHOR: encapsOffFromKPKE
def encapsOff : ProbComp ((Coins × TqVec params.k) × encoding.EncodedU) := do
  let coins ← $ᵗ Coins
  let aHat := prims.publicMatrix rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  pure ((coins, yHat), encoding.byteEncodeDUVec (encoding.compressDU u))
-- ANCHOR_END: encapsOffFromKPKE

/-- Online encapsulation `Enc.On`: from the offline state `(coins, ŷ)` and the
encapsulation key `ek = t̂`, sample the message `I` (the shared key) and output
the online ciphertext `ct1 = invNTT (t̂ ŷ) + e2 + decompress₁ (decode₁ I)`. -/
-- ANCHOR: encapsOnFromKPKE
def encapsOn (st : Coins × TqVec params.k) (ek : encoding.EncodedTHat) :
    ProbComp (encoding.EncodedV × Message) := do
  let (coins, yHat) := st
  let tHat := encoding.byteDecode12Vec ek
  let e2 := prims.prfEta2 coins (2 * params.k)
  let msg ← $ᵗ Message
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  pure (encoding.byteEncodeDV (encoding.compressDV v), msg)
-- ANCHOR_END: encapsOnFromKPKE

/-- Key generation against the fixed public matrix `Â = publicMatrix ρ`: sample
the secret `s` and error `e`, and output `ek = t̂ = Â ŝ + ê` and `dk = ŝ`
(both serialized). Mirrors `MLKEM.KPKE.keygenFromSeed` with `ρ` fixed as a public
parameter rather than derived per key pair. -/
def keygen : ProbComp (encoding.EncodedTHat × encoding.EncodedTHat) := do
  let sigma ← $ᵗ Seed32
  let aHat := prims.publicMatrix rho
  let s := prims.sampleVecEta1 sigma 0
  let e := prims.sampleVecEta1 sigma params.k
  let sHat := ring.nttVec s
  let eHat := ring.nttVec e
  let tHat := ring.matVecMul aHat sHat + eHat
  pure (encoding.byteEncode12Vec tHat, encoding.byteEncode12Vec sHat)

/-- Decapsulation: reassemble the K-PKE ciphertext and run `MLKEM.KPKE.decrypt`
to recover the message (the shared key). -/
-- ANCHOR: decapsFromKPKE
def decaps (sk : encoding.EncodedTHat) (c : encoding.EncodedU × encoding.EncodedV) :
    ProbComp (Option Message) :=
  pure (some (KPKE.decrypt ring encoding prims
    ({ sHatEncoded := sk } : KPKE.SecretKey params encoding)
    ({ uEncoded := c.1, vEncoded := c.2 } : KPKE.Ciphertext params encoding)))
-- ANCHOR_END: decapsFromKPKE

/-- The K-PKE KEM (IND-CPA, no FO transform) with ciphertext space
`C = C₀ × C₁ = EncodedU × EncodedV`. Encapsulation is `MLKEM.KPKE.encrypt` on a
freshly sampled message (the shared key); decapsulation is `MLKEM.KPKE.decrypt`. -/
-- ANCHOR: schemeFromKPKE
def scheme :
    KEMScheme ProbComp Message encoding.EncodedTHat encoding.EncodedTHat
      (encoding.EncodedU × encoding.EncodedV) where
  keygen := keygen params encoding ring prims rho
  encaps ek := do
    let coins ← $ᵗ Coins
    let msg ← $ᵗ Message
    let ct := KPKE.encrypt ring encoding prims
      ({ tHatEncoded := ek, rho := rho } : KPKE.PublicKey params encoding) msg coins
    pure ((ct.uEncoded, ct.vEncoded), msg)
  decaps := decaps params encoding ring prims
-- ANCHOR_END: schemeFromKPKE

/-- The online-offline structure for the K-PKE KEM: the ciphertext splits as
`ct = (ct0, ct1)`, and `factor` proves that the KEM's encapsulation
(`MLKEM.KPKE.encrypt`) equals the offline phase `encapsOff` followed by the
online phase `encapsOn`. -/
-- ANCHOR: onOffFromKPKE
def onOff : (scheme params encoding ring prims rho).OnOffStructure where
  St := Coins × TqVec params.k
  C₀ := encoding.EncodedU
  C₁ := encoding.EncodedV
  split := Equiv.refl (encoding.EncodedU × encoding.EncodedV)
  encapsOff := encapsOff params encoding ring prims rho
  encapsOn := encapsOn params encoding ring prims
  factor ek := by
    simp only [scheme, encapsOff, encapsOn, KPKE.encrypt, bind_assoc, pure_bind,
      Equiv.refl_symm, Equiv.coe_refl, id_eq]
-- ANCHOR_END: onOffFromKPKE

/-- The K-PKE on/off KEM at Kyber-768, with the concrete encoding, NTT, and
FFI-backed primitives; `rho` is the public matrix seed, treated as a public
parameter. -/
def schemeKyber768 (rho : Seed32) :
    KEMScheme ProbComp Message
      (Concrete.mlkem768Encoding.EncodedTHat) (Concrete.mlkem768Encoding.EncodedTHat)
      (Concrete.mlkem768Encoding.EncodedU × Concrete.mlkem768Encoding.EncodedV) :=
  scheme mlkem768 Concrete.mlkem768Encoding Concrete.concreteNTTRingOps
    Concrete.mlkem768Primitives rho

/-- The online-offline structure at Kyber-768. -/
def onOffKyber768 (rho : Seed32) : (schemeKyber768 rho).OnOffStructure :=
  onOff mlkem768 Concrete.mlkem768Encoding Concrete.concreteNTTRingOps
    Concrete.mlkem768Primitives rho

end KPKEOnOff
