/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.KEM.OnOffKEM.Defs
import LatticeCrypto.MLKEM.KPKE
import LatticeCrypto.MLKEM.Concrete.Instance

/-!
# Lightweight ML-KEM as an online-offline KEM (from K-PKE)

This file builds a genuine `KEMScheme.OnOffStructure` instance from VCVio's
spec-level Kyber core `MLKEM.KPKE` (the IND-CPA public-key encryption underlying
ML-KEM), following the "lightweight" instantiation of
[SCKA](https://eprint.iacr.org/2025/2267.pdf): the online-offline protocols are
instantiated with Kyber, and *"as we only require IND-CPA security, we forgo the
FO transform required for IND-CCA security"* (Sec. 4.1). So the base KEM here is
the raw K-PKE (no Fujisaki-Okamoto / implicit rejection), used as a KEM by
encapsulating a uniformly random message as the shared key.

## The online-offline split

Recall the K-PKE encryption `MLKEM.KPKE.encrypt`:

```
  u := invNTTVec (matTransposeVecMul Â ŷ) + e1        -- ct0
  v := invNTT (dot t̂ ŷ) + e2 + decompress₁ (decode₁ m) -- ct1
```

The offline component `u = ct0` depends only on the public matrix `Â` and the
encapsulation randomness, not on the peer's encapsulation key `t̂`. As noted in
[SCKA, Def. 2.1], ML-KEM is online-offline precisely by *viewing the public
matrix `Â` (equivalently its seed `ρ`) as a public parameter `par`*. Our
`OnOffStructure` has no `par` field, so we fix `ρ` as a module parameter of the
construction; `keygen` then samples key pairs against this shared matrix (the
matrix-reuse MLWE setting), and:

* `encapsOff` samples `(y, e1)` and outputs `ct0 = u` together with the state
  `(coins, ŷ)`, independent of the encapsulation key;
* `encapsOn` uses the encapsulation key `t̂` and the state to output `ct1 = v`
  and the shared key (the sampled message).

Decapsulation reuses `MLKEM.KPKE.decrypt`. Correctness/security are inherited
from the base `KEMScheme` (this file only establishes the on/off *structure*).

`schemeKyber768` / `onOffKyber768` fix the concrete Kyber-768 encoding, NTT, and
FFI-backed primitive bundles.
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
def encapsOff : ProbComp ((Coins × TqVec params.k) × encoding.EncodedU) := do
  let coins ← $ᵗ Coins
  let aHat := prims.publicMatrix rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  pure ((coins, yHat), encoding.byteEncodeDUVec (encoding.compressDU u))

/-- Online encapsulation `Enc.On`: from the offline state `(coins, ŷ)` and the
encapsulation key `ek = t̂`, sample the message `I` (the shared key) and output
the online ciphertext `ct1 = invNTT (t̂ ŷ) + e2 + decompress₁ (decode₁ I)`. -/
def encapsOn (st : Coins × TqVec params.k) (ek : encoding.EncodedTHat) :
    ProbComp (encoding.EncodedV × Message) := do
  let (coins, yHat) := st
  let tHat := encoding.byteDecode12Vec ek
  let e2 := prims.prfEta2 coins (2 * params.k)
  let msg ← $ᵗ Message
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  pure (encoding.byteEncodeDV (encoding.compressDV v), msg)

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
def decaps (sk : encoding.EncodedTHat) (c : encoding.EncodedU × encoding.EncodedV) :
    ProbComp (Option Message) :=
  pure (some (KPKE.decrypt ring encoding prims
    ({ sHatEncoded := sk } : KPKE.SecretKey params encoding)
    ({ uEncoded := c.1, vEncoded := c.2 } : KPKE.Ciphertext params encoding)))

/-- The lightweight (IND-CPA, no FO) ML-KEM/K-PKE KEM with ciphertext space
`C = C₀ × C₁ = EncodedU × EncodedV` and encapsulation written as the offline
phase followed by the online phase. -/
def scheme :
    KEMScheme ProbComp Message encoding.EncodedTHat encoding.EncodedTHat
      (encoding.EncodedU × encoding.EncodedV) where
  keygen := keygen params encoding ring prims rho
  encaps ek := do
    let (st, c0) ← encapsOff params encoding ring prims rho
    let (c1, k) ← encapsOn params encoding ring prims st ek
    pure ((c0, c1), k)
  decaps := decaps params encoding ring prims

/-- The online-offline structure for the lightweight K-PKE KEM: the ciphertext
splits as `ct = (ct0, ct1)` and encapsulation factors into `encapsOff` (offline,
key-independent) and `encapsOn` (online). -/
def onOff : (scheme params encoding ring prims rho).OnOffStructure where
  St := Coins × TqVec params.k
  C₀ := encoding.EncodedU
  C₁ := encoding.EncodedV
  split := Equiv.refl (encoding.EncodedU × encoding.EncodedV)
  encapsOff := encapsOff params encoding ring prims rho
  encapsOn := encapsOn params encoding ring prims
  factor _ := by simp [scheme]

/-- The lightweight on/off KEM at Kyber-768, with the concrete encoding, NTT, and
FFI-backed primitives; `rho` is the public matrix seed treated as a public
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
