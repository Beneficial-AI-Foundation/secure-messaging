/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import LatticeCrypto.MLKEM.KPKE
import LatticeCrypto.MLKEM.Concrete.Instance

/-!
Docs-local mirror of VCVio's K-PKE (`MLKEM.KPKE`).

A compiled package declaration exposes no source body to Verso, so these verbatim
copies of `LatticeCrypto.MLKEM.KPKE` exist only so the blueprint's `anchor` pill
can display the algorithm bodies in Def 2.3. Keep them in sync with the package;
they are not used by any proof.
-/

namespace SecureMessagingDocs.KPKESpec

open MLKEM MLKEM.KPKE

variable {params : Params} {encoding : Encoding params}

/- Private helpers used by VCVio's concrete centered-binomial sampler. -/
private def bitOf (b : UInt8) (j : Nat) : Nat :=
  ((b >>> j.toUInt8) &&& 1).toNat

private def getByteD (bytes : ByteArray) (i : Nat) : UInt8 :=
  (bytes[i]?).getD 0

private def vectorToByteArray {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  ByteArray.mk v.toArray

-- ANCHOR: kpkeNoiseSampling
def samplePolyCBD (eta : Nat) (bytes : ByteArray) : Rq :=
  let bits : Array Nat := Id.run do
    let mut b := Array.mkEmpty (bytes.size * 8)
    for k in [0:bytes.size] do
      for j in [0:8] do
        b := b.push (bitOf (getByteD bytes k) j)
    return b
  Vector.ofFn fun idx =>
    let i := idx.val
    let x := Id.run do
      let mut acc := 0
      for j in [0:eta] do
        acc := acc + bits.getD (2 * i * eta + j) 0
      return acc
    let y := Id.run do
      let mut acc := 0
      for j in [0:eta] do
        acc := acc + bits.getD (2 * i * eta + eta + j) 0
      return acc
    (x : Coeff) - (y : Coeff)

def prfCBD (eta : Nat) (sigma : Seed32) (n : Nat) : Rq :=
  let input := vectorToByteArray sigma |>.push n.toUInt8
  let prfOutput := MLKEM.Concrete.FFI.shake256 input (64 * eta).toUSize
  samplePolyCBD eta prfOutput
-- ANCHOR_END: kpkeNoiseSampling

-- ANCHOR: kpkeMatrixAndVectorSampling
def publicMatrix (prims : Primitives params encoding) (rho : Seed32) :
    TqMatrix params.k params.k :=
  Vector.ofFn fun i => Vector.ofFn fun j => prims.sampleNTT rho j i

def sampleVecEta1 (prims : Primitives params encoding) (seed : Seed32)
    (offset : ℕ) : RqVec params.k :=
  Vector.ofFn fun i => prims.prfEta1 seed (offset + i.val)

def sampleVecEta2 (prims : Primitives params encoding) (seed : Seed32)
    (offset : ℕ) : RqVec params.k :=
  Vector.ofFn fun i => prims.prfEta2 seed (offset + i.val)
-- ANCHOR_END: kpkeMatrixAndVectorSampling

-- ANCHOR: kpkeKeygen
def keygenFromSeed (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (d : Seed32) :
    PublicKey params encoding × SecretKey params encoding :=
  let (rho, sigma) := prims.gKeygen d
  let aHat := prims.publicMatrix rho
  let s := prims.sampleVecEta1 sigma 0
  let e := prims.sampleVecEta1 sigma params.k
  let sHat := ring.nttVec s
  let eHat := ring.nttVec e
  let tHat := ring.matVecMul aHat sHat + eHat
  ({ tHatEncoded := encoding.byteEncode12Vec tHat, rho := rho },
    { sHatEncoded := encoding.byteEncode12Vec sHat })
-- ANCHOR_END: kpkeKeygen

-- ANCHOR: kpkeEncrypt
def encrypt (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (ek : PublicKey params encoding) (msg : Message)
    (coins : Coins) : Ciphertext params encoding :=
  let tHat := encoding.byteDecode12Vec ek.tHatEncoded
  let aHat := prims.publicMatrix ek.rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let e2 := prims.prfEta2 coins (2 * params.k)
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  { uEncoded := encoding.byteEncodeDUVec (encoding.compressDU u)
    vEncoded := encoding.byteEncodeDV (encoding.compressDV v) }
-- ANCHOR_END: kpkeEncrypt

-- ANCHOR: kpkeDecrypt
def decrypt (ring : NTTRingOps) (encoding : Encoding params)
    (_prims : Primitives params encoding) (dk : SecretKey params encoding)
    (c : Ciphertext params encoding) : Message :=
  let (u', v') := encoding.decodeCiphertext c.uEncoded c.vEncoded
  let sHat := encoding.byteDecode12Vec dk.sHatEncoded
  let w := v' - ring.invNTT (ring.dot sHat (ring.nttVec u'))
  encoding.byteEncode1 (encoding.compress1 w)
-- ANCHOR_END: kpkeDecrypt

end SecureMessagingDocs.KPKESpec
