/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import LatticeCrypto.MLKEM.KEM

/-!
# Encoding-polymorphic incremental ML-KEM

This module defines incremental ML-KEM for any byte encoding `encoding`. The two encapsulation
stages use the samplers of ML-KEM. Only the encoded public vector and the encoded ciphertext
components depend on `encoding`.
-/

open OracleComp KEMScheme LatticeCrypto

namespace MLKEM

/-- The public-key header `(ρ, H(ek))`: the public-matrix seed and the hash of the complete
encoded encapsulation key. First-stage encapsulation uses only the header. -/
-- ANCHOR: incrementalHeader
def incrementalHeader {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding) :
    Seed32 × PublicKeyHash :=
  (ek.rho, encapsulationKeyHash encoding prims ek)
-- ANCHOR_END: incrementalHeader

/-- The values that the first encapsulation stage computes and the second stage needs: the
NTT-domain ephemeral vector `yHat`, the second noise polynomial `e2`, and the sampled ML-KEM
message `message` from which the first stage derives them. -/
-- ANCHOR: incrementalEncapsulationState
structure EncapsulationState (params : Params) where
  /-- NTT-domain form of the ephemeral vector `y`, used to compute the second ciphertext
  component. -/
  yHat : TqVec params.k
  /-- Second encapsulation-noise polynomial, added to the second ciphertext component. -/
  e2 : Rq
  /-- Sampled 32-byte ML-KEM message embedded in the second ciphertext component. -/
  message : Message
-- ANCHOR_END: incrementalEncapsulationState

/-- First encapsulation stage `((ρ, h), m) ↦ (st, u, k)`, where `(k, r) = G(m ‖ h)`. Here `st` is
the state for the second stage, `u` the encoded first ciphertext component and `k` the shared
secret. -/
-- ANCHOR: incrementalEncaps1
def incrementalEncaps1 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (hdr : Seed32 × PublicKeyHash) (m : Message) :
    EncapsulationState params × encoding.EncodedU × SharedSecret :=
  let (k, r) := prims.gEncaps m hdr.2
  let aHat := prims.publicMatrix hdr.1
  let y := prims.sampleVecEta1 r 0
  let e1 := prims.sampleVecEta2 r params.k
  let e2 := prims.prfEta2 r (2 * params.k)
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  ({ yHat, e2, message := m }, encoding.byteEncodeDUVec (encoding.compressDU u), k)
-- ANCHOR_END: incrementalEncaps1

/-- Second encapsulation stage `(st, t̂) ↦ v`: the encoded second ciphertext component, computed
from the state `st` and the encoded public vector `t̂`. It samples nothing and computes no NTT of
`y`. -/
-- ANCHOR: incrementalEncaps2
def incrementalEncaps2 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (st : EncapsulationState params)
    (vec : encoding.EncodedTHat) : encoding.EncodedV :=
  let tHat := encoding.byteDecode12Vec vec
  let mu := encoding.decompress1 (encoding.byteDecode1 st.message)
  let v := ring.invNTT (ring.dot tHat st.yHat) + st.e2 + mu
  encoding.byteEncodeDV (encoding.compressDV v)
-- ANCHOR_END: incrementalEncaps2

/-- Incremental ML-KEM for the byte encoding `encoding`. -/
-- ANCHOR: incrementalStructure
def incrementalStructure {params : Params} (ring : NTTRingOps)
    (encoding : Encoding params) (prims : Primitives params encoding)
    [DecidableEq encoding.EncodedTHat]
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV] :
    (asKEMScheme ring encoding prims).IncrementalStructure where
  PKheader := Seed32 × PublicKeyHash
  PKvector := encoding.EncodedTHat
  C₁ := encoding.EncodedU
  C₂ := encoding.EncodedV
  St := EncapsulationState params
  validPK hdr vec := decide
    (encapsulationKeyHash encoding prims { tHatEncoded := vec, rho := hdr.1 } = hdr.2)
  splitPK :=
    { toFun := fun ek => ⟨(incrementalHeader prims ek, ek.tHatEncoded), by simp [incrementalHeader]⟩
      invFun := fun parts => { tHatEncoded := parts.1.2, rho := parts.1.1.1 }
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨rho, h⟩, vec⟩, hvalid⟩
        have hh := of_decide_eq_true hvalid
        apply Subtype.ext
        simp only [incrementalHeader, hh] }
  splitC :=
    { toFun := fun c => (c.uEncoded, c.vEncoded)
      invFun := fun uv => { uEncoded := uv.1, vEncoded := uv.2 }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  encaps1 := fun hdr => do
    let m ←$ᵗ Message
    return incrementalEncaps1 ring prims hdr m
  encaps2 := fun st _hdr vec => return (incrementalEncaps2 ring st vec)
  factor := by
    intro ek
    simp only [asKEMScheme, Equiv.coe_fn_symm_mk, bind_assoc, pure_bind]
    rfl
-- ANCHOR_END: incrementalStructure

/-- The second stage samples no randomness. -/
def incrementalDeterministicEncaps2 {params : Params} (ring : NTTRingOps)
    (encoding : Encoding params) (prims : Primitives params encoding)
    [DecidableEq encoding.EncodedTHat]
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV] :
    (incrementalStructure ring encoding prims).DeterministicEncaps2 where
  encaps2Det := fun st _hdr vec => incrementalEncaps2 ring st vec
  encaps2_eq := fun _st _hdr _vec => rfl

/-- Decapsulation is deterministic: it is the total implicit-rejection computation of ML-KEM. -/
def incrementalDeterministicDecaps {params : Params} (ring : NTTRingOps)
    (encoding : Encoding params) (prims : Primitives params encoding)
    [DecidableEq encoding.EncodedTHat]
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV] :
    KEMScheme.DeterministicDecaps (asKEMScheme ring encoding prims) where
  decapsDet := fun dk c => some (decapsInternal ring encoding prims dk c)
  decaps_eq := fun _sk _c => rfl

/-- The three incremental operations with their outputs and the coins they sample. -/
-- ANCHOR: incrementalRandLeak
def incrementalRandLeak {params : Params} (ring : NTTRingOps)
    (encoding : Encoding params) (prims : Primitives params encoding)
    [DecidableEq encoding.EncodedTHat]
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV] :
    (asKEMScheme ring encoding prims).IncrementalRandLeak
      (incrementalStructure ring encoding prims) where
  KeygenRand := Seed32 × Seed32
  Encaps1Rand := Message
  Encaps2Rand := Unit
  keygenRleak := do
    let d ← $ᵗ Seed32
    let z ← $ᵗ Seed32
    return (keygenInternal ring encoding prims d z, (d, z))
  encaps1Rleak := fun hdr => do
    let m ← $ᵗ Message
    return (incrementalEncaps1 ring prims hdr m, m)
  encaps2Rleak := fun st _hdr vec =>
    return (incrementalEncaps2 ring st vec, ())
  keygen_fst := by
    simp only [asKEMScheme, keygen, bind_assoc, pure_bind]
  encaps1_fst := fun _hdr => by
    simp only [incrementalStructure, bind_assoc, pure_bind]
  encaps2_fst := fun _st _hdr _vec => by
    simp only [incrementalStructure, pure_bind]
-- ANCHOR_END: incrementalRandLeak

end MLKEM
