/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.KEM.MLKEM.Construction

/-!
# Incremental ML-KEM

This module instantiates `KEMScheme.IncrementalStructure` for `mlkemScheme`. The ML-KEM
algorithm is specified in [NIST FIPS 203](https://csrc.nist.gov/pubs/fips/203/final), and the
staged interface follows [Signal's ML-KEM Braid specification,
§§1.2–1.2.1](https://signal.org/docs/specifications/mlkembraid/).

The encapsulation key splits into the header `(ρ, H(ek))` and encoded `t̂`. In the code,
`rho` / `ρ` is the 32-byte public-matrix seed, `H(ek)` is the hash of the complete
encapsulation key, and `tHat` / `tHatEncoded` / `t̂` is the encoded NTT-domain public-key
vector. A hat denotes an NTT-domain value, so `yHat` is the NTT of the ephemeral vector `y`.
The ciphertext splits into encoded `u` and `v` components. The first stage also computes
`e2`, the second noise polynomial, and retains `message`, the sampled 32-byte ML-KEM message.
The `factor` field of `mlkemIncremental` identifies the staged computation with ML-KEM
encapsulation.
-/

open OracleComp KEMScheme LatticeCrypto

namespace MLKEM

/-- The incremental public-key header `(ρ, H(ek))`. The first stage uses both values in
`G(m ‖ H(ek))` and matrix expansion. -/
-- ANCHOR: incrementalHeader
def incrementalHeader {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding) :
    Seed32 × PublicKeyHash :=
  (ek.rho, encapsulationKeyHash encoding prims ek)
-- ANCHOR_END: incrementalHeader

/-- Values computed during the first incremental encapsulation stage and needed by the
second: the NTT-domain ephemeral vector `yHat`, second noise polynomial `e2`, and ML-KEM
`message`. This semantic state retains derived values rather than the raw coins. -/
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

/-- Given `(ρ, h)` and `m`, derives `(k, r) = G(m ‖ h)`, computes `yHat`, `e2`, and the
encoded `u` component, and returns them as the stage-2 state, first ciphertext component,
and shared secret. -/
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

/-- Given the derived stage-2 state and encoded `t̂`, decodes `tHat`, combines it with the
retained `yHat`, `e2`, and `message`, and returns the encoded `v` component without
re-sampling or recomputing an NTT. -/
-- ANCHOR: incrementalEncaps2
def incrementalEncaps2 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (st : EncapsulationState params)
    (vec : encoding.EncodedTHat) : encoding.EncodedV :=
  let tHat := encoding.byteDecode12Vec vec
  let mu := encoding.decompress1 (encoding.byteDecode1 st.message)
  let v := ring.invNTT (ring.dot tHat st.yHat) + st.e2 + mu
  encoding.byteEncodeDV (encoding.compressDV v)
-- ANCHOR_END: incrementalEncaps2

/-- The incremental ML-KEM structure of ML-KEM Braid, Section 1.2.1. Stage 1 produces an
`EncapsulationState` containing `yHat`, `e2`, and `message`; stage 2 consumes that state
without retaining raw coins. `validPK` checks the header hash against the reconstructed
public key. -/
-- ANCHOR: mlkemIncremental
def mlkemIncremental (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalStructure
-- ANCHOR_END: mlkemIncremental
    where
  PKheader := Seed32 × PublicKeyHash
  PKvector := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedTHat
  C₁ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedU
  C₂ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedV
  St := EncapsulationState (ParameterSet.params p)
  validPK hdr vec := decide
    (encapsulationKeyHash (Concrete.concreteEncoding (ParameterSet.params p)) prims
        { tHatEncoded := vec, rho := hdr.1 } = hdr.2)
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
    simp only [mlkemScheme, asKEMScheme, Equiv.coe_fn_symm_mk,
      bind_assoc, pure_bind]
    rfl

end MLKEM
