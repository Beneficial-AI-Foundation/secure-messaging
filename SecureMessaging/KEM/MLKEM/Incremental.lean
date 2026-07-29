/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.KEM.MLKEM.Construction

/-!
# Incremental ML-KEM

This module instantiates `KEMScheme.IncrementalStructure` for `mlkemScheme` as specified in
ML-KEM Braid, Section 1.2. The encapsulation key splits into the header `(ρ, H(ek))` and
encoded `t̂`; the ciphertext splits into its encoded `u` and `v` components. The `factor`
field of `mlkemIncremental` identifies the staged computation with ML-KEM encapsulation.
-/

open OracleComp KEMScheme LatticeCrypto

namespace MLKEM

/-- The incremental public-key header `(ρ, H(ek))`. The first stage uses both values in
`G(m ‖ H(ek))` and matrix expansion. -/
def incrementalHeader {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding) :
    Seed32 × PublicKeyHash :=
  (ek.rho, encapsulationKeyHash encoding prims ek)

/-- Given `(ρ, h)` and `m`, derives `(k, r) = G(m ‖ h)`, computes the encoded `u`
component from `ρ` and `r`, and returns `((m, r), u, k)`. -/
def incrementalEncaps1 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (hdr : Seed32 × PublicKeyHash) (m : Message) :
    (Message × Coins) × encoding.EncodedU × SharedSecret :=
  let (k, r) := prims.gEncaps m hdr.2
  let aHat := prims.publicMatrix hdr.1
  let y := prims.sampleVecEta1 r 0
  let e1 := prims.sampleVecEta2 r params.k
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  ((m, r), encoding.byteEncodeDUVec (encoding.compressDU u), k)

/-- Given retained state `(m, r)` and encoded `t̂`, recomputes the ephemeral noise from `r`
and returns the encoded `v` component. -/
def incrementalEncaps2 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (st : Message × Coins)
    (vec : encoding.EncodedTHat) : encoding.EncodedV :=
  let tHat := encoding.byteDecode12Vec vec
  let y := prims.sampleVecEta1 st.2 0
  let yHat := ring.nttVec y
  let e2 := prims.prfEta2 st.2 (2 * params.k)
  let mu := encoding.decompress1 (encoding.byteDecode1 st.1)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  encoding.byteEncodeDV (encoding.compressDV v)

/-- The incremental ML-KEM structure of ML-KEM Braid, Section 1.2.1. The intermediate state
is `(m, r)`, and `validPK` checks the header hash against the reconstructed public key. -/
def mlkemIncremental (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalStructure where
  PKheader := Seed32 × PublicKeyHash
  PKvector := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedTHat
  C₁ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedU
  C₂ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedV
  St := Message × Coins
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
  encaps2 := fun st _hdr vec => return (incrementalEncaps2 ring prims st vec)
  factor := by
    intro ek
    simp only [mlkemScheme, asKEMScheme, Equiv.coe_fn_symm_mk,
      bind_assoc, pure_bind]
    rfl

end MLKEM
