/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.MLKEM.Concrete.Encoding

/-!
# Output lengths of concrete ML-KEM encodings

These shape facts hold for every semantic input, including zero widths or vector lengths.
They use the supplied concrete encoder's output directly, without ring laws, canonical-input
conditions or primitive correctness assumptions.
-/

namespace MLKEM.Concrete

/-- The encoded public/secret polynomial vector occupies exactly `384 * k` bytes. -/
theorem concreteEncoding_tHat_size (params : Params) (v : TqVec params.k) :
    ((concreteEncoding params).byteEncode12Vec v).size = 384 * params.k := by
  simp [concreteEncoding, byteEncode12Vec, ByteArray.size]

/-- The first ciphertext vector occupies exactly `32 * du * k` bytes. -/
theorem concreteEncoding_u_size (params : Params) (v : RqVec params.k) :
    ((concreteEncoding params).byteEncodeDUVec v).size = 32 * params.du * params.k := by
  simp [concreteEncoding, byteEncodeVec, ByteArray.size]

/-- The second ciphertext polynomial occupies exactly `32 * dv` bytes. -/
theorem concreteEncoding_v_size (params : Params) (v : Rq) :
    ((concreteEncoding params).byteEncodeDV v).size = 32 * params.dv := by
  dsimp only [concreteEncoding, byteEncode]
  change (ByteArray.ofFn
    (n := (Array.ofFn (α := Nat) (n := ringDegree * params.dv) _).size / 8) _).size = _
  simp only [ByteArray.size_ofFn, Array.size_ofFn, ringDegree]
  omega

end MLKEM.Concrete
