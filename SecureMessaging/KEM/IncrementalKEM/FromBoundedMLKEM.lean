/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Bounded
import SecureMessaging.KEM.IncrementalKEM.MLKEM
import SecureMessaging.KEM.IncrementalKEM.FromMLKEM

/-!
# Incremental ML-KEM byte refinement

The bounded and raw interfaces specialize one implementation. The leaking computations agree
on the complete outputs, semantic state and original coins, not only on their first marginals.
-/

open OracleComp KEMScheme

namespace MLKEM.Bounded

variable (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))

local notation "q" => ParameterSet.params p
local notation "inc" => incrementalStructure ring (encoding q) (primitives q prims)
local notation "leak" => incrementalRandLeak ring (encoding q) (primitives q prims)

/-- Public-key validation hashes exactly the same bytes and seed. -/
theorem incremental_validPK_eq (hdr : Seed32 × PublicKeyHash) (vec : Bytes (384 * (q).k)) :
    (inc).validPK hdr vec =
      (mlkemIncremental p ring prims).validPK hdr (Concrete.vectorToByteArray vec) := rfl

/-- Splitting preserves the header and forgets only the vector length evidence. -/
theorem incremental_splitPK_eq (pk : EncapsulationKey q (encoding q)) :
    ((inc).toHeader pk, Concrete.vectorToByteArray ((inc).toVector pk)) =
      ((mlkemIncremental p ring prims).toHeader (toRawPK q pk),
        (mlkemIncremental p ring prims).toVector (toRawPK q pk)) := rfl

/-- Both split ciphertext components retain their exact bytes. -/
theorem incremental_splitC_eq (c : Ciphertext q (encoding q)) :
    Prod.map Concrete.vectorToByteArray Concrete.vectorToByteArray ((inc).splitC c) =
      (mlkemIncremental p ring prims).splitC (toRawC q c) := rfl

/-- The full generated key pair and both leaked seeds commute with forgetting. -/
theorem keygenRleak_refines :
    (fun z => (Prod.map (toRawPK q) (toRawSK q) z.1, z.2)) <$> (leak).keygenRleak =
      (mlkemIncrementalRandLeak p ring prims).keygenRleak := by
  simp only [mlkemIncrementalRandLeak, incrementalRandLeak, map_bind, map_pure]
  congr 1

/-- First-stage state, ciphertext, secret and sampled message are preserved jointly. -/
theorem encaps1Rleak_refines (hdr : Seed32 × PublicKeyHash) :
    (fun z => ((z.1.1, Concrete.vectorToByteArray z.1.2.1, z.1.2.2), z.2)) <$>
      (leak).encaps1Rleak hdr =
        (mlkemIncrementalRandLeak p ring prims).encaps1Rleak hdr := by
  simp only [mlkemIncrementalRandLeak, incrementalRandLeak, map_bind, map_pure]
  congr 1

/-- The pure second stage preserves its entire ciphertext/unit-leak result. -/
theorem encaps2Rleak_refines (st : EncapsulationState q)
    (hdr : Seed32 × PublicKeyHash) (vec : Bytes (384 * (q).k)) :
    Prod.map Concrete.vectorToByteArray id <$> (leak).encaps2Rleak st hdr vec =
      (mlkemIncrementalRandLeak p ring prims).encaps2Rleak st hdr
        (Concrete.vectorToByteArray vec) := by
  have hdet : Concrete.vectorToByteArray
      ((incrementalDeterministicEncaps2 ring (encoding q) (primitives q prims)).encaps2Det
        st hdr vec) =
      (mlkemDeterministicEncaps2 p ring prims).encaps2Det st hdr
        (Concrete.vectorToByteArray vec) := by
    apply ByteArray.ext_iff.2
    rfl
  change pure (Concrete.vectorToByteArray
      (incrementalEncaps2 (encoding := encoding q) ring st vec), ()) =
    (pure (incrementalEncaps2 (encoding := Concrete.concreteEncoding q) ring st
      (Concrete.vectorToByteArray vec), ()) : ProbComp (ByteArray × Unit))
  exact congrArg (fun v => (pure (v, ()) : ProbComp (ByteArray × Unit))) hdet

end MLKEM.Bounded
