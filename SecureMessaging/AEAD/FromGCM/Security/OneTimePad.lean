/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM
import ToVCVio.OracleComp.Constructions.BitVec

/-!
# GCM — one-time-pad composition for gctr

The rewrite of `GCM.gctr` on distinct counter blocks under an ideal cipher into an
XOR with a uniform keystream, giving one-time-pad confidentiality of the GCTR layer
(Phase 1 criterion 3, GCM-specific half).

`keystream_eq_blocksToBitVec` bridges `GCM.keystream` to the generic
`blocksToBitVec` map, so `gctr_eq_xor` restates `GCM.gctr` as an XOR with a
truncated block concatenation and all downstream reasoning happens through the
generic uniformity brick `probOutput_blocksToBitVec_uniform`.
-/

open OracleSpec OracleComp ENNReal

namespace GCM

/-! ## Bridging `keystream` to the generic concatenation map -/

/-- `GCM.keystream` is the generic truncated big-endian block concatenation
`blocksToBitVec` (the two definitions agree verbatim). Downstream files rewrite
through this bridge instead of unfolding `keystream`. -/
theorem keystream_eq_blocksToBitVec (blocks : List (BitVec 128)) (p : ℕ) :
    keystream blocks p = blocksToBitVec blocks p :=
  rfl

/-- `GCM.gctr` as an XOR with the truncated concatenation of the enciphered
counter blocks: `gctr ciph k icb x = x ^^^ MSB_p(CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …)`,
stated through the generic `blocksToBitVec` map. -/
theorem gctr_eq_xor {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) {p : ℕ} (x : BitVec p) :
    gctr ciph k icb x =
      x ^^^ blocksToBitVec ((counterChain icb ((p + 127) / 128)).map (ciph k)) p := by
  simp only [gctr, keystream_eq_blocksToBitVec]

/-! ## One-time-pad composition

Uniform keystream makes the XOR of any fixed message uniform, in the two shapes
the games consume: a single uniform `ks : BitVec L` draw (Phase 5's privacy
equality) and uniform independent 128-bit blocks fed through the truncated
concatenation (Phase 3's block-answers projection). The probabilistic content is
entirely `probOutput_xor_map` and `probOutput_blocksToBitVec_uniform`. -/

/-- **One-time pad, single-sample form**: XOR of a fixed message with one uniform
keystream draw `ks : BitVec L` hits every ciphertext with probability
`(Fintype.card (BitVec L))⁻¹`. The GCM-facing restatement of VCVio's
`probOutput_xor_uniform` with the message on the left of the XOR. -/
theorem probOutput_xor_keystream_uniform {L : ℕ} (m c : BitVec L) :
    Pr[= c | (fun ks : BitVec L => m ^^^ ks) <$> ($ᵗ BitVec L)] =
      (Fintype.card (BitVec L) : ℝ≥0∞)⁻¹ := by
  simp [probOutput_uniformSample]

/-- **One-time pad, block form**: sampling the `⌈L / 128⌉` keystream blocks
uniformly and independently, concatenating, truncating to `L` bits (covering the
final partial block), and XOR-ing into a fixed message is uniform on `BitVec L`.
The shape `gctr` takes after `gctr_eq_xor` once the enciphered counter blocks are
idealized to uniform. -/
theorem probOutput_gctr_uniform {L : ℕ} (m c : BitVec L) :
    Pr[= c | (fun v : Vector (BitVec 128) ((L + 127) / 128) =>
        m ^^^ blocksToBitVec v.toList L) <$> ($ᵗ Vector (BitVec 128) ((L + 127) / 128))] =
      (Fintype.card (BitVec L) : ℝ≥0∞)⁻¹ := by
  have hL : L ≤ 128 * ((L + 127) / 128) := by omega
  calc Pr[= c | (fun v : Vector (BitVec 128) ((L + 127) / 128) =>
          m ^^^ blocksToBitVec v.toList L) <$> ($ᵗ Vector (BitVec 128) ((L + 127) / 128))]
      = Pr[= c | (m ^^^ ·) <$> ((fun v : Vector (BitVec 128) ((L + 127) / 128) =>
          blocksToBitVec v.toList L) <$> ($ᵗ Vector (BitVec 128) ((L + 127) / 128)))] := by
        rw [Functor.map_map]
    _ = Pr[= m ^^^ c | (fun v : Vector (BitVec 128) ((L + 127) / 128) =>
          blocksToBitVec v.toList L) <$> ($ᵗ Vector (BitVec 128) ((L + 127) / 128))] :=
        probOutput_xor_map _ m c
    _ = (Fintype.card (BitVec L) : ℝ≥0∞)⁻¹ :=
        probOutput_blocksToBitVec_uniform _ L hL (m ^^^ c)

/-- The degenerate case `L = 0` of the single-sample form: `BitVec 0` is a
singleton, so the unique ciphertext is hit with probability `1`. The main theorem
covers this case rather than excluding it. -/
example (m c : BitVec 0) :
    Pr[= c | (fun ks : BitVec 0 => m ^^^ ks) <$> ($ᵗ BitVec 0)] = 1 := by
  simp [probOutput_uniformSample]

/-- The degenerate case `L = 0` of the block form: probability `1` on the unique
value of `BitVec 0`. -/
example (m c : BitVec 0) :
    Pr[= c | (fun v : Vector (BitVec 128) ((0 + 127) / 128) =>
        m ^^^ blocksToBitVec v.toList 0) <$> ($ᵗ Vector (BitVec 128) ((0 + 127) / 128))] = 1 := by
  simpa using probOutput_gctr_uniform m c

end GCM
