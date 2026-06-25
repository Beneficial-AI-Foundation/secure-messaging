/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Construction

/-!
# Encrypt-then-MAC — Correctness

Correctness proof for the EtM construction: if the base cipher `se` is correct,
then `etmAEAD se prf` is a correct `AEADScheme`.

Correctness is standard: for all keys and inputs, `Dec(Enc(m)) = m`.
-/

open OracleSpec OracleComp

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]

omit [DecidableEq AD] [DecidableEq C_e] in
/-- If the base cipher `se` is correct, then `etmAEAD se prf` is correct.

The proof is straightforward: the tag comparison
`prf.eval km (ad, c) == prf.eval km (ad, c)` is trivially `true`, so
`decrypt` always reaches the `se.decrypt` branch, which recovers the
plaintext by `hse`. -/
theorem etmAEAD_correct (se : DetSEAlg K_e M C_e)
    (prf : PRFScheme K_m (AD × C_e) T) (hse : se.Correct) :
    (etmAEAD se prf).Correct := by
  intro ⟨ke, km⟩ ad msg
  simp only [etmAEAD, beq_self_eq_true, ↓reduceIte]
  exact hse ke msg
