/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Construction

/-!
# One-time-key GCM — Correctness

Correctness proof for `gcmOneTimeAEAD`: for supported message lengths, decryption
recovers the plaintext. The tag check passes because `decrypt` recomputes the same
`S`/`T` as `encrypt`, and `gctr` is an involution (`gctr_involution`), so `GCTR`
inverts the ciphertext back to the plaintext.
-/

open OracleSpec OracleComp

/-- `gcmOneTimeAEAD` satisfies the ACD19 `AEADScheme.Correct`, given that the message
length is supported (`hL`). -/
-- ANCHOR: gcmOneTimeAEAD_correct
theorem gcmOneTimeAEAD_correct {K : Type} (prp : PRPScheme K (BitVec 128)) {L : ℕ}
    (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp L hL).Correct
-- ANCHOR_END: gcmOneTimeAEAD_correct
    := by
  rintro k ⟨⟨av, ad⟩, hav⟩ m
  have hv : ValidMsgLength L ∧ ValidAADLength av := ⟨hL, hav⟩
  simp only [gcmOneTimeAEAD, gcmEncrypt, gcmDecrypt]
  rw [if_pos hv]
  simp only [if_true, gctr_involution]
