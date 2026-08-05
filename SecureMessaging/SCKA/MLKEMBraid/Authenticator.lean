/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Nat.Basic

/-!
# Ratcheted Authenticator

A *ratcheted authenticator* evolves authentication state along a sequence of
epoch keys. At each epoch, the current state produces and verifies MAC tags,
separately for two message spaces (`Header` and `Ciphertext`). All operations
are pure and deterministic.

[SPACES]
- `InitKey`: initial key material.
- `EpochKey`: key material mixed in on each ratchet step.
- `AuthState`: local authenticator state.
- `Header`: header message space.
- `Ciphertext`: ciphertext message space.
- `Mac`: MAC tag space.
- Epochs are `ℕ`.

[ALGORITHMS]
- `init : InitKey → ℕ → AuthState`.
  Derive initial state from an initial key and epoch.
- `update : AuthState → ℕ → EpochKey → AuthState`.
  Ratchet state with an epoch key at the given epoch.
- `macHeader : AuthState → ℕ → Header → Mac` /
  `verifyHeader : AuthState → ℕ → Header → Mac → Bool`.
  MAC / verify for headers.
- `macCiphertext : AuthState → ℕ → Ciphertext → Mac` /
  `verifyCiphertext : AuthState → ℕ → Ciphertext → Mac → Bool`.
  MAC / verify for ciphertexts.

The `ℕ` argument is the epoch at which the operation acts: `init` and `update`
yield the state for that epoch; MAC and verify take the epoch the tag is bound
to.

[CORRECTNESS]
Tags produced from a state and epoch are accepted when verified with that same
state and epoch. For every `s : AuthState`, `ep : ℕ`, `h : Header`, and
`c : Ciphertext`:
- `verifyHeader s ep h (macHeader s ep h) = true`.
- `verifyCiphertext s ep c (macCiphertext s ep c) = true`.

Used for optional internal authentication in
[ML-KEM Braid §2.4](https://signal.org/docs/specifications/mlkembraid/#internal-authentication),
where `Ciphertext` is instantiated as the concatenation `ct₁ ‖ ct₂` of the two
KEM ciphertext parts, authenticated as a single message. In that protocol the
epoch is part of every MAC input, and header tags use the state before
`update` with the epoch key while ciphertext tags use the state after.
-/

/-- Epoch-indexed MAC state with separate header and ciphertext authentication. -/
-- ANCHOR: RatchetedAuthenticator
structure RatchetedAuthenticator
    (InitKey EpochKey AuthState Header Ciphertext Mac : Type) where
  /-- Initialize authenticator state from an initial key and epoch. -/
  init : InitKey → ℕ → AuthState
  /-- Ratchet the authenticator state with an epoch key at the given epoch. -/
  update : AuthState → ℕ → EpochKey → AuthState
  /-- MAC a header at the given epoch. -/
  macHeader : AuthState → ℕ → Header → Mac
  /-- Verify a MAC on a header at the given epoch. -/
  verifyHeader : AuthState → ℕ → Header → Mac → Bool
  /-- MAC a ciphertext at the given epoch. -/
  macCiphertext : AuthState → ℕ → Ciphertext → Mac
  /-- Verify a MAC on a ciphertext at the given epoch. -/
  verifyCiphertext : AuthState → ℕ → Ciphertext → Mac → Bool
  /-- Honestly produced header MACs verify successfully. -/
  verifyHeader_correct :
    ∀ (s : AuthState) (ep : ℕ) (h : Header),
      verifyHeader s ep h (macHeader s ep h) = true
  /-- Honestly produced ciphertext MACs verify successfully. -/
  verifyCiphertext_correct :
    ∀ (s : AuthState) (ep : ℕ) (c : Ciphertext),
      verifyCiphertext s ep c (macCiphertext s ep c) = true
-- ANCHOR_END: RatchetedAuthenticator
