/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Nat.Basic

/-!
# Ratcheted Authenticator

A *ratcheted authenticator* evolves authentication state from a sequence of epoch
keys. At each epoch, the current state produces and verifies tags for headers
and ciphertexts in separate domains. These tags are intended to
detect message modification without relying on an outer protocol. All
operations are pure and deterministic.

It is used for optional internal authentication of
headers and ciphertexts `C₁ ‖ C₂`  in
[ML-KEM Braid §2.4](https://signal.org/docs/specifications/mlkembraid/#internal-authentication)

[SPACES]
- `InitKey`: initial key material.
- `EpochKey`: key material mixed in on each ratchet step.
- `AuthState`: local authenticator state.
- `Header`: header message space.
- `Ciphertext`: complete-ciphertext message space.
- `Mac`: MAC tag space.
- Epochs are `ℕ`.

[ALGORITHMS]
- `init : InitKey → ℕ → AuthState`.
  Derive initial state from an initial key and epoch.
- `update : AuthState → ℕ → EpochKey → AuthState`.
  Deterministically ratchet state with an epoch key at the given epoch.
- `macHeader : AuthState → ℕ → Header → Mac` /
  `verifyHeader : AuthState → ℕ → Header → Mac → Bool`.
  Domain-separated MAC / verify for headers.
- `macCiphertext : AuthState → ℕ → Ciphertext → Mac` /
  `verifyCiphertext : AuthState → ℕ → Ciphertext → Mac → Bool`.
  Domain-separated MAC / verify for complete ciphertexts.

[CORRECTNESS]
Tags produced from a state and epoch are accepted when verified with that same
state and epoch. For every `s : AuthState`, `ep : ℕ`, `h : Header`, and
`c : Ciphertext`:
- `verifyHeader s ep h (macHeader s ep h) = true`.
- `verifyCiphertext s ep c (macCiphertext s ep c) = true`.
-/

/-- Epoch-indexed MAC state with domain-separated header and ciphertext authentication. -/
-- ANCHOR: RatchetedAuthenticator
structure RatchetedAuthenticator
    (InitKey EpochKey AuthState Header Ciphertext Mac : Type) where
  /-- Initialize authenticator state from an initial key and epoch. -/
  init : InitKey → ℕ → AuthState
  /-- Deterministically ratchet the authenticator state with an epoch key. -/
  update : AuthState → ℕ → EpochKey → AuthState
  /-- MAC a header at the given epoch. -/
  macHeader : AuthState → ℕ → Header → Mac
  /-- Verify a MAC on a header at the given epoch. -/
  verifyHeader : AuthState → ℕ → Header → Mac → Bool
  /-- MAC a complete ciphertext at the given epoch. -/
  macCiphertext : AuthState → ℕ → Ciphertext → Mac
  /-- Verify a MAC on a complete ciphertext at the given epoch. -/
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
