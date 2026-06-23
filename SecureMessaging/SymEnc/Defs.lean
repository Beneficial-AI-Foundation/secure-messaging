/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Deterministic Symmetric Encryption (Local Placeholder)

Formalization of a deterministic symmetric encryption primitive with one-time
IND$-CPA (real-or-random) security, following:

- [NRS14] Namprempre, Rogaway, Shrimpton.
  *Reconsidering Generic Composition.*
  EUROCRYPT 2014.
  — Section 2: "ivE scheme" `E : K × {0,1}^η × M → {0,1}*`.
  We omit the IV parameter because the key is one-time (IV absorbed into key).

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019.
  — One-time encryption setting where each key is used at most once.

This is a **local placeholder**. VCVio already has `SymmEncAlg`, but its
`encrypt`/`decrypt` are monadic (`K → M → m C`), i.e. possibly randomized, and
it carries only information-theoretic perfect-secrecy notions (Shannon) — not a
computational IND$-CPA game. ACD19's EtM proof needs a *deterministic* cipher
with a *computational one-time IND$-CPA* assumption, which is exactly what
`DetSEAlg` plus the game below provide. Tracked upstream at
<https://github.com/Verified-zkEVM/VCV-io/issues/411>; when VCVio delivers a
deterministic IND$-CPA variant, this file should be replaced by an import.

## Deviations from NRS14

- **No IV parameter**: NRS14's ivE scheme has `E(K, IV, M)`. We use
  `encrypt(K, M)` because the key is one-time and absorbs the IV role (as in
  ACD19's deterministic AEAD).
- **One query**: NRS14's ivE-security allows `q_e` encryption queries. We
  restrict to `q_e = 1` (one-time security).
- **No nonce**: NRS14 has a nonce `N` for multi-query freshness. Not needed
  when each key is used once.
-/

open OracleSpec OracleComp ENNReal

/-- A deterministic symmetric encryption scheme with key space `K`, message
space `M`, and ciphertext space `C`.

NRS14 Section 2: ivE scheme `E : K × {0,1}^η × M → {0,1}*`.
Deviation: no IV parameter (one-time key provides all randomness). -/
structure DetSEAlg (K M C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : ProbComp K
  /-- Deterministic encryption: `Enc(K, M) = C`. -/
  encrypt : K → M → C
  /-- Deterministic decryption: `Dec(K, C) = some M` or `none`. -/
  decrypt : K → C → Option M

namespace DetSEAlg

variable {K M C : Type}

/-- A `DetSEAlg` is correct if decryption always recovers the plaintext. -/
def Correct (se : DetSEAlg K M C) : Prop :=
  ∀ (k : K) (m : M), se.decrypt k (se.encrypt k m) = some m

section IndCPA

/-! ## One-Time IND$-CPA Security Game

NRS14 Section 2, "ivE-security" / Figure 4 encryption oracle.
Deviation: one query (`q_e = 1`), no nonce, deterministic encryption.

The adversary `A` has access to:
- Uniform randomness (`unifSpec`).
- A one-time encryption oracle `encrypt(m)`:
  if `b = false`, returns `some (Enc(K, m))`;
  if `b = true`, returns `some ($ᵗ C)` (uniform random ciphertext).
  Returns `none` on subsequent calls.

The game state is `Bool` tracking whether the encryption oracle has been called.

Note: we write "IndCPA" in identifiers to avoid the Lean syntax issue with `$`
in names, but the game is IND$-CPA (real ciphertext vs uniform random bits),
which is strictly stronger than standard IND-CPA (left-or-right).
-/

/-! ### Oracle spec -/

/-- Oracle spec (signatures only) for the one-time IND$-CPA game: uniform
randomness plus an encryption oracle `M →ₒ Option C`. -/
abbrev indCPASpec (M C : Type) := unifSpec + (M →ₒ Option C)

/-! ### Adversary -/

/-- One-time IND$-CPA adversary: a computation with access to uniform
randomness and the encryption oracle, outputting a guess bit. -/
abbrev IndCPA_Adversary (M C : Type) :=
  OracleComp (indCPASpec M C) Bool

/-! ### Oracle implementations -/

/-- Uniform-randomness oracle lifted to the game-state monad. -/
def oracleUnif :
    QueryImpl unifSpec (StateT Bool ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Bool ProbComp)

/-- One-time encryption oracle for the IND$-CPA game.
First call: if `b = false`, returns `some (se.encrypt k m)`;
            if `b = true`, returns `some ($ᵗ C)`.
Subsequent calls: returns `none`. -/
def oracleEncrypt [SampleableType C] (se : DetSEAlg K M C) (b : Bool) (k : K) :
    QueryImpl (M →ₒ Option C) (StateT Bool ProbComp) :=
  fun m => do
    if (← get) then pure none
    else do
      set true
      let c ← if b
        then liftM ($ᵗ C : ProbComp C)
        else pure (se.encrypt k m)
      return some c

/-- Complete oracle set for the one-time IND$-CPA game. -/
def indCPAImpl [SampleableType C] (se : DetSEAlg K M C) (b : Bool) (k : K) :
    QueryImpl (indCPASpec M C) (StateT Bool ProbComp) :=
  oracleUnif + oracleEncrypt se b k

/-! ### Security experiment -/

/-- One-time IND$-CPA experiment with a fixed challenge bit `b`.
The branch `b = false` is the real experiment; `b = true` is the random
experiment.

NRS14 Section 2: ivE-security experiment, restricted to one query. -/
def securityExpFixedBit [SampleableType C] (se : DetSEAlg K M C)
    (adversary : IndCPA_Adversary M C) (b : Bool) : ProbComp Bool := do
  let k ← se.keygen
  let (b', _) ← (simulateQ (indCPAImpl se b k) adversary).run false
  return b'

/-- One-time IND$-CPA distinguishing advantage:
`|Pr[A^{rand} = 1] - Pr[A^{real} = 1]|`.

NRS14 Section 2: `Adv^{ivE}_E(A)`, restricted to one query and no IV. -/
noncomputable def distAdvantage [SampleableType C] (se : DetSEAlg K M C)
    (adversary : IndCPA_Adversary M C) : ℝ :=
  |(Pr[= true | securityExpFixedBit se adversary true]).toReal -
   (Pr[= true | securityExpFixedBit se adversary false]).toReal|

end IndCPA

end DetSEAlg
