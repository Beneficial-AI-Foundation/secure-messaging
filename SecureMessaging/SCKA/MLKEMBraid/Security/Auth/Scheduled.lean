/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Construction

/-!
# Scheduled authenticator

A scheduled authenticator keeps a root and a MAC key. Each update feeds the previous root and an
update input to a schedule `F`, which returns the new root and the new MAC key. Tags depend only
on the MAC key, and verification recomputes the tag. The initial key is the update input of the
first update, at label `1`, from the fixed root `initRoot`.

`scheme P S irl` is ML-KEM Braid with this authenticator and a uniform initial key.
-/

@[expose] public section

open OracleComp

namespace MLKEMBraid.Auth

open Braid

/-- Root and MAC keys ratcheted by a schedule `F`; tags computed from the MAC key alone. -/
structure ScheduledAuthenticator (P : Parameters ProbComp) (Root MacKey : Type) where
  /-- The schedule: label, previous root, update input ↦ (new root, new MAC key). -/
  F : ℕ → Root → P.EpochKey → Root × MacKey
  /-- The root before initialisation (`0^32` in the specification and in Rust). -/
  initRoot : Root
  /-- The header tag computed from a MAC key at an epoch. -/
  macHeader : MacKey → ℕ → P.inc.PKheader → P.Mac
  /-- The ciphertext tag computed from a MAC key at an epoch. -/
  macCiphertext : MacKey → ℕ → P.inc.C₁ × P.inc.C₂ → P.Mac

variable {P : Parameters ProbComp} {Root MacKey : Type}

/-- The authenticator interface of `S`: the initial key is an update input at label `1`. -/
def ScheduledAuthenticator.toRatcheted [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) :
    RatchetedAuthenticator P.EpochKey P.EpochKey (Root × MacKey)
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac where
  init ik e := S.F e S.initRoot ik
  update s e k := S.F e s.1 k
  macHeader s e h := S.macHeader s.2 e h
  verifyHeader s e h t := decide (S.macHeader s.2 e h = t)
  macCiphertext s e c := S.macCiphertext s.2 e c
  verifyCiphertext s e c t := decide (S.macCiphertext s.2 e c = t)
  verifyHeader_correct := fun _ _ _ => by simp
  verifyCiphertext_correct := fun _ _ _ => by simp

/-- ML-KEM Braid with the scheduled authenticator `S` and a uniform initial key. -/
def scheme (P : Parameters ProbComp) [DecidableEq P.Mac] [SampleableType P.EpochKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc) :=
  Braid.scheme P S.toRatcheted irl ($ᵗ P.EpochKey)

end MLKEMBraid.Auth
