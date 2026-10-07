/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction

/-!
# Opp-BiKEM-CKA — Execution transcripts

Each epoch `e ≥ 1` of Opp-BiKEM-CKA runs one KEM instance. The *requester* of `e` (A for even
`e`, B for odd `e`) draws a key pair `(pk, sk) ← kem.keygen`; the *responder* encapsulates
`(c, k) ← kem.encaps pk` once it has decoded `pk`.

The module introduces:

* `Role.reqParity`, `Role.resParity` — the parity of the epochs at which a role requests and
  at which it responds;
* `EpochTranscript` — the samples drawn so far for one epoch, each with a proof of membership
  in the support of its sampler;
* `Transcript := ℤ → EpochTranscript` — an execution transcript, indexed by the construction's
  integer epochs; on reachable states only epochs `≥ 1` are populated
  (`PartyInv.keypair_pos`);
* the updates `EpochTranscript.empty`, `ofKeypair`, `setEnc` and the accessors `key`, `pk`.

The main invariant (`MainInvariant`) uses the transcript to tie together each party's
retained material, the chunks in transit, each receiver's buffer and decoded values, and both
game key tables. KEM correctness enters the proof only through the support memberships
recorded here.
-/
open OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Requester parity of a role: `A` requests at even epochs, `B` at odd ones. -/
def Role.reqParity : Role → ℤ
  | .A => 0
  | .B => 1

/-- Responder parity of a role: `A` responds at odd epochs, `B` at even ones. -/
def Role.resParity : Role → ℤ
  | .A => 1
  | .B => 0

/-- `A` requests at even epochs. -/
@[simp] theorem Role.reqParity_A : Role.A.reqParity = 0 := rfl
/-- `B` requests at odd epochs. -/
@[simp] theorem Role.reqParity_B : Role.B.reqParity = 1 := rfl
/-- `A` responds at odd epochs. -/
@[simp] theorem Role.resParity_A : Role.A.resParity = 1 := rfl
/-- `B` responds at even epochs. -/
@[simp] theorem Role.resParity_B : Role.B.resParity = 0 := rfl
/-- The peer requests at the role's responder parity. -/
@[simp] theorem Role.peer_reqParity (role : Role) : role.peer.reqParity = role.resParity := by
  cases role <;> rfl
/-- The peer responds at the role's requester parity. -/
@[simp] theorem Role.peer_resParity (role : Role) : role.peer.resParity = role.reqParity := by
  cases role <;> rfl
/-- The requester parity as a case split on the role. -/
theorem Role.reqParity_eq_ite (role : Role) :
    role.reqParity = if role = .A then 0 else 1 := by
  cases role <;> rfl
/-- The responder parity as a case split on the role. -/
theorem Role.resParity_eq_ite (role : Role) :
    role.resParity = if role = .A then 1 else 0 := by
  cases role <;> rfl

/-- The samples drawn so far for one epoch: the requester's key pair and the responder's
encapsulation, each with a proof of membership in the support of its sampler. -/
structure EpochTranscript (kem : KEMScheme ProbComp K PK SK C) where
  /-- The requester's key pair, once generated. -/
  keypair : Option (PK × SK)
  /-- The responder's ciphertext and encapsulated key, once encapsulated. -/
  enc : Option (C × K)
  /-- The key pair lies in the support of key generation. -/
  keypair_mem : ∀ pk sk, keypair = some (pk, sk) → (pk, sk) ∈ support kem.keygen
  /-- The encapsulation lies in the support of encapsulation to the epoch's public key. -/
  enc_mem : ∀ pk sk c k, keypair = some (pk, sk) → enc = some (c, k) →
    (c, k) ∈ support (kem.encaps pk)
  /-- Encapsulation requires the key pair. -/
  enc_keypair : enc.isSome = true → keypair.isSome = true

/-- An execution transcript: the epoch transcript of every integer epoch. -/
abbrev Transcript (kem : KEMScheme ProbComp K PK SK C) := ℤ → EpochTranscript kem

namespace EpochTranscript

variable {kem : KEMScheme ProbComp K PK SK C}

/-- The empty epoch transcript. -/
def empty (kem : KEMScheme ProbComp K PK SK C) : EpochTranscript kem where
  keypair := none
  enc := none
  keypair_mem := by simp
  enc_mem := by simp
  enc_keypair := by simp

/-- The epoch transcript of a freshly generated key pair, not yet encapsulated to. -/
def ofKeypair (pk : PK) (sk : SK)
    (hmem : (pk, sk) ∈ support kem.keygen) : EpochTranscript kem where
  keypair := some (pk, sk)
  enc := none
  keypair_mem := by
    intro pk' sk' h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hmem
  enc_mem := by simp
  enc_keypair := by simp

/-- Record an encapsulation `(c, k)` to the epoch's public key `pk`, given that it lies in the
support of `kem.encaps pk`. -/
def setEnc (tr : EpochTranscript kem) (pk : PK) (sk : SK) (c : C) (k : K)
    (hkp : tr.keypair = some (pk, sk)) (hmem : (c, k) ∈ support (kem.encaps pk)) :
    EpochTranscript kem where
  keypair := tr.keypair
  enc := some (c, k)
  keypair_mem := tr.keypair_mem
  enc_mem := by
    intro pk' sk' c' k' hkp' h
    rw [hkp] at hkp'
    simp only [Option.some.injEq, Prod.mk.injEq] at hkp' h
    obtain ⟨rfl, rfl⟩ := hkp'
    obtain ⟨rfl, rfl⟩ := h
    exact hmem
  enc_keypair := by
    intro _
    rw [hkp]
    rfl

/-- The empty epoch transcript has no key pair. -/
@[simp] theorem empty_keypair : (empty kem).keypair = none := rfl
/-- The empty epoch transcript has no encapsulation. -/
@[simp] theorem empty_enc : (empty kem).enc = none := rfl
/-- `ofKeypair pk sk` records the key pair `(pk, sk)`. -/
@[simp] theorem ofKeypair_keypair (pk : PK) (sk : SK) (hmem : (pk, sk) ∈ support kem.keygen) :
    (ofKeypair pk sk hmem : EpochTranscript kem).keypair = some (pk, sk) := rfl
/-- `ofKeypair` records no encapsulation. -/
@[simp] theorem ofKeypair_enc (pk : PK) (sk : SK) (hmem : (pk, sk) ∈ support kem.keygen) :
    (ofKeypair pk sk hmem : EpochTranscript kem).enc = none := rfl
/-- `setEnc` keeps the key pair. -/
@[simp] theorem setEnc_keypair (tr : EpochTranscript kem) (pk sk c k hkp hmem) :
    (tr.setEnc pk sk c k hkp hmem).keypair = tr.keypair := rfl
/-- `setEnc` records the encapsulation `(c, k)`. -/
@[simp] theorem setEnc_enc (tr : EpochTranscript kem) (pk sk c k hkp hmem) :
    (tr.setEnc pk sk c k hkp hmem).enc = some (c, k) := rfl

/-- The epoch key, once encapsulated. -/
def key (tr : EpochTranscript kem) : Option K := tr.enc.map Prod.snd

/-- The epoch's public key, once generated. -/
def pk (tr : EpochTranscript kem) : Option PK := tr.keypair.map Prod.fst

end EpochTranscript

end oppBiKemCKA
