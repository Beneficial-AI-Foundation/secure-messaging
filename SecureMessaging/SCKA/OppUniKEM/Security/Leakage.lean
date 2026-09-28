/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic

/-!
# Epochs exposed by send coins

**Rules.** `sendExposureA s s' r` and `sendExposureB s s' r` specify the
complete exposure sets for returned coins `r`. Key-generation coins expose
A's current epoch; offline, online, or combined encapsulation coins expose
B's current epoch. Deterministic retransmissions expose the empty set.

**Statement.** For each party X, every input state `s`, and every supported
successful leaking-send output with new state `s'` and coins `r`,
`sendExposureX s s' r = leakEpochsX s`.

**Proof.** Case analysis on the local protocol phase computes the exposure
set from `s`. Thus the guard against already challenged epochs has one
value across all successful samples. `Score` uses this fact to transfer
ordinary-send expectation bounds through the leakage marginals.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- A leaking send exposes A's current epoch exactly when it generates
a fresh key pair. Otherwise it only retransmits existing material. -/
def leakEpochsA {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : StA onoff Sym) : Finset ℕ :=
  if s.dkA.isNone then {s.t} else ∅

/-- A leaking send exposes B's current epoch if it runs offline
encapsulation or, after acknowledgement and public-key decoding, online
encapsulation. Sending another chunk of existing material exposes nothing. -/
def leakEpochsB {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : StB onoff Sym) : Finset ℕ :=
  if s.ct0.isNone || (s.ack.ctRec && s.ekA.isSome && s.ct1.isNone && s.stCt.isSome)
  then {s.t} else ∅

/-- Every supported leaking send by A exposes exactly `leakEpochsA s`.
Thus all supported successful samples from `s` have the same exposure guard. -/
theorem sendArleak_exposure
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : kem.OnOffRandLeak onoff)
    (s : StA onoff Sym)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (hout : out ∈ support (sendArleak kem onoff ecEk leak s)) :
    ∀ key msg epoch s' rand, out = some (key, msg, epoch, s', rand) →
      sendExposureA s s' rand =
        leakEpochsA s := by
  cases hdk : s.dkA <;> cases hek : s.ekA <;> cases hack : s.ack.ekRec <;>
    simp only [sendArleak, hdk, hek, hack, Bool.false_eq_true, ↓reduceIte,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Nat.zero_add] at hout
  all_goals
    first
    | obtain rfl := hout
    | obtain ⟨pk, sk, coins, hkp, rfl⟩ := hout
  all_goals
    intro key msg epoch s' rand h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp [sendExposureA, leakEpochsA, hdk]

/-- Every supported leaking send by B exposes exactly `leakEpochsB s`.
This includes offline, online, combined, and deterministic send branches. -/
theorem sendBrleak_exposure
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (s : StB onoff Sym)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (hout : out ∈ support (sendBrleak kem onoff ecCt0 ecCt1 leak s)) :
    ∀ key msg epoch s' rand, out = some (key, msg, epoch, s', rand) →
      sendExposureB s s' rand =
        leakEpochsB s := by
  cases hct0 : s.ct0 <;> cases hek : s.ekA <;>
    cases hct1 : s.ct1 <;> cases hst : s.stCt <;> cases hack : s.ack.ctRec <;>
    simp only [sendBrleak, hct0, hek, hct1, hst, hack, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, mem_support_bind_iff,
      mem_support_pure_iff, Prod.exists, Nat.zero_add] at hout
  all_goals
    first
    | obtain rfl := hout
    | obtain ⟨a, b, r, hs, rfl⟩ := hout
    | obtain ⟨st, ct, roff, hoff, c1, key, ron, hon, rfl⟩ := hout
  all_goals
    intro key msg epoch s' rand h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp [sendExposureB, leakEpochsB, hct0, hek, hct1, hst, hack]

end oppUniKemCKA
