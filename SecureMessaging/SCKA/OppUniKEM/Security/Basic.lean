/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import SecureMessaging.ErasureCode.Payload
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Opp-UniKEM security interface

Let `kem : KEMScheme ProbComp K PK SK C` be a KEM with on/off structure `onoff`,
leakage witness `leak : kem.OnOffRandLeak onoff`, and erasure-code symbol type `Sym`.

`SecurityAdversary leak Sym` is an adversary against Opp-UniKEM's full SCKA interface.
`SecuritySendQueryBound adv q` bounds the combined number of ordinary and leaking sends
by `q` on every oracle-response path.

For each party and local state, dropping the returned coins from a leaking send gives
its ordinary send as a computation. Every supported successful leaking send exposes
the current epoch when it samples KEM material, and the empty set otherwise.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- Opp-UniKEM's full SCKA oracle interface, with erasure-code symbols `Sym` and
coin types determined by `leak`. -/
abbrev securitySpec {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (leak : kem.OnOffRandLeak onoff) (Sym : Type) :=
  SCKAScheme.sckaSecuritySpec (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.OffRand leak.OnRand)

/-- An adversary against `securitySpec leak Sym`, returning a Boolean guess. -/
abbrev SecurityAdversary {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (leak : kem.OnOffRandLeak onoff) (Sym : Type) :=
  SCKAScheme.SCKAAdversary (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.OffRand leak.OnRand)

/-- `SecuritySendQueryBound adv q` means that every oracle-response path of `adv` makes at most
`q` sends, counting ordinary and leaking sends together (`sckaSecuritySpec.isSendQuery`). Other
queries may occur adaptively in any number and order. -/
-- ANCHOR: securitySendQueryBound
def SecuritySendQueryBound {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} {leak : kem.OnOffRandLeak onoff}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q
-- ANCHOR_END: securitySendQueryBound

section Marginals

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- For every local state `stA`, dropping the returned coins from `sendArleak stA`
gives `sendA stA` as a computation. -/
theorem sendArleak_forget
    (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : kem.OnOffRandLeak onoff)
    (stA : StA onoff Sym) :
    (do
      let out ← sendArleak kem onoff ecEk leak stA
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
      sendA kem onoff ecEk stA := by
  cases hdk : stA.dkA <;>
    simp [sendArleak, sendA, hdk, ← leak.keygen_fst, monad_norm]

/-- For every local state `stB`, dropping the returned coins from `sendBrleak stB`
gives `sendB stB` as a computation. -/
theorem sendBrleak_forget
    (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (stB : StB onoff Sym) :
    (do
      let out ← sendBrleak kem onoff ecCt0 ecCt1 leak stB
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
      sendB kem onoff ecCt0 ecCt1 stB := by
  cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;>
    cases hct1 : stB.ct1 <;> cases hst : stB.stCt <;>
    cases hack : stB.ack.ctRec <;>
    simp [sendBrleak, sendB, hct0, hek, hct1, hst, hack,
      ← leak.encapsOff_fst, ← leak.encapsOn_fst, monad_norm]

end Marginals

/-- The exposure set of A's leaking send: its current epoch when generating a key pair,
and the empty set otherwise. -/
def leakEpochsA {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : StA onoff Sym) : Finset ℕ :=
  if s.dkA.isNone then {s.t} else ∅

/-- The exposure set of B's leaking send: its current epoch when sampling offline or
online encapsulation material, and the empty set otherwise. -/
def leakEpochsB {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : StB onoff Sym) : Finset ℕ :=
  if s.ct0.isNone || (s.ack.ctRec && s.ekA.isSome && s.ct1.isNone && s.stCt.isSome)
  then {s.t} else ∅

/-- Every supported successful leaking send from `s` has exposure set `leakEpochsA s`. -/
theorem sendArleak_exposure
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : kem.OnOffRandLeak onoff)
    (s : StA onoff Sym)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (hout : out ∈ support (sendArleak kem onoff ecEk leak s)) :
    ∀ key msg epoch s' rand, out = some (key, msg, epoch, s', rand) →
      vulnRleakA s rand =
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
    simp [vulnRleakA, leakEpochsA, hdk]

/-- Every supported successful leaking send from `s` has exposure set `leakEpochsB s`. -/
theorem sendBrleak_exposure
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (s : StB onoff Sym)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (hout : out ∈ support (sendBrleak kem onoff ecCt0 ecCt1 leak s)) :
    ∀ key msg epoch s' rand, out = some (key, msg, epoch, s', rand) →
      vulnRleakB s rand =
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
    simp [vulnRleakB, leakEpochsB, hct0, hek, hct1, hst, hack]

end oppUniKemCKA
