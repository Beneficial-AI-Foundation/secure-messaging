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

**Definitions.**

- `securitySpec leak Sym`: the SCKA security oracle interface of Opp-UniKEM, with erasure-code
  symbols `Sym` and send coins determined by the leakage witness `leak`;
  `SecurityAdversary leak Sym` is a Boolean adversary against it.
- `SecuritySendQueryBound adv q`: on every oracle-response path, `adv` makes at most `q` ordinary
  and leaking sends in total.
- `leakEpochsA s`, `leakEpochsB s`: the epochs exposed by a successful leaking send from the
  local state `s`, as a function of `s` alone.

**Results.**

- `sendArleak_forget`, `sendBrleak_forget`: discarding the coins returned by a leaking send gives
  the ordinary send, as computations.
- `sendArleak_exposure`, `sendBrleak_exposure`: for every possible successful output of a leaking
  send from `s` with coins `rand`, the exposure policy gives `vulnRleakA s rand = leakEpochsA s`
  (respectively `vulnRleakB s rand = leakEpochsB s`).
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
  cases hct0 : stB.ct0 <;> cases hack : stB.ack.ctRec
  all_goals first
    | simp [sendBrleak, sendB, hct0, hack, ← leak.encapsOff_fst, monad_norm]; done
    | (cases hek : stB.ekA
       · simp [sendBrleak, sendB, hct0, hek, hack, ← leak.encapsOff_fst, monad_norm]
       · cases hct1 : stB.ct1
         · cases hst : stB.stCt <;>
             simp [sendBrleak, sendB, hct0, hek, hct1, hst, hack,
               ← leak.encapsOff_fst, ← leak.encapsOn_fst, monad_norm]
         · simp [sendBrleak, sendB, hct0, hek, hct1, hack, ← leak.encapsOff_fst, monad_norm])

/-- For every local state `stA`, `sendA stA` is the image of `sendArleak stA` under discarding
the returned coins. -/
theorem sendA_eq_map_sendArleak
    (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : kem.OnOffRandLeak onoff)
    (stA : StA onoff Sym) :
    sendA kem onoff ecEk stA =
      (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state)) <$>
        sendArleak kem onoff ecEk leak stA := by
  rw [← sendArleak_forget kem onoff ecEk leak stA, map_eq_bind_pure_comp]
  rfl

/-- The version of `sendA_eq_map_sendArleak` for B. -/
theorem sendB_eq_map_sendBrleak
    (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (stB : StB onoff Sym) :
    sendB kem onoff ecCt0 ecCt1 stB =
      (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state)) <$>
        sendBrleak kem onoff ecCt0 ecCt1 leak stB := by
  rw [← sendBrleak_forget kem onoff ecCt0 ecCt1 leak stB, map_eq_bind_pure_comp]
  rfl

/-- `sendA_eq_map_sendArleak` for the fields `sendA` and `sendArleak` of `scheme`. -/
theorem scheme_sendA_eq_map_sendArleak [DecidableEq Sym]
    (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (stA : StA onoff Sym) :
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak).sendA stA =
      (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state)) <$>
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak).sendArleak stA :=
  sendA_eq_map_sendArleak kem onoff ecEk leak stA

/-- `sendB_eq_map_sendBrleak` for the fields `sendB` and `sendBrleak` of `scheme`. -/
theorem scheme_sendB_eq_map_sendBrleak [DecidableEq Sym]
    (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (stB : StB onoff Sym) :
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak).sendB stB =
      (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state)) <$>
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak).sendBrleak stB :=
  sendB_eq_map_sendBrleak kem onoff ecCt0 ecCt1 leak stB

end Marginals

/-- The epochs exposed by a successful leaking send of A from `s`: `{s.t}` if A generates a key
pair (`s.dkA = none`), and `∅` otherwise. -/
def leakEpochsA {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : StA onoff Sym) : Finset ℕ :=
  if s.dkA.isNone then {s.t} else ∅

/-- The epochs exposed by a successful leaking send of B from `s`: `{s.t}` if B runs offline or
online encapsulation, and `∅` otherwise. -/
def leakEpochsB {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : StB onoff Sym) : Finset ℕ :=
  if s.ct0.isNone || (s.ack.ctRec && s.ekA.isSome && s.ct1.isNone && s.stCt.isSome)
  then {s.t} else ∅

/-- For every possible successful output of A's leaking send from `s`, its returned coins
`rand` satisfy `vulnRleakA s rand = leakEpochsA s`. -/
theorem sendArleak_exposure
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : kem.OnOffRandLeak onoff)
    (s : StA onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (epoch : ℕ) (s' : StA onoff Sym)
    (rand : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, epoch, s', rand) ∈ support (sendArleak kem onoff ecEk leak s)) :
    vulnRleakA s rand = leakEpochsA s := by
  generalize houtEq : some (key, msg, epoch, s', rand) = out at hout
  cases hdk : s.dkA <;> cases hek : s.ekA <;> cases hack : s.ack.ekRec <;>
    simp only [sendArleak, hdk, hek, hack, Bool.false_eq_true, ↓reduceIte,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Nat.zero_add] at hout
  all_goals
    first
    | obtain rfl := hout
    | obtain ⟨pk, sk, coins, hkp, rfl⟩ := hout
  all_goals
    simp only [Option.some.injEq, Prod.mk.injEq] at houtEq
    rcases houtEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp [vulnRleakA, leakEpochsA, hdk]

/-- The version of `sendArleak_exposure` for B: `vulnRleakB s rand = leakEpochsB s`. -/
theorem sendBrleak_exposure
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (s : StB onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (epoch : ℕ) (s' : StB onoff Sym)
    (rand : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, epoch, s', rand) ∈
      support (sendBrleak kem onoff ecCt0 ecCt1 leak s)) :
    vulnRleakB s rand = leakEpochsB s := by
  generalize houtEq : some (key, msg, epoch, s', rand) = out at hout
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
    simp only [Option.some.injEq, Prod.mk.injEq] at houtEq
    rcases houtEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp [vulnRleakB, leakEpochsB, hct0, hek, hct1, hst, hack]

end oppUniKemCKA
