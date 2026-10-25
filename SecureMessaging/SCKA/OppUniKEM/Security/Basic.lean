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

**Main results.** The SCKA security interface of Opp-UniKEM admits Boolean adversaries
(`securitySpec`, `SecurityAdversary`), whose *send budget* `q` bounds the ordinary and leaking sends
on every response path (`SecuritySendQueryBound adv q`).

- A leaking send without its coins is the ordinary send (`sendArleak_forget`, `sendBrleak_forget`).
- The epochs exposed by a successful leaking send from `s` depend on `s` alone: `{s.t}` if the send
  samples, else `∅` (`leakEpochsA`, `leakEpochsB`, `sendArleak_exposure`, `sendBrleak_exposure`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- The game state of Opp-UniKEM's SCKA games over `onoff` with symbol type `Sym`:
`SCKAScheme.GameState` with party states `StA onoff Sym` and `StB onoff Sym`, keys in `K`, and
messages in `Message Sym`. -/
abbrev GameState {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure) (Sym : Type) :=
  SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)

/-- Opp-UniKEM's SCKA security interface; the coin types come from `leak`. -/
abbrev securitySpec {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (leak : kem.OnOffRandLeak onoff) (Sym : Type) :=
  SCKAScheme.sckaSecuritySpec (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.OffRand leak.OnRand)

/-- A Boolean adversary against `securitySpec leak Sym`. -/
abbrev SecurityAdversary {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (leak : kem.OnOffRandLeak onoff) (Sym : Type) :=
  SCKAScheme.SCKAAdversary (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.OffRand leak.OnRand)

/-- Every response path of `adv` makes at most `q` ordinary or leaking sends (`isSendQuery`). -/
-- ANCHOR: securitySendQueryBound
def SecuritySendQueryBound {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} {leak : kem.OnOffRandLeak onoff}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q
-- ANCHOR_END: securitySendQueryBound

section Marginals

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Discarding the coins of `sendArleak stA` gives `sendA stA`, as computations. -/
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

/-- B version of `sendArleak_forget`. -/
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

/-- `sendA stA` is the image of `sendArleak stA` under discarding the coins. -/
theorem sendA_eq_map_sendArleak
    (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : kem.OnOffRandLeak onoff)
    (stA : StA onoff Sym) :
    sendA kem onoff ecEk stA =
      (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state)) <$>
        sendArleak kem onoff ecEk leak stA := by
  rw [← sendArleak_forget kem onoff ecEk leak stA, map_eq_bind_pure_comp]
  rfl

/-- B version of `sendA_eq_map_sendArleak`. -/
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

/-- `sendA_eq_map_sendArleak` for the fields of `scheme`. -/
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

/-- `sendB_eq_map_sendBrleak` for the fields of `scheme`. -/
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

variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

/-- Epochs exposed by A's successful leaking send from `stA`: `{stA.t}` if A generates a key pair
(`stA.dkA = none`), else `∅`. -/
def leakEpochsA {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (stA : StA onoff Sym) : Finset ℕ :=
  if stA.dkA.isNone then {stA.t} else ∅

/-- Epochs exposed by B's successful leaking send from `stB`: `{stB.t}` if B runs offline or
online encapsulation, else `∅`. -/
def leakEpochsB {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (stB : StB onoff Sym) : Finset ℕ :=
  if stB.ct0.isNone || (stB.ack.ctRec && stB.ekA.isSome && stB.ct1.isNone && stB.stCt.isSome)
  then {stB.t} else ∅

/-- Every possible successful output of `sendArleak stA` with coins `rand` has
`vulnRleakA stA rand = leakEpochsA stA`. -/
theorem sendArleak_exposure
    (stA : StA onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (epoch : ℕ) (stA' : StA onoff Sym)
    (rand : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, epoch, stA', rand) ∈ support (sendArleak kem onoff ecEk leak stA)) :
    vulnRleakA stA rand = leakEpochsA stA := by
  generalize houtEq : some (key, msg, epoch, stA', rand) = out at hout
  cases hdk : stA.dkA <;> cases hek : stA.ekA <;> cases hack : stA.ack.ekRec <;>
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

/-- B version of `sendArleak_exposure`: `vulnRleakB stB rand = leakEpochsB stB`. -/
theorem sendBrleak_exposure
    (stB : StB onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (epoch : ℕ) (stB' : StB onoff Sym)
    (rand : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, epoch, stB', rand) ∈
      support (sendBrleak kem onoff ecCt0 ecCt1 leak stB)) :
    vulnRleakB stB rand = leakEpochsB stB := by
  generalize houtEq : some (key, msg, epoch, stB', rand) = out at hout
  cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;>
    cases hct1 : stB.ct1 <;> cases hst : stB.stCt <;> cases hack : stB.ack.ctRec <;>
    simp only [sendBrleak, hct0, hek, hct1, hst, hack, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, mem_support_bind_iff,
      mem_support_pure_iff, Prod.exists, Nat.zero_add] at hout
  all_goals
    first
    | obtain rfl := hout
    | obtain ⟨a, b, r, hstB, rfl⟩ := hout
    | obtain ⟨st, ct, roff, hoff, c1, key, ron, hon, rfl⟩ := hout
  all_goals
    simp only [Option.some.injEq, Prod.mk.injEq] at houtEq
    rcases houtEq with ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp [vulnRleakB, leakEpochsB, hct0, hek, hct1, hst, hack]

end oppUniKemCKA
