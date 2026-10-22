/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction
import SecureMessaging.ErasureCode.Payload
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Opp-BiKEM security interface

This module specializes the full SCKA oracle interface and its send-query bound to Opp-BiKEM.
Discarding the coins returned by the shared leaking-send engine gives the ordinary send
computation, for either role and every local state.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Opp-BiKEM's full SCKA oracle interface, with erasure-code symbols `Sym` and
coin types determined by `leak`. -/
abbrev securitySpec
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : kem.RandLeak) (Sym : Type) :=
  SCKAScheme.sckaSecuritySpec
    (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.EncapsRand)

/-- An adversary against `securitySpec leak Sym`, returning a Boolean guess. -/
abbrev SecurityAdversary
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : kem.RandLeak) (Sym : Type) :=
  SCKAScheme.SCKAAdversary
    (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.EncapsRand)

/-- Every oracle-response path of `adv` makes at most `q` ordinary or leaking sends in total.
Other queries may occur adaptively in any number and order. -/
def SecuritySendQueryBound
    {kem : KEMScheme ProbComp K PK SK C}
    {leak : kem.RandLeak}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q

/-- For either role and every local state, dropping the returned coins from the leaking-send
engine gives the ordinary send computation, including effects preceding a failed send. -/
theorem sendWith_rleak_forget
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (kem : KEMScheme m K PK SK C)
    (role : Role)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (st : State PK SK C Sym) :
    (do
      let out ←
        sendWith role leak.keygenRleak leak.encapsRleak ecEk ecCt st
      pure (out.map fun (key, msg, epoch, state, _) =>
        (key, msg, epoch, state))) =
      send role kem ecEk ecCt st := by
  simp only [send, sendWith, ← leak.keygen_fst, ← leak.encaps_fst, bind_assoc, pure_bind]
  split
  · simp only [bind_assoc]
    refine bind_congr fun _ => ?_
    split_ifs <;> (try split) <;> simp
  · split_ifs <;> (try split) <;> simp

end oppBiKemCKA
