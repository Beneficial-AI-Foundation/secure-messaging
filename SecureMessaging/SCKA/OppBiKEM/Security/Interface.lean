/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.OppBiKEM.Construction
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Opp-BiKEM — Security interface

This module specializes the SCKA security oracle interface and adversary type to Opp-BiKEM.
`SecuritySendQueryBound adv q` limits the total number of ordinary and leaking sends on every
oracle-response path. The security bounds use this budget to bound both KEM failures and the
number of challengeable epochs.
-/

@[expose] public section

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
-- ANCHOR: SecuritySendQueryBound
def SecuritySendQueryBound
    {kem : KEMScheme ProbComp K PK SK C}
    {leak : kem.RandLeak}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q
-- ANCHOR_END: SecuritySendQueryBound

end oppBiKemCKA
