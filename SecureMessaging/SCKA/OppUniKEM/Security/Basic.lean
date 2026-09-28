/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import SecureMessaging.ErasureCode.Payload
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Opp-UniKEM query bound and send-projection lemmas

This file supplies the following definitions and lemmas for the security reduction.

* `securitySpec` and `SecurityAdversary` are type abbreviations for the existing
  `SCKAScheme.sckaSecuritySpec` and `SCKAScheme.SCKAAdversary`, specialized to
  Opp-UniKEM's state, message, key, and send-coin types.

* `SecuritySendQueryBound A q` requires at most `q` calls to `SendA`, `SendB`,
  `SendArleak`, and `SendBrleak` combined, on every response path of `A`.
  All other oracle calls have zero cost in this bound.

* `sendArleak_forget` and `sendBrleak_forget` prove
  `π <$> SendXrleak(s) = SendX(s)` for `X ∈ {A, B}`, where `π` removes only
  the returned coins and preserves the optional key, message, epoch, and
  next local state. The assumptions are the marginal laws in `OnOffRandLeak`.

The projection equalities concern the protocol's send algorithms. The
leaking-send game oracles additionally enforce exposure guards; invariant
preservation through those guards is proved in `SecureMessaging.SCKA.Security.Leakage`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- Type abbreviation for `SCKAScheme.sckaSecuritySpec` specialized to
Opp-UniKEM. `leak` determines the key-generation, offline, and online coin
types, and `Sym` is the erasure-code symbol type. -/
abbrev securitySpec {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (leak : kem.OnOffRandLeak onoff) (Sym : Type) :=
  SCKAScheme.sckaSecuritySpec (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.OffRand leak.OnRand)

/-- Type abbreviation for `SCKAScheme.SCKAAdversary` specialized to
Opp-UniKEM's oracle responses, with coin types determined by `leak` and
erasure-code symbol type `Sym`. The adversary returns a Boolean guess. -/
abbrev SecurityAdversary {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (leak : kem.OnOffRandLeak onoff) (Sym : Type) :=
  SCKAScheme.SCKAAdversary (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.OffRand leak.OnRand)

/-- Query-cost predicate: `true` precisely for `SendA`, `SendB`, `SendArleak`,
and `SendBrleak`. The `Unit` response parameters are immaterial because the
SCKA query domain is independent of its response types. -/
def isSecuritySendQuery :
    (SCKAScheme.sckaSecuritySpec Unit Unit Unit Unit Unit).Domain → Bool
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ())))))))) => true
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ()))))))) => true
  | .inl (.inl (.inl (.inl (.inr ())))) => true
  | .inl (.inl (.inl (.inr ()))) => true
  | _ => false

/-- `SecuritySendQueryBound A q` means that every oracle-response path of
`A` makes at most `q` sends, counting ordinary and leaking sends together.
Other queries may occur adaptively in any number and order. -/
-- ANCHOR: securitySendQueryBound
def SecuritySendQueryBound {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} {leak : kem.OnOffRandLeak onoff}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP (fun t => isSecuritySendQuery t = true) q
-- ANCHOR_END: securitySendQueryBound

section Marginals

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- For every local state `stA`, projecting out the coins from
`sendArleak stA` gives `sendA stA` as a monadic computation. The projection
retains the optional key, message, epoch, and successor state. -/
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

/-- For every local state `stB`, projecting out the coins from
`sendBrleak stB` gives `sendB stB` as a monadic computation. The equality
covers offline, online, combined, and deterministic send branches. -/
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

end oppUniKemCKA
