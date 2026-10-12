/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Oracles
import SecureMessaging.SCKA.Security.Transport

/-!
# Properties of assembled security oracles

Let `scka : SCKAScheme ProbComp IK StA StB I Rho Rand` be a scheme with exposure functions
`vulnA` and `vulnB`. Let `base` implement uniform-randomness, ordinary-send, and receive
queries, and let `chall` implement challenge queries, all on `GameState StA StB I Rho`.
`securityImplOf base chall vulnA vulnB scka` combines these oracles with the scheme's
leaking-send and corruption oracles.

Suppose discarding the returned send coins recovers each ordinary-send computation, and
`chall` satisfies `RecordsChallenges`: it retains the state or inserts the queried, unexposed epoch
into `challenged`. Then every invariant preserved by `base`, ordinary sends, and arbitrary
changes to `exposed` and `challenged` is preserved by the assembled security oracles.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- Assemble the security oracles for a proof game. `base` supplies uniform sampling,
ordinary sends, and receives; `chall` supplies challenges. Leaking sends and corruptions
use the given scheme and exposure functions. -/
def securityImplOf
    (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
    (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  base
    + oracleSendArleak vulnA.rleak scka + oracleSendBrleak vulnB.rleak scka
    + chall
    + oracleCorruptA vulnA.corrupt StB I Rho + oracleCorruptB vulnB.corrupt StA I Rho

variable (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
variable (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
variable (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
variable (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)

/-- If each component query from `s` produces only states satisfying `Inv`, then every
assembled security query from `s` does too. -/
theorem securityImplOf_preserves_at (Inv : GameState StA StB I Rho → Prop)
    (s : GameState StA StB I Rho)
    (hbase : ∀ t z, z ∈ support ((base t).run s) → Inv z.2)
    (hA : ∀ z ∈ support ((oracleSendArleak vulnA.rleak scka ()).run s), Inv z.2)
    (hB : ∀ z ∈ support ((oracleSendBrleak vulnB.rleak scka ()).run s), Inv z.2)
    (hC : ∀ (t : ℕ) z, z ∈ support ((chall t).run s) → Inv z.2)
    (hcA : ∀ z ∈ support ((oracleCorruptA vulnA.corrupt StB I Rho ()).run s), Inv z.2)
    (hcB : ∀ z ∈ support ((oracleCorruptB vulnB.corrupt StA I Rho ()).run s), Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact hbase t z hz
  · cases u; exact hA z hz
  · cases u; exact hB z hz
  · exact hC t z hz
  · cases u; exact hcA z hz
  · cases u; exact hcB z hz

/-- Suppose discarding send coins recovers ordinary sends and `chall` satisfies
`RecordsChallenges`. Let `Inv` hold at `s` and be preserved by arbitrary changes to `exposed`
and `challenged`. If `base` and both ordinary-send oracles produce only states satisfying
`Inv` from `s`, then every assembled security query from `s` does too. -/
theorem securityImplOf_preserves_at_of_book (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (hmB : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (hchall : RecordsChallenges chall)
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hbase : ∀ t z, z ∈ support ((base t).run s) → Inv z.2)
    (hsendA : ∀ z ∈ support ((oracleSendA scka ()).run s), Inv z.2)
    (hsendB : ∀ z ∈ support ((oracleSendB scka ()).run s), Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  have hexp : ∀ s exposed, Inv s → Inv { s with exposed := exposed } :=
    fun s exposed h => by simpa using hbook s exposed s.challenged h
  have hch : ∀ s challenged, Inv s → Inv { s with challenged := challenged } :=
    fun s challenged h => by simpa using hbook s s.exposed challenged h
  refine securityImplOf_preserves_at base chall vulnA vulnB scka Inv s hbase
    (fun z hz => oracleSendArleak_preservesInv_at scka vulnA.rleak hmA Inv hexp s hs hsendA z hz)
    (fun z hz => oracleSendBrleak_preservesInv_at scka vulnB.rleak hmB Inv hexp s hs hsendB z hz)
    (fun t z hz => hchall.preservesInv Inv hch t s hs z hz)
    (fun z hz => oracleCorruptA_preservesInv vulnA.corrupt Inv hexp () s hs z hz)
    (fun z hz => oracleCorruptB_preservesInv vulnB.corrupt Inv hexp () s hs z hz) t z hz

/-- If `base` and `base'` have equal query computations from `s`, and so do `chall` and
`chall'`, the two assembled security implementations have equal query computations from `s`. -/
theorem securityImplOf_run_eq
    (base' : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
    (chall' : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
    (s : GameState StA StB I Rho)
    (hbase : ∀ t, (base t).run s = (base' t).run s)
    (hchall : ∀ t : ℕ, (chall t).run s = (chall' t).run s)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) :
    (securityImplOf base chall vulnA vulnB scka t).run s =
      (securityImplOf base' chall' vulnA vulnB scka t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact hbase t
  · rfl
  · rfl
  · exact hchall t
  · rfl
  · rfl

end SCKAScheme
