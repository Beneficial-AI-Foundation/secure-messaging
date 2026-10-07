/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Oracles
import SecureMessaging.SCKA.Security.CorrectnessOracles
import SecureMessaging.SCKA.Security.Transport

/-!
# Preservation by the security oracle family

Let:

- `scka : SCKAScheme ProbComp IK StA StB I Rho Rand` be a scheme;
- `vulnA`, `vulnB` be its game exposure policies;
- `base` implement `sckaCorrectnessSpec Rho` on `GameState StA StB I Rho`;
- `chall` implement `ℕ →ₒ Option I` on the same state space.

Let `F := securityImplOf base chall vulnA vulnB scka`. The security game uses
`base := sckaCorrectnessImpl scka` and `chall := challOf (fun _ => b)` for a fixed bit `b`.

An invariant insensitive to `exposed` and `challenged` is preserved by `F` as soon as `base`
and the two ordinary sends preserve it, provided the leaking sends are forgetful and `chall`
satisfies `RecordsChallenges`. Under the same hypotheses, no query of `F` removes an exposed
epoch, and A's send-counter bound for `base` extends to `F`, counting all four security send
queries.

Equality of the `base` and challenge queries at a state also gives equality of the full
security-family queries at that state.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]
variable (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
variable (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
variable (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
variable (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)

/-- If every component query from `s` has only successors satisfying `Inv`, so does every
query of `F` from `s`. -/
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

/-- Let `Inv` hold at `s` and be preserved by arbitrary updates to `exposed` and `challenged`.
If forgetting send coins recovers ordinary sends and `chall` records challenges, preservation
of `Inv` by `base` and ordinary sends from `s` implies preservation by `F` from `s`. -/
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

/-- If forgetting send coins recovers ordinary sends and `chall` records challenges, `F`
preserves every invariant preserved by `base`, ordinary sends, and arbitrary updates to
`exposed` and `challenged`. -/
theorem securityImplOf_preservesInv_of_book (Inv : GameState StA StB I Rho → Prop)
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
    (hbase : QueryImpl.PreservesInv base Inv)
    (hsendA : QueryImpl.PreservesInv (oracleSendA scka) Inv)
    (hsendB : QueryImpl.PreservesInv (oracleSendB scka) Inv) :
    QueryImpl.PreservesInv (securityImplOf base chall vulnA vulnB scka) Inv :=
  fun t s hs z hz => securityImplOf_preserves_at_of_book base chall vulnA vulnB scka Inv
    hbook hmA hmB hchall s hs (fun t => hbase t s hs) (hsendA () s hs) (hsendB () s hs) t z hz

/-- If `base` keeps the exposed set and `chall` records challenges, no query of `F` removes an
exposed epoch. -/
theorem securityImplOf_exposed_subset
    (hbase : ∀ t s z, z ∈ support ((base t).run s) → z.2.exposed = s.exposed)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    s.exposed ⊆ z.2.exposed := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [hbase t s z hz]
  · exact oracleSendArleak_exposed_subset vulnA.rleak scka u s z hz
  · exact oracleSendBrleak_exposed_subset vulnB.rleak scka u s z hz
  · rw [(hchall.exposed_nA_eq t s z hz).1]
  · exact oracleCorruptA_exposed_subset vulnA.corrupt u s z hz
  · exact oracleCorruptB_exposed_subset vulnB.corrupt u s z hz

/-- Assume `chall` records challenges and `base` increases A's send counter by at most one
on send queries and does not increase it otherwise. Then `F` satisfies the same bound,
counting all four security send queries. -/
theorem securityImplOf_nA_step
    (hbase : ∀ t s z, z ∈ support ((base t).run s) →
      z.2.nA ≤ s.nA + if isSendQuery t then 1 else 0)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    z.2.nA ≤ s.nA + if sckaSecuritySpec.isSendQuery t then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [sckaSecuritySpec.isSendQuery_OCorrectness]
    exact hbase t s z hz
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using oracleSendArleak_nA_le vulnA.rleak scka () s z hz
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleSendBrleak_nA_eq vulnB.rleak scka () s z hz).le.trans (Nat.le_succ _)
  · simpa [sckaSecuritySpec.isSendQuery] using (hchall.exposed_nA_eq t s z hz).2.le
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleCorruptA_challenged_nA_eq vulnA.corrupt () s z hz).2.le
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleCorruptB_challenged_nA_eq vulnB.corrupt () s z hz).2.le

/-- Two instances of the family with equal `base` queries and equal challenge queries from `s`
have equal queries from `s`. -/
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
