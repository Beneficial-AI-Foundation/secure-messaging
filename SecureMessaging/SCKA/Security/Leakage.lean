/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Invariant preservation for leaking sends

**Parameters.** Fix a scheme, party X, send-exposure rule, and predicate
`J : GameState → Prop`.

**Assumptions.** For every local state, forgetting send coins gives the
ordinary send. The ordinary game send preserves `J`. For every game state
`s` and epoch set `E`, `J(s)` implies `J({s with exposed := E})`.

**Conclusion.** For every initial state `s` satisfying `J`, every supported
successor of the guarded leaking game send also satisfies `J`.

**Proof.** Rejection retains `s`. For acceptance, marginal equality places
the coin-free output in the ordinary send's support. Its successor satisfies
`J`, and the exposure update preserves `J` by assumption. Opp-UniKEM uses
these lemmas to transfer its correctness invariants to leaking sends.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- Fix a game state `s` satisfying `Inv`. Assume forgetting A's send coins
recovers its ordinary send, every supported ordinary-send successor from
`s` satisfies `Inv`, and updating exposure preserves `Inv`. Then every
supported guarded leaking-send successor from `s` satisfies `Inv`. -/
theorem oracleSendArleak_preservesInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → StA → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hplain : ∀ z ∈ support ((oracleSendA scka ()).run s), Inv z.2)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka ()).run s)) : Inv z.2 := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none =>
      simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      have hout' : some (key, msg, epoch, state) ∈ support (scka.sendA s.stA) := by
        rw [← hm]
        exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩
      dsimp only at hz
      split at hz
      · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
      · cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          suffices h : Inv { z.2 with exposed := s.exposed } by
            simpa using hbook _ z.2.exposed h
          refine hplain
            (z.1.map (fun (t, ti, msg, _) => (t, ti, msg)),
              { z.2 with exposed := s.exposed }) ?_
          obtain rfl := hz
          simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
            StateT.run_monadLift, monadLift_self, bind_assoc]
          apply (mem_support_bind_iff _ _ _).mpr
          exact ⟨_, hout', by simp⟩

/-- Fix a game state `s` satisfying `Inv`. Assume forgetting B's send coins
recovers its ordinary send, every supported ordinary-send successor from
`s` satisfies `Inv`, and updating exposure preserves `Inv`. Then every
supported guarded leaking-send successor from `s` satisfies `Inv`. -/
theorem oracleSendBrleak_preservesInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → StB → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hplain : ∀ z ∈ support ((oracleSendB scka ()).run s), Inv z.2)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka ()).run s)) : Inv z.2 := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none =>
      simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      have hout' : some (key, msg, epoch, state) ∈ support (scka.sendB s.stB) := by
        rw [← hm]
        exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩
      dsimp only at hz
      split at hz
      · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
      · cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          suffices h : Inv { z.2 with exposed := s.exposed } by
            simpa using hbook _ z.2.exposed h
          refine hplain
            (z.1.map (fun (t, ti, msg, _) => (t, ti, msg)),
              { z.2 with exposed := s.exposed }) ?_
          obtain rfl := hz
          simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
            StateT.run_monadLift, monadLift_self, bind_assoc]
          apply (mem_support_bind_iff _ _ _).mpr
          exact ⟨_, hout', by simp⟩

/-- If forgetting A's leaked coins recovers its ordinary send, then every
ordinary-send invariant preserved by exposure updates is also preserved
by the guarded leaking-send oracle. -/
theorem oracleSendArleak_preservesInv
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → StA → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (hplain : QueryImpl.PreservesInv (oracleSendA scka) Inv) :
    QueryImpl.PreservesInv (oracleSendArleak leak scka) Inv := by
  intro u s hs z hz
  cases u
  exact oracleSendArleak_preservesInv_at scka leak hm Inv hbook s hs
    (hplain () s hs) z hz

/-- If forgetting B's leaked coins recovers its ordinary send, then every
ordinary-send invariant preserved by exposure updates is also preserved
by the guarded leaking-send oracle. -/
theorem oracleSendBrleak_preservesInv
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → StB → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (hplain : QueryImpl.PreservesInv (oracleSendB scka) Inv) :
    QueryImpl.PreservesInv (oracleSendBrleak leak scka) Inv := by
  intro u s hs z hz
  cases u
  exact oracleSendBrleak_preservesInv_at scka leak hm Inv hbook s hs
    (hplain () s hs) z hz

end SCKAScheme
