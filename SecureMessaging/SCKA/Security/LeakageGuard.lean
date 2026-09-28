/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Leakage
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Deterministic outcomes of fixed leakage guards

Fix an input state `s` and an exposure set `E` shared by all supported
successful outputs of a leaking send. If `E` intersects `s.challenged`,
the oracle returns rejection and retains `s` with probability one. If all
local outputs are successful and the guard accepts, stopping on any epoch
of `E` terminates every supported execution of that query. Both statements
retain all sampling performed before the guard is evaluated.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- For every scheme, state, and common exposure set `E`, if every
successful leaking A-send exposes `E` and `E` intersects `challenged`,
then the guarded query returns `none` and the original state almost surely. -/
theorem oracleSendArleak_rejected_evalDist
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA next coins = E)
    (hguard : E ∩ s.challenged ≠ ∅) :
    𝒟[(oracleSendArleak leak scka ()).run s] = 𝒟[(pure (none, s) : ProbComp _)] := by
  apply evalDist_ext
  intro z
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  apply ToVCVio.probOutput_bind_of_const'
  intro out hout
  cases out with
  | none => rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    dsimp only
    rw [hE key msg epoch next coins hout, if_pos hguard]
    rfl

/-- For every scheme and state, suppose each supported local leaking
A-send succeeds and exposes the same set `E`, disjoint from `challenged`.
Stopping the guarded query on an epoch `e ∈ E` always returns termination. -/
theorem oracleSendArleak_stop_of_exposure
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ) (e : ℕ)
    (hsuccess : none ∉ support (scka.sendArleak s.stA))
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA next coins = E)
    (hguard : E ∩ s.challenged = ∅) (he : e ∈ E)
    (z : Option (Option (ℕ × Option ℕ × Rho × Rand)) × GameState StA StB I Rho)
    (hz : z ∈ support (((stopOnState (oracleSendArleak leak scka)
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) :
    z.1 = none := by
  change z ∈ support (do
    let out ← (oracleSendArleak leak scka ()).run s
    pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc, mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => exact False.elim (hsuccess hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    simp only [hE key msg epoch next coins hout, hguard, ne_eq, not_true_eq_false,
      ↓reduceIte] at hz
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff, exists_eq_left, Finset.mem_union, he, or_true,
        decide_true, ↓reduceIte] at hz
    all_goals obtain rfl := hz; rfl

/-- For every scheme, state, and common exposure set `E`, if every
successful leaking B-send exposes `E` and `E` intersects `challenged`,
then the guarded query returns `none` and the original state almost surely. -/
theorem oracleSendBrleak_rejected_evalDist
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB next coins = E)
    (hguard : E ∩ s.challenged ≠ ∅) :
    𝒟[(oracleSendBrleak leak scka ()).run s] = 𝒟[(pure (none, s) : ProbComp _)] := by
  apply evalDist_ext
  intro z
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  apply ToVCVio.probOutput_bind_of_const'
  intro out hout
  cases out with
  | none => rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    dsimp only
    rw [hE key msg epoch next coins hout, if_pos hguard]
    rfl

/-- For every scheme and state, suppose each supported local leaking
B-send succeeds and exposes the same set `E`, disjoint from `challenged`.
Stopping the guarded query on an epoch `e ∈ E` always returns termination. -/
theorem oracleSendBrleak_stop_of_exposure
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ) (e : ℕ)
    (hsuccess : none ∉ support (scka.sendBrleak s.stB))
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB next coins = E)
    (hguard : E ∩ s.challenged = ∅) (he : e ∈ E)
    (z : Option (Option (ℕ × Option ℕ × Rho × Rand)) × GameState StA StB I Rho)
    (hz : z ∈ support (((stopOnState (oracleSendBrleak leak scka)
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) :
    z.1 = none := by
  change z ∈ support (do
    let out ← (oracleSendBrleak leak scka ()).run s
    pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc, mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => exact False.elim (hsuccess hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    simp only [hE key msg epoch next coins hout, hguard, ne_eq, not_true_eq_false,
      ↓reduceIte] at hz
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff, exists_eq_left, Finset.mem_union, he, or_true,
        decide_true, ↓reduceIte] at hz
    all_goals obtain rfl := hz; rfl

end SCKAScheme
