/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Averaging send algorithms through the game oracle

**Parameters.** Fix a sampler `sample`, scheme family `F`, target scheme
`T`, and game state `s`, with common state, key, message, and coin types.

**Statement.** If sampling `a` and running `F(a)`'s local send from `s`
has the same output distribution as `T`'s local send, then the corresponding
game sends have the same joint response/state distribution. For leaking
sends, both games use the same send-exposure function.

**Proof.** Move the outer sample into the local-send computation. The
remaining game bookkeeping is a shared continuation, including message and
key recording, correctness checks, and the leaking-send exposure guard.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand τ : Type} [DecidableEq I]

/-- For every sampler, scheme family, target scheme, and input state,
equality of the averaged local A-send distribution implies equality of
the averaged A-send game oracle's response/state distribution. -/
theorem oracleSendA_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : 𝒟[(do let a ← sample; (family a).sendA s.stA)] = 𝒟[target.sendA s.stA]) :
    𝒟[(do let a ← sample; (oracleSendA (family a) ()).run s)] =
      𝒟[(oracleSendA target ()).run s] := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc, evalDist_bind, h, ← evalDist_bind]

/-- For every sampler, scheme family, target scheme, and input state,
equality of the averaged local B-send distribution implies equality of
the averaged B-send game oracle's response/state distribution. -/
theorem oracleSendB_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : 𝒟[(do let a ← sample; (family a).sendB s.stB)] = 𝒟[target.sendB s.stB]) :
    𝒟[(do let a ← sample; (oracleSendB (family a) ()).run s)] =
      𝒟[(oracleSendB target ()).run s] := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc, evalDist_bind, h, ← evalDist_bind]

/-- For every sampler, scheme family, target scheme, state, and common
A-send exposure rule, equality of averaged local leaking-send distributions
implies equality of their guarded game response/state distributions. -/
theorem oracleSendArleak_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → StA → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (h : 𝒟[(do let a ← sample; (family a).sendArleak s.stA)] =
      𝒟[target.sendArleak s.stA]) :
    𝒟[(do let a ← sample; (oracleSendArleak leak (family a) ()).run s)] =
      𝒟[(oracleSendArleak leak target ()).run s] := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc, evalDist_bind, h, ← evalDist_bind]

/-- For every sampler, scheme family, target scheme, state, and common
B-send exposure rule, equality of averaged local leaking-send distributions
implies equality of their guarded game response/state distributions. -/
theorem oracleSendBrleak_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → StB → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (h : 𝒟[(do let a ← sample; (family a).sendBrleak s.stB)] =
      𝒟[target.sendBrleak s.stB]) :
    𝒟[(do let a ← sample; (oracleSendBrleak leak (family a) ()).run s)] =
      𝒟[(oracleSendBrleak leak target ()).run s] := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc, evalDist_bind, h, ← evalDist_bind]

end SCKAScheme
