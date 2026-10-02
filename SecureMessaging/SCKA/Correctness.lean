/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import ToVCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Invariants of the SCKA correctness game

If the two send oracles and the two receive oracles of the correctness game preserve a predicate
on the game state, then every query of the game preserves it, since the uniform-randomness oracle
leaves the state unchanged. The known-prefix assertion of those oracles holds whenever every
epoch from `1` to the checked epoch has a key, and recording the key of the next epoch extends
such a prefix.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-- The uniform-randomness oracle preserves every predicate on the game state. -/
theorem oracleUnif_preservesInv (Inv : GameState StA StB I Rho → Prop) :
    QueryImpl.PreservesInv (oracleUnif StA StB I Rho) Inv :=
  fun t => StateT.preservesInv_monadLift ((QueryImpl.ofLift unifSpec ProbComp) t) Inv

/-- If the send and receive oracles preserve `Inv`, then so does every query of the correctness
game. -/
theorem sckaCorrectnessImpl_preservesInv [DecidableEq I]
    {scka : SCKAScheme ProbComp IK StA StB I Rho Rand} {Inv : GameState StA StB I Rho → Prop}
    (hSendA : QueryImpl.PreservesInv (oracleSendA scka) Inv)
    (hSendB : QueryImpl.PreservesInv (oracleSendB scka) Inv)
    (hRecvA : QueryImpl.PreservesInv (oracleRecvA scka) Inv)
    (hRecvB : QueryImpl.PreservesInv (oracleRecvB scka) Inv) :
    QueryImpl.PreservesInv (sckaCorrectnessImpl scka) Inv :=
  ((((oracleUnif_preservesInv Inv).add hSendA).add hSendB).add hRecvA).add hRecvB

/-- The known-prefix assertion up to epoch `n` holds when every epoch from `1` to `n` has a
key. -/
theorem knownPrefix_eq_true {key : ℕ → Option I} {n : ℕ}
    (hkey : ∀ t, 0 < t → t ≤ n → key t ≠ none) :
    (List.range (n + 1)).all (fun t => t = 0 || (key t).isSome) = true := by
  rw [List.all_eq_true]
  intro t ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · simp
  · simpa [Option.isSome_iff_ne_none, hpos.ne'] using
      hkey t hpos (Nat.lt_succ_iff.mp (List.mem_range.mp ht))

/-- If `key` has keys for exactly the epochs from `1` through `c`, then recording a key for epoch
`c + 1` gives keys for exactly the epochs from `1` through `c + 1`. -/
theorem update_succ_ne_none_iff {key : ℕ → Option I} {c : ℕ}
    (hkey : ∀ t, key t ≠ none ↔ 0 < t ∧ t ≤ c) (k : I) (t : ℕ) :
    Function.update key (c + 1) (some k) t ≠ none ↔ 0 < t ∧ t ≤ c + 1 := by
  by_cases ht : t = c + 1
  · subst t
    simp
  · rw [Function.update_of_ne ht, hkey t]
    omega

end SCKAScheme
