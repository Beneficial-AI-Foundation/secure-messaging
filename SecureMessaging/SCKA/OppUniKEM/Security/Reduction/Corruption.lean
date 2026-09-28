/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Corruption responses under marked states

**Statement.** Fix a selected epoch `e` and an honest game state `s` with
`e ∉ s.exposed`. For either party, performing corruption in the marked
state and revealing its response equals performing honest corruption,
stopping if its successor exposes `e`, and marking that successor.

**Proof.** Marking preserves the vulnerable-epoch set and therefore the
corruption guard. A rejected corruption returns `none` and retains the
state. An accepted corruption terminates exactly when the returned state
contains unavailable selected-epoch material. Erased material is returned
successfully. These equalities establish both corruption cases of the
selected-epoch simulation relation.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

set_option backward.dsimp.instances true in
/-- For every selected epoch `e` and state `s` with `e ∉ s.exposed`,
A's marked corruption followed by revelation equals honest corruption
stopped on exposure of `e`, with the successor state marked. -/
theorem corruptA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (e : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) :
    ((revealAfter (revealResponse (revealA (onoff := onoff)))
      (SCKAScheme.oracleCorruptA
        (fun u => if u.dkA.isSome then {u.t} else ∅)
        (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym)
        (Option K) (Message Sym) ())).run).run (markState e s) =
      Prod.map id (markState e) <$>
        ((stopOnState (SCKAScheme.oracleCorruptA (vulnA base onoff)
          (StB onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleCorruptA (vulnA base onoff)
      (StB onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))
  have hv := markA_vulnerable e s.stA
  by_cases hg : vulnA base onoff s.stA ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptA, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [markState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealResponse, revealA_markA_eq, markState, Prod.map]
  all_goals by_cases he : e ∈ vulnA base onoff s.stA <;> simp [he]


set_option backward.dsimp.instances true in
/-- For every selected epoch `e` and state `s` with `e ∉ s.exposed`,
B's marked corruption followed by revelation equals honest corruption
stopped on exposure of `e`, with the successor state marked. -/
theorem corruptB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (e : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) :
    ((revealAfter (revealResponse (revealB (onoff := onoff)))
      (SCKAScheme.oracleCorruptB
        (fun u => if u.stCt.isSome then {u.t} else ∅)
        (StateA (Option SK) PK onoff.C₀ Sym)
        (Option K) (Message Sym) ())).run).run (markState e s) =
      Prod.map id (markState e) <$>
        ((stopOnState (SCKAScheme.oracleCorruptB (vulnB base onoff)
          (StA onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleCorruptB (vulnB base onoff)
      (StA onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))
  have hv := markB_vulnerable e s.stB
  by_cases hg : vulnB base onoff s.stB ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptB, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [markState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealResponse, revealB_markB_eq, markState, Prod.map]
  all_goals by_cases he : e ∈ vulnB base onoff s.stB <;> simp [he]


end oppUniKemCKA.Security.Embedding
