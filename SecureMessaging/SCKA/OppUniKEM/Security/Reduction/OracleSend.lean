/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Send
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SendShape

/-!
# Send oracles under marked game states

**Statements.** For a selected epoch `e`, pinned material `m`, and honest
game state `s`, marking commutes with A's ordinary send oracle. It also
commutes with B's ordinary send oracle when `s` satisfies `reachableInv`.
The equality concerns the joint distribution of the public response and
the complete successor game state.

**Proof.** Apply the local send relations and compare the game's updates.
Marking preserves key availability, message tables, and epoch counters.
A derives no key. When B derives a key, transcript consistency gives an
empty counterpart entry, so the consistency assertion agrees in both games.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

set_option backward.dsimp.instances true in
/-- For every selected epoch, material value, and honest state, A's
symbolic send oracle has the same response/state distribution as the
honest pinned send oracle followed by marking its successor. -/
theorem oracleSendA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(SCKAScheme.oracleSendA
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ()).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      (SCKAScheme.oracleSendA (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s] := by
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind]
  dsimp only [symbolicScheme, honestScheme, scheme, markState]
  rw [sendA_mark base onoff ecEk leak m e (decide (s.stB.t = e))
    ((s.keyB s.stA.t).map (mark e s.stA.t)) (s.keyB s.stA.t) s.stA]
  simp only [bind_map_left, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none => simp [StateT.run_pure, markState, markA, markB, Prod.map]
  | some out =>
    rcases out with ⟨key, msg, t, next⟩
    have hk := sendA_key_none
      (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
      (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
      ecEk s.stA key msg t next hout
    subst key
    simp [StateT.run_set, markState, markA, markB, Prod.map]

set_option backward.dsimp.instances true in
/-- For every transcript-consistent state `s`, B's symbolic send oracle
has the same response/state distribution as its honest pinned send oracle
followed by marking. The transcript supplies the empty counterpart entry
for every newly recorded key. -/
theorem oracleSendB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) :
    𝒟[(SCKAScheme.oracleSendB
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ()).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      (SCKAScheme.oracleSendB (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s] := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind]
  dsimp only [symbolicScheme, honestScheme, scheme, markState]
  rw [sendB_mark base onoff ecCt0 ecCt1 leak m e (decide (s.stA.t = e))
    ((s.keyB s.stA.t).map (mark e s.stA.t)) (s.keyB s.stA.t) s.stB]
  simp only [bind_map_left, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none => simp [StateT.run_pure, markState, markA, markB, Prod.map]
  | some out =>
    rcases out with ⟨key, msg, t, next⟩
    cases key with
    | none => simp [StateT.run_set, markState, markA, markB, Prod.map]
    | some key =>
      rcases key with ⟨epoch, k⟩
      obtain ⟨rfl, hc⟩ := sendB_key_fresh
        (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB epoch k msg t next hout
      have hk := (keys_none_before_online base onoff ecEk ecCt0 ecCt1 s hs hc).1
      simp [StateT.run_set, markState, markA, markB,
        Prod.map, hk, ← mark_update]

end oppUniKemCKA.Security.Embedding
