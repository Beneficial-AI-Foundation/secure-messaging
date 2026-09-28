/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OracleSend

/-!
# Leaking-send guards under marked states

**Statement.** Fix selected epoch `e`, material value `m`, and a game
state `s` with `e ∉ s.exposed`. A symbolic leaking send followed by coin
revelation has the same joint distribution as its honest pinned send,
stopped if it exposes `e`, followed by state marking. For B, assume also
`reachableInv s` to justify the new-key consistency check.

**Proof.** Coin marking preserves the sampling-phase constructor and hence
the exposure guard. Rejected sends retain the original state. Accepted
sampling phases at `e` expose that epoch and have unavailable coins.
Deterministic retransmissions return no coins and continue. The local send
relations preserve the remaining message, key-table, and counter updates.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

set_option maxHeartbeats 600000 in
-- The guard and revelation cases compare complete states with different coin types.
set_option backward.dsimp.instances true in
/-- For every unexposed selected epoch, material value, and honest state,
A's guarded symbolic leaking send followed by revelation equals the
distribution of the stopped honest leaking send with its successor marked. -/
theorem oracleSendArleak_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) :
    𝒟[((revealAfter (revealResponse (fun out => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
      (SCKAScheme.oracleSendArleak sendExposureA
        (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ())).run).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      ((stopOnState (SCKAScheme.oracleSendArleak sendExposureA
        (honestScheme ecEk ecCt0 ecCt1 m e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s] := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change 𝒟[_] = 𝒟[Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleSendArleak sendExposureA
      (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))]
  simp only [SCKAScheme.oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  dsimp only [symbolicScheme, honestScheme, scheme, markState]
  rw [sendArleak_mark base onoff ecEk leak m e (decide (s.stB.t = e))
    ((s.keyB s.stA.t).map (mark e s.stA.t)) (s.keyB s.stA.t) s.stA]
  simp only [bind_map_left]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none =>
    simp [StateT.run_pure, markState, markA, markB, Prod.map, revealResponse, hs]
  | some out =>
    rcases out with ⟨key, msg, t, next, coins⟩
    obtain ⟨rfl, hcoins⟩ := sendArleak_shape
      (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t)) ecEk
        (Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
      s.stA key msg t next coins hout
    rcases hcoins with rfl | ⟨r, rfl⟩
    all_goals
      have heq : (s.stA.t = e) ↔ (e = s.stA.t) := eq_comm
      by_cases he : e = s.stA.t <;> by_cases hc : s.stA.t ∈ s.challenged <;>
        (try simp only [he] at hs) <;>
        simp [sendExposureA, markCoins, revealResponse, revealCoins, mark,
          StateT.run_set, StateT.run_pure,
          markState, markA, markB, Prod.map, hs, heq, he, hc]

set_option maxHeartbeats 1600000 in
-- Four coin phases are compared both with and without a newly recorded key.
set_option backward.dsimp.instances true in
/-- For every transcript-consistent state with unexposed selected epoch,
B's guarded symbolic leaking send followed by revelation equals the
distribution of its stopped honest leaking send with successor marking.
This includes offline, online, combined sampling, and retransmission. -/
theorem oracleSendBrleak_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) (hinv : reachableInv base onoff ecEk ecCt0 ecCt1 s) :
    𝒟[((revealAfter (revealResponse (fun out => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
      (SCKAScheme.oracleSendBrleak sendExposureB
        (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ())).run).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      ((stopOnState (SCKAScheme.oracleSendBrleak sendExposureB
        (honestScheme ecEk ecCt0 ecCt1 m e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s] := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change 𝒟[_] = 𝒟[Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleSendBrleak sendExposureB
      (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))]
  simp only [SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  dsimp only [symbolicScheme, honestScheme, scheme, markState]
  rw [sendBrleak_mark base onoff ecCt0 ecCt1 leak m e (decide (s.stA.t = e))
    ((s.keyB s.stA.t).map (mark e s.stA.t)) (s.keyB s.stA.t) s.stB]
  simp only [bind_map_left]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none =>
    simp [StateT.run_pure, markState, markA, markB, Prod.map, revealResponse, hs]
  | some out =>
    rcases out with ⟨key, msg, t, next, coins⟩
    have hcoins := sendBrleak_coins
      (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t)) ecCt0 ecCt1
        (Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
      s.stB key msg t next coins hout
    cases key with
    | none =>
      rcases hcoins with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r₀, r₁, rfl⟩
      all_goals
        have heq : (s.stB.t = e) ↔ (e = s.stB.t) := eq_comm
        by_cases he : e = s.stB.t <;> by_cases hc : s.stB.t ∈ s.challenged <;>
          (try simp only [he] at hs) <;>
          simp [sendExposureB, markCoins, revealResponse, revealCoins, mark,
            StateT.run_set, StateT.run_pure,
            markState, markA, markB, Prod.map, hs, heq, he, hc]
    | some key =>
      rcases key with ⟨epoch, k⟩
      obtain ⟨rfl, hct⟩ := sendBrleak_key_fresh
        (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t)) ecCt0 ecCt1
        (Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        s.stB epoch k msg t next coins hout
      have hk := (keys_none_before_online base onoff ecEk ecCt0 ecCt1 s hinv hct).1
      simp only [Option.map_some, ← mark_update]
      rcases hcoins with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r₀, r₁, rfl⟩
      all_goals
        have heq : (s.stB.t = e) ↔ (e = s.stB.t) := eq_comm
        by_cases he : e = s.stB.t <;> by_cases hc : s.stB.t ∈ s.challenged <;>
          (try simp only [he] at hs) <;>
          simp [sendExposureB, markCoins, revealResponse, revealCoins, mark,
            StateT.run_set, StateT.run_pure,
            markState, markA, markB, Prod.map, hs, heq, he, hc, hk]

end oppUniKemCKA.Security.Embedding
