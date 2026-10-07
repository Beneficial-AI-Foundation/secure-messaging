/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.Security

/-!
# The per-query simulation relation

**Setting.** Fix material `m`, a selected epoch `e`, and a challenge key `kStar`. For an honest
game state `s`, the simulator runs from `markState e s` and the honest intermediate game, stopped
after the first query exposing `e` (`honestStopped`), runs from `s`.

**Results.**

- `oracle_mark`: for every transcript-consistent state `s` with `e ∉ s.exposed` and every
  security query, the simulator's query from `markState e s` has the joint response/state
  distribution of the stopped honest query from `s` followed by marking the successor.
- The cases of `oracle_mark`: `correctnessOracle_mark` for sends and receives
  (`oracleSendA_mark`, `oracleSendB_mark`, `oracleRecvA_mark`, `oracleRecvB_mark`),
  `oracleSendArleak_mark` and `oracleSendBrleak_mark` for leaking sends, whose coins at `e` stop
  the honest game, and `corruptA_mark` and `corruptB_mark` for corruptions, which stop it when
  they expose `e`.
- `honest_recvA_eq_ideal`: A's receive in the honest game is the auxiliary receive.
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
        ((stopOnState (SCKAScheme.oracleCorruptA (vulnCorrA base onoff)
          (StB onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleCorruptA (vulnCorrA base onoff)
      (StB onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))
  have hv := markA_vulnerable e s.stA
  by_cases hg : vulnCorrA base onoff s.stA ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptA, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [markState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealResponse, revealA_markA_eq, markState, Prod.map]
  all_goals by_cases he : e ∈ vulnCorrA base onoff s.stA <;> simp [he]


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
        ((stopOnState (SCKAScheme.oracleCorruptB (vulnCorrB base onoff)
          (StA onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleCorruptB (vulnCorrB base onoff)
      (StA onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))
  have hv := markB_vulnerable e s.stB
  by_cases hg : vulnCorrB base onoff s.stB ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptB, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [markState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealResponse, revealB_markB_eq, markState, Prod.map]
  all_goals by_cases he : e ∈ vulnCorrB base onoff s.stB <;> simp [he]


end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

omit [DecidableEq K] in
/-- For every material value, selected epoch, game state, and message,
A's pinned receive equals the auxiliary receive using B's recorded key
as its constant decapsulation result. -/
theorem honest_recvA_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (msg : Message Sym) :
    (honestScheme ecEk ecCt0 ecCt1 m e s).recvA s.stA msg =
      recvA base onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  cases bit
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.stA.dkA <;> cases hc : s.stA.ct0 <;> cases hk : s.keyB s.stA.t
  all_goals
    simp only [honestScheme, scheme, recvA, hd, hc, hk,
      Option.bind_eq_bind, Option.pure_def]
    repeat' (split <;> simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Bool.and_eq_true, beq_iff_eq, Option.bind_some, Option.bind_none])

set_option backward.dsimp.instances true in
/-- For every honest state and message index, B's symbolic receive oracle
equals its honest pinned receive oracle followed by marking. Both message
availability and correctness bookkeeping are preserved. -/
theorem oracleRecvB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (SCKAScheme.oracleRecvB
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) n).run (markState e s) =
    Prod.map id (markState e) <$>
      (SCKAScheme.oracleRecvB (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s := by
  simp only [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgA n with
  | none => simp [markState, markA, markB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [markState, hm]
    dsimp only [symbolicScheme, scheme]
    rw [recvB_mark]
    have heq : (honestScheme ecEk ecCt0 ecCt1 m e s).recvB s.stB msg =
        recvB base onoff ecEk s.stB msg := rfl
    rw [heq]
    cases hr : recvB base onoff ecEk s.stB msg with
    | none => simp [StateT.run_set, markState, markA, markB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      have hk := recvB_key_none base onoff ecEk s.stB msg key t next hr
      subst key
      simp [StateT.run_set, markState, markA, markB, Prod.map]

set_option backward.dsimp.instances true in
/-- For every honest state and message index, A's symbolic receive oracle
equals its honest pinned receive oracle followed by marking. A's auxiliary
decapsulation uses B's recorded key, keeping each consistency check equal. -/
theorem oracleRecvA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (SCKAScheme.oracleRecvA
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) n).run (markState e s) =
    Prod.map id (markState e) <$>
      (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s := by
  simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgB n with
  | none => simp [markState, markA, markB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [markState, hm]
    dsimp only [symbolicScheme, scheme]
    rw [recvA_mark]
    have heq := honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak m e s msg
    rw [heq]
    cases hr : recvA base onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg with
    | none => simp [StateT.run_set, markState, markA, markB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      cases key with
      | none => simp [StateT.run_set, markState, markA, markB, Prod.map]
      | some key =>
        rcases key with ⟨epoch, k⟩
        obtain ⟨rfl, hk⟩ := recvA_key_source base onoff ecCt0 ecCt1
          (s.keyB s.stA.t) s.stA msg epoch k t next hr
        simp [StateT.run_set, markState, markA, markB,
          Prod.map, hk, ← mark_update]

end oppUniKemCKA.Security.Embedding

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
      (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
       (s.keyB s.stA.t))
      (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
       (s.keyB s.stA.t))
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
        (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB epoch k msg t next hout
      have hk := (keys_none_before_online base onoff ecEk ecCt0 ecCt1 s hs hc).1
      simp [StateT.run_set, markState, markA, markB,
        Prod.map, hk, ← mark_update]

end oppUniKemCKA.Security.Embedding

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
      (SCKAScheme.oracleSendArleak vulnRleakA
        (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ())).run).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      ((stopOnState (SCKAScheme.oracleSendArleak vulnRleakA
        (honestScheme ecEk ecCt0 ecCt1 m e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s] := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change 𝒟[_] = 𝒟[Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleSendArleak vulnRleakA
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
      (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
       (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t)) ecEk
        (Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
      s.stA key msg t next coins hout
    rcases hcoins with rfl | ⟨r, rfl⟩
    all_goals
      have heq : (s.stA.t = e) ↔ (e = s.stA.t) := eq_comm
      by_cases he : e = s.stA.t <;> by_cases hc : s.stA.t ∈ s.challenged <;>
        (try simp only [he] at hs) <;>
        simp [vulnRleakA, markCoins, revealResponse, revealCoins, mark,
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
      (SCKAScheme.oracleSendBrleak vulnRleakB
        (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ())).run).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      ((stopOnState (SCKAScheme.oracleSendBrleak vulnRleakB
        (honestScheme ecEk ecCt0 ecCt1 m e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s] := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change 𝒟[_] = 𝒟[Prod.map id (markState e) <$> (do
    let z ← (SCKAScheme.oracleSendBrleak vulnRleakB
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
      (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
       (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t)) ecCt0 ecCt1
        (Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
      s.stB key msg t next coins hout
    cases key with
    | none =>
      rcases hcoins with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r₀, r₁, rfl⟩
      all_goals
        have heq : (s.stB.t = e) ↔ (e = s.stB.t) := eq_comm
        by_cases he : e = s.stB.t <;> by_cases hc : s.stB.t ∈ s.challenged <;>
          (try simp only [he] at hs) <;>
          simp [vulnRleakB, markCoins, revealResponse, revealCoins, mark,
            StateT.run_set, StateT.run_pure,
            markState, markA, markB, Prod.map, hs, heq, he, hc]
    | some key =>
      rcases key with ⟨epoch, k⟩
      obtain ⟨rfl, hct⟩ := sendBrleak_key_fresh
        (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t)) ecCt0 ecCt1
        (Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        s.stB epoch k msg t next coins hout
      have hk := (keys_none_before_online base onoff ecEk ecCt0 ecCt1 s hinv hct).1
      simp only [Option.map_some, ← mark_update]
      rcases hcoins with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r₀, r₁, rfl⟩
      all_goals
        have heq : (s.stB.t = e) ↔ (e = s.stB.t) := eq_comm
        by_cases he : e = s.stB.t <;> by_cases hc : s.stB.t ∈ s.challenged <;>
          (try simp only [he] at hs) <;>
          simp [vulnRleakB, markCoins, revealResponse, revealCoins, mark,
            StateT.run_set, StateT.run_pure,
            markState, markA, markB, Prod.map, hs, heq, he, hc, hk]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- For every transcript-consistent state and correctness-interface query,
the symbolic query's joint distribution is the honest pinned query's joint
distribution followed by successor marking. -/
theorem correctnessOracle_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) :
    𝒟[(SCKAScheme.sckaCorrectnessImpl
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) t).run (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s] := by
  rcases t with ((((n | u) | u) | n) | n)
  · simp [SCKAScheme.sckaCorrectnessImpl, SCKAScheme.oracleUnif,
      Prod.map, markState, markA, markB]
  · cases u
    exact oracleSendA_mark base onoff ecEk ecCt0 ecCt1 leak m e s
  · cases u
    exact oracleSendB_mark base onoff ecEk ecCt0 ecCt1 leak m e s hs
  · exact congrArg evalDist (oracleRecvA_mark base onoff ecEk ecCt0 ecCt1 leak m e n s)
  · exact congrArg evalDist (oracleRecvB_mark base onoff ecEk ecCt0 ecCt1 leak m e n s)

/-- For every selected material value, epoch, supplied challenge key,
transcript-consistent unexposed state, and security query, the reduction's
joint optional-response/state distribution equals the stopped honest
intermediate query followed by marking the successor. -/
theorem oracle_mark [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (he : e ∉ s.exposed) :
    𝒟[((oracle base onoff ecEk ecCt0 ecCt1 leak e m.keygen.1.1 m.ciphertext kStar t).run).run
      (markState e s)] =
    𝒟[Prod.map id (markState e) <$>
      ((honestStopped base onoff ecEk ecCt0 ecCt1 leak m e kStar t).run).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · apply evalDist_lift_eq_stopOnState_map
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s))
      (SCKAScheme.sckaCorrectnessImpl (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s))
      (markState e) (fun u => decide (e ∈ u.exposed)) t s
      (correctnessOracle_mark base onoff ecEk ecCt0 ecCt1 leak m e t s hs)
    intro z hz
    have h := (SCKAScheme.correctnessImpl_securitySets_eq _ t s z hz).1
    simp [h, he]
  · cases u
    exact oracleSendArleak_mark base onoff ecEk ecCt0 ecCt1 leak m e s he
  · cases u
    exact oracleSendBrleak_mark base onoff ecEk ecCt0 ecCt1 leak m e s he hs
  · apply evalDist_lift_eq_stopOnState_map
      (pinnedChallenge onoff e kStar) (challenge onoff e kStar)
      (markState e) (fun u => decide (e ∈ u.exposed)) t s
      (congrArg evalDist (challenge_mark onoff e kStar t s))
    intro z hz
    simp [((pinnedChallenge_recordsChallenges onoff e kStar).exposed_nA_eq t s z hz).1, he]
  · cases u
    exact congrArg evalDist (corruptA_mark base onoff e s he)
  · cases u
    exact congrArg evalDist (corruptB_mark base onoff e s he)

end oppUniKemCKA.Security.Embedding
