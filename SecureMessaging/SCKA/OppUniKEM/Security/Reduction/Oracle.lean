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

**Setting.** Fix a challenge epoch `e`, a candidate key `kStar : K`, and pre-sampled epoch material
`m : KEMMaterial leak` (`Simulator`). Let:

- `hideState e s` (`Relation`) be the state map from an honest game state `s` to the simulator's
  state `SimState`, replacing the secret key, offline state, and recorded keys of epoch `e` by
  `none` (hidden);
- `Sim := oracle … e m.keygen.1.1 m.ciphertext kStar` (`Simulator`) be the simulator's security
  oracles with the public key and ciphertext of `m` embedded at epoch `e`;
- `Hon := honestStopped … m e kStar` (`Game`) be the honest security oracles with the samples of
  epoch `e` pinned to `m`, stopped (`⊥`) at the first query whose successor exposes `e`.

**Main result** (`oracle_hide`). For every security query `t` and every state `s` satisfying
`reachableInv s` and `e ∉ s.exposed`, running `Sim` on `t` from `hideState e s` has the same
joint response/state distribution as running `Hon` on `t` from `s` and applying `hideState e` to
the successor state:

```text
𝒟[((Sim t).run).run (hideState e s)] =
  𝒟[Prod.map id (hideState e) <$> ((Hon t).run).run s]
```
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

set_option backward.dsimp.instances true in
/-- If `e ∉ s.exposed`, corrupting party A in the simulator from `hideState e s` coincides with
corrupting party A in the stopped honest game from `s` and applying `hideState e` to the successor
state. -/
private theorem corruptA_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (e : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) :
    ((revealAfter (revealA (onoff := onoff))
      (SCKAScheme.oracleCorruptA
        (fun u => if u.dkA.isSome then {u.t} else ∅)
        (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym)
        (Option K) (Message Sym) ())).run).run (hideState e s) =
      Prod.map id (hideState e) <$>
        ((stopOnState (SCKAScheme.oracleCorruptA (vulnCorrA base onoff)
          (StB onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (hideState e) <$> (do
    let z ← (SCKAScheme.oracleCorruptA (vulnCorrA base onoff)
      (StB onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))
  have hv := hideA_vulnerable e s.stA
  by_cases hg : vulnCorrA base onoff s.stA ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptA, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [hideState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealA_hideA_eq, hideState, Prod.map]
  all_goals by_cases he : e ∈ vulnCorrA base onoff s.stA <;> simp [he]

set_option backward.dsimp.instances true in
/-- B version of `corruptA_hide`, with `revealB`. -/
private theorem corruptB_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (e : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) :
    ((revealAfter (revealB (onoff := onoff))
      (SCKAScheme.oracleCorruptB
        (fun u => if u.stCt.isSome then {u.t} else ∅)
        (StateA (Option SK) PK onoff.C₀ Sym)
        (Option K) (Message Sym) ())).run).run (hideState e s) =
      Prod.map id (hideState e) <$>
        ((stopOnState (SCKAScheme.oracleCorruptB (vulnCorrB base onoff)
          (StA onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (hideState e) <$> (do
    let z ← (SCKAScheme.oracleCorruptB (vulnCorrB base onoff)
      (StA onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))
  have hv := hideB_vulnerable e s.stB
  by_cases hg : vulnCorrB base onoff s.stB ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptB, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [hideState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealB_hideB_eq, hideState, Prod.map]
  all_goals by_cases he : e ∈ vulnCorrB base onoff s.stB <;> simp [he]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

omit [DecidableEq K] in
/-- Party A's receive transition in `honestScheme m e s` is definitionally `recvA` with decapsulation
replaced by the lookup `fun _ _ => s.keyB s.stA.t`. -/
theorem honest_recvA_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (msg : Message Sym) :
    (honestScheme ecEk ecCt0 ecCt1 m e s).recvA s.stA msg =
      recvA base onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg := rfl

/-- Party B's receive oracle `oracleRecvB` over `simScheme` from `hideState e s` coincides with
running `oracleRecvB` over `honestScheme` from `s` and applying `hideState e` to the successor
state. -/
private theorem oracleRecvB_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (SCKAScheme.oracleRecvB
      (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s) n).run (hideState e s) =
    Prod.map id (hideState e) <$>
      (SCKAScheme.oracleRecvB (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s := by
  simp only [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgA n with
  | none => simp [hideState, hideA, hideB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [hideState, hm]
    dsimp only [simScheme, scheme]
    rw [recvB_hide]
    have heq : (honestScheme ecEk ecCt0 ecCt1 m e s).recvB s.stB msg =
        recvB base onoff ecEk s.stB msg := rfl
    rw [heq]
    cases hr : recvB base onoff ecEk s.stB msg with
    | none => simp [StateT.run_set, hideState, hideA, hideB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      have hk := recvB_key_none base onoff ecEk s.stB msg key t next hr
      subst key
      simp [StateT.run_set, hideState, hideA, hideB, Prod.map]

/-- A version of `oracleRecvB_hide`. -/
private theorem oracleRecvA_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (SCKAScheme.oracleRecvA
      (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s) n).run (hideState e s) =
    Prod.map id (hideState e) <$>
      (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s := by
  simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgB n with
  | none => simp [hideState, hideA, hideB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [hideState, hm]
    dsimp only [simScheme, scheme]
    rw [recvA_hide]
    have heq := honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak m e s msg
    rw [heq]
    cases hr : recvA base onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg with
    | none => simp [StateT.run_set, hideState, hideA, hideB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      cases key with
      | none => simp [StateT.run_set, hideState, hideA, hideB, Prod.map]
      | some key =>
        rcases key with ⟨epoch, k⟩
        obtain ⟨rfl, hk⟩ := recvA_key_source base onoff ecCt0 ecCt1
          (s.keyB s.stA.t) s.stA msg epoch k t next hr
        simp [StateT.run_set, hideState, hideA, hideB,
          Prod.map, hk, ← hide_update]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

set_option backward.dsimp.instances true in
/-- Party A's ordinary send oracle `oracleSendA` over `simScheme` from `hideState e s` has the
same response/state distribution as running `oracleSendA` over `honestScheme` from `s` and applying
`hideState e` to the successor state. -/
private theorem oracleSendA_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(SCKAScheme.oracleSendA
      (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ()).run (hideState e s)] =
    𝒟[Prod.map id (hideState e) <$>
      (SCKAScheme.oracleSendA (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s] := by
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind]
  dsimp only [simScheme, honestScheme, scheme, hideState]
  rw [sendA_hide base onoff ecEk leak m e (decide (s.stB.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stA]
  simp only [bind_map_left, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none => simp [StateT.run_pure, hideState, hideA, hideB, Prod.map]
  | some out =>
    rcases out with ⟨key, msg, t, next⟩
    have hk := sendA_key_none
      (honestKem m e s) (honestOnOff m e s)
      ecEk s.stA key msg t next hout
    subst key
    simp [StateT.run_set, hideState, hideA, hideB, Prod.map]

set_option backward.dsimp.instances true in
/-- B version of `oracleSendA_hide`, under `reachableInv`. -/
private theorem oracleSendB_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) :
    𝒟[(SCKAScheme.oracleSendB
      (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ()).run (hideState e s)] =
    𝒟[Prod.map id (hideState e) <$>
      (SCKAScheme.oracleSendB (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s] := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind]
  dsimp only [simScheme, honestScheme, scheme, hideState]
  rw [sendB_hide base onoff ecCt0 ecCt1 leak m e (decide (s.stA.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stB]
  simp only [bind_map_left, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none => simp [StateT.run_pure, hideState, hideA, hideB, Prod.map]
  | some out =>
    rcases out with ⟨key, msg, t, next⟩
    cases key with
    | none => simp [StateT.run_set, hideState, hideA, hideB, Prod.map]
    | some key =>
      rcases key with ⟨epoch, k⟩
      obtain ⟨rfl, hc⟩ := sendB_key_fresh
        (honestKem m e s) (honestOnOff m e s)
        ecCt0 ecCt1 s.stB epoch k msg t next hout
      have hk := (keys_none_before_online base onoff ecEk ecCt0 ecCt1 s hs hc).1
      simp [StateT.run_set, hideState, hideA, hideB,
        Prod.map, hk, ← hide_update]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

set_option backward.dsimp.instances true in
/-- If `e ∉ s.exposed`, party A's leaking send in the simulator from `hideState e s` has the same
response/state distribution as party A's leaking send in the stopped honest game from `s` followed
by `hideState e`. -/
private theorem oracleSendArleak_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) :
    𝒟[((revealAfter (fun out => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins))
      (SCKAScheme.oracleSendArleak vulnRleakA
        (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ())).run).run (hideState e s)] =
    𝒟[Prod.map id (hideState e) <$>
      ((stopOnState (SCKAScheme.oracleSendArleak vulnRleakA
        (honestScheme ecEk ecCt0 ecCt1 m e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s] := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change 𝒟[_] = 𝒟[Prod.map id (hideState e) <$> (do
    let z ← (SCKAScheme.oracleSendArleak vulnRleakA
      (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))]
  simp only [SCKAScheme.oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  dsimp only [simScheme, honestScheme, scheme, hideState]
  rw [sendArleak_hide base onoff ecEk leak m e (decide (s.stB.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stA]
  simp only [bind_map_left]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none =>
    simp [StateT.run_pure, hideState, hideA, hideB, Prod.map, hs]
  | some out =>
    rcases out with ⟨key, msg, t, next, coins⟩
    obtain ⟨rfl, hcoins⟩ := sendArleak_shape
      (honestKem m e s) (honestOnOff m e s) ecEk
        (honestLeak m e s)
      s.stA key msg t next coins hout
    rcases hcoins with rfl | ⟨r, rfl⟩
    all_goals
      have heq : (s.stA.t = e) ↔ (e = s.stA.t) := eq_comm
      by_cases he : e = s.stA.t <;> by_cases hc : s.stA.t ∈ s.challenged <;>
        (try simp only [he] at hs) <;>
        simp [vulnRleakA, hideCoins, revealCoins, hide,
          StateT.run_set, StateT.run_pure,
          hideState, hideA, hideB, Prod.map, hs, heq, he, hc]

set_option backward.dsimp.instances true in
/-- B version of `oracleSendArleak_hide`, under `reachableInv`. -/
private theorem oracleSendBrleak_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : e ∉ s.exposed) (hinv : reachableInv base onoff ecEk ecCt0 ecCt1 s) :
    𝒟[((revealAfter (fun out => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins))
      (SCKAScheme.oracleSendBrleak vulnRleakB
        (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s) ())).run).run (hideState e s)] =
    𝒟[Prod.map id (hideState e) <$>
      ((stopOnState (SCKAScheme.oracleSendBrleak vulnRleakB
        (honestScheme ecEk ecCt0 ecCt1 m e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s] := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change 𝒟[_] = 𝒟[Prod.map id (hideState e) <$> (do
    let z ← (SCKAScheme.oracleSendBrleak vulnRleakB
      (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s
    pure (if decide (e ∈ z.2.exposed) then none else some z.1, z.2))]
  simp only [SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  dsimp only [simScheme, honestScheme, scheme, hideState]
  rw [sendBrleak_hide base onoff ecCt0 ecCt1 leak m e (decide (s.stA.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stB]
  simp only [bind_map_left]
  apply evalDist_bind_congr
  intro out hout
  cases out with
  | none =>
    simp [StateT.run_pure, hideState, hideA, hideB, Prod.map, hs]
  | some out =>
    rcases out with ⟨key, msg, t, next, coins⟩
    have hcoins := sendBrleak_coins
      (honestKem m e s) (honestOnOff m e s) ecCt0 ecCt1
        (honestLeak m e s)
      s.stB key msg t next coins hout
    cases key with
    | none =>
      rcases hcoins with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r₀, r₁, rfl⟩
      all_goals
        have heq : (s.stB.t = e) ↔ (e = s.stB.t) := eq_comm
        by_cases he : e = s.stB.t <;> by_cases hc : s.stB.t ∈ s.challenged <;>
          (try simp only [he] at hs) <;>
          simp [vulnRleakB, hideCoins, revealCoins, hide,
            StateT.run_set, StateT.run_pure,
            hideState, hideA, hideB, Prod.map, hs, heq, he, hc]
    | some key =>
      rcases key with ⟨epoch, k⟩
      obtain ⟨rfl, hct⟩ := sendBrleak_key_fresh
        (honestKem m e s) (honestOnOff m e s) ecCt0 ecCt1
        (honestLeak m e s)
        s.stB epoch k msg t next coins hout
      have hk := (keys_none_before_online base onoff ecEk ecCt0 ecCt1 s hinv hct).1
      simp only [Option.map_some, ← hide_update]
      rcases hcoins with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r₀, r₁, rfl⟩
      all_goals
        have heq : (s.stB.t = e) ↔ (e = s.stB.t) := eq_comm
        by_cases he : e = s.stB.t <;> by_cases hc : s.stB.t ∈ s.challenged <;>
          (try simp only [he] at hs) <;>
          simp [vulnRleakB, hideCoins, revealCoins, hide,
            StateT.run_set, StateT.run_pure,
            hideState, hideA, hideB, Prod.map, hs, heq, he, hc, hk]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- Under `reachableInv s`, every correctness query `t` of `sckaCorrectnessImpl` over
`simScheme` from `hideState e s` has the same response/state distribution as running `t` over
`honestScheme` from `s` and applying `hideState e` to the successor state. -/
private theorem correctnessOracle_hide
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) :
    𝒟[(SCKAScheme.sckaCorrectnessImpl
      (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s) t).run (hideState e s)] =
    𝒟[Prod.map id (hideState e) <$>
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s] := by
  rcases t with ((((n | u) | u) | n) | n)
  · simp [SCKAScheme.sckaCorrectnessImpl, SCKAScheme.oracleUnif,
      Prod.map, hideState, hideA, hideB]
  · cases u
    exact oracleSendA_hide base onoff ecEk ecCt0 ecCt1 leak m e s
  · cases u
    exact oracleSendB_hide base onoff ecEk ecCt0 ecCt1 leak m e s hs
  · exact congrArg evalDist (oracleRecvA_hide base onoff ecEk ecCt0 ecCt1 leak m e n s)
  · exact congrArg evalDist (oracleRecvB_hide base onoff ecEk ecCt0 ecCt1 leak m e n s)

/-- For every security query `t` and every state `s` satisfying `reachableInv s` and
`e ∉ s.exposed`, running the simulator `oracle … e m.keygen.1.1 m.ciphertext kStar` on `t` from
`hideState e s` has the same response/state distribution as running `honestStopped … m e kStar` on
`t` from `s` and applying `hideState e` to the successor state. -/
theorem oracle_hide [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : KEMMaterial leak) (e : ℕ) (kStar : K) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (he : e ∉ s.exposed) :
    𝒟[((oracle base onoff ecEk ecCt0 ecCt1 leak e m.keygen.1.1 m.ciphertext kStar t).run).run
      (hideState e s)] =
    𝒟[Prod.map id (hideState e) <$>
      ((honestStopped base onoff ecEk ecCt0 ecCt1 leak m e kStar t).run).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · apply evalDist_lift_eq_stopOnState_map
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s))
      (SCKAScheme.sckaCorrectnessImpl (simScheme base onoff ecEk ecCt0 ecCt1 leak m e s))
      (hideState e) (fun u => decide (e ∈ u.exposed)) t s
      (correctnessOracle_hide base onoff ecEk ecCt0 ecCt1 leak m e t s hs)
    intro z hz
    have h := (SCKAScheme.correctnessImpl_securitySets_eq _ t s z hz).1
    simp [h, he]
  · cases u
    exact oracleSendArleak_hide base onoff ecEk ecCt0 ecCt1 leak m e s he
  · cases u
    exact oracleSendBrleak_hide base onoff ecEk ecCt0 ecCt1 leak m e s he hs
  · apply evalDist_lift_eq_stopOnState_map
      (pinnedChallenge onoff e kStar) (challenge onoff e kStar)
      (hideState e) (fun u => decide (e ∈ u.exposed)) t s
      (congrArg evalDist (challenge_hide onoff e kStar t s))
    intro z hz
    simp [((pinnedChallenge_recordsChallenges onoff e kStar).exposed_nA_eq t s z hz).1, he]
  · cases u
    exact congrArg evalDist (corruptA_hide base onoff e s he)
  · cases u
    exact congrArg evalDist (corruptB_hide base onoff e s he)

end oppUniKemCKA.Security.Embedding
