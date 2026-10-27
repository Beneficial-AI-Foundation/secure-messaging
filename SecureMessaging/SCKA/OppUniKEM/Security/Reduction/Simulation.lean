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
# The simulation theorem

Fix a KEM `kem` with shared-key space `K` and deterministic decapsulation, correct erasure codes
for Opp-UniKEM, an SCKA adversary `adv`, an epoch `e` at which the reduction embeds its IND-CPA
challenge, and a version `x ∈ {real, random}`. Let `leak` record the coins of the KEM samplers.
A sample `kemMat ← sampleMaterial leak` consists of the outputs and coins of key generation,
offline encapsulation, and online encapsulation. For an independent uniform key `k`, write
`k_real := kemMat.key` and `k_random := k`.

Consider two experiments running `adv` from their respective empty initial states, with both
parties at epoch `1`, empty message and key tables, and empty exposure and challenge sets. Let
`s₀` denote the honest initial state. Both replace A's decapsulation by B's recorded key for A's
current epoch. Eligible challenges at epoch `t` return a uniform key if `0 < t < e`, `k_x` if
`t = e`, and the recorded key otherwise.

- The fixed branch `𝓑_e^x` (`fixedBranch … adv e true` for `real`, `… false` for `random`)
  samples `kemMat` and `k`, inserts `kemMat`'s public key and ciphertext at epoch `e`, and hides
  the corresponding secret key, offline state, shared key, and coins. A permitted corruption or
  leaking send that would reveal a hidden value stops the run with output `false`.
- The honest game `P_e(kemMat, k_x)` fixes all sampling outputs and coins at epoch `e` to
  `kemMat` and returns `false` at the first exposure of `e`. Formally, this is
  `optionRun (honestStopped … kemMat e k_x) adv s₀`.

Other epochs sample honestly, and both experiments return `adv`'s output on normal completion.
The simulation theorem is the acceptance equality (`fixedBranch_eq_honestStopped`):

```text
Pr[𝓑_e^x = true] = Pr[kemMat ← sampleMaterial leak; k ←$ K; P_e(kemMat, k_x) = true].
```
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

set_option backward.dsimp.instances true in
/-- Let `hideState e s` hide the local secrets and recorded keys of epoch `e` in `s`.
If `e ∉ s.exposed`, corrupting A in the simulator equals corrupting A in the honest game stopped
at exposure of `e`, followed by hiding the successor state. -/
private theorem corruptA_hide
    (e : ℕ) (s : GameState onoff Sym)
    (hs : e ∉ s.exposed) :
    ((revealAfter (revealA (onoff := onoff))
      (SCKAScheme.oracleCorruptA
        (fun u => if u.dkA.isSome then {u.t} else ∅)
        (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym)
        (Option K) (Message Sym) ())).run).run (hideState e s) =
      Prod.map id (hideState e) <$>
        ((stopOnState (SCKAScheme.oracleCorruptA (vulnCorrA kem onoff)
          (StB onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (hideState e) <$> (do
    let res ← (SCKAScheme.oracleCorruptA (vulnCorrA kem onoff)
      (StB onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ res.2.exposed) then none else some res.1, res.2))
  have hv := hideA_vulnerable e s.stA
  by_cases hg : vulnCorrA kem onoff s.stA ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptA, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [hideState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealA_hideA_eq, hideState, Prod.map]
  all_goals by_cases he : e ∈ vulnCorrA kem onoff s.stA <;> simp [he]

set_option backward.dsimp.instances true in
/-- B version of `corruptA_hide`, with `revealB`. -/
private theorem corruptB_hide
    (e : ℕ) (s : GameState onoff Sym)
    (hs : e ∉ s.exposed) :
    ((revealAfter (revealB (onoff := onoff))
      (SCKAScheme.oracleCorruptB
        (fun u => if u.stCt.isSome then {u.t} else ∅)
        (StateA (Option SK) PK onoff.C₀ Sym)
        (Option K) (Message Sym) ())).run).run (hideState e s) =
      Prod.map id (hideState e) <$>
        ((stopOnState (SCKAScheme.oracleCorruptB (vulnCorrB kem onoff)
          (StA onoff Sym) K (Message Sym)) (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ = Prod.map id (hideState e) <$> (do
    let res ← (SCKAScheme.oracleCorruptB (vulnCorrB kem onoff)
      (StA onoff Sym) K (Message Sym) ()).run s
    pure (if decide (e ∈ res.2.exposed) then none else some res.1, res.2))
  have hv := hideB_vulnerable e s.stB
  by_cases hg : vulnCorrB kem onoff s.stB ∩ s.challenged ≠ ∅
  all_goals
    simp only [SCKAScheme.oracleCorruptB, StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [hideState]
    simp only [hv]
    simp [hg, hs, StateT.run_pure,
      revealB_hideB_eq, hideState, Prod.map]
  all_goals by_cases he : e ∈ vulnCorrB kem onoff s.stB <;> simp [he]

section

variable [DecidableEq K] [DecidableEq Sym]

/-- Party B's receive with the KEM challenge embedded (`simScheme`) from `hideState e s` equals
receiving with the KEM samples at `e` fixed to `kemMat` (`honestScheme`) from `s`, followed by
hiding the successor state. -/
private theorem oracleRecvB_hide
    (kemMat : KEMMaterial leak) (e n : ℕ)
    (s : GameState onoff Sym) :
    (SCKAScheme.oracleRecvB
      (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s) n).run (hideState e s) =
    Prod.map id (hideState e) <$>
      (SCKAScheme.oracleRecvB (honestScheme ecEk ecCt0 ecCt1 kemMat e s) n).run s := by
  simp only [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgA n with
  | none => simp [hideState, hideA, hideB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [hideState, hm]
    dsimp only [simScheme, scheme]
    rw [recvB_hide]
    have heq : (honestScheme ecEk ecCt0 ecCt1 kemMat e s).recvB s.stB msg =
        recvB kem onoff ecEk s.stB msg := rfl
    rw [heq]
    cases hr : recvB kem onoff ecEk s.stB msg with
    | none => simp [StateT.run_set, hideState, hideA, hideB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      have hk := recvB_key_none kem onoff ecEk s.stB msg key t next hr
      subst key
      simp [StateT.run_set, hideState, hideA, hideB, Prod.map]

/-- A version of `oracleRecvB_hide`. -/
private theorem oracleRecvA_hide
    (kemMat : KEMMaterial leak) (e n : ℕ)
    (s : GameState onoff Sym) :
    (SCKAScheme.oracleRecvA
      (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s) n).run (hideState e s) =
    Prod.map id (hideState e) <$>
      (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 kemMat e s) n).run s := by
  simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgB n with
  | none => simp [hideState, hideA, hideB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [hideState, hm]
    dsimp only [simScheme, scheme]
    rw [recvA_hide]
    have heq := stageScheme_recvA_eq_ideal kem onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e s msg
    rw [heq]
    cases hr : recvA kem onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg with
    | none => simp [StateT.run_set, hideState, hideA, hideB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      cases key with
      | none => simp [StateT.run_set, hideState, hideA, hideB, Prod.map]
      | some key =>
        rcases key with ⟨epoch, k⟩
        obtain ⟨rfl, hk⟩ := recvA_key_source kem onoff ecCt0 ecCt1
          (s.keyB s.stA.t) s.stA msg epoch k t next hr
        simp [StateT.run_set, hideState, hideA, hideB,
          Prod.map, hk, ← hide_update]

end

section

variable [DecidableEq K] [DecidableEq Sym]

set_option backward.dsimp.instances true in
/-- Party A's ordinary send oracle `oracleSendA` over `simScheme` from `hideState e s` has the
same response/state distribution as running `oracleSendA` over `honestScheme` from `s` and applying
`hideState e` to the successor state. -/
private theorem oracleSendA_hide
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym) :
    (SCKAScheme.oracleSendA
      (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s) ()).run (hideState e s) =ᵈ
    Prod.map id (hideState e) <$>
      (SCKAScheme.oracleSendA (honestScheme ecEk ecCt0 ecCt1 kemMat e s) ()).run s := by
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind]
  dsimp only [simScheme, honestScheme, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
    Stage.onlineFlag, scheme, hideState]
  rw [sendA_hide kem onoff ecEk leak kemMat e (decide (s.stB.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stA]
  simp only [bind_map_left, bind_assoc, pure_bind]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro out hout
  cases out with
  | none => simp [StateT.run_pure, hideState, hideA, hideB, Prod.map]
  | some out =>
    rcases out with ⟨key, msg, t, next⟩
    have hk := sendA_key_none
      (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
      ecEk s.stA key msg t next hout
    subst key
    simp [StateT.run_set, hideState, hideA, hideB, Prod.map]

set_option backward.dsimp.instances true in
/-- B version of `oracleSendA_hide`, for states consistent with a protocol transcript
(`reachableInv`). -/
private theorem oracleSendB_hide
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) :
    (SCKAScheme.oracleSendB
      (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s) ()).run (hideState e s) =ᵈ
    Prod.map id (hideState e) <$>
      (SCKAScheme.oracleSendB (honestScheme ecEk ecCt0 ecCt1 kemMat e s) ()).run s := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind]
  dsimp only [simScheme, honestScheme, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
    Stage.onlineFlag, scheme, hideState]
  rw [sendB_hide kem onoff ecCt0 ecCt1 leak kemMat e (decide (s.stA.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stB]
  simp only [bind_map_left, bind_assoc, pure_bind]
  apply OracleComp.EvalDistEq.bind_congr_of_support
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
        (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
        ecCt0 ecCt1 s.stB epoch k msg t next hout
      have hk := (keys_none_before_online kem onoff ecEk ecCt0 ecCt1 s hs hc).1
      simp [StateT.run_set, hideState, hideA, hideB,
        Prod.map, hk, ← hide_update]

end

section

variable [DecidableEq K] [DecidableEq Sym]

set_option backward.dsimp.instances true in
/-- If `e ∉ s.exposed`, party A's leaking send in the simulator from `hideState e s` has the same
response/state distribution as party A's leaking send in the stopped honest game from `s` followed
by `hideState e`. -/
private theorem oracleSendArleak_hide
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hs : e ∉ s.exposed) :
    ((revealAfter (fun out => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins))
      (SCKAScheme.oracleSendArleak vulnRleakA
        (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s) ())).run).run (hideState e s) =ᵈ
    Prod.map id (hideState e) <$>
      ((stopOnState (SCKAScheme.oracleSendArleak vulnRleakA
        (honestScheme ecEk ecCt0 ecCt1 kemMat e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ =ᵈ Prod.map id (hideState e) <$> (do
    let res ← (SCKAScheme.oracleSendArleak vulnRleakA
      (honestScheme ecEk ecCt0 ecCt1 kemMat e s) ()).run s
    pure (if decide (e ∈ res.2.exposed) then none else some res.1, res.2))
  simp only [SCKAScheme.oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  dsimp only [simScheme, honestScheme, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
    Stage.onlineFlag, scheme, hideState]
  rw [sendArleak_hide kem onoff ecEk leak kemMat e (decide (s.stB.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stA]
  simp only [bind_map_left]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro out hout
  cases out with
  | none =>
    simp [StateT.run_pure, hideState, hideA, hideB, Prod.map, hs]
  | some out =>
    rcases out with ⟨key, msg, t, next, coins⟩
    obtain ⟨rfl, hcoins⟩ := sendArleak_shape
      (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s) ecEk
        (stageLeak .pinned kemMat e s)
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
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : GameState onoff Sym)
    (hs : e ∉ s.exposed) (hinv : reachableInv kem onoff ecEk ecCt0 ecCt1 s) :
    ((revealAfter (fun out => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins))
      (SCKAScheme.oracleSendBrleak vulnRleakB
        (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s) ())).run).run (hideState e s) =ᵈ
    Prod.map id (hideState e) <$>
      ((stopOnState (SCKAScheme.oracleSendBrleak vulnRleakB
        (honestScheme ecEk ecCt0 ecCt1 kemMat e s))
        (fun u => decide (e ∈ u.exposed)) ()).run).run s := by
  rw [revealAfter_run]
  simp only [stopOnState, OptionT.run_mk]
  change _ =ᵈ Prod.map id (hideState e) <$> (do
    let res ← (SCKAScheme.oracleSendBrleak vulnRleakB
      (honestScheme ecEk ecCt0 ecCt1 kemMat e s) ()).run s
    pure (if decide (e ∈ res.2.exposed) then none else some res.1, res.2))
  simp only [SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, map_bind, bind_assoc]
  dsimp only [simScheme, honestScheme, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
    Stage.onlineFlag, scheme, hideState]
  rw [sendBrleak_hide kem onoff ecCt0 ecCt1 leak kemMat e (decide (s.stA.t = e))
    ((s.keyB s.stA.t).map (hide e s.stA.t)) (s.keyB s.stA.t) s.stB]
  simp only [bind_map_left]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro out hout
  cases out with
  | none =>
    simp [StateT.run_pure, hideState, hideA, hideB, Prod.map, hs]
  | some out =>
    rcases out with ⟨key, msg, t, next, coins⟩
    have hcoins := sendBrleak_coins
      (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s) ecCt0 ecCt1
        (stageLeak .pinned kemMat e s)
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
        (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s) ecCt0 ecCt1
        (stageLeak .pinned kemMat e s)
        s.stB epoch k msg t next coins hout
      have hk := (keys_none_before_online kem onoff ecEk ecCt0 ecCt1 s hinv hct).1
      simp only [Option.map_some, ← hide_update]
      rcases hcoins with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r₀, r₁, rfl⟩
      all_goals
        have heq : (s.stB.t = e) ↔ (e = s.stB.t) := eq_comm
        by_cases he : e = s.stB.t <;> by_cases hc : s.stB.t ∈ s.challenged <;>
          (try simp only [he] at hs) <;>
          simp [vulnRleakB, hideCoins, revealCoins, hide,
            StateT.run_set, StateT.run_pure,
            hideState, hideA, hideB, Prod.map, hs, heq, he, hc, hk]

end

section

variable [DecidableEq K] [DecidableEq Sym]

/-- Under `reachableInv s`, every correctness query `t` of `sckaCorrectnessImpl` over
`simScheme` from `hideState e s` has the same response/state distribution as running `t` over
`honestScheme` from `s` and applying `hideState e` to the successor state. -/
private theorem correctnessOracle_hide
    (kemMat : KEMMaterial leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) :
    (SCKAScheme.sckaCorrectnessImpl
      (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s) t).run (hideState e s) =ᵈ
    Prod.map id (hideState e) <$>
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 kemMat e s) t).run s := by
  rcases t with ((((n | u) | u) | n) | n)
  · simp [SCKAScheme.sckaCorrectnessImpl, SCKAScheme.oracleUnif,
      Prod.map, hideState, hideA, hideB]
  · cases u
    exact oracleSendA_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e s
  · cases u
    exact oracleSendB_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e s hs
  · exact ToVCVio.evalDistEq_of_eq (oracleRecvA_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e n s)
  · exact ToVCVio.evalDistEq_of_eq (oracleRecvB_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e n s)

/-- For every security query `t` and every state `s` satisfying `reachableInv s` and
`e ∉ s.exposed`, running the simulator `simOracle … e kemMat.pk kemMat.ciphertext kStar` on `t` from
`hideState e s` has the same response/state distribution as running `honestStopped … kemMat e kStar`
on `t` from `s` and applying `hideState e` to the successor state. -/
theorem simOracle_hide [SampleableType K]
    (kemMat : KEMMaterial leak) (e : ℕ) (kStar : K) (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (he : e ∉ s.exposed) :
    ((simOracle kem onoff ecEk ecCt0 ecCt1 leak e kemMat.pk kemMat.ciphertext kStar t).run).run
      (hideState e s) =ᵈ
    Prod.map id (hideState e) <$>
      ((honestStopped kem onoff ecEk ecCt0 ecCt1 leak kemMat e kStar t).run).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · apply evalDistEq_lift_stopOnState_map
      (SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 kemMat e s))
      (SCKAScheme.sckaCorrectnessImpl (simScheme kem onoff ecEk ecCt0 ecCt1 leak kemMat e s))
      (hideState e) (fun u => decide (e ∈ u.exposed)) t s
      (correctnessOracle_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e t s hs)
    intro res hres
    have h := (SCKAScheme.correctnessImpl_securitySets_eq _ t s res hres).1
    simp [h, he]
  · cases u
    exact oracleSendArleak_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e s he
  · cases u
    exact oracleSendBrleak_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e s he hs
  · apply evalDistEq_lift_stopOnState_map
      (pinnedChallenge onoff e kStar) (challenge onoff e kStar)
      (hideState e) (fun u => decide (e ∈ u.exposed)) t s
      (ToVCVio.evalDistEq_of_eq (challenge_hide onoff e kStar t s))
    intro res hres
    simp [((pinnedChallenge_recordsChallenges onoff e kStar).exposed_nA_eq t s res hres).1, he]
  · cases u
    exact ToVCVio.evalDistEq_of_eq (corruptA_hide kem onoff e s he)
  · cases u
    exact ToVCVio.evalDistEq_of_eq (corruptB_hide kem onoff e s he)

end

/-! ## Whole runs -/

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

include hDet hEk hCt0 hCt1 in
/-- Let `kemMat ∈ support (sampleMaterial leak)`, and let `s` be a state consistent with a protocol
transcript (`reachableInv s`) in which `e` is unexposed and A's key pair and B's offline
encapsulation output at `e`, when present, are those of `kemMat` (`consistentMat kemMat e s`).
Then `adv` accepts with the same probability against
`simOracle … e kemMat.pk kemMat.ciphertext kStar` from `hideState e s` and against
`honestStopped … kemMat e kStar` from `s`. -/
private theorem optionRun_hide_eq
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hsrc : consistentMat kemMat e s) (he : e ∉ s.exposed) :
    Pr{let x ← (optionRun
      (simOracle kem onoff ecEk ecCt0 ecCt1 leak e kemMat.pk kemMat.ciphertext kStar)
      adv (hideState e s))}[x = true] =
    Pr{let x ← (optionRun
        (honestStopped kem onoff ecEk ecCt0 ecCt1 leak kemMat e kStar) adv s)}[x = true] := by
  apply prEvent_optionRun_eq_of_state_map _ _ (hideState e)
    (fun s => (reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧ consistentMat kemMat e s) ∧
      e ∉ s.exposed)
  · intro t s hs res hres hcont
    change res ∈ support (do
      let out ← (honestOracle kem onoff ecEk ecCt0 ecCt1 leak kemMat e kStar t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hres
    obtain ⟨out, hout, hres⟩ := (mem_support_bind_iff _ _ _).mp hres
    obtain rfl := (mem_support_pure_iff _ _).mp hres
    have hex : e ∉ out.2.exposed := by
      by_contra h
      simp only [h, decide_true, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at hcont
    exact ⟨honestScheme_preserves_reachableInv_consistentMat kem onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak kemMat hm e _ (pinnedChallenge_recordsChallenges onoff e kStar)
      t s hs.1 out hout, hex⟩
  · intro t s hs
    exact simOracle_hide kem onoff ecEk ecCt0 ecCt1 leak kemMat e kStar t s hs.1.1 hs.2
  · exact ⟨⟨hs, hsrc⟩, he⟩

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- `hideState e` maps the initial game state to the simulator's initial state. -/
private theorem hideState_initial (e : ℕ) :
    hideState e (oppUniKemCKA.Reduction.Internal.initialGame (Sym := Sym) kem onoff) =
      initial onoff := by
  simp [hideState, hideA, hideB, initial, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

include hDet hEk hCt0 hCt1 in
/-- For `kemMat ∈ support (sampleMaterial leak)`, the simulator run `run` (`Simulator`) satisfies
`Pr[run adv e kemMat.pk kemMat.ciphertext kStar = true] =
Pr[optionRun (honestStopped kemMat e kStar) adv s₀ = true]`. -/
theorem run_eq_honestStopped
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym) :
    Pr{let x ← (run
        kem onoff ecEk ecCt0 ecCt1 leak adv e kemMat.pk kemMat.ciphertext kStar)}[x = true] =
    Pr{let x ← (optionRun (honestStopped kem onoff ecEk ecCt0 ecCt1 leak kemMat e kStar)
      adv (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] := by
  have hrun : run kem onoff ecEk ecCt0 ecCt1 leak adv e kemMat.pk kemMat.ciphertext kStar =
      optionRun (simOracle kem onoff ecEk ecCt0 ecCt1 leak e
        kemMat.pk kemMat.ciphertext kStar) adv (initial onoff) := by
    simp [run, optionRun, StateT.run'_eq, bind_pure_comp, Functor.map_map]
  rw [hrun, ← hideState_initial kem onoff e]
  exact optionRun_hide_eq kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak kemMat hm e kStar adv _
    (reachableInv_init kem onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
    (consistentMat_initial kem onoff leak kemMat e)
    (by simp [oppUniKemCKA.Reduction.Internal.initialGame, SCKAScheme.initGameState])

include hDet hEk hCt0 hCt1 in
/-- `Pr[fixedBranch adv e b = true] =
Pr[kemMat ← sampleMaterial leak; k ←$ K; optionRun (honestStopped kemMat e k_x) adv s₀ = true]`,
where `x` is `real` for `b = true` and `random` for `b = false`, so `k_x` is `kemMat.key` or `k`.
-/
theorem fixedBranch_eq_honestStopped
    (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) :
    Pr{let x ← fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv e b}[x = true] =
    Pr{let x ← (do
      let kemMat ← sampleMaterial leak
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped kem onoff ecEk ecCt0 ecCt1 leak kemMat e
        (if b then kemMat.key else k)) adv
        (oppUniKemCKA.Reduction.Internal.initialGame kem onoff))}[x = true] := by
  rw [fixedBranch_eq_material]
  simp only [map_bind]
  refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kemMat hm => ?_
  refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun k _ => ?_
  exact run_eq_honestStopped kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak kemMat hm e _ adv

end

end oppUniKemCKA.Security.Embedding
