/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator
import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.Security

/-!
# Hiding challenge-epoch secrets in honest states

**Setting.** Throughout this module, we consider:

- a challenge epoch `e` and a candidate key `kStar`;
- pre-sampled epoch material `kemMat : KEMMaterial leak` (`Simulator`), bundling the outputs and
  coins of the three sampling phases of one epoch (key generation, offline encapsulation, and online
  encapsulation);
- the simulator's secret values (`Simulator`), wrapped in `Option` (`some x` when known to the
  simulator and `none` when hidden);
- the pinned KEM `Pinned.kem kemMat` (`Simulator`), whose designated sampling phases return the
  corresponding outputs stored in `kemMat`;
- the simulator `simOracle` (`Simulator`), which runs over the simulated KEM `simKem` embedding the
  IND-CPA challenge at epoch `e`.

**Main results.** For an honest game state `s`, the state map `hideState e s` hides the secret
values of epoch `e` (party A's decapsulation key, party B's offline state, and the keys recorded at
`e`) by setting them to `none` and wraps all other secret values in `some`.

- Each local send and receive over the simulated KEM `simKem` from a hidden state equals the same
  operation over `Pinned.kem kemMat` from the honest state, followed by hiding (`*_hide`).
- The simulator's challenge oracle from `hideState e s` coincides with the *pinned challenge*
  `pinnedChallenge e kStar := challengeWith id e kStar` from `s`, followed by `hideState e`
  (`challenge_hide`).
- Revealing a local state fails (`none`) if and only if a corruption exposes epoch `e`
  (`revealA_hideA_eq`, `revealB_hideB_eq`).
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

/-- Every possible successful result of `sendA stA` has key component `none`. -/
theorem sendA_key_none (stA : StA onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (t : ℕ) (next : StA onoff Sym)
    (hout : some (key, msg, t, next) ∈ support (sendA kem onoff ecEk stA)) :
    key = none := by
  cases hd : stA.dkA <;> cases hp : stA.ekA <;> cases ha : stA.ack.ekRec <;>
    simp only [sendA, hd, hp, ha, Bool.false_eq_true, ↓reduceIte,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
  all_goals aesop

/-- A key `(t, k)` output by `sendB stB` has `t = stB.t` and `stB.ct1 = none`. -/
theorem sendB_key_fresh (stB : StB onoff Sym)
    (t : ℕ) (k : K) (msg : Message Sym) (tsnd : ℕ) (next : StB onoff Sym)
    (hout : some (some (t, k), msg, tsnd, next) ∈
      support (sendB kem onoff ecCt0 ecCt1 stB)) :
    t = stB.t ∧ stB.ct1 = none := by
  cases hc0 : stB.ct0 <;> cases hp : stB.ekA <;> cases hc1 : stB.ct1 <;>
    cases hst : stB.stCt <;> cases ha : stB.ack.ctRec <;>
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, mem_support_bind_iff,
      mem_support_pure_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq,
      Option.some_ne_none] at hout
  all_goals aesop

/-- `sendArleak stA` outputs no key and returns no coins or key-generation coins. -/
theorem sendArleak_shape
    (stA : StA onoff Sym) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StA onoff Sym)
    (coins : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, t, next, coins) ∈ support (sendArleak kem onoff ecEk leak stA)) :
    key = none ∧ (coins = .none ∨ ∃ r, coins = .keygen r) := by
  cases hd : stA.dkA <;> cases hp : stA.ekA <;> cases ha : stA.ack.ekRec <;>
    simp only [sendArleak, hd, hp, ha, Bool.false_eq_true, ↓reduceIte,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
  all_goals aesop

/-- `sendBrleak stB` returns no coins, offline coins, online coins, or both. -/
theorem sendBrleak_coins
    (stB : StB onoff Sym) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StB onoff Sym)
    (coins : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, t, next, coins) ∈
      support (sendBrleak kem onoff ecCt0 ecCt1 leak stB)) :
    coins = .none ∨ (∃ r, coins = .off r) ∨ (∃ r, coins = .on r) ∨
      (∃ r₀ r₁, coins = .offOn r₀ r₁) := by
  cases hc0 : stB.ct0 <;> cases hp : stB.ekA <;> cases hc1 : stB.ct1 <;>
    cases hst : stB.stCt <;> cases ha : stB.ack.ctRec <;>
    simp only [sendBrleak, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, mem_support_bind_iff,
      mem_support_pure_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq] at hout
  all_goals aesop

/-- Leaking version of `sendB_key_fresh`. -/
theorem sendBrleak_key_fresh
    (stB : StB onoff Sym) (t : ℕ) (k : K) (msg : Message Sym)
    (tsnd : ℕ) (next : StB onoff Sym)
    (coins : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (some (t, k), msg, tsnd, next, coins) ∈
      support (sendBrleak kem onoff ecCt0 ecCt1 leak stB)) :
    t = stB.t ∧ stB.ct1 = none := by
  apply sendB_key_fresh kem onoff ecCt0 ecCt1 stB t k msg tsnd next
  rw [← sendBrleak_forget kem onoff ecCt0 ecCt1 leak stB]
  exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩

/-- Under `reachableInv s` and `s.stB.ct1 = none`, no key is recorded for B's epoch `s.stB.t`. -/
theorem keys_none_before_online
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hc : s.stB.ct1 = none) :
    s.keyA s.stB.t = none ∧ s.keyB s.stB.t = none := by
  classical
  obtain ⟨T, hT⟩ := hs
  have hon : (T s.stB.t).on = none := by
    have h := hT.onB
    rw [hc] at h
    simpa using h
  have hk : (T s.stB.t).key = none := by simp [EpochTranscript.key, hon]
  rw [hT.keyA, hT.keyB, hk]
  simp

/-- Hide a secret value of epoch `t`: returns `none` if `t = e` and `some value` otherwise. -/
def hide {α : Type} (e t : ℕ) (value : α) : Option α :=
  if t = e then none else some value

variable {kem onoff} in
/-- Map party A's honest state `stA` to the simulator's state by hiding A's decapsulation key when
`stA.t = e`. -/
def hideA
    (e : ℕ) (stA : StA onoff Sym) : StateA (Option SK) PK onoff.C₀ Sym where
  dkA := stA.dkA.map (hide e stA.t)
  ekA := stA.ekA
  ct0 := stA.ct0
  t := stA.t
  ich := stA.ich
  lch := stA.lch
  ack := stA.ack

variable {kem onoff} in
/-- Map party B's honest state `stB` to the simulator's state by hiding B's offline state when
`stB.t = e`. -/
def hideB
    (e : ℕ) (stB : StB onoff Sym) : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym where
  ekA := stB.ekA
  ct0 := stB.ct0
  ct1 := stB.ct1
  stCt := stB.stCt.map (hide e stB.t)
  t := stB.t
  ich := stB.ich
  lch := stB.lch
  ack := stB.ack

variable {kem onoff} in
/-- Map an honest game state `s` to the simulator's state `SimState` by hiding the local secrets of
both parties and the recorded keys at epoch `e`. -/
def hideState
    (e : ℕ) (s : GameState onoff Sym) :
    SimState onoff Sym where
  stA := hideA e s.stA
  stB := hideB e s.stB
  keyA t := (s.keyA t).map (hide e t)
  keyB t := (s.keyB t).map (hide e t)
  msgA := s.msgA
  msgB := s.msgB
  nA := s.nA
  nB := s.nB
  tcurA := s.tcurA
  tcurB := s.tcurB
  exposed := s.exposed
  challenged := s.challenged
  correct := s.correct

/-- Hiding a key table commutes with recording `k` at epoch `t`. -/
theorem hide_update (e t : ℕ) (table : ℕ → Option K) (k : K) :
    (fun u => (Function.update table t (some k) u).map (hide e u)) =
      Function.update (fun u => (table u).map (hide e u)) t (some (hide e t k)) := by
  funext u
  by_cases h : u = t <;> simp [h, Function.update_of_ne]

variable {kem onoff} in
/-- `revealA (hideA e stA) = if e ∈ vulnCorrA stA then none else some stA`. -/
theorem revealA_hideA_eq (e : ℕ) (stA : StA onoff Sym) :
    revealA (hideA e stA) = if e ∈ vulnCorrA kem onoff stA then none else some stA := by
  rcases stA with ⟨dk, pk, ct, t, ich, lch, ack⟩
  cases dk <;> by_cases ht : t = e <;>
    simp_all [revealA, revealField, hideA, hide, vulnCorrA, eq_comm]

variable {kem onoff} in
/-- B version of `revealA_hideA_eq`. -/
theorem revealB_hideB_eq (e : ℕ) (stB : StB onoff Sym) :
    revealB (hideB e stB) = if e ∈ vulnCorrB kem onoff stB then none else some stB := by
  rcases stB with ⟨pk, ct0, ct1, st, t, ich, lch, ack⟩
  cases st <;> by_cases ht : t = e <;>
    simp_all [revealB, revealField, hideB, hide, vulnCorrB, eq_comm]

variable {kem onoff} in
/-- The corruption-vulnerable epochs of `hideA e stA` (`{t}` when holding a secret key, else `∅`)
equal `vulnCorrA stA`. -/
theorem hideA_vulnerable (e : ℕ) (stA : StA onoff Sym) :
    (if (hideA e stA).dkA.isSome then {(hideA e stA).t} else ∅) = vulnCorrA kem onoff stA := by
  cases h : stA.dkA <;> simp [hideA, vulnCorrA, h]

variable {kem onoff} in
/-- B version of `hideA_vulnerable`. -/
theorem hideB_vulnerable (e : ℕ) (stB : StB onoff Sym) :
    (if (hideB e stB).stCt.isSome then {(hideB e stB).t} else ∅) = vulnCorrB kem onoff stB := by
  cases h : stB.stCt <;> simp [hideB, vulnCorrB, h]

section

variable [DecidableEq Sym]

/-- `recvB stB msg` outputs no key. -/
theorem recvB_key_none (stB : StB onoff Sym) (msg : Message Sym)
    (key : Option (ℕ × K)) (t : ℕ) (next : StB onoff Sym)
    (h : recvB kem onoff ecEk stB msg = some (key, t, next)) : key = none := by
  unfold recvB at h
  repeat' split at h
  all_goals simp_all

/-- A key `(t, k)` output by A's receive with decapsulation result `key` has `t = stA.t` and
`key = some k`. -/
theorem recvA_key_source (key : Option K)
    (stA : StA onoff Sym) (msg : Message Sym)
    (t : ℕ) (k : K) (trcv : ℕ) (next : StA onoff Sym)
    (h : recvA kem onoff (fun _ _ => key) ecCt0 ecCt1 stA msg =
      some (some (t, k), trcv, next)) :
    t = stA.t ∧ key = some k := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  by_cases ht : stA.t = epoch
  all_goals
    simp only [recvA, ht, ↓reduceIte] at h
    repeat' split at h
    all_goals simp_all

/-- Party B's receive over the simulated KEM from `hideB e stB` equals `recvB stB msg` followed by
`hideB e`. -/
theorem recvB_hide (e : ℕ)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K))
    (stB : StB onoff Sym) (msg : Message Sym) :
    recvB (simKem kem onoff selectedA selectedB pkStar ctStar key)
      (simOnOff kem onoff selectedA selectedB pkStar ctStar key) ecEk (hideB e stB) msg =
      (recvB kem onoff ecEk stB msg).map (fun (_, t, u) => (none, t, hideB e u)) := by
  rcases msg with ⟨ch, ack, t, b⟩
  by_cases hadv : stB.t < t
  all_goals
    simp only [recvB, hideB, hadv, ↓reduceIte]
    repeat' (split <;> simp_all only [Option.map_none, Option.map_some])

set_option maxHeartbeats 800000 in
-- Splitting the receive branches also expands the state-hiding equations.
/-- Party A's receive over the simulated KEM with decapsulation result `key.map (hide e stA.t)` from
`hideA e stA` equals A's receive with result `key` from `stA`, followed by hiding the output key and
state. -/
theorem recvA_hide (e : ℕ)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option K)
    (stA : StA onoff Sym) (msg : Message Sym) :
    recvA (simKem kem onoff selectedA selectedB pkStar ctStar (key.map (hide e stA.t)))
      (simOnOff kem onoff selectedA selectedB pkStar ctStar (key.map (hide e stA.t)))
      (simDet kem onoff selectedA selectedB pkStar ctStar (key.map (hide e
        stA.t))).decapsDet
      ecCt0 ecCt1 (hideA e stA) msg =
      (recvA kem onoff (fun _ _ => key) ecCt0 ecCt1 stA msg).map
        (fun (out, t, u) =>
          (out.map (fun (epoch, k) => (epoch, hide e epoch k)), t, hideA e u)) := by
  rcases msg with ⟨ch, ack, t, b⟩
  cases b
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : stA.dkA <;> cases hc : stA.ct0 <;> cases hk : key
  all_goals
    simp only [recvA, hideA, hd, hc, Option.bind_eq_bind, Option.pure_def]
    repeat' (split <;> simp_all only [Option.bind_some, Option.bind_none,
      Option.map_none, Option.map_some])
  all_goals
    simp_all only [Fin.mk_one, Fin.isValue, Bool.and_eq_true, beq_iff_eq]
    repeat' (split <;> simp_all only [Option.map_none, Option.map_some, and_true,
      Bool.not_eq_true, Nat.add_eq_left, one_ne_zero, and_false, ↓reduceIte])

end

variable {kem} in
/-- Challenge oracle on honest game states: `challengeWith` reading recorded keys directly. -/
def pinnedChallenge [SampleableType K]
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K)
      (StateT (GameState onoff Sym) ProbComp) :=
  challengeWith id e kStar

variable {kem} in
/-- Running `challenge onoff e kStar t` from `hideState e s` coincides with running
`pinnedChallenge onoff e kStar t` from `s` and applying `hideState e` to the successor state. -/
theorem challenge_hide [SampleableType K]
    (e : ℕ) (kStar : K) (t : ℕ)
    (s : GameState onoff Sym) :
    (challenge onoff e kStar t).run (hideState e s) =
      Prod.map id (hideState e) <$> (pinnedChallenge onoff e kStar t).run s := by
  simp only [challenge, pinnedChallenge, challengeWith, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [hideState, hg, StateT.run_pure, Prod.map]
  · cases hA : s.keyA t <;> cases hB : s.keyB t
    all_goals
      simp only [hideState, hA, hB, Option.map_none, Option.map_some, hg, ↓reduceIte]
    all_goals
      by_cases hr : 0 < t ∧ t < e <;> by_cases ht : t = e <;>
        simp [hr, ht, hide, StateT.run_bind, StateT.run_set, StateT.run_pure,
          StateT.run_monadLift, monadLift_self,
          hideState, Prod.map]

variable {kem} in
/-- `pinnedChallenge` records challenges (`SCKAScheme.RecordsChallenges`). -/
theorem pinnedChallenge_recordsChallenges [SampleableType K]
    (e : ℕ) (kStar : K) :
    SCKAScheme.RecordsChallenges (pinnedChallenge (Sym := Sym) onoff e kStar) := by
  intro t s res hres
  by_cases helig : t ∈ s.exposed ∨ t ∈ s.challenged
  · left
    simp only [pinnedChallenge, challengeWith, StateT.run_bind, StateT.run_get, pure_bind, helig,
      ↓reduceIte, StateT.run_pure, mem_support_pure_iff] at hres
    rw [hres]
  · simp only [pinnedChallenge, challengeWith, StateT.run_bind, StateT.run_get, pure_bind, helig,
      ↓reduceIte] at hres
    repeat' split at hres
    all_goals
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_map, StateT.run_set,
        StateT.run_monadLift, monadLift_self, bind_pure_comp,
        map_pure, Functor.map_map, mem_support_pure_iff,
        support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hres
    all_goals
      first
      | (obtain rfl := hres; exact Or.inl rfl)
      | (obtain ⟨_, rfl⟩ := hres; exact Or.inr ⟨fun h => helig (Or.inl h), rfl⟩)

variable {kem} in
/-- For an eligible `e`, `pinnedChallenge e kStar e` from `s` is `pure (some kStar, s')`, where
`s'` adds `e` to `challenged`. -/
theorem pinnedChallenge_selected [SampleableType K]
    (e : ℕ) (kStar : K)
    (s : GameState onoff Sym)
    (helig : ¬(e ∈ s.exposed ∨ e ∈ s.challenged))
    (hkey : (s.keyA e).isSome ∨ (s.keyB e).isSome) :
    (pinnedChallenge onoff e kStar e).run s =
      pure (some kStar, { s with challenged := insert e s.challenged }) := by
  cases hA : s.keyA e <;> cases hB : s.keyB e
  all_goals try simp [hA, hB] at hkey
  all_goals simp [pinnedChallenge, challengeWith, helig, hA, hB, StateT.run_bind,
    StateT.run_get, StateT.run_set]

variable {kem} in
/-- Unless `t = e` and `e` is eligible, `pinnedChallenge e k t` and `pinnedChallenge e k' t` are
equal computations from `s`. -/
theorem pinnedChallenge_eq_of_unused [SampleableType K]
    (e t : ℕ) (k k' : K)
    (s : GameState onoff Sym)
    (h : ¬(t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))) :
    (pinnedChallenge onoff e k t).run s = (pinnedChallenge onoff e k' t).run s := by
  by_cases ht : t = e
  · subst t
    by_cases hg : e ∈ s.exposed ∨ e ∈ s.challenged
    · simp [pinnedChallenge, challengeWith, hg, StateT.run_bind, StateT.run_get]
    · have hk : s.keyA e = none ∧ s.keyB e = none := by
        cases hA : s.keyA e <;> cases hB : s.keyB e <;> simp_all
      simp [pinnedChallenge, challengeWith, hg, hk, StateT.run_bind, StateT.run_get]
  · simp only [pinnedChallenge, challengeWith, ht, ↓reduceIte]

variable {kem} in
/-- If every key recorded at `e` in `s` equals `kStar`, then from `s`,
`pinnedChallenge e kStar t = oracleChall (decide (0 < t ∧ t < e)) t`. -/
theorem pinnedChallenge_eq_recorded [SampleableType K]
    (e : ℕ) (kStar : K) (t : ℕ)
    (s : GameState onoff Sym)
    (hkey : ∀ k, s.keyA e = some k ∨ s.keyB e = some k → k = kStar) :
    (pinnedChallenge onoff e kStar t).run s =
      (SCKAScheme.oracleChall (decide (0 < t ∧ t < e))
        (StA onoff Sym) (StB onoff Sym) K (Message Sym) t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e with
      | none =>
        cases hB : s.keyB e with
        | none => simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA, hB]
        | some k =>
          have hk := hkey k (.inr hB)
          subst k
          simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA, hB]
      | some k =>
        have hk := hkey k (.inl hA)
        subst k
        simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA, hB, ht, hr]

/-- Hide each coin returned by a send in epoch `t` via `hide e t`. -/
def hideCoins {KG OFF ON : Type} (e t : ℕ) :
    SendRand KG OFF ON → SendRand (Option KG) (Option OFF) (Option ON)
  | .none => .none
  | .keygen r => .keygen (hide e t r)
  | .off r => .off (hide e t r)
  | .on r => .on (hide e t r)
  | .offOn r₀ r₁ => .offOn (hide e t r₀) (hide e t r₁)

/-- Party A's leaking send over the simulated KEM from `hideA e stA` (with A selected iff
`stA.t = e`) equals A's leaking send over `Pinned.kem kemMat` from `stA` followed by hiding the
state and coins; the output key is `none`. -/
theorem sendArleak_hide
    (kemMat : KEMMaterial leak) (e : ℕ) (selectedB : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (stA : StA onoff Sym) :
    sendArleak (simKem kem onoff (decide (stA.t = e)) selectedB kemMat.pk kemMat.ciphertext keyS)
      (simOnOff kem onoff (decide (stA.t = e)) selectedB kemMat.pk kemMat.ciphertext keyS)
      ecEk (simLeak kem onoff leak (decide (stA.t = e)) selectedB
        kemMat.pk kemMat.ciphertext keyS) (hideA e stA) =
    (fun out => out.map (fun (_, msg, epoch, next, coins) =>
      (none, msg, epoch, hideA e next, hideCoins e stA.t coins))) <$>
      sendArleak (Pinned.kem kemMat (decide (stA.t = e)) selectedB selectedB keyH)
        (Pinned.onOff kemMat (decide (stA.t = e)) selectedB selectedB keyH) ecEk
        (Pinned.leakage leak kemMat (decide (stA.t = e)) selectedB selectedB keyH) stA := by
  by_cases he : stA.t = e <;> cases hd : stA.dkA
  all_goals
    simp only [sendArleak, hideA, hd, Option.map_none, Option.map_some]
    simp [keygenLeak, hideCoins, hide, he, monad_norm]

set_option maxHeartbeats 1400000 in
-- Each leakage phase expands its output, coin conversion, and state update.
/-- B version of `sendArleak_hide`; the output key is also hidden via `hide e`. -/
theorem sendBrleak_hide
    (kemMat : KEMMaterial leak) (e : ℕ) (selectedA : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (stB : StB onoff Sym) :
    sendBrleak (simKem kem onoff selectedA (decide (stB.t = e)) kemMat.pk kemMat.ciphertext keyS)
      (simOnOff kem onoff selectedA (decide (stB.t = e)) kemMat.pk kemMat.ciphertext keyS)
      ecCt0 ecCt1 (simLeak kem onoff leak selectedA (decide (stB.t = e))
        kemMat.pk kemMat.ciphertext keyS) (hideB e stB) =
    (fun out => out.map (fun (key, msg, epoch, next, coins) =>
      (key.map (fun (t, k) => (t, hide e t k)), msg, epoch,
        hideB e next, hideCoins e stB.t coins))) <$>
      sendBrleak (Pinned.kem kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH)
        (Pinned.onOff kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH) ecCt0 ecCt1
        (Pinned.leakage leak kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH)
        stB := by
  by_cases he : stB.t = e <;> cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;>
    cases hct1 : stB.ct1 <;> cases hst : stB.stCt <;> cases hack : stB.ack.ctRec
  all_goals
    simp only [sendBrleak, hideB, hct0, hek, hct1, hst, Option.map_none, Option.map_some]
    simp [offLeak, onLeak, KEMMaterial.ciphertext, hideCoins, hide,
      he, hct0, hek, hct1, hst, hack, monad_norm]

/-- Ordinary-send version of `sendArleak_hide`. -/
theorem sendA_hide
    (kemMat : KEMMaterial leak) (e : ℕ) (selectedB : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (stA : StA onoff Sym) :
    sendA (simKem kem onoff (decide (stA.t = e)) selectedB kemMat.pk kemMat.ciphertext keyS)
      (simOnOff kem onoff (decide (stA.t = e)) selectedB kemMat.pk kemMat.ciphertext keyS)
      ecEk (hideA e stA) =
    (fun out => out.map (fun (_, msg, epoch, next) => (none, msg, epoch, hideA e next))) <$>
      sendA (Pinned.kem kemMat (decide (stA.t = e)) selectedB selectedB keyH)
        (Pinned.onOff kemMat (decide (stA.t = e)) selectedB selectedB keyH) ecEk stA := by
  rw [sendA_eq_map_sendArleak _ _ ecEk
      (simLeak kem onoff leak (decide (stA.t = e)) selectedB kemMat.pk kemMat.ciphertext keyS),
    sendA_eq_map_sendArleak _ _ ecEk
      (Pinned.leakage leak kemMat (decide (stA.t = e)) selectedB selectedB keyH),
    sendArleak_hide kem onoff ecEk leak kemMat e selectedB keyS keyH stA,
    Functor.map_map, Functor.map_map]
  congr 1
  funext out
  rcases out with _ | ⟨key, msg, epoch, next, coins⟩ <;> rfl

/-- Ordinary-send version of `sendBrleak_hide`. -/
theorem sendB_hide
    (kemMat : KEMMaterial leak) (e : ℕ) (selectedA : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (stB : StB onoff Sym) :
    sendB (simKem kem onoff selectedA (decide (stB.t = e)) kemMat.pk kemMat.ciphertext keyS)
      (simOnOff kem onoff selectedA (decide (stB.t = e)) kemMat.pk kemMat.ciphertext keyS)
      ecCt0 ecCt1 (hideB e stB) =
    (fun out => out.map (fun (key, msg, epoch, next) =>
      (key.map (fun (t, k) => (t, hide e t k)), msg, epoch, hideB e next))) <$>
      sendB (Pinned.kem kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH)
        (Pinned.onOff kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH)
        ecCt0 ecCt1 stB := by
  rw [sendB_eq_map_sendBrleak
      (simKem kem onoff selectedA (decide (stB.t = e)) kemMat.pk kemMat.ciphertext keyS)
      (simOnOff kem onoff selectedA (decide (stB.t = e)) kemMat.pk kemMat.ciphertext keyS)
      ecCt0 ecCt1
      (simLeak kem onoff leak selectedA (decide (stB.t = e)) kemMat.pk kemMat.ciphertext keyS),
    sendB_eq_map_sendBrleak
      (Pinned.kem kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH)
      (Pinned.onOff kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH) ecCt0 ecCt1
      (Pinned.leakage leak kemMat selectedA (decide (stB.t = e)) (decide (stB.t = e)) keyH),
    sendBrleak_hide kem onoff ecCt0 ecCt1 leak kemMat e selectedA keyS keyH stB,
    Functor.map_map, Functor.map_map]
  congr 1
  funext out
  rcases out with _ | ⟨key, msg, epoch, next, coins⟩ <;> rfl

end oppUniKemCKA.Security.Embedding
