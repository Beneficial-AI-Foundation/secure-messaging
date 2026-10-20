/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints

/-!
# Sampling stages

**Setting.** Let `m` be complete material, `e` a selected epoch, and `b` a mode bit. Each
sampling phase of epoch `e` is either *pinned*, returning its stored output in `m`, or *fresh*,
sampling at its protocol call. A `Stage` fixes this choice for each phase:

| `Stage` | key generation | offline encapsulation | online encapsulation |
| --- | --- | --- | --- |
| `onlineFresh` | pinned | pinned | fresh |
| `encapsFresh` | pinned | fresh | fresh |
| `fresh` | fresh | fresh | fresh |

The pinned hybrid `hybridOracle m e b` pins all three phases. The modules
`OnlineDeferral`, `OfflineDeferral`, and `KeygenDeferral` relate it to `onlineFresh`, then
`encapsFresh`, then `fresh`, each making one more phase fresh.

**Definitions.**

- `schemeAt stage m e s`: Opp-UniKEM for a query from game state `s`, with the KEM
  `Pinned.kem m` pinning each phase that `stage` pins and whose party is at epoch `e`;
  decapsulation returns B's recorded key for A's current epoch.
- `oracle stage m e b := securityImplAt (schemeAt stage m e) (challOf (adjacentMode e b))`;
  `stopped stage m e b` stops it at the first query whose successor state exposes `e`.

**Results.** `oracle_fresh_eq_ideal`: `oracle .fresh m e b` is the ideal game's oracle
`idealSecurityImpl (adjacentMode e b)`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- The selected-epoch sampling phases that return stored outputs (*pinned*); the other
phases sample at their protocol calls (*fresh*). -/
inductive Stage where
  /-- Online encapsulation is fresh; key generation and offline encapsulation are pinned. -/
  | onlineFresh
  /-- Both encapsulation phases are fresh; key generation is pinned. -/
  | encapsFresh
  /-- All three phases are fresh. -/
  | fresh
  deriving DecidableEq

/-- Whether stage `stage` pins key generation at the selected epoch. -/
def Stage.pinsKeygen (stage : Stage) : Bool := decide (stage ≠ .fresh)

/-- Whether stage `stage` pins offline encapsulation at the selected epoch. -/
def Stage.pinsOffline (stage : Stage) : Bool := decide (stage = .onlineFresh)

/-- KEM of `schemeAt stage m e s`: `Pinned.kem m` pinning key generation and offline
encapsulation as `stage` does for parties at epoch `e`, never pinning online encapsulation,
with decapsulation result `s.keyB s.stA.t`. -/
abbrev stageKem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    KEMScheme ProbComp K PK SK C :=
  Pinned.kem m (stage.pinsKeygen && decide (s.stA.t = e))
    (stage.pinsOffline && decide (s.stB.t = e)) false (s.keyB s.stA.t)

/-- On/off structure of `stageKem stage m e s`. -/
abbrev stageOnOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (stageKem stage m e s).OnOffStructure :=
  Pinned.onOff m (stage.pinsKeygen && decide (s.stA.t = e))
    (stage.pinsOffline && decide (s.stB.t = e)) false (s.keyB s.stA.t)

/-- Leakage witnesses of `stageKem stage m e s`. -/
abbrev stageLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (stageKem stage m e s).OnOffRandLeak (stageOnOff stage m e s) :=
  Pinned.leakage leak m (stage.pinsKeygen && decide (s.stA.t = e))
    (stage.pinsOffline && decide (s.stB.t = e)) false (s.keyB s.stA.t)

/-- Opp-UniKEM for a query from game state `s` in stage `stage`: a phase returns its stored
output in `m` exactly when `stage` pins it and its party is at epoch `e`. Decapsulation returns
B's recorded key for A's current epoch. -/
abbrev schemeAt [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  let sa := stage.pinsKeygen && decide (s.stA.t = e)
  let soff := stage.pinsOffline && decide (s.stB.t = e)
  let key := s.keyB s.stA.t
  scheme (Pinned.kem m sa soff false key) (Pinned.onOff m sa soff false key)
    (Pinned.deterministic m sa soff false key) ecEk ecCt0 ecCt1
    (Pinned.leakage leak m sa soff false key)

/-- Security oracles of stage `stage`: a query from `s` is answered by `schemeAt stage m e s`,
with challenge oracle `challOf (adjacentMode e b)`. -/
def oracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  securityImplAt base onoff leak (schemeAt ecEk ecCt0 ecCt1 stage m e)
    (SCKAScheme.challOf (adjacentMode e b))

/-- `oracle stage m e b` stopped at the first query whose successor state exposes `e`: that
query answers `none`. -/
def stopped [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (OptionT (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp)) :=
  stopOnState (oracle base onoff ecEk ecCt0 ecCt1 leak stage m e b)
    (fun s => decide (e ∈ s.exposed))

/-- In every stage, A's receive in `schemeAt stage m e s` is `recvA` with decapsulation
replaced by the constant `s.keyB s.stA.t`, as in the ideal game. -/
theorem recvA_eq_ideal [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (msg : Message Sym) :
    (schemeAt ecEk ecCt0 ecCt1 stage m e s).recvA s.stA msg =
      recvA base onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  cases bit
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.stA.dkA <;> cases hc : s.stA.ct0 <;> cases hk : s.keyB s.stA.t
  all_goals
    simp only [schemeAt, scheme, recvA, hd, hc, hk,
      Option.bind_eq_bind, Option.pure_def]
    repeat' (split <;> simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Bool.and_eq_true, beq_iff_eq, Option.bind_some, Option.bind_none])

/-- The stage `fresh` pins no key generation. -/
theorem Stage.pinsKeygen_fresh_and (t e : ℕ) :
    (Stage.pinsKeygen .fresh && decide (t = e)) = false := by
  simp [Stage.pinsKeygen]

/-- The stage `fresh` pins no offline encapsulation. -/
theorem Stage.pinsOffline_fresh_and (t e : ℕ) :
    (Stage.pinsOffline .fresh && decide (t = e)) = false := by
  simp [Stage.pinsOffline]

/-- B's leaking send in `schemeAt .fresh m e s` is that of Opp-UniKEM over `base`. -/
theorem sendBrleak_fresh_eq [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (hDet : base.DeterministicDecaps)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB : StB onoff Sym) :
    (schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendBrleak stB =
    (scheme base onoff hDet ecEk ecCt0 ecCt1 leak).sendBrleak stB := by
  dsimp only [schemeAt]
  rw [Stage.pinsKeygen_fresh_and, Stage.pinsOffline_fresh_and]
  simp only [scheme]
  cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;> cases hct1 : stB.ct1 <;>
    cases hst : stB.stCt <;> cases hack : stB.ack.ctRec
  all_goals
    simp only [sendBrleak, hct0, hek, hct1]
    try dsimp only [Pinned.leakage]
    simp [hct0, hek, hct1, hst, hack, monad_norm]

/-- The ordinary-send version of `sendBrleak_fresh_eq`. -/
theorem sendB_fresh_eq [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (hDet : base.DeterministicDecaps)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB : StB onoff Sym) :
    (schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendB stB =
    (scheme base onoff hDet ecEk ecCt0 ecCt1 leak).sendB stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_fresh_eq base onoff ecEk ecCt0 ecCt1 leak hDet m e s stB]

/-- For every `m`, `e`, and `b`, `oracle .fresh m e b` equals the ideal game's oracle
`idealSecurityImpl (adjacentMode e b)`. -/
theorem oracle_fresh_eq_ideal [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) :
    oracle base onoff ecEk ecCt0 ecCt1 leak .fresh m e b =
      idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b) := by
  have hkg : Stage.pinsKeygen .fresh = false := rfl
  funext t
  apply StateT.ext
  intro s
  simp only [securityImplAt, oracle, StateT.run_bind, StateT.run_get, pure_bind]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA, schemeAt, scheme, sendA, Pinned.kem, Pinned.onOff,
        Pinned.keygen,
        hkg, Bool.false_and, Bool.false_eq_true, if_false]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind]
      rw [sendB_fresh_eq base onoff ecEk ecCt0 ecCt1 leak hDet m e s _]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      cases hm : s.msgB n with
      | none =>
        simp only [oracleRecvAIdeal, schemeWithDecaps, SCKAScheme.oracleRecvA,
          StateT.run_bind, StateT.run_get, pure_bind, hm]
      | some entry =>
        rcases entry with ⟨msg, tsnd⟩
        simp only []
        rw [recvA_eq_ideal]
        simp only [oracleRecvAIdeal, schemeWithDecaps, SCKAScheme.oracleRecvA,
          StateT.run_bind, StateT.run_get, pure_bind, hm]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvB, schemeAt, scheme, recvB]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendArleak, schemeAt, scheme, sendArleak,
      Pinned.kem, Pinned.onOff, Pinned.leakage,
      hkg, Bool.false_and, Bool.false_eq_true, if_false]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind]
    rw [sendBrleak_fresh_eq base onoff ecEk ecCt0 ecCt1 leak hDet m e s _]
  · rfl
  · rfl
  · rfl

end oppUniKemCKA.Security.Embedding.Sampling
