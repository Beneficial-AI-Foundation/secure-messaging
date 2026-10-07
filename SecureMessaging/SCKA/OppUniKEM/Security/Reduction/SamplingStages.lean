/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints

/-!
# Sampling stages

**Setting.** Fix complete material `m`, a selected epoch `e`, and a mode bit `b`.

**Definitions.**

- `Stage`: `fixed` uses the stored key-generation, offline, and online outputs of `m` at epoch
  `e`; `onlineFresh` samples online encapsulation at its protocol call; `encapsFresh` also
  samples offline encapsulation there; `fresh` samples all three phases there.
- `schemeAt stage m e s`: Opp-UniKEM with the KEM `Pinned.kem m` flagging the phases that `stage`
  keeps stored and whose party is at epoch `e`; decapsulation returns B's recorded key.
- `oracle stage m e b := securityImplAt (schemeAt stage m e) (challOf (adjacentMode e b))`, and
  `stopped` stops it after the first query exposing `e`. The stage `fixed` is the pinned hybrid.

**Results.** `oracle_fresh_eq_ideal`: the stage `fresh` is the auxiliary game with mode
`adjacentMode e b`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- Four successive games, distinguished by which selected-epoch sampling
phases use stored material and which sample at the protocol call. -/
inductive Stage where
  /-- Key generation, offline encapsulation, and online encapsulation use stored outputs. -/
  | fixed
  /-- Online encapsulation samples at its actual inputs; the two source phases remain fixed. -/
  | onlineFresh
  /-- Both encapsulation phases sample at their protocol calls; key generation remains fixed. -/
  | encapsFresh
  /-- All three phases sample at their protocol calls. -/
  | fresh
  deriving DecidableEq

/-- Whether stage `stage` pins key generation at the selected epoch. -/
def Stage.pinsKeygen (stage : Stage) : Bool := decide (stage ≠ .fresh)

/-- Whether stage `stage` pins offline encapsulation at the selected epoch. -/
def Stage.pinsOffline (stage : Stage) : Bool :=
  decide (stage = .fixed ∨ stage = .onlineFresh)

/-- Whether stage `stage` pins online encapsulation at the selected epoch. -/
def Stage.pinsOnline (stage : Stage) : Bool := decide (stage = .fixed)

/-- Protocol scheme for a single query from state `s` in sampling stage
`stage`. A phase is pinned exactly when the stage pins it and its party is
at the selected epoch. Auxiliary decapsulation uses B's recorded key. -/
abbrev schemeAt [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  let sa := stage.pinsKeygen && decide (s.stA.t = e)
  let soff := stage.pinsOffline && decide (s.stB.t = e)
  let son := stage.pinsOnline && decide (s.stB.t = e)
  let key := s.keyB s.stA.t
  scheme (Pinned.kem m sa soff son key) (Pinned.onOff m sa soff son key)
    (Pinned.deterministic m sa soff son key) ecEk ecCt0 ecCt1
    (Pinned.leakage leak m sa soff son key)

/-- Sampling-stage game: the protocol instance `schemeAt stage m e s` with the hybrid challenge
oracle `challOf (adjacentMode e b)`. -/
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

/-- Stop a staged auxiliary execution after any query exposing epoch `e`.
The optional response denotes continuation or termination. -/
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

/-- For every sampling stage, material value, epoch, state, and input
message, A's receive equals auxiliary receive with B's recorded key as
constant decapsulation result. Sampling-stage choices affect send algorithms. -/
theorem recvA_eq_auxiliary [DecidableEq Sym]
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

/-- Fresh-stage pin flags combined with any epoch test are all `false`. -/
theorem Stage.pinsKeygen_fresh_and (t e : ℕ) :
    (Stage.pinsKeygen .fresh && decide (t = e)) = false := by
  simp [Stage.pinsKeygen]
theorem Stage.pinsOffline_fresh_and (t e : ℕ) :
    (Stage.pinsOffline .fresh && decide (t = e)) = false := by
  simp [Stage.pinsOffline]
theorem Stage.pinsOnline_fresh_and (t e : ℕ) :
    (Stage.pinsOnline .fresh && decide (t = e)) = false := by
  simp [Stage.pinsOnline]

/-- B's leaking send in the fully fresh stage equals the original leaking send. -/
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
  rw [Stage.pinsKeygen_fresh_and, Stage.pinsOffline_fresh_and, Stage.pinsOnline_fresh_and]
  simp only [scheme]
  cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;> cases hct1 : stB.ct1 <;>
    cases hst : stB.stCt <;> cases hack : stB.ack.ctRec
  all_goals
    simp only [sendBrleak, hct0, hek, hct1]
    try dsimp only [Pinned.leakage]
    simp [hct0, hek, hct1, hst, hack, monad_norm]

/-- B's ordinary send in the fully fresh stage equals the original ordinary send. Derived from
`sendBrleak_fresh_eq` by forgetting the coins. -/
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

/-- For every material value, epoch, and mode, the fully fresh sampling
oracle equals the auxiliary oracle with challenge mode `adjacentMode e b`.
All sampling uses the original KEM algorithms. -/
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
        rw [recvA_eq_auxiliary]
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
