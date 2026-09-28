/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.OppUniKEM.Security.IdealGame

/-!
# Successive deferral of the selected KEM samples

**Stages.** `fixed` uses all three components of material `m` at epoch `e`.
`onlineFresh` samples the online component at its actual protocol inputs.
`encapsFresh` also samples the offline component when requested. `fresh`
samples all three components when requested. Other epochs always sample
from the original KEM algorithms.

**Games.** Each stage uses the same auxiliary receive, hybrid challenge
mode, leakage guards, and stop-on-exposure rule. The first stage is the
pinned hybrid. The last stage is the ordinary auxiliary hybrid. Deferring
samples in this order makes the online sampler's public-key and offline-state
dependencies explicit.
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

/-- KEM whose three sampling phases are independently selected by Boolean
flags. Decapsulation returns the auxiliary result `key`. -/
abbrev kem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    KEMScheme ProbComp K PK SK C where
  keygen := Pinned.keygen m pinKeygen
  encaps pk := do
    let (st, ct0) ← Pinned.encapsOff m pinOffline
    let (ct1, k) ← Pinned.encapsOn m pinOnline st pk
    pure (onoff.split.symm (ct0, ct1), k)
  decaps _ _ := pure key

/-- Constant decapsulation for every choice of sampling flags. -/
abbrev deterministic {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure for the independently selected samplers, using the
original ciphertext split. Its encapsulation factorization is definitional. -/
abbrev onOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).OnOffStructure where
  St := onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := Pinned.encapsOff m pinOffline
  encapsOn := Pinned.encapsOn m pinOnline
  factor _ := rfl

/-- Leakage samplers return stored outputs and coins for pinned phases and
use the original leakage witness for fresh phases. Their marginals give
the corresponding ordinary samplers. -/
abbrev leakage {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).OnOffRandLeak
      (onOff m pinKeygen pinOffline pinOnline key) where
  KeygenRand := leak.KeygenRand
  OffRand := leak.OffRand
  OnRand := leak.OnRand
  keygenRleak := if pinKeygen then pure m.keygen else leak.keygenRleak
  encapsOffRleak := if pinOffline then pure m.off else leak.encapsOffRleak
  encapsOnRleak st pk := if pinOnline then pure m.on else leak.encapsOnRleak st pk
  keygen_fst := by cases pinKeygen <;> simp [Pinned.keygen, leak.keygen_fst]
  encapsOff_fst := by cases pinOffline <;> simp [Pinned.encapsOff, leak.encapsOff_fst]
  encapsOn_fst st pk := by cases pinOnline <;> simp [Pinned.encapsOn, leak.encapsOn_fst]

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
  scheme (kem m sa soff son key) (onOff m sa soff son key)
    (deterministic m sa soff son key) ecEk ecCt0 ecCt1 (leakage leak m sa soff son key)

/-- Full auxiliary oracle family for a sampling stage. Challenges follow
`adjacentMode e b`; every other operation uses the same SCKA interface and
exposure rules as the pinned hybrid. -/
def oracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  fun t => (get : StateT
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))) >>= fun s =>
    let scka := schemeAt ecEk ecCt0 ecCt1 stage m e s
    match (motive := ∀ query,
        StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
          ProbComp ((securitySpec leak Sym).Range query)) t with
    | .inl (.inl (.inl (.inl (.inl t)))) => SCKAScheme.sckaCorrectnessImpl scka t
    | .inl (.inl (.inl (.inl (.inr u)))) => SCKAScheme.oracleSendArleak sendExposureA scka u
    | .inl (.inl (.inl (.inr u))) => SCKAScheme.oracleSendBrleak sendExposureB scka u
    | .inl (.inl (.inr t)) =>
      SCKAScheme.oracleChall (adjacentMode e b t) (StA onoff Sym) (StB onoff Sym) K (Message Sym) t
    | .inl (.inr u) =>
      SCKAScheme.oracleCorruptA (vulnA base onoff) (StB onoff Sym) K (Message Sym) u
    | .inr u =>
      SCKAScheme.oracleCorruptB (vulnB base onoff) (StA onoff Sym) K (Message Sym) u

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

/-- For every material value, epoch, mode, and query, the fully pinned
sampling stage equals the pinned hybrid oracle as a stateful computation. -/
theorem oracle_fixed_eq_hybrid [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) :
    oracle base onoff ecEk ecCt0 ecCt1 leak .fixed m e b =
      hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e b := by
  funext t
  apply StateT.ext
  intro s
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals
    simp only [oracle, hybridOracle, honestOracle, StateT.run_bind,
      StateT.run_get, pure_bind] <;> rfl


/-- For every material value, epoch, and state, the fully fresh scheme is
the original protocol with constant auxiliary decapsulation. The material
value has no effect on any of its algorithms. -/
theorem schemeAt_fresh_eq [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    schemeAt ecEk ecCt0 ecCt1 .fresh m e s =
      scheme (keyDecapsKEM base (s.keyB s.stA.t))
        (keyDecapsOnOff base onoff (s.keyB s.stA.t))
        (keyDecapsDet base (s.keyB s.stA.t)) ecEk ecCt0 ecCt1
        (keyDecapsLeak base onoff leak (s.keyB s.stA.t)) := by
  rcases base with ⟨kg, enc, dec⟩
  rcases onoff with ⟨St, C₀, C₁, split, off, online, factor⟩
  have hfactor : enc = (fun pk => do
      let out ← off
      let result ← online out.1 pk
      pure (split.symm (out.2, result.1), result.2)) := funext factor
  subst enc
  rfl


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
  funext t
  apply StateT.ext
  intro s
  simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind]
  rw [schemeAt_fresh_eq base onoff ecEk ecCt0 ecCt1 leak m e s]
  have hsend : sendB (keyDecapsKEM base (s.keyB s.stA.t))
      (keyDecapsOnOff base onoff (s.keyB s.stA.t)) ecCt0 ecCt1 s.stB =
      sendB base onoff ecCt0 ecCt1 s.stB := by
    cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
      cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
    all_goals
      simp only [sendB, hc0, hp, hc1, hst, ha, pure_bind,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hleak : sendBrleak (keyDecapsKEM base (s.keyB s.stA.t))
      (keyDecapsOnOff base onoff (s.keyB s.stA.t)) ecCt0 ecCt1
      (keyDecapsLeak base onoff leak (s.keyB s.stA.t)) s.stB =
      sendBrleak base onoff ecCt0 ecCt1 leak s.stB := by
    cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
      cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
    all_goals
      simp only [sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals first | rfl | skip
    simp only [idealSecurityImpl, SCKAScheme.sckaCorrectnessImpl,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, SCKAScheme.oracleSendB,
      StateT.run_bind, StateT.run_get, pure_bind]
    dsimp only [scheme]
    rw [hsend]
  all_goals first | rfl | skip
  simp only [idealSecurityImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
    SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only [scheme]
  rw [hleak]
  apply bind_congr
  rintro ⟨out, next⟩
  cases out with
  | none => rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    cases coins <;> cases key <;> rfl


/-- For every material value and sampling flags, A's exposure annotation
for the staged KEM equals the original annotation on the same local states
and returned coins. It depends only on the epoch and coin constructor. -/
theorem sendExposureA_eq
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (sa soff son : Bool) (key : Option K) :
    sendExposureA (onoff := onOff m sa soff son key) (Sym := Sym)
      (KeygenRand := leak.KeygenRand) (OffRand := leak.OffRand) (OnRand := leak.OnRand) =
    sendExposureA (onoff := onoff) := by
  funext old next coins
  cases coins <;> rfl

/-- For every material value and sampling flags, B's exposure annotation
for the staged KEM equals the original annotation on the same local states
and returned coins, including the combined offline/online constructor. -/
theorem sendExposureB_eq
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (sa soff son : Bool) (key : Option K) :
    sendExposureB (onoff := onOff m sa soff son key) (Sym := Sym)
      (KeygenRand := leak.KeygenRand) (OffRand := leak.OffRand) (OnRand := leak.OnRand) =
    sendExposureB (onoff := onoff) := by
  funext old next coins
  cases coins <;> rfl


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
      recvA (keyDecapsKEM base (s.keyB s.stA.t))
        (keyDecapsOnOff base onoff (s.keyB s.stA.t))
        (keyDecapsDet base (s.keyB s.stA.t)) ecCt0 ecCt1 s.stA msg := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  cases bit
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.stA.dkA <;> cases hc : s.stA.ct0 <;> cases hk : s.keyB s.stA.t
  all_goals
    simp only [schemeAt, scheme, recvA, hd, hc, deterministic, hk]
    repeat' (split <;> simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Bool.and_eq_true, beq_iff_eq, Option.some.injEq, Prod.mk.injEq, true_and])

end oppUniKemCKA.Security.Embedding.Sampling
