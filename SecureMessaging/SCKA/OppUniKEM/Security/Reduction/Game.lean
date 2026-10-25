/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Receive

/-!
# Pinned protocol instances and the honest intermediate game

**Setting.** Throughout this module, we consider:

- a challenge epoch `e` and a candidate key `kStar`;
- a *KEM material* `kemMat : KEMMaterial leak` (`Simulator`), that is, a pre-sampled record of the
  outputs and coins produced by the sampling phases of a single epoch (key generation, offline
  encapsulation, and online encapsulation);
- the pinned KEM `Pinned.kem kemMat` (`Simulator`), whose designated sampling phases return the
  corresponding outputs stored in `kemMat` and whose decapsulation returns a prescribed key;
- the transcript consistency invariant `reachableInv` (`Correctness.Invariant`), stating that a game
  state is consistent with a transcript of the protocol.

**Definitions.** A *stage* (`Stage`) selects which sampling phases of epoch `e` are *pinned*,
reading their output from `kemMat`, and which are *fresh*, sampling at their protocol call. The
instance `stageScheme stage kemMat e s` is Opp-UniKEM over the KEM pinned accordingly, for a query
from state `s`, with A outputting B's recorded key instead of decapsulating; the *honest instance*
`honestScheme kemMat e s` is its fully pinned stage.

**Main results.** The *honest intermediate game* `honestStopped kemMat e kStar` runs the security
oracles over `honestScheme kemMat e` with the challenges of `pinnedChallenge e kStar` (`Relation`),
and stops at the first exposure of `e`.

- Party A's receive in `stageScheme stage kemMat e s` is the protocol receive with decapsulation
  replaced by the lookup of B's recorded key (`stageScheme_recvA_eq_ideal`).
- For possible material and a challenge oracle that only records challenges, the security oracles
  over `honestScheme kemMat e` preserve `reachableInv`, `consistentMat kemMat e` (the stored
  key-generation and offline outputs of epoch `e` are those of `kemMat`), and the property that
  every key B records at `e` is `kemMat.key`
  (`honestScheme_preserves_simulationInv`, `honestScheme_preserves_keyB_eq`).
-/

/-! ## Pinned protocol instances -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Which sampling phases of the challenge epoch are *pinned*, reading their output from the KEM
material, and which are *fresh*, sampling at their protocol call:

| `Stage`       | key generation | offline encapsulation | online encapsulation |
| ------------- | -------------- | --------------------- | -------------------- |
| `pinned`      | pinned         | pinned                | pinned               |
| `onlineFresh` | pinned         | pinned                | fresh                |
| `encapsFresh` | pinned         | fresh                 | fresh                |
| `fresh`       | fresh          | fresh                 | fresh                |
-/
inductive Stage where
  /-- All three phases are pinned. -/
  | pinned
  /-- Online encapsulation is fresh; key generation and offline encapsulation are pinned. -/
  | onlineFresh
  /-- Both encapsulation phases are fresh; key generation is pinned. -/
  | encapsFresh
  /-- All three phases are fresh. -/
  | fresh
  deriving DecidableEq

/-- The key-generation flag of `Pinned.kem` at `stage`: `sel` (whether A is at the challenge epoch)
if `stage` pins key generation, and `false` otherwise. -/
def Stage.keygenFlag : Stage → Bool → Bool
  | .pinned, sel => sel
  | .onlineFresh, sel => sel
  | .encapsFresh, sel => sel
  | .fresh, _ => false

/-- The offline-encapsulation flag of `Pinned.kem` at `stage`: `sel` (whether B is at the challenge
epoch) if `stage` pins offline encapsulation, and `false` otherwise. -/
def Stage.offlineFlag : Stage → Bool → Bool
  | .pinned, sel => sel
  | .onlineFresh, sel => sel
  | .encapsFresh, _ => false
  | .fresh, _ => false

/-- The online-encapsulation flag of `Pinned.kem` at `stage`: `sel` (whether B is at the challenge
epoch) if `stage` pins online encapsulation, and `false` otherwise. -/
def Stage.onlineFlag : Stage → Bool → Bool
  | .pinned, sel => sel
  | .onlineFresh, _ => false
  | .encapsFresh, _ => false
  | .fresh, _ => false

/-- KEM of `stageScheme stage kemMat e s`: `Pinned.kem kemMat` pinning the phases of `stage` at
epoch `e` (A's key generation if `s.stA.t = e`, B's encapsulations if `s.stB.t = e`), with
decapsulation returning `s.keyB s.stA.t`. -/
abbrev stageKem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    KEMScheme ProbComp K PK SK C :=
  Pinned.kem kemMat (stage.keygenFlag (decide (s.stA.t = e)))
    (stage.offlineFlag (decide (s.stB.t = e))) (stage.onlineFlag (decide (s.stB.t = e)))
    (s.keyB s.stA.t)

/-- On/off structure of `stageKem stage kemMat e s`. -/
abbrev stageOnOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (stageKem stage kemMat e s).OnOffStructure :=
  Pinned.onOff kemMat (stage.keygenFlag (decide (s.stA.t = e)))
    (stage.offlineFlag (decide (s.stB.t = e))) (stage.onlineFlag (decide (s.stB.t = e)))
    (s.keyB s.stA.t)

/-- Deterministic-decapsulation witness of `stageKem stage kemMat e s`. -/
abbrev stageDet {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (stageKem stage kemMat e s).DeterministicDecaps :=
  Pinned.deterministic kemMat (stage.keygenFlag (decide (s.stA.t = e)))
    (stage.offlineFlag (decide (s.stB.t = e))) (stage.onlineFlag (decide (s.stB.t = e)))
    (s.keyB s.stA.t)

/-- Leakage witnesses of `stageKem stage kemMat e s`. -/
abbrev stageLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (stageKem stage kemMat e s).OnOffRandLeak (stageOnOff stage kemMat e s) :=
  Pinned.leakage leak kemMat (stage.keygenFlag (decide (s.stA.t = e)))
    (stage.offlineFlag (decide (s.stB.t = e))) (stage.onlineFlag (decide (s.stB.t = e)))
    (s.keyB s.stA.t)

/-- Opp-UniKEM over `stageKem stage kemMat e s`, for a query from game state `s`. -/
abbrev stageScheme [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  let sa := stage.keygenFlag (decide (s.stA.t = e))
  let soff := stage.offlineFlag (decide (s.stB.t = e))
  let son := stage.onlineFlag (decide (s.stB.t = e))
  let key := s.keyB s.stA.t
  scheme (Pinned.kem kemMat sa soff son key) (Pinned.onOff kemMat sa soff son key)
    (Pinned.deterministic kemMat sa soff son key) ecEk ecCt0 ecCt1
    (Pinned.leakage leak kemMat sa soff son key)

/-- The *honest instance*: Opp-UniKEM with every sampling phase of epoch `e` pinned to `kemMat`,
that is, `stageScheme .pinned kemMat e s`. -/
abbrev honestScheme [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  stageScheme ecEk ecCt0 ecCt1 .pinned kemMat e s

/-- Party A's receive transition in `stageScheme stage kemMat e s` equals `recvA` with
decapsulation replaced by the lookup `fun _ _ => s.keyB s.stA.t`. -/
theorem stageScheme_recvA_eq_ideal [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (msg : Message Sym) :
    (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s).recvA s.stA msg =
      recvA base onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  cases bit
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.stA.dkA <;> cases hc : s.stA.ct0 <;> cases hk : s.keyB s.stA.t
  all_goals
    simp only [stageScheme, scheme, recvA, hd, hc, hk,
      Option.bind_eq_bind, Option.pure_def]
    repeat' (split <;> simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Bool.and_eq_true, beq_iff_eq, Option.bind_some, Option.bind_none])

/-! ## The honest intermediate game -/

/-- The simulator's protocol instance at honest state `s`: Opp-UniKEM over the simulated KEM `kem`
with challenge `(kemMat.pk, kemMat.ciphertext)`, A selected iff `s.stA.t = e`, and B selected iff
`s.stB.t = e`. -/
abbrev simScheme [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  let sa := decide (s.stA.t = e)
  let sb := decide (s.stB.t = e)
  let key := (s.keyB s.stA.t).map (hide e s.stA.t)
  scheme (kem base onoff sa sb kemMat.pk kemMat.ciphertext key)
    (onOff base onoff sa sb kemMat.pk kemMat.ciphertext key)
    (deterministic base onoff sa sb kemMat.pk kemMat.ciphertext key) ecEk ecCt0 ecCt1
    (leakage base onoff leak sa sb kemMat.pk kemMat.ciphertext key)

/-- Security oracles answering a query from `s` with the instance `schemeOf s`, challenge
oracle `chall`, and Opp-UniKEM's exposure policies. -/
def securityImplAt [DecidableEq K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff)
    (schemeOf : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp)) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  fun t => (get : StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
      ProbComp (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))) >>= fun s =>
    let scka := schemeOf s
    match (motive := ∀ query,
        StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
          ProbComp ((securitySpec leak Sym).Range query)) t with
    | .inl (.inl (.inl (.inl (.inl t)))) => SCKAScheme.sckaCorrectnessImpl scka t
    | .inl (.inl (.inl (.inl (.inr u)))) => SCKAScheme.oracleSendArleak vulnRleakA scka u
    | .inl (.inl (.inl (.inr u))) => SCKAScheme.oracleSendBrleak vulnRleakB scka u
    | .inl (.inl (.inr t)) => chall t
    | .inl (.inr u) =>
      SCKAScheme.oracleCorruptA (vulnCorrA base onoff) (StB onoff Sym) K (Message Sym) u
    | .inr u =>
      SCKAScheme.oracleCorruptB (vulnCorrB base onoff) (StA onoff Sym) K (Message Sym) u

/-- From `s`, each query of `securityImplAt schemeOf chall` is that of `securityImplOf` over
`schemeOf s`. -/
theorem securityImplAt_run [DecidableEq K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff)
    (schemeOf : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (securityImplAt base onoff leak schemeOf chall t).run s =
      (SCKAScheme.securityImplOf (SCKAScheme.sckaCorrectnessImpl (schemeOf s)) chall
        (exposureA base onoff leak) (exposureB base onoff leak) (schemeOf s) t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u) <;> rfl

/-- Assume that `Inv` does not depend on `exposed` and `challenged`, that each ordinary send of
`schemeOf s` is its leaking send with the coins forgotten, and that `chall` records challenges.
If `Inv s` holds and the correctness queries of `schemeOf s` preserve `Inv` from `s`, then so
does every query of `securityImplAt schemeOf chall`. -/
theorem securityImplAt_preserves_at [DecidableEq K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff)
    (schemeOf : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (Inv : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ s st, (do
      let out ← (schemeOf s).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendA st)
    (hmB : ∀ s st, (do
      let out ← (schemeOf s).sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendB st)
    (hchall : SCKAScheme.RecordsChallenges chall)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) (hs : Inv s)
    (hbase : ∀ t z, z ∈ support ((SCKAScheme.sckaCorrectnessImpl (schemeOf s) t).run s) →
      Inv z.2)
    (t : (securitySpec leak Sym).Domain)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((securityImplAt base onoff leak schemeOf chall t).run s)) : Inv z.2 := by
  rw [securityImplAt_run] at hz
  exact SCKAScheme.securityImplOf_preserves_at_of_book _ _ _ _ _ Inv hbook (hmA s) (hmB s)
    s hs hbase
    (fun t => hchall.preservesInv Inv (fun s C h => by simpa using hbook s s.exposed C h) t s hs)
    (hbase SCKAScheme.sckaCorrectnessSpec.OSendA)
    (hbase SCKAScheme.sckaCorrectnessSpec.OSendB) t z hz

/-- Under the same assumptions on `Inv`, the sends, and `chall` as `securityImplAt_preserves_at`:
if, for every `s` satisfying `Inv`, the correctness queries of `schemeOf s` preserve `Inv` from
`s`, then `securityImplAt schemeOf chall` preserves `Inv`. -/
theorem securityImplAt_preservesInv [DecidableEq K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff)
    (schemeOf : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (Inv : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ s st, (do
      let out ← (schemeOf s).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendA st)
    (hmB : ∀ s st, (do
      let out ← (schemeOf s).sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendB st)
    (hchall : SCKAScheme.RecordsChallenges chall)
    (hbase : ∀ s, Inv s → ∀ t z,
      z ∈ support ((SCKAScheme.sckaCorrectnessImpl (schemeOf s) t).run s) → Inv z.2) :
    QueryImpl.PreservesInv (securityImplAt base onoff leak schemeOf chall) Inv :=
  fun t s hs z hz => securityImplAt_preserves_at base onoff leak schemeOf chall Inv hbook hmA hmB
    hchall s hs (hbase s hs) t z hz

/-- The honest intermediate game:
`securityImplAt (honestScheme kemMat e) (pinnedChallenge e kStar)`. -/
def honestOracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (kStar : K) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 kemMat e)
    (pinnedChallenge onoff e kStar)

/-- `honestOracle kemMat e kStar` stopped at the exposure of `e` (an outer `none`); a rejection by
the game stays an inner `none`. -/
def honestStopped [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (kStar : K) :=
  stopOnState (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e kStar)
    (fun s => decide (e ∈ s.exposed))

/-- Assume that, averaged over `a ← sample`, the four sends of `schemeOf a s` have the
distributions of those of `target s`, and that the receives of `schemeOf a s` and `target s`
agree for every `a ∈ support sample`. Then averaging
`securityImplAt (schemeOf a) chall t` from `s` over `a ← sample` gives the joint response/state
distribution of `securityImplAt target chall t` from `s`. -/
theorem securityImplAt_sample_eq [DecidableEq K] {τ : Type}
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (sample : ProbComp τ)
    (schemeOf : τ → SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (target : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hsendA : (do let a ← sample; (schemeOf a s).sendA s.stA) =ᵈ (target s).sendA s.stA)
    (hsendB : (do let a ← sample; (schemeOf a s).sendB s.stB) =ᵈ (target s).sendB s.stB)
    (hsendArleak : (do let a ← sample; (schemeOf a s).sendArleak s.stA) =ᵈ
      (target s).sendArleak s.stA)
    (hsendBrleak : (do let a ← sample; (schemeOf a s).sendBrleak s.stB) =ᵈ
      (target s).sendBrleak s.stB)
    (hrecvA : ∀ a ∈ support sample, ∀ ρ,
      (schemeOf a s).recvA s.stA ρ = (target s).recvA s.stA ρ)
    (hrecvB : ∀ a ∈ support sample, ∀ ρ,
      (schemeOf a s).recvB s.stB ρ = (target s).recvB s.stB ρ)
    (t : (securitySpec leak Sym).Domain) :
    (do let a ← sample; (securityImplAt base onoff leak (schemeOf a) chall t).run s) =ᵈ
      (securityImplAt base onoff leak target chall t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · exact ToVCVio.evalDistEq_bind_of_const' sample fun _ _ => rfl
    · cases u
      simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact SCKAScheme.oracleSendA_sample_eq _ _ _ s hsendA
    · cases u
      simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact SCKAScheme.oracleSendB_sample_eq _ _ _ s hsendB
    · simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_bind_of_const' sample fun a ha =>
        SCKAScheme.oracleRecvA_run_congr _ _ s (hrecvA a ha) n
    · simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_bind_of_const' sample fun a ha =>
        SCKAScheme.oracleRecvB_run_congr _ _ s (hrecvB a ha) n
  · cases u
    simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind]
    exact SCKAScheme.oracleSendArleak_sample_eq _ _ _ _ s hsendArleak
  · cases u
    simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind]
    exact SCKAScheme.oracleSendBrleak_sample_eq _ _ _ _ s hsendBrleak
  all_goals exact ToVCVio.evalDistEq_bind_of_const' sample fun _ _ => rfl

end oppUniKemCKA.Security.Embedding

/-! ## The stored source material -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Material-consistency invariant for epoch `e`: if A is at epoch `e` and holds a decapsulation
key, its key pair is `(kemMat.pk, kemMat.sk)`; if B is at epoch `e` and holds an offline state, its
offline state and offline ciphertext are `(kemMat.st, kemMat.ct0)`. -/
def consistentMat {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  (s.stA.t = e → s.stA.dkA.isSome →
    s.stA.ekA = some kemMat.pk ∧ s.stA.dkA = some kemMat.sk) ∧
  (s.stB.t = e → s.stB.stCt.isSome →
    s.stB.stCt = some kemMat.st ∧ s.stB.ct0 = some kemMat.ct0)

/-- Under `reachableInv`, if B holds no online ciphertext, A and B are in the same epoch. -/
theorem epochs_eq_before_online
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hc : s.stB.ct1 = none) :
    s.stA.t = s.stB.t := by
  obtain ⟨T, hT⟩ := hs
  have hon : (T s.stB.t).on = none := by
    have h := hT.onB
    rw [hc] at h
    simpa using h
  have hn : ¬s.stB.t < s.stA.t := by
    intro hlt
    have h := hT.pastComplete s.stB.t hT.epochPosB hlt
    simp [EpochTranscript.key, hon] at h
  have := hT.epochs
  omega

/-- Under `reachableInv` and `consistentMat kemMat e`, if B is at `e` with public key `pk`, offline
state `st`, and no online ciphertext, then `pk = kemMat.pk` and `st = kemMat.st`. -/
private theorem pinned_online_inputs
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hm : consistentMat kemMat e s)
    (he : s.stB.t = e) (pk : PK) (st : onoff.St)
    (hp : s.stB.ekA = some pk) (hst : s.stB.stCt = some st) (hc : s.stB.ct1 = none) :
    pk = kemMat.pk ∧ st = kemMat.st := by
  have ht := epochs_eq_before_online base onoff ecEk ecCt0 ecCt1 s hs hc
  obtain ⟨T, hT⟩ := hs
  obtain ⟨sk, hpk⟩ := hT.decodedEk pk hp
  have hpair := hT.keypairA
  rw [ht, hpk] at hpair
  have ha : s.stA.ekA = some pk ∧ s.stA.dkA = some sk := by
    cases hpA : s.stA.ekA <;> cases hsA : s.stA.dkA <;>
      simp_all [Option.map₂]
  have hsrcA := hm.1 (ht.trans he) (by simp [ha.2])
  have hsrcB := hm.2 he (by simp [hst])
  exact ⟨Option.some.inj (ha.1.symm.trans hsrcA.1),
    Option.some.inj (hst.symm.trans hsrcB.1)⟩

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- A's successful send in `honestScheme kemMat e s` preserves `consistentMat kemMat e`. -/
private theorem sendA_preserves_consistentMat
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : consistentMat kemMat e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StA onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendA (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
        ecEk s.stA)) :
    consistentMat kemMat e { s with stA := next } := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [sendA, hd, hp, ha, Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    simp only [Pinned.keygen, Stage.keygenFlag, he, decide_true, decide_false, ↓reduceIte,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [consistentMat]
    all_goals aesop

/-- B version of `sendA_preserves_consistentMat`. -/
private theorem sendB_preserves_consistentMat
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : consistentMat kemMat e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StB onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendB (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
        ecCt0 ecCt1 s.stB)) :
    consistentMat kemMat e { s with stB := next } := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    simp only [Pinned.encapsOff, Pinned.encapsOn, Stage.offlineFlag, Stage.onlineFlag, he,
      decide_true, decide_false, ↓reduceIte, pure_bind, mem_support_bind_iff,
      mem_support_pure_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [consistentMat]
    all_goals aesop

/-- B's successful receive preserves `consistentMat kemMat e`. -/
private theorem recvB_preserves_consistentMat [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : consistentMat kemMat e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StB onoff Sym)
    (hout : recvB base onoff ecEk s.stB msg = some (key, t, next)) :
    consistentMat kemMat e { s with stB := next } := by
  obtain h | h := oppUniKemCKA.Reduction.Internal.recvB_kem_source_shape
    base onoff ecEk s.stB msg key t next hout
  · exact ⟨hs.1, by simpa only [h.1, h.2.1, h.2.2.1] using hs.2⟩
  · exact ⟨hs.1, by simp [h.2.1]⟩

/-- A version of `recvB_preserves_consistentMat`, in `honestScheme kemMat e s`. -/
private theorem recvA_preserves_consistentMat [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : consistentMat kemMat e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StA onoff Sym)
    (hout : (honestScheme ecEk ecCt0 ecCt1 kemMat e s).recvA s.stA msg = some (key, t, next)) :
    consistentMat kemMat e { s with stA := next } := by
  rcases oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
    (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
    (stageDet .pinned kemMat e s).decapsDet
    ecCt0 ecCt1 s.stA msg key t next hout with h | h
  · exact ⟨by simpa only [h.1, h.2.1, h.2.2] using hs.1, hs.2⟩
  · exact ⟨by simp [h.2.2.1], hs.2⟩

/-- The correctness oracles of `honestScheme kemMat e s` preserve `consistentMat kemMat e`. -/
theorem honestCorrectness_preserves_consistentMat [DecidableEq K] [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : consistentMat kemMat e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 kemMat e s) t).run s)) :
    consistentMat kemMat e z.2 := by
  apply SCKAScheme.correctnessImpl_preserves_localInv_at _
    (fun a b => consistentMat kemMat e { s with stA := a, stB := b }) s hs ?_ ?_ ?_ ?_ t z hz
  · exact fun key msg t next hout =>
      sendA_preserves_consistentMat ecEk kemMat e s hs key msg t next hout
  · exact fun key msg t next hout =>
      sendB_preserves_consistentMat ecCt0 ecCt1 kemMat e s hs key msg t next hout
  · exact fun msg key t next hout =>
      recvA_preserves_consistentMat ecEk ecCt0 ecCt1 kemMat e s hs msg key t next hout
  · exact fun msg key t next hout =>
      recvB_preserves_consistentMat base onoff ecEk leak kemMat e s hs msg key t next hout

/-- The initial game state satisfies `consistentMat kemMat e`. -/
theorem consistentMat_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (kemMat : KEMMaterial leak) (e : ℕ) :
    consistentMat (Sym := Sym) kemMat e
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff) := by
  simp [consistentMat, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- For `kemMat ∈ support (sampleMaterial leak)`, every possible output of
`Pinned.keygen kemMat selected` is one of `base.keygen`. -/
private theorem pinned_keygen_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (kemMat : KEMMaterial leak)
    (hm : kemMat ∈ support (sampleMaterial leak)) (selected : Bool)
    (pair : PK × SK) (h : pair ∈ support (Pinned.keygen kemMat selected)) :
    pair ∈ support base.keygen := by
  cases selected
  · exact h
  · obtain rfl := (mem_support_pure_iff _ _).mp h
    exact (sampleMaterial_ordinary_support leak kemMat hm).1

/-- For `kemMat ∈ support (sampleMaterial leak)`, every possible output of A's send in
`honestScheme kemMat e s` is one of `sendA` over `base`. -/
private theorem sendA_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym))
    (hout : out ∈ support
      (sendA (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
        ecEk s.stA)) :
    out ∈ support (sendA base onoff ecEk s.stA) := by
  cases hd : s.stA.dkA with
  | none =>
    simp only [sendA, hd, pure_bind, mem_support_bind_iff] at hout ⊢
    obtain ⟨pair, hpair, hout⟩ := hout
    exact ⟨pair, pinned_keygen_support leak kemMat hm _ pair hpair, hout⟩
  | some sk => simpa only [sendA, hd] using hout

/-- B version of `sendA_pinned_support`, under `reachableInv` and `consistentMat kemMat e`. -/
private theorem sendB_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : consistentMat kemMat e s)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym))
    (hout : out ∈ support
      (sendB (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
        ecCt0 ecCt1 s.stB)) :
    out ∈ support (sendB base onoff ecCt0 ecCt1 s.stB) := by
  have hoff := (sampleMaterial_ordinary_support leak kemMat hm).2.1
  have hon := (sampleMaterial_ordinary_support leak kemMat hm).2.2
  by_cases he : s.stB.t = e
  · cases hc0 : s.stB.ct0 with
    | none =>
      obtain ⟨T, hT⟩ := hs
      have hack := hT.ctRecB_eq_false_of_ct0_eq_none hc0
      simp only [sendB, hc0, hack, Bool.not_false, Pinned.encapsOff, Stage.offlineFlag,
        he, decide_true, ↓reduceIte, pure_bind] at hout
      simp only [sendB, hc0, hack, he, Bool.not_false, ↓reduceIte, pure_bind,
        mem_support_bind_iff]
      exact ⟨kemMat.off.1, hoff, hout⟩
    | some ct0 =>
      simp only [sendB, hc0, pure_bind] at hout ⊢
      cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
        cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
      all_goals
        simp only [hp, hc1, hst, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.encapsOn, Stage.onlineFlag, he, decide_true] at hout ⊢
        first
        | exact hout
        | have hinputs := pinned_online_inputs base onoff ecEk ecCt0 ecCt1
            leak kemMat e s hs hsrc he _ _ hp hst hc1
          apply (mem_support_bind_iff _ _ _).mpr
          refine ⟨kemMat.on.1, ?_, hout⟩
          simpa only [hinputs.1, hinputs.2] using hon
  · cases hc0 : s.stB.ct0 with
    | none =>
      obtain ⟨T, hT⟩ := hs
      have hack := hT.ctRecB_eq_false_of_ct0_eq_none hc0
      simpa only [sendB, hc0, hack, Bool.not_false, pure_bind,
        Pinned.onOff, Pinned.encapsOff, Stage.offlineFlag, he, decide_false, Bool.false_eq_true,
        ↓reduceIte] using hout
    | some ct0 =>
      cases ha : s.stB.ack.ctRec
      all_goals
        simp only [sendB, hc0, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.encapsOn, Stage.onlineFlag, he, decide_false] at hout ⊢
        first
        | exact hout
        | cases hp : s.stB.ekA <;> simp only [hp] at hout ⊢
          all_goals first
          | exact hout
          | cases hc1 : s.stB.ct1 <;> simp only [hc1] at hout ⊢
            all_goals first
            | exact hout
            | cases hst : s.stB.stCt <;> simpa only [hst] using hout

/-- For `kemMat ∈ support (sampleMaterial leak)`, every possible result of A's send oracle of
`honestScheme kemMat e s` from `s` is one of A's send oracle over `base`. -/
theorem oracleSendA_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendA (honestScheme ecEk ecCt0 ecCt1 kemMat e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendA (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  rw [SCKAScheme.mem_support_oracleSendA_run_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  exact ⟨out, sendA_pinned_support base onoff ecEk leak kemMat hm e s out hout, hz⟩

/-- B version of `oracleSendA_pinned_support`, under `reachableInv` and `consistentMat kemMat e`. -/
theorem oracleSendB_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : consistentMat kemMat e s)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendB (honestScheme ecEk ecCt0 ecCt1 kemMat e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendB (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  rw [SCKAScheme.mem_support_oracleSendB_run_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  exact ⟨out, sendB_pinned_support base onoff ecEk ecCt0 ecCt1 leak
    kemMat hm e s hs hsrc out hout, hz⟩

end oppUniKemCKA.Security.Embedding

/-! ## Invariants of the honest game -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- If B's send in `honestScheme kemMat e s` can output a key `k` at epoch `e`, then
`k = kemMat.key`. -/
private theorem sendB_selected_key
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (k : K) (msg : Message Sym) (t : ℕ) (next : StB onoff Sym)
    (hout : some (some (e, k), msg, t, next) ∈ support
      (sendB (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
        ecCt0 ecCt1 s.stB)) : k = kemMat.key := by
  have he : s.stB.t = e := (sendB_key_fresh
    (stageKem .pinned kemMat e s) (stageOnOff .pinned kemMat e s)
    ecCt0 ecCt1 s.stB e k msg t next hout).1.symm
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, Pinned.encapsOff, Pinned.encapsOn,
      Stage.offlineFlag, Stage.onlineFlag, he, decide_true, mem_support_pure_iff,
      Option.some.injEq, Prod.mk.injEq] at hout
    simp_all

/-- The correctness oracles of `honestScheme kemMat e` preserve the property that every key B
records at `e` is `kemMat.key`. -/
private theorem honestCorrectness_preserves_keyB_eq [DecidableEq K] [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : ∀ k, s.keyB e = some k → k = kemMat.key)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 kemMat e s) t).run s)) :
    ∀ k, z.2.keyB e = some k → k = kemMat.key := by
  apply SCKAScheme.correctnessImpl_preserves_keyBInv_at _
    (fun keyB => ∀ k, keyB e = some k → k = kemMat.key) s hs ?_ ?_ t z hz
  · intro tI k msg t next hout k' hk'
    by_cases he : tI = e
    · subst tI
      simp only [Function.update_self, Option.some.injEq] at hk'
      exact hk' ▸ sendB_selected_key ecCt0 ecCt1 kemMat e s k msg t next hout
    · exact hs k' (by simpa [Function.update, Ne.symm he] using hk')
  · intro msg tI k t next hr
    exact absurd (recvB_key_none base onoff ecEk s.stB msg _ t next hr) (Option.some_ne_none _)

/-- If the challenge oracle `chall` only records challenges (`RecordsChallenges chall`), then
`securityImplAt (honestScheme kemMat e) chall` preserves the property that every key B records at
`e` is `kemMat.key`. -/
theorem honestScheme_preserves_keyB_eq
    [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv
      (securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 kemMat e) chall)
      (fun s => ∀ k, s.keyB e = some k → k = kemMat.key) :=
  securityImplAt_preservesInv base onoff leak _ chall _ (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _) hchall
    (fun s hs t => honestCorrectness_preserves_keyB_eq ecEk ecCt0 ecCt1 kemMat e t s hs)

/-- In the initial game state, every key B records at `e` is `kemMat.key`, since B records none. -/
theorem keyB_eq_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (kemMat : KEMMaterial leak) (e : ℕ) :
    ∀ k, (oppUniKemCKA.Reduction.Internal.initialGame (Sym := Sym) base onoff).keyB e = some k →
      k = kemMat.key := by
  simp [oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

/-- Under `reachableInv`, a key A records at epoch `e` is also recorded by B. -/
private theorem recordedA_eq_recordedB
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s)
    (e : ℕ) (k : K) (hk : s.keyA e = some k) : s.keyB e = some k := by
  obtain ⟨T, hT⟩ := hs
  rw [hT.keyA] at hk
  split_ifs at hk with hzero hpast
  simpa only [hT.keyB] using hk

/-- Under `reachableInv`, if every key B records at `e` is `kemMat.key`, then so is every key
recorded at `e` by either party. -/
theorem recorded_eq_key
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hm : ∀ k, s.keyB e = some k → k = kemMat.key)
    (k : K) (hk : s.keyA e = some k ∨ s.keyB e = some k) : k = kemMat.key := by
  apply hm k
  exact hk.elim (recordedA_eq_recordedB base onoff ecEk ecCt0 ecCt1 s hs e k) id

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- For possible `kemMat`, the correctness oracles of `honestScheme kemMat e`
preserve `reachableInv` on states satisfying `consistentMat kemMat e`. -/
private theorem honestCorrectness_preserves_reachableInv
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : consistentMat kemMat e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 kemMat e s) t).run s)) :
    reachableInv base onoff ecEk ecCt0 ecCt1 z.2 := by
  rcases t with ((((n | u) | u) | n) | n)
  · exact SCKAScheme.oracleUnif_preservesInv _ n s hs z hz
  · cases u
    exact oracleSendA_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos () s hs z
      (oracleSendA_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak kemMat hm e s z hz)
  · cases u
    exact oracleSendB_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak () s hs z
      (oracleSendB_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak
        kemMat hm e s hs hsrc z hz)
  · apply oracleRecvAIdeal_preserves_reachableInv base onoff hDet ecEk ecCt0 hCt0
      ecCt1 hCt1 leak n s hs z
    have heq :
        (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 kemMat e s) n).run s =
        (oracleRecvAIdeal base onoff hDet ecEk ecCt0 ecCt1 leak n).run s := by
      change (SCKAScheme.oracleRecvA _ n).run s =
        (SCKAScheme.oracleRecvA (schemeWithDecaps base onoff hDet ecEk ecCt0 ecCt1 leak
          (fun _ _ => s.keyB s.stA.t)) n).run s
      simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      simp_rw [stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e s]
      rfl
    exact heq ▸ hz
  · exact oracleRecvB_preserves_reachableInv base onoff hDet ecEk hEk ecEk.ec.nchunk_pos
      ecCt0 ecCt1 leak n s hs z hz

/-- For possible `kemMat` and a challenge oracle `chall` that only records challenges
(`RecordsChallenges chall`), `securityImplAt (honestScheme kemMat e) chall` preserves
`reachableInv ∧ consistentMat kemMat e`. -/
theorem honestScheme_preserves_simulationInv
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv
      (securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 kemMat e) chall)
      (fun s => reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ consistentMat kemMat e s) :=
  securityImplAt_preservesInv base onoff leak _ chall _
    (fun _ E C h => ⟨reachableInv_with_security_bookkeeping h.1 E C, h.2⟩)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _) hchall
    (fun s hs t z hz => ⟨honestCorrectness_preserves_reachableInv base onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak kemMat hm e t s hs.1 hs.2 z hz,
      honestCorrectness_preserves_consistentMat ecEk ecCt0 ecCt1 kemMat e t s hs.2 z hz⟩)

end oppUniKemCKA.Security.Embedding
