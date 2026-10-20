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
# The honest intermediate game

**Setting.** `m` is complete material with pinned KEM `Pinned.kem m`, `e` a selected epoch, and
`kStar` a candidate key (`Simulator`).

**Definitions.**

- `securityImplAt schemeOf chall`: the security oracles answering a query from `s` with the
  instance `schemeOf s` and challenge oracle `chall`.
- `honestScheme m e s`: Opp-UniKEM over `honestKem m e s`, which pins A's key generation if
  `s.stA.t = e` and B's encapsulation if `s.stB.t = e`; A's receive outputs B's recorded key.
  `markedScheme m e s` is the simulator's instance.
- *Honest intermediate game*:
  `honestOracle m e kStar := securityImplAt (honestScheme m e) (pinnedChallenge e kStar)`;
  `honestStopped m e kStar` answers `⊥` at the first query whose successor state exposes `e`.
- `pinnedSources m e s`: at epoch `e`, A's key pair and B's offline output, when present, are
  `m.keygen.1` and `m.off.1`.

**Results.**

- `honestCorrectness_preserves_pinnedSources`: correctness queries preserve `pinnedSources m e`.
- `oracleSendA_pinned_support`, `oracleSendB_pinned_support`: for
  `m ∈ support (sampleMaterial leak)` and `reachableInv s` (and `pinnedSources m e s` for B),
  every possible result of a send oracle of `honestScheme m e s` is one of the oracle over `base`.
-/

/-! ## The honest intermediate game -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- KEM of `honestScheme m e s`: `Pinned.kem m` pinning A's key generation if `s.stA.t = e` and
B's encapsulation if `s.stB.t = e`; decapsulation returns `s.keyB s.stA.t`. -/
abbrev honestKem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    KEMScheme ProbComp K PK SK C :=
  Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
    (s.keyB s.stA.t)

/-- On/off structure of `honestKem m e s`. -/
abbrev honestOnOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (honestKem m e s).OnOffStructure :=
  Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
    (s.keyB s.stA.t)

/-- Deterministic-decapsulation witness of `honestKem m e s`. -/
abbrev honestDet {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (honestKem m e s).DeterministicDecaps :=
  Pinned.deterministic m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
    (s.keyB s.stA.t)

/-- Leakage witnesses of `honestKem m e s`. -/
abbrev honestLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (honestKem m e s).OnOffRandLeak (honestOnOff m e s) :=
  Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
    (s.keyB s.stA.t)

/-- Opp-UniKEM over `honestKem m e s`, for a query from game state `s`. -/
abbrev honestScheme [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  let sa := decide (s.stA.t = e)
  let sb := decide (s.stB.t = e)
  let key := s.keyB s.stA.t
  scheme (Pinned.kem m sa sb sb key) (Pinned.onOff m sa sb sb key)
    (Pinned.deterministic m sa sb sb key) ecEk ecCt0 ecCt1 (Pinned.leakage leak m sa sb sb key)

/-- The simulator's instance for `s`: Opp-UniKEM over the marked `kem` with challenge
`(pk_m, ct_m)`, A selected iff `s.stA.t = e`, and B iff `s.stB.t = e`. -/
abbrev markedScheme [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  let sa := decide (s.stA.t = e)
  let sb := decide (s.stB.t = e)
  let key := (s.keyB s.stA.t).map (mark e s.stA.t)
  scheme (kem base onoff sa sb m.keygen.1.1 m.ciphertext key)
    (onOff base onoff sa sb m.keygen.1.1 m.ciphertext key)
    (deterministic base onoff sa sb m.keygen.1.1 m.ciphertext key) ecEk ecCt0 ecCt1
    (leakage base onoff leak sa sb m.keygen.1.1 m.ciphertext key)

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

/-- Let `Inv` ignore `exposed` and `challenged`, the ordinary sends of each `schemeOf s` forget
the coins of its leaking sends, and `chall` record challenges. If `Inv s` and the correctness
queries of `schemeOf s` preserve `Inv` from `s`, so does every query of `securityImplAt`. -/
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

/-- `securityImplAt_preserves_at` at every state: `securityImplAt schemeOf chall` preserves
`Inv`. -/
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

/-- The honest intermediate game: `securityImplAt (honestScheme m e) (pinnedChallenge e kStar)`. -/
def honestOracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 m e)
    (pinnedChallenge onoff e kStar)

/-- `honestOracle m e kStar` stopped at the exposure of `e` (an outer `none`); a rejection by
the game stays an inner `none`. -/
def honestStopped [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) :=
  stopOnState (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
    (fun s => decide (e ∈ s.exposed))

/-- Let `sample` never fail and fix `s`. If, averaged over `a ← sample`, the four sends of
`schemeOf a s` have the distributions of those of `target s`, and the receives agree for every
`a ∈ support sample`, then averaging `securityImplAt (schemeOf a) chall t` from `s` over `a`
gives the joint response/state distribution of `securityImplAt target chall t` from `s`. -/
theorem securityImplAt_sample_eq [DecidableEq K] {τ : Type}
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (sample : ProbComp τ) [NeverFail sample]
    (schemeOf : τ → SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (target : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) →
      SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
        (SendRand leak.KeygenRand leak.OffRand leak.OnRand))
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hsendA : 𝒟[(do let a ← sample; (schemeOf a s).sendA s.stA)] = 𝒟[(target s).sendA s.stA])
    (hsendB : 𝒟[(do let a ← sample; (schemeOf a s).sendB s.stB)] = 𝒟[(target s).sendB s.stB])
    (hsendArleak : 𝒟[(do let a ← sample; (schemeOf a s).sendArleak s.stA)] =
      𝒟[(target s).sendArleak s.stA])
    (hsendBrleak : 𝒟[(do let a ← sample; (schemeOf a s).sendBrleak s.stB)] =
      𝒟[(target s).sendBrleak s.stB])
    (hrecvA : ∀ a ∈ support sample, ∀ ρ,
      (schemeOf a s).recvA s.stA ρ = (target s).recvA s.stA ρ)
    (hrecvB : ∀ a ∈ support sample, ∀ ρ,
      (schemeOf a s).recvB s.stB ρ = (target s).recvB s.stB ρ)
    (t : (securitySpec leak Sym).Domain) :
    𝒟[(do let a ← sample; (securityImplAt base onoff leak (schemeOf a) chall t).run s)] =
      𝒟[(securityImplAt base onoff leak target chall t).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · exact ToVCVio.evalDist_bind_of_const' sample fun _ _ => rfl
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
      exact ToVCVio.evalDist_bind_of_const' sample fun a ha =>
        SCKAScheme.oracleRecvA_run_congr _ _ s (hrecvA a ha) n
    · simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDist_bind_of_const' sample fun a ha =>
        SCKAScheme.oracleRecvB_run_congr _ _ s (hrecvB a ha) n
  · cases u
    simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind]
    exact SCKAScheme.oracleSendArleak_sample_eq _ _ _ _ s hsendArleak
  · cases u
    simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind]
    exact SCKAScheme.oracleSendBrleak_sample_eq _ _ _ _ s hsendBrleak
  all_goals exact ToVCVio.evalDist_bind_of_const' sample fun _ _ => rfl

end oppUniKemCKA.Security.Embedding

/-! ## The stored source material -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- At epoch `e`: A's key pair, if A holds a decapsulation key, is `m.keygen.1`; B's offline
state and ciphertext, if B holds an offline state, are `m.off.1`. -/
def pinnedSources {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  (s.stA.t = e → s.stA.dkA.isSome →
    s.stA.ekA = some m.keygen.1.1 ∧ s.stA.dkA = some m.keygen.1.2) ∧
  (s.stB.t = e → s.stB.stCt.isSome →
    s.stB.stCt = some m.off.1.1 ∧ s.stB.ct0 = some m.off.1.2)

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

/-- Under `reachableInv` and `pinnedSources m e`, if B is at `e` with public key `pk`, offline
state `st`, and no online ciphertext, then `pk = m.keygen.1.1` and `st = m.off.1.1`. -/
private theorem pinned_online_inputs
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hm : pinnedSources m e s)
    (he : s.stB.t = e) (pk : PK) (st : onoff.St)
    (hp : s.stB.ekA = some pk) (hst : s.stB.stCt = some st) (hc : s.stB.ct1 = none) :
    pk = m.keygen.1.1 ∧ st = m.off.1.1 := by
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

/-- A's successful send in `honestScheme m e s` preserves `pinnedSources m e`. -/
private theorem sendA_preserves_pinnedSources
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StA onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendA (honestKem m e s) (honestOnOff m e s)
        ecEk s.stA)) :
    pinnedSources m e { s with stA := next } := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [sendA, hd, hp, ha, Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    try dsimp only [Pinned.kem, Pinned.onOff] at hout
    simp only [Pinned.keygen, he, decide_true, decide_false, ↓reduceIte, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [pinnedSources] <;> aesop

/-- B version of `sendA_preserves_pinnedSources`. -/
private theorem sendB_preserves_pinnedSources
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StB onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendB (honestKem m e s) (honestOnOff m e s)
        ecCt0 ecCt1 s.stB)) :
    pinnedSources m e { s with stB := next } := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    try dsimp only [Pinned.kem, Pinned.onOff] at hout
    simp only [Pinned.encapsOff, Pinned.encapsOn, he, decide_true, decide_false,
      ↓reduceIte, pure_bind, mem_support_bind_iff, mem_support_pure_iff,
      Prod.exists, Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [pinnedSources] <;> aesop

/-- B's successful receive preserves `pinnedSources m e`. -/
private theorem recvB_preserves_pinnedSources [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StB onoff Sym)
    (hout : recvB base onoff ecEk s.stB msg = some (key, t, next)) :
    pinnedSources m e { s with stB := next } := by
  obtain h | h := oppUniKemCKA.Reduction.Internal.recvB_kem_source_shape
    base onoff ecEk s.stB msg key t next hout
  · exact ⟨hs.1, by simpa only [h.1, h.2.1, h.2.2.1] using hs.2⟩
  · exact ⟨hs.1, by simp [h.2.1]⟩

/-- A version of `recvB_preserves_pinnedSources`, in `honestScheme m e s`. -/
private theorem recvA_preserves_pinnedSources [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StA onoff Sym)
    (hout : (honestScheme ecEk ecCt0 ecCt1 m e s).recvA s.stA msg = some (key, t, next)) :
    pinnedSources m e { s with stA := next } := by
  rcases oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
    (honestKem m e s) (honestOnOff m e s)
    (honestDet m e s).decapsDet
    ecCt0 ecCt1 s.stA msg key t next hout with h | h
  · exact ⟨by simpa only [h.1, h.2.1, h.2.2] using hs.1, hs.2⟩
  · exact ⟨by simp [h.2.2.1], hs.2⟩

/-- The correctness oracles of `honestScheme m e s` preserve `pinnedSources m e`. -/
theorem honestCorrectness_preserves_pinnedSources [DecidableEq K] [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s)) :
    pinnedSources m e z.2 := by
  apply SCKAScheme.correctnessImpl_preserves_localInv_at _
    (fun a b => pinnedSources m e { s with stA := a, stB := b }) s hs ?_ ?_ ?_ ?_ t z hz
  · exact fun key msg t next hout =>
      sendA_preserves_pinnedSources ecEk m e s hs key msg t next hout
  · exact fun key msg t next hout =>
      sendB_preserves_pinnedSources ecCt0 ecCt1 m e s hs key msg t next hout
  · exact fun msg key t next hout =>
      recvA_preserves_pinnedSources ecEk ecCt0 ecCt1 m e s hs msg key t next hout
  · exact fun msg key t next hout =>
      recvB_preserves_pinnedSources base onoff ecEk leak m e s hs msg key t next hout

/-- The initial game state satisfies `pinnedSources m e`. -/
theorem pinnedSources_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (m : Material leak) (e : ℕ) :
    pinnedSources (Sym := Sym) m e
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff) := by
  simp [pinnedSources, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- For `m ∈ support (sampleMaterial leak)`, every possible output of `Pinned.keygen m selected`
is one of `base.keygen`. -/
private theorem pinned_keygen_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) (selected : Bool)
    (pair : PK × SK) (h : pair ∈ support (Pinned.keygen m selected)) :
    pair ∈ support base.keygen := by
  cases selected
  · exact h
  · obtain rfl := (mem_support_pure_iff _ _).mp h
    exact (sampleMaterial_ordinary_support leak m hm).1

/-- For `m ∈ support (sampleMaterial leak)`, every possible output of A's send in
`honestScheme m e s` is one of `sendA` over `base`. -/
private theorem sendA_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym))
    (hout : out ∈ support
      (sendA (honestKem m e s) (honestOnOff m e s)
        ecEk s.stA)) :
    out ∈ support (sendA base onoff ecEk s.stA) := by
  cases hd : s.stA.dkA with
  | none =>
    simp only [sendA, hd, pure_bind, mem_support_bind_iff] at hout ⊢
    obtain ⟨pair, hpair, hout⟩ := hout
    exact ⟨pair, pinned_keygen_support leak m hm _ pair hpair, hout⟩
  | some sk => simpa only [sendA, hd] using hout

/-- B version of `sendA_pinned_support`, under `reachableInv` and `pinnedSources m e`. -/
private theorem sendB_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym))
    (hout : out ∈ support
      (sendB (honestKem m e s) (honestOnOff m e s)
        ecCt0 ecCt1 s.stB)) :
    out ∈ support (sendB base onoff ecCt0 ecCt1 s.stB) := by
  have hoff := (sampleMaterial_ordinary_support leak m hm).2.1
  have hon := (sampleMaterial_ordinary_support leak m hm).2.2
  by_cases he : s.stB.t = e
  · cases hc0 : s.stB.ct0 with
    | none =>
      obtain ⟨T, hT⟩ := hs
      have hack := hT.ctRecB_eq_false_of_ct0_eq_none hc0
      simp only [sendB, hc0, hack, Bool.not_false, Pinned.encapsOff,
        he, decide_true, ↓reduceIte, pure_bind] at hout
      simp only [sendB, hc0, hack, he, Bool.not_false, ↓reduceIte, pure_bind,
        mem_support_bind_iff]
      exact ⟨m.off.1, hoff, hout⟩
    | some ct0 =>
      simp only [sendB, hc0, pure_bind] at hout ⊢
      cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
        cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
      all_goals
        simp only [hp, hc1, hst, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.encapsOn, he, decide_true] at hout ⊢
        first
        | exact hout
        | have hinputs := pinned_online_inputs base onoff ecEk ecCt0 ecCt1
            leak m e s hs hsrc he _ _ hp hst hc1
          apply (mem_support_bind_iff _ _ _).mpr
          refine ⟨m.on.1, ?_, hout⟩
          simpa only [hinputs.1, hinputs.2] using hon
  · cases hc0 : s.stB.ct0 with
    | none =>
      obtain ⟨T, hT⟩ := hs
      have hack := hT.ctRecB_eq_false_of_ct0_eq_none hc0
      simpa only [sendB, hc0, hack, Bool.not_false, pure_bind,
        Pinned.onOff, Pinned.encapsOff, he, decide_false, Bool.false_eq_true,
        ↓reduceIte] using hout
    | some ct0 =>
      cases ha : s.stB.ack.ctRec
      all_goals
        simp only [sendB, hc0, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.encapsOn, he, decide_false] at hout ⊢
        first
        | exact hout
        | cases hp : s.stB.ekA <;> simp only [hp] at hout ⊢
          all_goals first
          | exact hout
          | cases hc1 : s.stB.ct1 <;> simp only [hc1] at hout ⊢
            all_goals first
            | exact hout
            | cases hst : s.stB.stCt <;> simpa only [hst] using hout

/-- For `m ∈ support (sampleMaterial leak)`, every possible result of A's send oracle of
`honestScheme m e s` from `s` is one of A's send oracle over `base`. -/
theorem oracleSendA_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendA (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendA (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  rw [SCKAScheme.mem_support_oracleSendA_run_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  exact ⟨out, sendA_pinned_support base onoff ecEk leak m hm e s out hout, hz⟩

/-- B version of `oracleSendA_pinned_support`, under `reachableInv` and `pinnedSources m e`. -/
theorem oracleSendB_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendB (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendB (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  rw [SCKAScheme.mem_support_oracleSendB_run_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  exact ⟨out, sendB_pinned_support base onoff ecEk ecCt0 ecCt1 leak
    m hm e s hs hsrc out hout, hz⟩

end oppUniKemCKA.Security.Embedding
