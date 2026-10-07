/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Material
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# The honest intermediate game

**Setting.** Fix complete material `m`, a selected epoch `e`, and a challenge key `kStar`.

**Definitions.**

- `honestScheme m e s`: Opp-UniKEM with the KEM `Pinned.kem m` flagging the phases of the
  parties at epoch `e` in the game state `s`, and decapsulation returning B's recorded key for
  A's current epoch; `symbolicScheme m e s` is the simulator's instance for `s`.
- `securityImplAt schemeOf chall`: the security oracles of the protocol instance `schemeOf s`
  selected by the current state `s`, with challenge oracle `chall` and Opp-UniKEM's exposure
  policies.
- `honestOracle m e kStar := securityImplAt (honestScheme m e) (pinnedChallenge e kStar)`: the
  honest intermediate game; `honestStopped` stops it after the first query exposing `e`.

**Results.** `securityImplAt_run` identifies each query with the security oracle family over
`schemeOf s`. `securityImplAt_preserves_at` and `securityImplAt_preservesInv`: for every
challenge oracle that records challenges, an invariant insensitive to the bookkeeping sets is
preserved if the correctness oracles of the selected instances preserve it.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Instantiate the honest protocol for one query from state `s`. Samplers
use `m` when the corresponding party is at epoch `e`; decapsulation returns
B's recorded key for A's current epoch. -/
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

/-- Instantiate the symbolic protocol for one query corresponding to honest
state `s`. Selected private values are unavailable; auxiliary decapsulation
returns the marked form of B's recorded key. -/
abbrev symbolicScheme [DecidableEq Sym]
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

/-- The security oracles of the protocol instance selected by the current state: a query from
state `s` is answered by `scka := schemeOf s` as in the security game, with challenge oracle
`chall` and Opp-UniKEM's exposure policies. `securityImplAt_run` identifies each query with
`securityImplOf (sckaCorrectnessImpl scka) chall exposureA exposureB scka`. -/
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

/-- A query of `securityImplAt schemeOf chall` from `s` is the query of the security oracle
family over `schemeOf s` with challenge oracle `chall`. -/
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

/-- Let `Inv` be insensitive to the bookkeeping sets, let the leaking sends of every selected
instance forget their coins to the ordinary sends, and let `chall` record challenges. If `Inv s`
holds and every correctness query of `schemeOf s` from `s` preserves `Inv`, then every query of
`securityImplAt schemeOf chall` from `s` preserves `Inv`. -/
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

/-- Under the hypotheses of `securityImplAt_preserves_at` for every state, `securityImplAt
schemeOf chall` preserves `Inv`. -/
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

/-- Honest intermediate game: the protocol instance `honestScheme m e s` with challenge oracle
`pinnedChallenge e kStar`. -/
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

/-- Honest intermediate oracle with termination after any query whose
successor exposes the selected epoch `e`. The stopped response is represented
by the outer `OptionT`; ordinary oracle rejection remains an inner `none`. -/
def honestStopped [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) :=
  stopOnState (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
    (fun s => decide (e ∈ s.exposed))

/-- Lift averaged local equalities to the state-indexed security oracles. Let `sample` be a
never-failing computation returning `a : τ`, let `schemeOf a` for each `a` and `target` be
state-indexed schemes, and let `chall` be a challenge oracle. Fix a state `s`. Assume:

- averaged over `a ← sample`, each of the four sends of `schemeOf a s` from the local state in
  `s` has the distribution of the same send of `target s`;
- for every `a ∈ support sample` and message `ρ`, the two receives of `schemeOf a s` and
  `target s` agree on the local state in `s` and `ρ`.

Then, for every query `t`, the joint response/state distribution of
`securityImplAt (schemeOf a) chall t` from `s`, averaged over `a ← sample`, is that of
`securityImplAt target chall t` from `s`. -/
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
