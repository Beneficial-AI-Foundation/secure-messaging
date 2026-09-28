/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Pinned
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Challenge
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Honest intermediate game for the selected epoch

**Parameters.** Fix complete selected-epoch material `m`, its epoch `e`,
and a supplied challenge key `kStar`.

**Construction.** `honestOracle` runs the original SCKA operations with
the pinned samplers from `Pinned`. A's auxiliary decapsulation uses B's
recorded key. The challenge oracle substitutes `kStar` only at epoch `e`.
The game retains honest private material, returned coins, and recorded
keys. Exposure guards use the original Opp-UniKEM policies.

**Role in the proof.** `honestStopped` terminates after a query exposes
`e`. Marking private material relates this execution to the IND-CPA
simulator. Deferring the components of `m` to their unique sampling phases
relates the honest intermediate game to the adjacent auxiliary hybrids.
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
  scheme (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
    (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
    (Pinned.deterministic m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
    ecEk ecCt0 ecCt1
    (Pinned.leakage leak m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))

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

/-- Full honest intermediate oracle family. Each protocol operation uses
the current state's pinned scheme. Challenges use `pinnedChallenge`;
corruptions use the original state-vulnerability functions. -/
def honestOracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  fun t => (get : StateT
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))) >>= fun s =>
    let scka := honestScheme ecEk ecCt0 ecCt1 m e s
    match (motive := ∀ query,
        StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
          ProbComp ((securitySpec leak Sym).Range query)) t with
    | .inl (.inl (.inl (.inl (.inl t)))) => SCKAScheme.sckaCorrectnessImpl scka t
    | .inl (.inl (.inl (.inl (.inr u)))) => SCKAScheme.oracleSendArleak sendExposureA scka u
    | .inl (.inl (.inl (.inr u))) => SCKAScheme.oracleSendBrleak sendExposureB scka u
    | .inl (.inl (.inr t)) => pinnedChallenge onoff e kStar t
    | .inl (.inr u) =>
      SCKAScheme.oracleCorruptA (vulnA base onoff) (StB onoff Sym) K (Message Sym) u
    | .inr u =>
      SCKAScheme.oracleCorruptB (vulnB base onoff) (StA onoff Sym) K (Message Sym) u

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

end oppUniKemCKA.Security.Embedding
