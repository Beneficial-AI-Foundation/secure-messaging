/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Explicit SCKA exposure policies

An exposure policy of a party gives the epochs that the security game marks as exposed. Revealing
the local state `st` exposes `corrupt st`. A send that reveals its coins `r` and proposes the new
state `st'` exposes `send st st' r`. If these epochs meet the challenged epochs, the game refuses
the send and keeps neither the new state nor its bookkeeping.

The SCKA security game of `SCKA.Defs` uses callbacks that see only the state before a send and
its coins. The policies here can also see the new state, so they express the rule of
[SCKA, Fig. 1]: `ExposurePolicy.ofDelta V` exposes `V st' \ V st`, the epochs that the new state
exposes and the old state does not. This module keeps that rule available, so that a protocol
proof can relate its game to [SCKA, Fig. 1]. The ML-KEM Braid proof does this in
`MLKEMBraid.NoAuth.securityGame_equiv_delta`.
-/

open OracleSpec OracleComp

namespace SCKAScheme

/-- Epoch-exposure rules for one party, supplied to the security game. -/
-- ANCHOR: ExposurePolicy
structure ExposurePolicy (St Rand : Type) where
  /-- Epochs compromised by revealing the local state. -/
  corrupt : St → Finset ℕ
  /-- Epochs compromised by send coins, given the old and new local states. -/
  send : St → St → Rand → Finset ℕ
-- ANCHOR_END: ExposurePolicy

namespace ExposurePolicy

variable {IK StA StB I Rho Rand : Type}

/-- The exposure policy with send exposure `V st' \ V st`. -/
def ofDelta {St Rand : Type} (V : St → Finset ℕ) :
    SCKAScheme.ExposurePolicy St Rand where
  corrupt := V
  send := fun st st' _ => V st' \ V st

/-- A's leaking send. It refuses a send whose exposed epochs meet the challenged epochs. -/
-- ANCHOR: oracleSendArleak
def oracleSendArleak [DecidableEq I] (leakA : StA → StA → Rand → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    match ← liftM (scka.sendArleak state.stA) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stA', rand) =>
      let vuln' := leakA state.stA stA' rand
      -- req vuln' ∩ Challenged = ∅
      if vuln' ∩ state.challenged ≠ ∅ then pure none
      else
        let exposed' := state.exposed ∪ vuln'
        let assertMonotonicity := state.tcurA ≤ tsnd
        let assertKnownPrefix (keyA : ℕ → Option I) :=
          (List.range (tsnd + 1)).all (fun t => t = 0 || (keyA t).isSome)
        let nA' := state.nA + 1
        let msgA' := Function.update state.msgA nA' (some (ρ, tsnd))
        match keyOpt with
        | none =>
          set { state with
            stA := stA', tcurA := tsnd, exposed := exposed',
            msgA := msgA', nA := nA',
            correct := state.correct && assertMonotonicity && assertKnownPrefix state.keyA }
          return some (tsnd, none, ρ, rand)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyA tI).isNone
          let assertConsistentKeys := (state.keyB tI).isNone || state.keyB tI == some key
          let keyA' := Function.update state.keyA tI (some key)
          set { state with
            stA := stA', tcurA := tsnd, exposed := exposed', keyA := keyA',
            msgA := msgA', nA := nA',
            correct := state.correct
              && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix keyA' }
          return some (tsnd, some tI, ρ, rand)
-- ANCHOR_END: oracleSendArleak

/-- B's leaking send, with the same refusal rule as A's. -/
-- ANCHOR: oracleSendBrleak
def oracleSendBrleak [DecidableEq I] (leakB : StB → StB → Rand → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    match ← liftM (scka.sendBrleak state.stB) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stB', rand) =>
      let vuln' := leakB state.stB stB' rand
      if vuln' ∩ state.challenged ≠ ∅ then pure none
      else
        let exposed' := state.exposed ∪ vuln'
        let assertMonotonicity := state.tcurB ≤ tsnd
        let assertKnownPrefix (keyB : ℕ → Option I) :=
          (List.range (tsnd + 1)).all (fun t => t = 0 || (keyB t).isSome)
        let nB' := state.nB + 1
        let msgB' := Function.update state.msgB nB' (some (ρ, tsnd))
        match keyOpt with
        | none =>
          set { state with
            stB := stB', tcurB := tsnd, exposed := exposed',
            msgB := msgB', nB := nB',
            correct := state.correct && assertMonotonicity && assertKnownPrefix state.keyB }
          return some (tsnd, none, ρ, rand)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyB tI).isNone
          let assertConsistentKeys := (state.keyA tI).isNone || state.keyA tI == some key
          let keyB' := Function.update state.keyB tI (some key)
          set { state with
            stB := stB', tcurB := tsnd, exposed := exposed', keyB := keyB',
            msgB := msgB', nB := nB',
            correct := state.correct
              && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix keyB' }
          return some (tsnd, some tI, ρ, rand)
-- ANCHOR_END: oracleSendBrleak

/-- The security oracles with the exposure policies `exposureA` and `exposureB`. -/
-- ANCHOR: sckaSecurityImpl
def sckaSecurityImpl (isRandom : Bool) (exposureA : ExposurePolicy StA Rand)
    (exposureB : ExposurePolicy StB Rand)
    [SampleableType I] [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  sckaCorrectnessImpl scka
    + oracleSendArleak exposureA.send scka + oracleSendBrleak exposureB.send scka
    + oracleChall isRandom StA StB I Rho
    + oracleCorruptA exposureA.corrupt StB I Rho + oracleCorruptB exposureB.corrupt StA I Rho
-- ANCHOR_END: sckaSecurityImpl

/-- Initialize the parties, sample the bit and test the adversary's guess. -/
-- ANCHOR: securityExp
def securityExp [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (exposureA : ExposurePolicy StA Rand)
      (exposureB : ExposurePolicy StB Rand) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (sckaSecurityImpl b exposureA exposureB scka) adversary).run
    (initGameState stA stB)
  return (b == b')
-- ANCHOR_END: securityExp

/-- Guessing advantage under the explicit exposure policy. -/
-- ANCHOR: sckaGuessAdvantage
noncomputable def sckaGuessAdvantage [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (exposureA : ExposurePolicy StA Rand) (exposureB : ExposurePolicy StB Rand) : ℝ :=
  |(Pr{let x ← securityExp scka adversary exposureA exposureB}[x = true]).toReal - 1 / 2|
-- ANCHOR_END: sckaGuessAdvantage

end ExposurePolicy
end SCKAScheme
