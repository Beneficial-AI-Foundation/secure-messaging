/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Interface
import SecureMessaging.SCKA.OppBiKEM.Security.Exposure
import SecureMessaging.SCKA.OppBiKEM.Security.IdealReceive
import SecureMessaging.SCKA.OppBiKEM.Security.Hybrid
import SecureMessaging.SCKA.OppBiKEM.Security.Cancellation
import SecureMessaging.SCKA.OppBiKEM.Security.Injected
import SecureMessaging.SCKA.OppBiKEM.Security.Reduction

/-!
# Opp-BiKEM — Checked security definitions

This module collects the definitions underlying the public security results in `Security`.
Each `recall` checks an imported declaration against the signature and body written here, up to
definitional equality.

The implementations and their proofs live in the topic modules named in the sections below.
Those modules import their dependencies directly. The public `Security` module imports this
reference so that building its theorems also checks these restatements.

A definition is restated here when a public statement reaches it and it is defined in a
`Security.*` module. The sections run in dependency order: each uses only earlier ones.

The results also depend on definitions outside these security modules: the protocol `scheme`
and its exposure predicate (`Construction`); receive recovery and the initial game state
`initState` from which every run starts (`Correctness.RecvSpec`,
`Correctness.Quantitative.Main`); the generic SCKA games and advantage (`SCKA.Defs`,
`SCKA.Security`); stopped runs (ToVCVio `Stop`); the KEM games, correctness error and leakage
interface (VCVio and ToVCVio `KeyEncapMech`); and the erasure-code interface (`ErasureCode`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-! ## The interface — `Security.Interface`

The SCKA oracle interface and adversary type specialized to Opp-BiKEM, and the budget on the
adversary's send queries. -/

recall securitySpec
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : kem.RandLeak) (Sym : Type) :=
  SCKAScheme.sckaSecuritySpec
    (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.EncapsRand)

recall SecurityAdversary
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : kem.RandLeak) (Sym : Type) :=
  SCKAScheme.SCKAAdversary
    (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.EncapsRand)

recall SecuritySendQueryBound
    {kem : KEMScheme ProbComp K PK SK C}
    {leak : kem.RandLeak}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q

/-! ## The exposure policy — `Security.Exposure`

`exposure role leak` says which epochs a corruption or an accepted leaking send exposes. A
leaking send exposes the epochs of the key pair and encapsulation it performs (`rleakEpochs`). -/

recall rleakEpochs {RK RE : Type} (role : Role)
    (st : State PK SK C Sym) (rand : SendRand RK RE) : Finset ℕ :=
  let keyEpoch := st.res.resEpoch + 2 + role.offset
  let encEpoch := st.res.resEpoch + if rand.keygenRand.isSome then 2 else 0
  let epochs : Finset ℤ :=
    (if rand.keygenRand.isSome then {keyEpoch} else ∅) ∪
    (if rand.encapsRand.isSome then {encEpoch} else ∅)
  (epochs.filter fun e => 0 < e).image Int.toNat

recall exposure {kem : KEMScheme ProbComp K PK SK C}
    (role : Role) (leak : kem.RandLeak) :
    SCKAScheme.VulnerableEpochs (State PK SK C Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) where
  corrupt := vuln
  rleak := rleakEpochs role

/-! ### Send guards

These guards determine when a send generates a key pair or encapsulates. -/

recall sendKeygenGuard (role : Role) (st : State PK SK C Sym) : Bool :=
  st.req.ek.isNone &&
    decide (st.res.resEpoch ∈ st.ack.ctRec ∧
      st.res.resEpoch + role.offset ∈ st.ack.ctRec)

recall sendEncapsGuard (role : Role) (st : State PK SK C Sym) : Bool :=
  let tRes := st.res.resEpoch + if sendKeygenGuard role st then 2 else 0
  decide (tRes + role.offset ∈ st.ack.ekRec) &&
    decide (tRes ∉ st.ack.ctRec) &&
    st.res.ct.isNone &&
    decide (tRes ∈ st.ack.ekRec)

/-! ## The ideal receive — `Security.IdealReceive`

An ideal receive copies the peer's recorded key for the received epoch instead of
decapsulating. `schemeWithRecv` replaces only the receive functions of the scheme. -/

recall idealRecover (peerKey : ℕ → Option K) : ℤ → SK → C → Option K :=
  fun q _ _ => peerKey q.toNat

recall schemeWithRecv [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (recvA' : StA PK SK C Sym → Message Sym → Option (Option (ℕ × K) × ℕ × StA PK SK C Sym))
    (recvB' : StB PK SK C Sym → Message Sym → Option (Option (ℕ × K) × ℕ × StB PK SK C Sym)) :
    SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) :=
  { scheme kem hDet ecEk ecCt leak with recvA := recvA', recvB := recvB' }

recall oracleRecvAIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  fun n => do
    let s ← get
    SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n

recall oracleRecvBIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  fun n => do
    let s ← get
    SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n

recall idealCorrectnessImpl [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    + SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak)
    + SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak)
    + oracleRecvAIdeal kem hDet ecEk ecCt leak + oracleRecvBIdeal kem hDet ecEk ecCt leak

/-! ## Hybrids — `Security.Hybrid`

The hybrid with threshold `T` is the ideal game answering eligible challenges at epochs below
`T` with independent uniform keys and all others with recorded keys. -/

recall hybridRandom (T : ℕ) : ℕ → Bool := fun t => decide (t < T)

recall hybridSecurityImpl [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (random : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.securityImplOf (idealCorrectnessImpl kem hDet ecEk ecCt leak)
    (SCKAScheme.oracleChallOn random _ _ _ _) (exposure .A leak) (exposure .B leak)
    (scheme kem hDet ecEk ecCt leak)

recall hybridExp [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (T : ℕ) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom T)) adv).run'
    (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))

/-! ## The stopping test — `Security.Cancellation`

A run is stopped at the first query after which the target epoch is exposed. -/

recall targetExposed (t : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Bool :=
  decide (t ∈ s.exposed)

/-! ## Target injection — `Security.Injected`

The injected oracles fix the public key, stored secret, ciphertext and recorded key at a target
epoch `t`. The owner's key generation for `t` returns the injected key pair, and the peer's
encapsulation for `t` returns the injected ciphertext and key. Receives are ideal, and `random`
selects the uniform challenge answers. -/

recall sendGeneratesTarget (role : Role) (t : ℕ) (st : State PK SK C Sym) : Bool :=
  sendKeygenGuard role st && decide (st.res.resEpoch + 2 + role.offset = (t : ℤ))

recall sendEncapsulatesTarget (role : Role) (t : ℕ) (st : State PK SK C Sym) : Bool :=
  sendEncapsGuard role st &&
    decide (st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) = (t : ℤ))

recall TargetInjection (PK SK C K : Type) : Type

recall TargetInjection.mk {PK SK C K : Type} (pk : PK) (sk : SK) (ct : C) (key : K) :
    TargetInjection PK SK C K

recall TargetInjection.pk {PK SK C K : Type} (inj : TargetInjection PK SK C K) : PK
recall TargetInjection.sk {PK SK C K : Type} (inj : TargetInjection PK SK C K) : SK
recall TargetInjection.ct {PK SK C K : Type} (inj : TargetInjection PK SK C K) : C
recall TargetInjection.key {PK SK C K : Type} (inj : TargetInjection PK SK C K) : K

section Injected

variable (kem : KEMScheme ProbComp K PK SK C)

recall injectedKeygen (role : Role) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) : ProbComp ((PK × SK) × Unit) :=
  if sendGeneratesTarget role t st then pure ((inj.pk, inj.sk), ())
  else do let keys ← kem.keygen; pure (keys, ())

recall injectedEncaps (role : Role) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) (pk : PK) : ProbComp ((C × K) × Unit) :=
  if sendEncapsulatesTarget role t st then pure ((inj.ct, inj.key), ())
  else do let out ← kem.encaps pk; pure (out, ())

recall injectedSend (role : Role)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (t : ℕ) (inj : TargetInjection PK SK C K) (st : State PK SK C Sym) :
    ProbComp (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym)) := do
  let out ← sendWith role (injectedKeygen kem role t inj st) (injectedEncaps kem role t inj st)
    ecEk ecCt st
  pure (out.map fun (key?, ρ, epoch, st', _) => (key?, ρ, epoch, st'))

variable [DecidableEq K] [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

recall injectedScheme (t : ℕ) (inj : TargetInjection PK SK C K) :
    SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) :=
  { scheme kem hDet ecEk ecCt leak with
      sendA := injectedSend kem .A ecEk ecCt t inj
      sendB := injectedSend kem .B ecEk ecCt t inj }

recall injectedCorrectnessImpl (t : ℕ) (inj : TargetInjection PK SK C K) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    + SCKAScheme.oracleSendA (injectedScheme kem hDet ecEk ecCt leak t inj)
    + SCKAScheme.oracleSendB (injectedScheme kem hDet ecEk ecCt leak t inj)
    + oracleRecvAIdeal kem hDet ecEk ecCt leak + oracleRecvBIdeal kem hDet ecEk ecCt leak

variable [SampleableType K]

recall injectedSecurityImpl (t : ℕ) (inj : TargetInjection PK SK C K) (random : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.securityImplOf (injectedCorrectnessImpl kem hDet ecEk ecCt leak t inj)
    (SCKAScheme.oracleChallOn random _ _ _ _) (exposure .A leak) (exposure .B leak)
    (scheme kem hDet ecEk ecCt leak)

end Injected

/-! ## The KEM reductions — `Security.Reduction`

`reduction` embeds its KEM challenge at a fixed target `t` and runs the adversary against the
injected oracles, stopped when `t` is exposed. `securityReduction` draws one target uniformly
from `1, …, 2q` and runs that reduction. -/

section Reduction

variable (kem : KEMScheme ProbComp K PK SK C)

variable [DecidableEq K] [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

variable [SampleableType K]

recall reductionRun (adv : SecurityAdversary leak Sym) (t : ℕ) (pkStar : PK) (cStar : C)
    (kStar : K) : ProbComp Bool := do
  let (_, dummySk) ← kem.keygen
  stoppedRun
    (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨pkStar, dummySk, cStar, kStar⟩
      (hybridRandom t))
    (targetExposed t) adv (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))

recall reduction (adv : SecurityAdversary leak Sym) (t : ℕ) : kem.IND_CPA_Adversary where
  State := PK
  preChallenge := pure
  postChallenge := fun pk c k => reductionRun kem hDet ecEk ecCt leak adv t pk c k

recall securityTargetChoice (n : ℕ) : ProbComp ℕ :=
  if hn : n = 0 then pure 1
  else
    letI : NeZero n := ⟨hn⟩
    (fun i : Fin n => i.val + 1) <$> ($ᵗ (Fin n) : ProbComp (Fin n))

recall securityReduction (adv : SecurityAdversary leak Sym) (q : ℕ) : kem.IND_CPA_Adversary where
  State := PK × ℕ
  preChallenge pk := do pure (pk, ← securityTargetChoice (2 * q))
  postChallenge st c k := reductionRun kem hDet ecEk ecCt leak adv st.2 st.1 c k

end Reduction

end oppBiKemCKA
