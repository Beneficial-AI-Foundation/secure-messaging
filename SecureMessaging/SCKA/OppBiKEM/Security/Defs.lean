/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction
import SecureMessaging.SCKA.OppBiKEM.Correctness.RecvSpec
import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.Main
import SecureMessaging.ErasureCode.Payload
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Opp-BiKEM — Security definitions

**Frozen definitions.** The security theorems of Opp-BiKEM (`security`, `security_positive`,
`security_sum`, `security_uniform` in `Security`) are stated in terms of `scheme`, `exposure`,
`SecurityAdversary`, `SecuritySendQueryBound`, `reduction` and `securityReduction`. This module
holds every definition of the security modules that those statements depend on, transitively.
Changing any declaration here changes what the theorems say, while no declaration outside this
module does. The proof modules import it and may be changed freely as long as the statements of
their headline theorems are preserved; the proof-side games (`idealSecurityImpl`,
`hybridSecurityImpl`, `eagerSecurityImpl`, …) and every lemma live there.

The statements also depend on definitions outside the security modules: `scheme`, `sendWith`,
`recvA`, `recvB`, `vuln` and `SendRand` (`Construction`); `recvWith` (`Correctness.RecvSpec`)
and the initial game state `initState` (`Correctness.Quantitative.Main`);
`sckaSecuritySpec`, `SCKAAdversary`, `securityExp`, `sckaGuessAdvantage`, the game oracles and
`securityImplOf`, `oracleChallOn` (`SCKA.Defs`, `SCKA.Security`); `stoppedRun` (ToVCVio `Stop`);
`IND_CPA_Adversary`, `IND_CPA_Advantage`, `correctnessError`, `RandLeak`, `DeterministicDecaps`
(VCVio and ToVCVio `KeyEncapMech`); `ErasureCodePayload` and `ec.Correct` (`ErasureCode`).
`hybrid_hop_eq_reduction` additionally mentions the proof-side hybrid `hybridExp` (`Hybrid`).

**Contents.**

- The interface: `securitySpec`, `SecurityAdversary`, `SecuritySendQueryBound`.
- The exposure policy: `rleakEpochs`, `exposure`, and the send guards `sendKeygenGuard`,
  `sendEncapsGuard` that decide which operations a send performs.
- The ideal receive: `idealRecover`, `schemeWithRecv`, `oracleRecvAIdeal`, `oracleRecvBIdeal`.
- The challenge selection `hybridRandom` and the stopping test `targetExposed`.
- The KEM reduction: `sendGeneratesTarget`, `sendEncapsulatesTarget`, `TargetInjection`, the
  injected send and oracles (`injectedKeygen`, `injectedEncaps`, `injectedSend`,
  `injectedScheme`, `injectedCorrectnessImpl`, `injectedSecurityImpl`), `reductionRun` and
  `reduction`.
- The combined reduction: `securityTargetChoice` selects one positive target, and
  `securityReduction` runs its reduction. `Reduction` explains both adversaries; `Security`
  states their bounds.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-! ## The interface -/

/-- Opp-BiKEM's full SCKA oracle interface, with erasure-code symbols `Sym` and
coin types determined by `leak`. -/
abbrev securitySpec
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : kem.RandLeak) (Sym : Type) :=
  SCKAScheme.sckaSecuritySpec
    (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.EncapsRand)

/-- An adversary against `securitySpec leak Sym`, returning a Boolean guess. -/
abbrev SecurityAdversary
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : kem.RandLeak) (Sym : Type) :=
  SCKAScheme.SCKAAdversary
    (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.EncapsRand)

/-- Every oracle-response path of `adv` makes at most `q` ordinary or leaking sends in total.
Other queries may occur adaptively in any number and order. -/
-- ANCHOR: SecuritySendQueryBound
def SecuritySendQueryBound
    {kem : KEMScheme ProbComp K PK SK C}
    {leak : kem.RandLeak}
    (adv : SecurityAdversary leak Sym) (q : ℕ) : Prop :=
  adv.IsQueryBoundP
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) q
-- ANCHOR_END: SecuritySendQueryBound

/-! ## The exposure policy -/

/-- Positive epochs excluded by the presence of key-generation or encapsulation randomness.
The flags identify operations; the exclusion does not assert key reconstruction. -/
def rleakEpochs {RK RE : Type} (role : Role)
    (st : State PK SK C Sym) (rand : SendRand RK RE) : Finset ℕ :=
  let keyEpoch := st.res.resEpoch + 2 + role.offset
  let encEpoch := st.res.resEpoch + if rand.keygenRand.isSome then 2 else 0
  let epochs : Finset ℤ :=
    (if rand.keygenRand.isSome then {keyEpoch} else ∅) ∪
    (if rand.encapsRand.isSome then {encEpoch} else ∅)
  (epochs.filter fun e => 0 < e).image Int.toNat

/-- Build the conservative epoch-exclusion policy for state exposure and send randomness leakage.
Membership alone does not certify reconstruction or satisfy the oracle's acceptance guard. -/
def exposure {kem : KEMScheme ProbComp K PK SK C}
    (role : Role) (leak : kem.RandLeak) :
    SCKAScheme.VulnerableEpochs (State PK SK C Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) where
  corrupt := vuln
  rleak := rleakEpochs role

/-- Whether the send control flow generates a key pair and advances the responder epoch.
This guard constrains the local public key and ciphertext acknowledgements. -/
def sendKeygenGuard (role : Role) (st : State PK SK C Sym) : Bool :=
  st.req.ek.isNone &&
    decide (st.res.resEpoch ∈ st.ack.ctRec ∧
      st.res.resEpoch + role.offset ∈ st.ack.ctRec)

/-- The encapsulation control-flow guard, after any key-generation epoch advance and before
peer-key lookup. It does not assert that the peer key exists or that the send succeeds. -/
def sendEncapsGuard (role : Role) (st : State PK SK C Sym) : Bool :=
  let tRes := st.res.resEpoch + if sendKeygenGuard role st then 2 else 0
  decide (tRes + role.offset ∈ st.ack.ekRec) &&
    decide (tRes ∉ st.ack.ctRec) &&
    st.res.ct.isNone &&
    decide (tRes ∈ st.ack.ekRec)

/-! ## The ideal receive -/

/-- Recovery by the peer's recorded key: ignore the secret key and ciphertext and return the
peer's table entry for the received epoch. -/
def idealRecover (peerKey : ℕ → Option K) : ℤ → SK → C → Option K :=
  fun q _ _ => peerKey q.toNat

/-- The Opp-BiKEM scheme with both receive algorithms replaced. -/
def schemeWithRecv [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (recvA' : StA PK SK C Sym → Message Sym → Option (Option (ℕ × K) × ℕ × StA PK SK C Sym))
    (recvB' : StB PK SK C Sym → Message Sym → Option (Option (ℕ × K) × ℕ × StB PK SK C Sym)) :
    SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) :=
  { scheme kem hDet ecEk ecCt leak with recvA := recvA', recvB := recvB' }

/-- A's ideal receive oracle: A receives with B's recorded keys of the current game state in
place of decapsulation. -/
def oracleRecvAIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  fun n => do
    let s ← get
    SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n

/-- B's ideal receive oracle: B receives with A's recorded keys of the current game state in
place of decapsulation. -/
def oracleRecvBIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  fun n => do
    let s ← get
    SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n

/-! ## Challenge selection and stopping test -/

/-- Random challenge answers exactly at the epochs below the threshold `T`. -/
def hybridRandom (T : ℕ) : ℕ → Bool := fun t => decide (t < T)

/-- The stopping test for target epoch `t`: `t` is exposed. -/
def targetExposed (t : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Bool :=
  decide (t ∈ s.exposed)

/-! ## The KEM reduction -/

/-- Whether a send by `role` from `st` generates the key pair of key epoch `t`: the
key-generation guard holds and the new key epoch is `t`. -/
def sendGeneratesTarget (role : Role) (t : ℕ) (st : State PK SK C Sym) : Bool :=
  sendKeygenGuard role st && decide (st.res.resEpoch + 2 + role.offset = (t : ℤ))

/-- Whether a send by `role` from `st` encapsulates for epoch `t`: the encapsulation guard holds
and the responder epoch after any key-generation advance is `t`. -/
def sendEncapsulatesTarget (role : Role) (t : ℕ) (st : State PK SK C Sym) : Bool :=
  sendEncapsGuard role st &&
    decide (st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) = (t : ℤ))

/-- The values injected at the target epoch: the public key and secret of its key pair, and the
ciphertext and key of its encapsulation. -/
structure TargetInjection (PK SK C K : Type) where
  /-- The target epoch's public key. -/
  pk : PK
  /-- The secret stored for the target epoch. -/
  sk : SK
  /-- The target epoch's ciphertext. -/
  ct : C
  /-- The key recorded for the target epoch at encapsulation. -/
  key : K

section Injected

variable (kem : KEMScheme ProbComp K PK SK C)

/-- Key generation of an injected send from `st`: the injected pair if this send generates the
target's key pair, honest key generation otherwise. -/
def injectedKeygen (role : Role) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) : ProbComp ((PK × SK) × Unit) :=
  if sendGeneratesTarget role t st then pure ((inj.pk, inj.sk), ())
  else do let keys ← kem.keygen; pure (keys, ())

/-- Encapsulation of an injected send from `st`: the injected ciphertext and key if this send
encapsulates for the target epoch, honest encapsulation to the given public key otherwise. -/
def injectedEncaps (role : Role) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) (pk : PK) : ProbComp ((C × K) × Unit) :=
  if sendEncapsulatesTarget role t st then pure ((inj.ct, inj.key), ())
  else do let out ← kem.encaps pk; pure (out, ())

/-- The ordinary send with the target epoch's key generation and encapsulation replaced by the
injected values; the operations performed are decided from the initial state as in `sendWith`. -/
def injectedSend (role : Role) (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (t : ℕ) (inj : TargetInjection PK SK C K) (st : State PK SK C Sym) :
    ProbComp (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym)) := do
  let out ← sendWith role (injectedKeygen kem role t inj st) (injectedEncaps kem role t inj st)
    ecEk ecCt st
  pure (out.map fun (key?, ρ, epoch, st', _) => (key?, ρ, epoch, st'))

variable [DecidableEq K] [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-- The Opp-BiKEM scheme with both ordinary sends injected at target epoch `t`. Leaking sends and
receives are those of `scheme`. -/
def injectedScheme (t : ℕ) (inj : TargetInjection PK SK C K) :
    SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) :=
  { scheme kem hDet ecEk ecCt leak with
      sendA := injectedSend kem .A ecEk ecCt t inj
      sendB := injectedSend kem .B ecEk ecCt t inj }

/-- The injected correctness oracles: uniform sampling, the injected ordinary sends and the ideal
receives. -/
def injectedCorrectnessImpl (t : ℕ) (inj : TargetInjection PK SK C K) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    + SCKAScheme.oracleSendA (injectedScheme kem hDet ecEk ecCt leak t inj)
    + SCKAScheme.oracleSendB (injectedScheme kem hDet ecEk ecCt leak t inj)
    + oracleRecvAIdeal kem hDet ecEk ecCt leak + oracleRecvBIdeal kem hDet ecEk ecCt leak

variable [SampleableType K]

/-- The injected security oracles with challenge selection `random`: `securityImplOf` over the
injected correctness oracles, with the Opp-BiKEM exposure policy and the honest leaking sends
and corruptions of `scheme`. -/
def injectedSecurityImpl (t : ℕ) (inj : TargetInjection PK SK C K) (random : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.securityImplOf (injectedCorrectnessImpl kem hDet ecEk ecCt leak t inj)
    (SCKAScheme.oracleChallOn random _ _ _ _) (exposure .A leak) (exposure .B leak)
    (scheme kem hDet ecEk ecCt leak)

/-- The reduction's simulation at target `t` for the KEM challenge `(pkStar, cStar, kStar)`: draw
an independent key pair for the placeholder secret, then run the adversary against the injected
oracles with selection `hybridRandom t`, stopping with output `false` once `t` is exposed. -/
def reductionRun (adv : SecurityAdversary leak Sym) (t : ℕ) (pkStar : PK) (cStar : C)
    (kStar : K) : ProbComp Bool := do
  let (_, dummySk) ← kem.keygen
  stoppedRun
    (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨pkStar, dummySk, cStar, kStar⟩
      (hybridRandom t))
    (targetExposed t) adv (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))

/-- The IND-CPA reduction at target epoch `t`: it forwards the public key unchanged and runs
`reductionRun` on the challenge. -/
def reduction (adv : SecurityAdversary leak Sym) (t : ℕ) : kem.IND_CPA_Adversary where
  State := PK
  preChallenge := pure
  postChallenge := fun pk c k => reductionRun kem hDet ecEk ecCt leak adv t pk c k

/-- Choose uniformly from the positive epochs `1, …, n` when `n > 0`, and choose `1` when
`n = 0`. The combined reduction calls this sampler with `n = 2 * q`. -/
def securityTargetChoice (n : ℕ) : ProbComp ℕ :=
  if hn : n = 0 then pure 1
  else
    letI : NeZero n := ⟨hn⟩
    (fun i : Fin n => i.val + 1) <$> ($ᵗ (Fin n) : ProbComp (Fin n))

/-- The combined IND-CPA reduction: choose a target uniformly from `1, …, 2q` before the
challenge, retain it with the public key, and run that target's simulation on the challenge.
For `q = 0`, the target is `1`. -/
-- ANCHOR: securityReduction
def securityReduction (adv : SecurityAdversary leak Sym) (q : ℕ) : kem.IND_CPA_Adversary where
  State := PK × ℕ
  preChallenge pk := do pure (pk, ← securityTargetChoice (2 * q))
  postChallenge st c k := reductionRun kem hDet ecEk ecCt leak adv st.2 st.1 c k
-- ANCHOR_END: securityReduction

end Injected

end oppBiKemCKA
