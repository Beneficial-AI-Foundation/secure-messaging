/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Cancellation

/-!
# Opp-BiKEM — The KEM reduction

**Setting.** Fix a target epoch `t`. The IND-CPA adversary `R_t := reduction … adv t` against
`kem` receives a public key `pkStar` and a challenge `(cStar, kStar)`, where `kStar` is either
the encapsulated key or an independent uniform key, and runs `adv` against the *injected
oracles* `injectedSecurityImpl t ⟨pkStar, dummySk, cStar, kStar⟩ (hybridRandom t)`, stopped at
the first exposure of `t` (`reductionRun`):

```text
R_t.pre(pkStar):          return pkStar
R_t.post(cStar, kStar):   (_, dummySk) ← kem.keygen
                          run adv against the injected oracles from the initial state
                          return false if stopped, else the output of adv
```

The injected oracles answer as the ideal security game (`IdealReceive`), except:

| Operation                                      | Answer                                      |
| ---------------------------------------------- | ------------------------------------------- |
| the owner's key generation for key epoch `t`   | `pkStar`, with placeholder secret `dummySk` |
| the peer's encapsulation for epoch `t`         | `(cStar, kStar)`                            |
| eligible challenge at epoch `e`                | uniform if `e < t`, else the recorded key   |
| corruption or leaking send exposing `t`        | stop with output `false`                    |

In particular the challenge of `t` returns the recorded `kStar`. Whether a send generates the
key pair of `t` or encapsulates for `t` is decided from the sender's state before the send, as
`sendWith` decides its operations (`sendGeneratesTarget`, `sendEncapsulatesTarget`). Receives
are ideal, so the placeholder secret is never read. The same injected oracles with the honest
secret and the encapsulated key describe the hybrids with eagerly drawn samples (`Eager`), and
the simulation theorem relating them to `R_t` is `probOutput_stoppedEagerExp_eq_reductionRun`
(`Simulation`). Every definition here is computable.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

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

/-- With no injection at any send, the injected send is the ordinary send. -/
lemma injectedSend_eq_send (role : Role) (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) (hgen : sendGeneratesTarget role t st = false)
    (henc : sendEncapsulatesTarget role t st = false) :
    injectedSend kem role ecEk ecCt t inj st = send role kem ecEk ecCt st := by
  have henc' : injectedEncaps kem role t inj st =
      (fun pk => (do let out ← kem.encaps pk; pure (out, ()))) := by
    funext pk
    simp only [injectedEncaps, henc, Bool.false_eq_true, ↓reduceIte]
  simp only [injectedSend, injectedKeygen, hgen, Bool.false_eq_true, ↓reduceIte, henc', send]

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

/-- The reduction does nothing before the challenge. -/
@[simp] lemma reduction_preChallenge (adv : SecurityAdversary leak Sym) (t : ℕ) (pk : PK) :
    (reduction kem hDet ecEk ecCt leak adv t).preChallenge pk = pure pk := rfl

/-- The reduction's post-challenge phase is `reductionRun`. -/
@[simp] lemma reduction_postChallenge (adv : SecurityAdversary leak Sym) (t : ℕ) (pk : PK)
    (c : C) (k : K) :
    (reduction kem hDet ecEk ecCt leak adv t).postChallenge pk c k =
      reductionRun kem hDet ecEk ecCt leak adv t pk c k := rfl

end Injected

end oppBiKemCKA
