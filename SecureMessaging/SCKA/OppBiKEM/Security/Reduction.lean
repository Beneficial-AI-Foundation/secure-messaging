/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Cancellation

/-!
# Opp-BiKEM — The KEM reduction

The definitions below are in `Defs`; this module records their basic laws.

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
the simulation theorem relating them to `R_t` is `prEvent_stoppedEagerExp_eq_reductionRun`
(`Simulation`). Every definition is computable.

The combined adversary `B := securityReduction … adv q` draws one target uniformly from
`1, …, 2q` using `securityTargetChoice`, stores it with `pkStar`, and runs the same simulation:

```text
B.pre(pkStar):            t ← securityTargetChoice (2q)
                          return (pkStar, t)
B.post((pkStar, t), c, k): run reductionRun … adv t pkStar c k
```

For `q = 0`, the target is `1`. The target draw is independent of the KEM material. Averaging
its signed branch gaps telescopes to the endpoint hybrid gap divided by `2q` for `q > 0`
(`securityReduction_signed_gap_eq`, `Proofs`), giving the single-adversary bound `security`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

section Injected

variable (kem : KEMScheme ProbComp K PK SK C)

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

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

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
