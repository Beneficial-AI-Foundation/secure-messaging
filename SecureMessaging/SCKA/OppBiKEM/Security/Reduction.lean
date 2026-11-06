/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.OppBiKEM.Security.Cancellation
public import SecureMessaging.SCKA.OppBiKEM.Security.Injected

/-!
# Opp-BiKEM — The KEM reduction

This module defines the fixed-target and combined IND-CPA adversaries and their pre- and
post-challenge behavior. Their simulations use the oracle implementation from `Injected`.

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

The injected oracles (`Injected`) answer as the ideal security game (`IdealReceive`), except:

| Operation                                      | Answer                                      |
| ---------------------------------------------- | ------------------------------------------- |
| the owner's key generation for key epoch `t`   | `pkStar`, with placeholder secret `dummySk` |
| the peer's encapsulation for epoch `t`         | `(cStar, kStar)`                            |
| eligible challenge at epoch `e`                | uniform if `e < t`, else the recorded key   |
| corruption or leaking send exposing `t`        | stop with output `false`                    |


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

@[expose] public section

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

section Reduction

variable (kem : KEMScheme ProbComp K PK SK C)

variable [DecidableEq K] [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

variable [SampleableType K]

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

end Reduction

section ReductionLemmas

variable (kem : KEMScheme ProbComp K PK SK C)

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-- The reduction's pre-challenge phase returns the given public key. -/
@[simp] lemma reduction_preChallenge (adv : SecurityAdversary leak Sym) (t : ℕ) (pk : PK) :
    (reduction kem hDet ecEk ecCt leak adv t).preChallenge pk = pure pk := rfl

/-- The reduction's post-challenge phase is `reductionRun`. -/
@[simp] lemma reduction_postChallenge (adv : SecurityAdversary leak Sym) (t : ℕ) (pk : PK)
    (c : C) (k : K) :
    (reduction kem hDet ecEk ecCt leak adv t).postChallenge pk c k =
      reductionRun kem hDet ecEk ecCt leak adv t pk c k := rfl

end ReductionLemmas

end oppBiKemCKA
