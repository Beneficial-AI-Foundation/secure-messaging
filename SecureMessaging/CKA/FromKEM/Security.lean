/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Correctness

/-!
# CKA from KEM — Security Statements

This file states the security property for the generic CKA-from-KEM construction
of [ACD19, Section 4.1.2].

The paper's Theorem 2 says that the generic KEM-based construction has
`Delta_CKA = 0` and reduces CKA security to KEM security. 

Only statement-level content belongs in this PR. The reduction adversary and
the game-hopping proof are intentionally represented by theorem signatures with
`sorry` bodies.
-/

open OracleSpec OracleComp ENNReal

namespace kemCKA

variable {K PK SK C : Type}

/-- The challenged epoch must be a send epoch for the challenged party in the
A-first alternating CKA game.

The CKA game starts with A sending. Since both send/challenge and receive
increment the local party counter, A can be challenged on odd send counters and
B on positive even send counters.
-/
def challengeEpochCompatible (gp : CKAScheme.GameParams) : Prop :=
  match gp.challengedParty with
  | .A => gp.challengeEpoch % 2 = 1
  | .B => gp.challengeEpoch % 2 = 0 ∧ 0 < gp.challengeEpoch

/-- Parameter admissibility for applying the generic KEM-to-CKA security
statement.

* `ΔFS = 0` records the paper's claim that the generic KEM construction achieves
  optimal forward-secrecy delay.
* `2 ≤ ΔPCS` records the paper/game convention that corruptions and randomness
  leaks are excluded less than two epochs before the challenge.
* `challengeEpochCompatible` says the static challenge epoch is actually a send
  epoch for the challenged party in the A-first alternating game.
-/
structure AdmissibleParams (gp : CKAScheme.GameParams) : Prop where
  deltaFS_zero : gp.ΔFS = 0
  two_le_deltaPCS : 2 ≤ gp.ΔPCS
  challenge_epoch_compatible : challengeEpochCompatible gp

/-- The CKA adversary interface specialized to the KEM construction.

This is a named alias for discoverability: the adversary receives the same
send/receive/challenge/corrupt/randomness-leak oracle family as the generic CKA
security game, with `Rand = Unit` because the current VCV-io KEM interface does
not expose explicit KEM coins.
-/
abbrev Adversary (K PK SK C : Type) :=
  CKAScheme.CKAAdversary (State PK SK) (Message C PK) K Unit

/-- IND-CPA reductions generated from CKA adversaries.

`ProbComp` is definitionally `OracleComp unifSpec`, so the existing VCV-io
KEM IND-CPA adversary interface applies directly to `kem.toKEM`.
-/
abbrev INDCPAReduction [SampleableType K]
    (kem : KEMForCKA ProbComp K PK SK C)
    (_adv : Adversary K PK SK C)
    (_gp : CKAScheme.GameParams) :=
  kem.toKEM.IND_CPA_Adversary

/-- Main security statement for CKA from a KEM.

For every CKA adversary and admissible challenge parameters, there exists an
IND-CPA adversary against the underlying KEM whose advantage upper-bounds the
CKA security advantage of the constructed protocol.

Crypto reading: the only challenge key that can help the CKA adversary is the
KEM encapsulated key at the challenged send. Since the adversary never receives
a KEM decapsulation oracle in this passive CKA model, IND-CPA is the intended
KEM assumption for this statement.
-/
theorem security_reduces_to_ind_cpa [SampleableType K] [DecidableEq K]
    (kem : KEMForCKA ProbComp K PK SK C)
    (adv : Adversary K PK SK C)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    ∃ red : INDCPAReduction kem adv gp,
      CKAScheme.securityAdvantage (kemCKA kem) adv gp ≤
        kem.toKEM.IND_CPA_Advantage ProbCompRuntime.probComp red := by
  sorry

end kemCKA
