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

/-- The CKA adversary interface specialized to the leaking KEM construction.

The adversary receives the generic CKA security oracle family with the
send-randomness type `KEMRandLeak.Rand leak`: the randomness of KEM
encapsulation paired with the randomness of the fresh next KEM key pair.
-/
abbrev Adversary {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : KEMRandLeak kem) :=
  CKAScheme.CKAAdversary (State PK SK) (Message C PK) K leak.Rand

/-- IND-CPA reductions generated from CKA adversaries. -/
abbrev INDCPAReduction [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (leak : KEMRandLeak kem)
    (_adv : Adversary (kem := kem) leak)
    (_gp : CKAScheme.GameParams) :=
  KEMScheme.IND_CPA_Adversary kem

/-- Existential security-reduction statement for CKA from a KEM.

For every CKA adversary and admissible challenge parameters, there exists an
IND-CPA adversary against the input KEM whose advantage upper-bounds the
CKA security advantage of the constructed protocol.

The statement is intentionally existential: this specification PR records the
proof obligation. A later proof PR should refine the existential witness to a
named concrete reduction.
-/
theorem security_reduces_to_ind_cpa_exists [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    ∃ red : INDCPAReduction kem leak adv gp,
      CKAScheme.ckaGuessAdvantage (scheme kem hDet leak) adv gp ≤
        KEMScheme.IND_CPA_Advantage (kem := kem) ProbCompRuntime.probComp red := by
  sorry

end kemCKA
