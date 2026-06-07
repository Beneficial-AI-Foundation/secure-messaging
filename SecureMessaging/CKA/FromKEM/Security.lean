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
`Delta_CKA = 0` and reduces CKA security to KEM security. The paper's proof is
constructive: it builds an explicit IND-CPA adversary from the CKA adversary.
The statement below is an existential placeholder for that theorem; the proof
PR for issue #5 will replace it with a statement about a concrete reduction,
an explicitly constructed IND-CPA adversary proved to satisfy the bound.
-/

open OracleSpec OracleComp ENNReal KEMScheme

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
send-randomness type `RandLeak.Rand leak`: the randomness of KEM encapsulation
paired with the randomness of the fresh next KEM key pair.
-/
abbrev Adversary {K PK SK C : Type}
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem) :=
  CKAScheme.CKAAdversary (State PK SK) (Message C PK) K leak.Rand

/-- Existential security-reduction statement for CKA from a KEM.

For every perfectly correct KEM, CKA adversary, and admissible challenge
parameters, there exists an IND-CPA adversary against the KEM whose advantage
upper-bounds the CKA distinguishing advantage of the constructed protocol.
The bound compares like with like: `CKAScheme.ckaDistAdvantage` is the gap
between the real-key and random-key branches of the CKA game (twice
`CKAScheme.ckaGuessAdvantage`), and `KEMScheme.IND_CPA_Advantage` is the
Boolean bias `|Pr[true] - Pr[false]|` of the single IND-CPA game.

The statement is an existential placeholder, not the final form of [ACD19,
Theorem 2], whose proof is constructive. The proof PR for issue #5 will
replace the existential with a concrete reduction — an explicitly constructed
IND-CPA adversary — and prove this bound for it.
-/
theorem security_reduces_to_ind_cpa_exists [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    ∃ red : KEMScheme.IND_CPA_Adversary kem,
      CKAScheme.ckaDistAdvantage (scheme kem hDet leak) adv gp ≤
        KEMScheme.IND_CPA_Advantage (kem := kem) ProbCompRuntime.probComp red := by
  sorry

end kemCKA
