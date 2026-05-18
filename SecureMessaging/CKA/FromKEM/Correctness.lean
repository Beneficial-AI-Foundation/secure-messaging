/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Construction

/-!
# CKA from KEM — Correctness Statements

This file states the correctness properties for the generic CKA-from-KEM
construction of [ACD19, Section 4.1.2].

The deliverable for Issue #3 is the specification surface: definitions and
property statements. Proofs are intentionally left as `sorry` for later PRs.
-/

open OracleSpec OracleComp ENNReal

namespace kemCKA

variable {K PK SK C : Type}

/-- One honest KEM-CKA send followed by the matching receive produces the same
epoch key, assuming the underlying VCV-io KEM is perfectly correct.

This is the local, one-step correctness statement behind the game theorem:
if a sender encapsulates to `pk`, publishes `(c, pk')`, and stores `sk'`, then
the receiver holding the matching `sk` decapsulates `c` to the sender's key and
stores `pk'` for the next send phase.

The statement is phrased as a probability-1 support property rather than by
opening the internals of `ProbComp`, so later proof work can choose the most
convenient VCV-io support lemmas.
-/
theorem send_recv_agree [DecidableEq K]
    (kem : KEMForCKA ProbComp K PK SK C)
    (hkem : kem.toKEM.PerfectlyCorrect ProbCompRuntime.probComp) :
    Pr[= true |
      do
        let (pk, sk) ← kem.toKEM.keygen
        let sent? ← send kem (.sendReady pk)
        match sent? with
        | none => return false
        | some (keyS, msg, _) =>
            match recv kem (.recvReady sk) msg with
            | none => return false
            | some (keyR, _) => return decide (keyR = keyS)] = 1 := by
  sorry

/-- Correctness of the CKA-from-KEM construction in the existing CKA correctness
game.

For every adversary using only the honest send/receive oracles, the game returns
`true` with probability one, provided the underlying KEM is perfectly correct.

Crypto reading: the CKA epoch key produced by the sender is exactly the key
recovered by the receiver at each delivered epoch. This is the CKA analogue of
KEM decapsulation recovering the encapsulated shared key.
-/
theorem correctness [DecidableEq K]
    (kem : KEMForCKA ProbComp K PK SK C)
    (hkem : kem.toKEM.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : CKAScheme.CKACorrectnessAdversary (Message C PK) K) :
    Pr[= true | CKAScheme.correctnessExp (kemCKA kem) adv] = 1 := by
  sorry

end kemCKA
