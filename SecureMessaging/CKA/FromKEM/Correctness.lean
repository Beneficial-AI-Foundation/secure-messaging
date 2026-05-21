/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Construction

/-!
# CKA from KEM — Correctness Statements

This file states the correctness properties for the generic CKA-from-KEM
construction of [ACD19, Section 4.1.2].

The KEM correctness property is:

```
(pk, sk) ← keygen
(c, k)   ← encaps pk
k'       ← decaps sk c
return k' = some k
```

Perfect correctness means this experiment succeeds with probability exactly 1.
-/

open OracleSpec OracleComp ENNReal

namespace kemCKA

variable {K PK SK C : Type}

/-- One-step correctness for the KEM-based CKA construction.

The experiment samples an initial KEM key pair `(pk, sk)`, runs the CKA send
algorithm from `sendReady pk`, and then runs the matching CKA receive algorithm
from `recvReady sk` on the transmitted message. Under the hypothesis that
honestly generated KEM encapsulations always decapsulate to the encapsulated
key, the receiver recovers the sender's epoch key with probability one.

This is the local correctness obligation for the state transition in
[ACD19, Section 4.1.2]: after sending `(c, pk')`, the sender stores `sk'`,
while the receiver stores `pk'` for the next phase.
-/
theorem send_recv_agree [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    Pr[= true |
      do
        let (pk, sk) ← kem.keygen
        let sent? ← send kem (.sendReady pk)
        match sent? with
        | none => return false
        | some (keyS, msg, _) =>
            match recv hDet (.recvReady sk) msg with
            | none => return false
            | some (keyR, _) => return decide (keyR = keyS)] = 1 := by
  sorry

/-- Correctness of the CKA-from-KEM construction in the existing CKA correctness
game.

For every adversary using only the honest send/receive oracles, the game returns
`true` with probability one under the KEM correctness hypothesis.
-/
theorem correctness [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : CKAScheme.CKACorrectnessAdversary (Message C PK) K) :
    Pr[= true | CKAScheme.correctnessExp (kemCKA kem hDet) adv] = 1 := by
  sorry

end kemCKA
