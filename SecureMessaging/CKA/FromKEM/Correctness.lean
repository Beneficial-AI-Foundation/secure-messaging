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

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

variable {K PK SK C : Type}

/-- One-step correctness for the KEM-based CKA construction.

The experiment samples an initial KEM key pair `(pk, sk)`, runs the honest-send
branch of `send` from `sendReady pk` inline — encapsulate under `pk`, then
generate the next key pair — and runs the CKA receive algorithm from
`recvReady sk` on the transmitted message `(c, pkNext)`. The receiver must
recover the sender's epoch key; receive failure counts as a correctness
failure, matching the generic CKA correctness oracle.

The target is probability exactly `1` because the statement is the CKA-shaped
form of the KEM perfect-correctness hypothesis `hkem`, itself an exact
`Pr[⋯] = 1` statement; the extra key-generation step only supplies the next
public key and does not affect the decapsulated key.
-/
theorem send_recv_agree [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    Pr[= true |
      do
        let (pk, sk) ← kem.keygen
        let (c, keyS) ← kem.encaps pk
        let (pkNext, _skNext) ← kem.keygen
        match recv hDet (.recvReady sk) (c, pkNext) with
        | none => return false
        | some (keyR, _) => return decide (keyR = keyS)] = 1 := by
  sorry

/-- Correctness of the CKA-from-KEM construction in the existing CKA correctness
game.

For every adversary using only the honest send/receive oracles, the game returns
`true` with probability one under the KEM correctness hypothesis. The statement
is proved for an arbitrary randomness-leak package `leak`: the correctness game
never queries the randomness-leaking send oracles, so correctness is independent
of the choice of `leak`.
-/
theorem correctness [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : CKAScheme.CKACorrectnessAdversary (Message C PK) K) :
    Pr[= true | CKAScheme.correctnessExp (scheme kem hDet leak) adv] = 1 := by
  sorry

end kemCKA
