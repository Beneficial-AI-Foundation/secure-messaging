/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Construction

/-!
# The exposure policy E⁺

`successorExposure` exposes the stored epoch and its successor on every corruption, and on every
send that reveals the coins of key generation or of first-stage encapsulation.

This policy is stated in the native form of the SCKA security game: a function of the state
before the query. It has no counterpart in the delta form `vuln st' \ vuln st` of [SCKA, Fig. 1]:
key generation keeps the epoch of the state, so the delta of the set `{epoch, epoch + 1}` is empty
on that send. The policy is conservative; no claim is made that it is the least policy for which
the security theorem holds.
-/

@[expose] public section

namespace MLKEMBraid.Auth

open Braid

/-- Every corruption exposes the stored epoch and its successor; a leak of key-generation or
first-stage encapsulation coins exposes both; other leaks expose nothing. -/
def successorExposure (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc)
    (Root MacKey : Type) :
    SCKAScheme.VulnerableEpochs (State P (Root × MacKey))
      (SendRand irl.KeygenRand irl.Encaps1Rand) where
  corrupt st := {st.epoch, st.epoch + 1}
  rleak st coins := match coins with
    | .none => ∅
    | .keygen _ | .encaps1 _ => {st.epoch, st.epoch + 1}

end MLKEMBraid.Auth
