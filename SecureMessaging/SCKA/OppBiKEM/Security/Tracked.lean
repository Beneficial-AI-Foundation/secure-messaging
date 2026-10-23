/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.Main
import SecureMessaging.SCKA.OppBiKEM.Security.Invariant

/-!
# Opp-BiKEM — Security runs with a sticky failure flag

With deterministic decapsulation and correct erasure codes, every supported adaptive security
run from the initial state satisfies `GameInv` when its historical KEM-failure flag is clear.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The existing security oracles with a never-cleared flag recording current KEM failure
after each query. -/
abbrev trackedSecurityImpl
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool)
        ProbComp) :=
  trackedImpl
    (SCKAScheme.sckaSecurityImpl b (exposure .A leak) (exposure .B leak)
      (scheme kem hDet ecEk ecCt leak))
    (kemFailure hDet)

/-- With deterministic decapsulation and correct erasure codes, the tracked security oracles
preserve `trackedInv`: the flag is set, or `GameInv` holds without current KEM failure. -/
theorem trackedSecurityImpl_preservesInv
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct)
    (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak)
    (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem hDet ecEk ecCt leak b)
      (trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet)) :=
  trackedImpl_preserves _ _ _
    (security_gameInv_step_of_noFailure kem hDet ecEk ecCt hEk hCt leak b)

/-- A supported outcome of a tracked security run from the initial state whose historical
KEM-failure flag is clear satisfies `GameInv` and has no current KEM failure. -/
lemma security_noFailure_of_flag_false
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct)
    (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak)
    (b : Bool)
    {α : Type}
    (adv : OracleComp (securitySpec leak Sym) α)
    (z : α ×
      (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool))
    (hz : z ∈ support
      ((simulateQ (trackedSecurityImpl kem hDet ecEk ecCt leak b) adv).run
        (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym), false)))
    (hflag : z.2.2 = false) :
    GameInv kem ecEk ecCt z.2.1 ∧ kemFailure hDet z.2.1 = false :=
  trackedInv_of_flag_false
    (simulateQ_run_preservesInv _ _
      (trackedSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak b) adv _
      (trackedInv_init kem hDet ecEk ecCt) z hz) hflag

/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `z` is a supported outcome of an arbitrary adaptive security computation `adv` from the
  initial state with its historical KEM-failure flag initially clear;
* the historical KEM-failure flag in `z` is clear.

Then the final game state satisfies `GameInv`, for either challenge bit.
-/
theorem security_gameInv_of_noFailure
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct)
    (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak)
    (b : Bool)
    {α : Type}
    (adv : OracleComp (securitySpec leak Sym) α)
    (z : α ×
      (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool))
    (hz : z ∈ support
      ((simulateQ (trackedSecurityImpl kem hDet ecEk ecCt leak b) adv).run
        (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym), false)))
    (hflag : z.2.2 = false) :
    GameInv kem ecEk ecCt z.2.1 :=
  (security_noFailure_of_flag_false kem hDet ecEk ecCt hEk hCt leak b adv z hz hflag).1

end oppBiKemCKA
