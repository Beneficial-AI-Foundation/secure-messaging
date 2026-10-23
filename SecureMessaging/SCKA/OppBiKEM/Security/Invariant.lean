/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.RecvStep
import SecureMessaging.SCKA.OppBiKEM.Security.Exposure
import SecureMessaging.SCKA.Security

/-!
# Opp-BiKEM — Security oracle invariant

With deterministic decapsulation and correct erasure codes, every supported security-query
output satisfies `GameInv` when the current state satisfies the invariant and has no current
KEM failure.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Replacing the exposed and challenged sets by arbitrary finite sets preserves `GameInv`. -/
theorem gameInv_with_security_bookkeeping
    {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym}
    {ecCt : ErasureCodePayload C Sym}
    {s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)}
    (h : GameInv kem ecEk ecCt s)
    (exposed challenged : Finset ℕ) :
    GameInv kem ecEk ecCt
      { s with exposed := exposed, challenged := challenged } :=
  h

/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* the current state satisfies `GameInv`;
* the current state has no KEM failure.

Then every supported output of any security query satisfies `GameInv`, for either challenge bit.
-/
theorem security_gameInv_step_of_noFailure
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct)
    (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak)
    (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s)
    (hfail : kemFailure hDet s = false) :
    ∀ z ∈ support ((SCKAScheme.sckaSecurityImpl b
        (exposure .A leak) (exposure .B leak)
        (scheme kem hDet ecEk ecCt leak) t).run s),
      GameInv kem ecEk ecCt z.2 := by
  intro z hz
  exact SCKAScheme.securityImplOf_preserves_at_of_book _ _ _ _ _
    (GameInv kem ecEk ecCt)
    (fun _ E C h => gameInv_with_security_bookkeeping h E C)
    (sendWith_rleak_forget kem .A ecEk ecCt leak)
    (sendWith_rleak_forget kem .B ecEk ecCt leak) s hs
    (fun t => gameInv_step_of_noFailure kem hDet ecEk ecCt hEk hCt leak t s hs hfail)
    (fun t => SCKAScheme.oracleChall_preservesInv b _
      (fun s C h => by simpa using gameInv_with_security_bookkeeping h s.exposed C) t s hs)
    (gameInv_step_of_noFailure kem hDet ecEk ecCt hEk hCt leak
      SCKAScheme.sckaCorrectnessSpec.OSendA s hs hfail)
    (gameInv_step_of_noFailure kem hDet ecEk ecCt hEk hCt leak
      SCKAScheme.sckaCorrectnessSpec.OSendB s hs hfail) t z hz

end oppBiKemCKA
