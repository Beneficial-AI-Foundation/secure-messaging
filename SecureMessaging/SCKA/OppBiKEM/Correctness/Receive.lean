/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness.Receive
import SecureMessaging.SCKA.OppBiKEM.Correctness.Invariant

/-!
# Opp-BiKEM recorded receives and current epochs

For a supported successful receive from message-epoch-consistent tables, the
receiver's current epoch is the maximum of its old value and the delivered
message's sending epoch. The other party's current epoch is unchanged.

The outer `some` hypothesis neither asserts `correct = true` nor guarantees
successful receipt of every recorded message.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- A successful recorded receive at A updates its horizon using the message epoch. -/
theorem oracleRecvA_recorded_currentEpoch
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (s s' : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : MessageEpochsConsistent s)
    (n trcv : ℕ) (tI : Option ℕ)
    (hout : (some (trcv, tI), s') ∈ support
      ((SCKAScheme.oracleRecvA (scheme kem hDet ecEk ecCt leak) n).run s)) :
    ∃ ρ : Message Sym,
      s.msgB n = some (ρ, trcv) ∧
      ρ.sendingEpoch = trcv ∧
      s'.tcurA = max s.tcurA ρ.sendingEpoch ∧
      s'.tcurB = s.tcurB := by
  obtain ⟨ρ, hmsg, hepoch⟩ :=
    oracleRecvA_matches_recorded_epoch kem hDet ecEk ecCt leak s s' hs n trcv tI hout
  have hcurrent := SCKAScheme.oracleRecvA_success_currentEpoch
    (scheme kem hDet ecEk ecCt leak) s s' n trcv tI hout
  refine ⟨ρ, hmsg, hepoch, ?_, hcurrent.2⟩
  simpa only [hepoch] using hcurrent.1

/-- A successful recorded receive at B updates its horizon using the message epoch. -/
theorem oracleRecvB_recorded_currentEpoch
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (s s' : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : MessageEpochsConsistent s)
    (n trcv : ℕ) (tI : Option ℕ)
    (hout : (some (trcv, tI), s') ∈ support
      ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s)) :
    ∃ ρ : Message Sym,
      s.msgA n = some (ρ, trcv) ∧
      ρ.sendingEpoch = trcv ∧
      s'.tcurB = max s.tcurB ρ.sendingEpoch ∧
      s'.tcurA = s.tcurA := by
  obtain ⟨ρ, hmsg, hepoch⟩ :=
    oracleRecvB_matches_recorded_epoch kem hDet ecEk ecCt leak s s' hs n trcv tI hout
  have hcurrent := SCKAScheme.oracleRecvB_success_currentEpoch
    (scheme kem hDet ecEk ecCt leak) s s' n trcv tI hout
  refine ⟨ρ, hmsg, hepoch, ?_, hcurrent.2⟩
  simpa only [hepoch] using hcurrent.1

end oppBiKemCKA
