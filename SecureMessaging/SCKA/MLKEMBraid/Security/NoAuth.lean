/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Exposure
import SecureMessaging.SCKA.MLKEMBraid.Construction

/-!
# Braid without internal authentication

The authenticator keeps no state, emits unit tags and accepts every tag. The exposure policy
`exposure` exposes the current epoch when a send that reveals its coins generates a key pair or
runs the first stage of encapsulation. On every send output that the protocol can produce, this
policy agrees with the rule `vuln st' \ vuln st` (`sendExposure_eq_delta`).
-/

open OracleComp

namespace MLKEMBraid.NoAuth

/-- The authenticator with unit state and unit tags that accepts every tag. -/
-- ANCHOR: noAuthAuthenticator
def auth (P : Parameters ProbComp) (hMac : P.Mac = Unit) :
    RatchetedAuthenticator Unit P.EpochKey Unit
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac where
  init := fun _ _ => ()
  update := fun _ _ _ => ()
  macHeader := fun _ _ _ => hMac.symm ▸ ()
  macCiphertext := fun _ _ _ => hMac.symm ▸ ()
  verifyHeader := fun _ _ _ _ => true
  verifyCiphertext := fun _ _ _ _ => true
  verifyHeader_correct := fun _ _ _ => rfl
  verifyCiphertext_correct := fun _ _ _ => rfl
-- ANCHOR_END: noAuthAuthenticator

/-- The Braid scheme with the authenticator `auth`. -/
def scheme (P : Parameters ProbComp) [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) :=
  MLKEMBraid.scheme P (auth P hMac) irl (pure ())

/-- The epochs that revealing the local state exposes: none before key generation, while
awaiting a header, or after receiving a header and before first-stage encapsulation. Otherwise
the current epoch. -/
def vuln {P : Parameters ProbComp} (st : State P Unit) : Finset ℕ :=
  match st with
  | .keysUnsampled .. | .noHeaderReceived .. | .headerReceived .. => ∅
  | _ => {st.epoch}

/-- The epochs that a send exposes when it reveals its coins: the current epoch for the coins of
key generation or of first-stage encapsulation, and none otherwise. The new state is not used. -/
def sendExposure {P : Parameters ProbComp} {KeygenRand Encaps1Rand : Type}
    (st _st' : State P Unit) (coins : SendRand KeygenRand Encaps1Rand) : Finset ℕ :=
  match coins with
  | .none => ∅
  | .keygen _ | .encaps1 _ => {st.epoch}

/-- The exposure policy of Braid without authentication: `vuln` for corruption and
`sendExposure` for a send that reveals its coins. -/
def exposure (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.ExposurePolicy (State P Unit)
      (SendRand irl.KeygenRand irl.Encaps1Rand) where
  corrupt := vuln
  send := sendExposure

/-- The exposure policy with the send rule `vuln st' \ vuln st` of [SCKA, Fig. 1]. -/
def deltaExposure (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.ExposurePolicy (State P Unit)
      (SendRand irl.KeygenRand irl.Encaps1Rand) :=
  SCKAScheme.ExposurePolicy.ofDelta vuln

/-- On every output that the leaking send can produce, `sendExposure` equals the rule
`vuln st' \ vuln st`. -/
theorem sendExposure_eq_delta
    (P : Parameters ProbComp) (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (st : State P Unit)
    (out : SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand)
    (hout : out ∈ support
      (MLKEMBraid.sendRleak P irl (auth P hMac) st)) :
    (exposure P irl).send st out.1.state out.2 =
      vuln out.1.state \ vuln st := by
  cases st
  case keysUnsampled e a =>
    simp only [MLKEMBraid.sendRleak, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨⟨⟨pk, sk⟩, r⟩, _, rfl⟩ := hout
    simp [exposure, sendExposure, vuln, State.epoch]
  case headerReceived e a hdr dec =>
    simp only [MLKEMBraid.sendRleak, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨⟨⟨es, ct1, k⟩, r⟩, _, rfl⟩ := hout
    simp [exposure, sendExposure, vuln, State.epoch]
  all_goals
    simp only [MLKEMBraid.sendRleak, MLKEMBraid.send, map_pure, mem_support_pure_iff] at hout
    subst hout
    simp [exposure, sendExposure, vuln, State.epoch]

end MLKEMBraid.NoAuth
