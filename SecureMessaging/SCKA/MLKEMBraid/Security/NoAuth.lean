/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.Defs
public import SecureMessaging.SCKA.MLKEMBraid.Construction

/-!
# Braid without internal authentication

The authenticator keeps no state, emits unit tags and accepts every tag. For a send that reveals
its coins, the exposure functions `nativeExposure` expose the current epoch when the send generates
a key pair or runs the first stage of encapsulation. On every send output that the protocol can
produce, these epochs are `vuln st' \ vuln st`, as in the rule of [SCKA, Fig. 1]
(`sendExposure_eq_delta`).
-/

@[expose] public section

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
-- ANCHOR: noAuthScheme
def scheme (P : Parameters ProbComp)
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) :=
  MLKEMBraid.scheme P (auth P hMac) irl (pure ())
-- ANCHOR_END: noAuthScheme

/-- The epochs that revealing the local state exposes: none before key generation, while
awaiting a header, after receiving a header and before first-stage encapsulation, or after the
second stage of encapsulation, when the state keeps only the encoder of `ct₂` (`ct2Sampled`).
Otherwise the current epoch. -/
-- ANCHOR: noAuthVuln
def vuln {P : Parameters ProbComp} (st : State P Unit) : Finset ℕ :=
  match st with
  | .keysUnsampled .. | .noHeaderReceived .. | .headerReceived .. | .ct2Sampled .. => ∅
  | _ => {st.epoch}
-- ANCHOR_END: noAuthVuln

/-- The epochs that a send exposes when it reveals its coins: the current epoch for the coins of
key generation or of first-stage encapsulation, and none otherwise. -/
-- ANCHOR: noAuthSendExposure
def sendExposure {P : Parameters ProbComp} {KeygenRand Encaps1Rand : Type}
    (st : State P Unit) (coins : SendRand KeygenRand Encaps1Rand) : Finset ℕ :=
  match coins with
  | .none => ∅
  | .keygen _ | .encaps1 _ => {st.epoch}
-- ANCHOR_END: noAuthSendExposure

/-- The exposure functions of Braid without authentication: `vuln` for corruption and
`sendExposure` for a send that reveals its coins. -/
-- ANCHOR: nativeExposure
def nativeExposure (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.VulnerableEpochs (State P Unit)
      (SendRand irl.KeygenRand irl.Encaps1Rand) where
  corrupt := vuln
  rleak := sendExposure
-- ANCHOR_END: nativeExposure

/-- On every output of the leaking send from `st`, the epochs that the coins expose are
`vuln st' \ vuln st`, where `st'` is the new state. This is the rule of [SCKA, Fig. 1]. -/
theorem sendExposure_eq_delta
    (P : Parameters ProbComp) (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (st : State P Unit)
    (out : SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand)
    (hout : out ∈ support
      (MLKEMBraid.sendRleak P irl (auth P hMac) st)) :
    (nativeExposure P irl).rleak st out.2 = vuln out.1.state \ vuln st := by
  cases st
  case keysUnsampled e a =>
    simp only [MLKEMBraid.sendRleak, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨⟨⟨pk, sk⟩, r⟩, _, rfl⟩ := hout
    simp [nativeExposure, sendExposure, vuln, State.epoch]
  case headerReceived e a hdr dec =>
    simp only [MLKEMBraid.sendRleak, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨⟨⟨es, ct1, k⟩, r⟩, _, rfl⟩ := hout
    simp [nativeExposure, sendExposure, vuln, State.epoch]
  all_goals
    simp only [MLKEMBraid.sendRleak, MLKEMBraid.send, map_pure, mem_support_pure_iff] at hout
    subst hout
    simp [nativeExposure, sendExposure, vuln, State.epoch]

end MLKEMBraid.NoAuth
