/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Authenticator
public import VCVio.CryptoFoundations.PRG

/-!
# Key hiding of a ratcheted authenticator

Let `auth` be a ratcheted authenticator and `sampleInitKey` a sampler of its initial keys. For an
epoch `e`, an initial key `ik` and an epoch key `κ`, the authenticator state *entering* `e`,
computed from a state `a`, is `auth.init ik 1` if `e = 1` and
`auth.update a (e - 1) κ` otherwise (`hiddenState`). The *hidden operations* on it are the header
tag and its verification at `e`, the ciphertext tag and its verification at `e - 1`, and the
update at `e` with an epoch key `u` (`hiddenAuth`).

A key-hiding adversary `adv` chooses an epoch `e` and keeps a state. It then receives an epoch key
and the hidden operations, for `ik ← sampleInitKey` and uniform `κ` and `u`, and outputs a bit. The
experiment `authHideExp auth sampleInitKey adv real` hands it `u` if `real` and an independent
uniform key otherwise. The advantage `authHideAdvantage auth sampleInitKey adv` is the difference
in acceptance probability between the two experiments,
`|Pr[authHideExp … adv true = true] - Pr[authHideExp … adv false = true]|`.
-/

@[expose] public section

open OracleSpec OracleComp

namespace Braid

/-- The operations of an authenticator on a hidden state, as functions of a state `a`:
the header tag and its verification, the ciphertext tag and its verification, and the update. The
verifications accept honest tags. -/
structure HiddenAuth (AuthState Header Ciphertext Mac : Type) where
  /-- The header tag under the hidden state of `a`. -/
  macHeader : AuthState → Header → Mac
  /-- The header verification under the hidden state of `a`. -/
  verifyHeader : AuthState → Header → Mac → Bool
  /-- The ciphertext tag under the hidden state of `a`. -/
  macCiphertext : AuthState → Ciphertext → Mac
  /-- The ciphertext verification under the hidden state of `a`. -/
  verifyCiphertext : AuthState → Ciphertext → Mac → Bool
  /-- The update of the hidden state of `a`. -/
  next : AuthState → AuthState
  /-- Honest header tags verify. -/
  verifyHeader_correct : ∀ a h, verifyHeader a h (macHeader a h) = true
  /-- Honest ciphertext tags verify. -/
  verifyCiphertext_correct : ∀ a c, verifyCiphertext a c (macCiphertext a c) = true

/-- An adversary against the key hiding of an authenticator: it chooses an epoch and keeps a
state, then receives an epoch key and the operations on the hidden state, and outputs a bit. -/
structure AuthHideAdversary (EpochKey AuthState Header Ciphertext Mac : Type) where
  /-- The information kept between choosing the epoch and guessing. -/
  State : Type
  /-- Choose the epoch and the kept information. -/
  context : ProbComp (ℕ × State)
  /-- Guess from the kept information, the epoch key and the hidden operations. -/
  guess : State → EpochKey → HiddenAuth AuthState Header Ciphertext Mac → ProbComp Bool

variable {InitKey EpochKey AuthState Header Ciphertext Mac : Type}
  (auth : RatchetedAuthenticator InitKey EpochKey AuthState Header Ciphertext Mac)

/-- The authenticator state entering epoch `e` as a function of a state `a`: the initial state
`auth.init ik 1` of the initial key `ik` if `e = 1`, and the update `auth.update a (e - 1) κ` of
`a` at epoch `e - 1` with the epoch key `κ` otherwise. -/
def hiddenState (e : ℕ) (ik : InitKey) (κ : EpochKey) (a : AuthState) : AuthState :=
  if e = 1 then auth.init ik 1 else auth.update a (e - 1) κ

/-- The operations of `auth` on `hide a`, as functions of a state `a`, for a map `hide` of
authenticator states (`hiddenState auth e ik κ` in `authHideExp`): header tags and verifications
at `e`, ciphertext tags and verifications at `e - 1`, and the update at `e` keyed by `u`. -/
def hiddenAuth (hide : AuthState → AuthState) (e : ℕ) (u : EpochKey) :
    HiddenAuth AuthState Header Ciphertext Mac where
  macHeader a := auth.macHeader (hide a) e
  verifyHeader a := auth.verifyHeader (hide a) e
  macCiphertext a := auth.macCiphertext (hide a) (e - 1)
  verifyCiphertext a := auth.verifyCiphertext (hide a) (e - 1)
  next a := auth.update (hide a) e u
  verifyHeader_correct a := auth.verifyHeader_correct (hide a) e
  verifyCiphertext_correct a := auth.verifyCiphertext_correct (hide a) (e - 1)

/-- The key-hiding experiment: `(e, st) ← adv.context`, `ik ← sampleInitKey` and
`u, u', κ ←$ EpochKey`, then `adv.guess st (if real then u else u') h` for the hidden operations
`h := hiddenAuth auth (hiddenState auth e ik κ) e u`, whose update uses `u`. -/
-- ANCHOR: authHideExp
def authHideExp [SampleableType EpochKey] (sampleInitKey : ProbComp InitKey)
    (adv : AuthHideAdversary EpochKey AuthState Header Ciphertext Mac) (real : Bool) :
    ProbComp Bool := do
  let (e, st) ← adv.context
  let ik ← sampleInitKey
  let u ← ($ᵗ EpochKey : ProbComp EpochKey)
  let u' ← ($ᵗ EpochKey : ProbComp EpochKey)
  let κ ← ($ᵗ EpochKey : ProbComp EpochKey)
  adv.guess st (if real then u else u') (hiddenAuth auth (hiddenState auth e ik κ) e u)
-- ANCHOR_END: authHideExp

/-- The advantage of a key-hiding adversary `adv`: the difference in acceptance probability
between the experiments that hand `adv` the key of the hidden update or an independent uniform
key, `|Pr[authHideExp … adv true = true] - Pr[authHideExp … adv false = true]|`. -/
noncomputable def authHideAdvantage [SampleableType EpochKey] (sampleInitKey : ProbComp InitKey)
    (adv : AuthHideAdversary EpochKey AuthState Header Ciphertext Mac) : ℝ :=
  (𝒟[authHideExp auth sampleInitKey adv true].boolDist
    𝒟[authHideExp auth sampleInitKey adv false]).toReal

end Braid
