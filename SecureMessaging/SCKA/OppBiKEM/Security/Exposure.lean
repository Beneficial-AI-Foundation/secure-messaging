/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Basic

/-!
# Opp-BiKEM — Exposure policy

`exposure` conservatively excludes positive epochs associated with retained keys or leaked send
randomness. `sendWith_exposure` identifies its randomness-leakage set from the initial state for
every successful supported output. The security oracle's separate acceptance guard still applies.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Positive epochs excluded by the presence of key-generation or encapsulation randomness.
The flags identify operations; the exclusion does not assert key reconstruction. -/
def rleakEpochs {RK RE : Type} (role : Role)
    (st : State PK SK C Sym) (rand : SendRand RK RE) : Finset ℕ :=
  let keyEpoch := st.res.resEpoch + 2 + role.offset
  let encEpoch := st.res.resEpoch + if rand.keygenRand.isSome then 2 else 0
  let epochs : Finset ℤ :=
    (if rand.keygenRand.isSome then {keyEpoch} else ∅) ∪
    (if rand.encapsRand.isSome then {encEpoch} else ∅)
  (epochs.filter fun e => 0 < e).image Int.toNat

/-- Build the conservative epoch-exclusion policy for state exposure and send randomness leakage.
Membership alone does not certify reconstruction or satisfy the oracle's acceptance guard. -/
def exposure {kem : KEMScheme ProbComp K PK SK C}
    (role : Role) (leak : kem.RandLeak) :
    SCKAScheme.VulnerableEpochs (State PK SK C Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) where
  corrupt := vuln
  rleak := rleakEpochs role

/-- The corruption policy of `exposure` is `vuln`. -/
@[simp] lemma exposure_corrupt {kem : KEMScheme ProbComp K PK SK C}
    (role : Role) (leak : kem.RandLeak) :
    (exposure (Sym := Sym) role leak).corrupt = vuln :=
  rfl

/-- The leakage policy of `exposure` is `rleakEpochs role`. -/
@[simp] lemma exposure_rleak {kem : KEMScheme ProbComp K PK SK C}
    (role : Role) (leak : kem.RandLeak) :
    (exposure (Sym := Sym) role leak).rleak = rleakEpochs role :=
  rfl

/-- Whether the send control flow generates a key pair and advances the responder epoch.
This guard constrains the local public key and ciphertext acknowledgements. -/
def sendKeygenGuard (role : Role) (st : State PK SK C Sym) : Bool :=
  st.req.ek.isNone &&
    decide (st.res.resEpoch ∈ st.ack.ctRec ∧
      st.res.resEpoch + role.offset ∈ st.ack.ctRec)

/-- The encapsulation control-flow guard, after any key-generation epoch advance and before
peer-key lookup. It does not assert that the peer key exists or that the send succeeds. -/
def sendEncapsGuard (role : Role) (st : State PK SK C Sym) : Bool :=
  let tRes := st.res.resEpoch + if sendKeygenGuard role st then 2 else 0
  decide (tRes + role.offset ∈ st.ack.ekRec) &&
    decide (tRes ∉ st.ack.ctRec) &&
    st.res.ct.isNone &&
    decide (tRes ∈ st.ack.ekRec)

/-- Positive epochs excluded by the send-operation guards in the initial state.
The unit values record presence only, rather than actual coins or key reconstruction. -/
def leakEpochs (role : Role) (st : State PK SK C Sym) : Finset ℕ :=
  rleakEpochs role st
    ({ keygenRand := if sendKeygenGuard role st then some () else none
       encapsRand := if sendEncapsGuard role st then some () else none } :
      SendRand Unit Unit)

/-- Membership in `vuln` means a positive epoch at which a decapsulation key is retained. -/
lemma mem_vuln_iff (st : State PK SK C Sym) (t : ℕ) :
    t ∈ vuln st ↔ 0 < t ∧ ∃ sk : SK, ((t : ℤ), sk) ∈ st.req.dk := by
  simp only [vuln, Finset.mem_image, Finset.mem_filter, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨e, ⟨⟨⟨e', sk⟩, hmem, rfl⟩, hpos⟩, rfl⟩
    refine ⟨by omega, sk, ?_⟩
    rwa [Int.toNat_of_nonneg hpos.le]
  · rintro ⟨ht, sk, hmem⟩
    exact ⟨t, ⟨⟨(t, sk), hmem, rfl⟩, by omega⟩, by simp⟩

/-- Membership in `rleakEpochs` means a positive epoch selected by a present randomness field. -/
theorem mem_rleakEpochs_iff
    {RK RE : Type} (role : Role)
    (st : State PK SK C Sym) (rand : SendRand RK RE) (t : ℕ) :
    t ∈ rleakEpochs role st rand ↔
      0 < t ∧
        ((rand.keygenRand.isSome = true ∧
            (t : ℤ) = st.res.resEpoch + 2 + role.offset) ∨
          (rand.encapsRand.isSome = true ∧
            (t : ℤ) =
              st.res.resEpoch + (if rand.keygenRand.isSome then 2 else 0))) := by
  simp only [rleakEpochs, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨e, ⟨he, hpos⟩, rfl⟩
    split_ifs at he <;> simp_all <;> omega
  · rintro ⟨ht, h⟩
    exact ⟨t, ⟨by split_ifs <;> simp_all, by omega⟩, by simp⟩

/-- Both state exposure and randomness leakage exclude only positive epochs. -/
theorem exposure_positive
    {kem : KEMScheme ProbComp K PK SK C}
    (role : Role) (leak : kem.RandLeak)
    (st : State PK SK C Sym)
    (rand : SendRand leak.KeygenRand leak.EncapsRand) :
    (∀ t ∈ (exposure role leak).corrupt st, 0 < t) ∧
      (∀ t ∈ (exposure role leak).rleak st rand, 0 < t) := by
  constructor
  · intro t ht
    exact ((mem_vuln_iff st t).mp ht).1
  · intro t ht
    exact ((mem_rleakEpochs_iff role st rand t).mp ht).1

/-- Assume:

* `some (key, msg, epoch, st', rand)` is a supported output of `sendWith`.

Then the randomness flags equal the initial-state operation guards, the responder epoch records
the key-generation advance, a generated secret key is stored at its integer epoch, and an emitted
key is present exactly when encapsulation randomness is present, at the responder epoch's `toNat`.
No reachability or positivity of the generated or emitted epochs is assumed. -/
theorem sendWith_operation_facts
    {RK RE : Type} (role : Role)
    (keygen : ProbComp ((PK × SK) × RK))
    (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (epoch : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key, msg, epoch, st', rand) ∈
      support (sendWith role keygen encaps ecEk ecCt st)) :
    rand.keygenRand.isSome = sendKeygenGuard role st ∧
      rand.encapsRand.isSome = sendEncapsGuard role st ∧
      st'.res.resEpoch =
        st.res.resEpoch + (if rand.keygenRand.isSome then 2 else 0) ∧
      (rand.keygenRand.isSome = true →
        ∃ sk : SK, (st.res.resEpoch + 2 + role.offset, sk) ∈ st'.req.dk) ∧
      rand.encapsRand.isSome = key.isSome ∧
      (∀ (t : ℕ) (k : K), key = some (t, k) →
        t = (st.res.resEpoch + (if rand.keygenRand.isSome then 2 else 0)).toNat) := by
  unfold sendWith at hout
  dsimp only at hout
  repeat' first
    | split at hout
    | (rw [mem_support_bind_iff] at hout; obtain ⟨x, _, hout⟩ := hout)
  all_goals simp only [support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hout
  all_goals obtain ⟨rfl, rfl, rfl, rfl, hrand⟩ := hout
  all_goals
    have hkey : rand.keygenRand.isSome = sendKeygenGuard role st := by
      rw [hrand]
      simp_all [sendKeygenGuard]
    refine ⟨hkey, ?_⟩
    simp only [sendEncapsGuard, ← hkey, hrand]
    simp_all

/-- Assume:

* `some (key, msg, epoch, st', rand)` is a successful supported output of `sendWith`.

Then its leaked-randomness exclusion set equals the initial-state guard-based set `leakEpochs`.
The security oracle's acceptance guard is a separate condition. -/
theorem sendWith_exposure
    {RK RE : Type} (role : Role)
    (keygen : ProbComp ((PK × SK) × RK))
    (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (epoch : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key, msg, epoch, st', rand) ∈
      support (sendWith role keygen encaps ecEk ecCt st)) :
    rleakEpochs role st rand = leakEpochs role st := by
  obtain ⟨hkey, henc, _⟩ :=
    sendWith_operation_facts role keygen encaps ecEk ecCt st key msg epoch st' rand hout
  ext t
  by_cases hk : sendKeygenGuard role st <;>
    by_cases hr : sendEncapsGuard role st <;>
    simp [leakEpochs, mem_rleakEpochs_iff, hkey, henc, hk, hr]

end oppBiKemCKA
