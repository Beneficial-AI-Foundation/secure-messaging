/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Basic

/-!
# Opp-BiKEM — Exposure policy

**Main results.** The exposure policy `exposure role leak` of Opp-BiKEM's security game
(`Defs`) declares which epochs a corruption or an accepted leaking send exposes:

- a corruption of a party exposes the positive epochs whose secret keys it retains (`vuln`,
  `exposure_corrupt`, `mem_vuln_iff`);
- an accepted leaking send exposes the positive epochs of the key pair it generates and of the
  encapsulation it performs (`rleakEpochs`, `exposure_rleak`, `mem_rleakEpochs_iff`).

The epochs exposed by a successful leaking send from a local state `st` depend on `st` alone:
they are the epochs of the operations the send performs, decided by the guards
`sendKeygenGuard` and `sendEncapsGuard` of `Defs` (`leakEpochs`, `sendWith_exposure`). Exposure
records which operations touched an epoch; it does not assert that the leaked coins reconstruct
a secret, and the security oracle's acceptance guard is a separate condition.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

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
