/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Hybrid
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Opp-BiKEM — Cancellation of exposed-target paths

The adjacent hybrids with thresholds `t` and `t + 1` differ only in the answer to an accepted
challenge of epoch `t`. Once epoch `t` is exposed, that challenge is rejected forever and the
two hybrids agree, while an accepted challenge of `t` makes every later exposure of `t`
rejected. Stopping both runs with output `false` at the first query after which `t` is exposed
therefore leaves the signed difference of their acceptance probabilities unchanged
(`hybridExp_sub_eq_stopped_sub`). The stopped runs are what the KEM reduction simulates.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The stopping test for target epoch `t`: `t` is exposed. -/
def targetExposed (t : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Bool :=
  decide (t ∈ s.exposed)

/-- Committed states for target epoch `t`: `t` is challenged and not exposed. From such a state
the challenge of `t` is rejected and `t` can no longer be exposed. -/
def TargetCommitted (t : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  t ∈ s.challenged ∧ t ∉ s.exposed

/-- A committed state does not satisfy the stopping test. -/
lemma targetExposed_eq_false_of_committed (t : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : TargetCommitted t s) : targetExposed t s = false := by
  simp [targetExposed, hs.2]

section Hybrid

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-! ## Bookkeeping -/

omit [SampleableType K] in
/-- Every ideal correctness query keeps the exposed and challenged sets. -/
lemma idealCorrectnessImpl_bookkeeping
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z) (hz : z ∈ support ((idealCorrectnessImpl kem hDet ecEk ecCt leak t).run s)) :
    z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged := by
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · exact SCKAScheme.oracleUnif_preservesInv
      (fun u => u.exposed = s.exposed ∧ u.challenged = s.challenged) n s ⟨rfl, rfl⟩ z hz
  · obtain ⟨out, -, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, k⟩, ρ, tsnd, stA'⟩ <;> simp [SCKAScheme.sendAUpdate]
  · obtain ⟨out, -, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, k⟩, ρ, tsnd, stB'⟩ <;> simp [SCKAScheme.sendBUpdate]
  · change z ∈ support ((SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, stA', -, -, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rcases keyOpt with _ | ⟨tI, k⟩ <;> simp [SCKAScheme.recvAUpdate]
  · change z ∈ support ((SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, stB', -, -, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rcases keyOpt with _ | ⟨tI, k⟩ <;> simp [SCKAScheme.recvBUpdate]

/-- Every hybrid query shrinks neither the exposed nor the challenged set, and every epoch it
newly exposes was not challenged before it. -/
lemma hybridSecurityImpl_bookkeeping (random : ℕ → Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z) (hz : z ∈ support ((hybridSecurityImpl kem hDet ecEk ecCt leak random t).run s)) :
    s.exposed ⊆ z.2.exposed ∧ s.challenged ⊆ z.2.challenged ∧
      ∀ e ∈ z.2.exposed, e ∉ s.exposed → e ∉ s.challenged := by
  refine SCKAScheme.securityImplOf_bookkeeping _ _ _ _ _ s
    (fun t z hz => idealCorrectnessImpl_bookkeeping kem hDet ecEk ecCt leak t s z hz)
    (fun e z hz => ?_) t z hz
  rcases SCKAScheme.oracleChall_support (random e) s e z hz with ⟨h, -⟩ | ⟨-, -, h⟩
  · rw [h]; exact ⟨rfl, le_rfl⟩
  · rw [h]; exact ⟨rfl, Finset.subset_insert _ _⟩

/-- Every hybrid query keeps an exposed epoch exposed. -/
lemma hybridSecurityImpl_preserves_exposed (random : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (hybridSecurityImpl kem hDet ecEk ecCt leak random)
      (fun s => e ∈ s.exposed) :=
  fun t s hs z hz =>
    (hybridSecurityImpl_bookkeeping kem hDet ecEk ecCt leak random t s z hz).1 hs

/-- Every hybrid query keeps a committed state committed. -/
lemma hybridSecurityImpl_preserves_committed (random : ℕ → Bool) (e : ℕ) :
    QueryImpl.PreservesInv (hybridSecurityImpl kem hDet ecEk ecCt leak random)
      (TargetCommitted e) := by
  intro t s hs z hz
  obtain ⟨-, hc, hnew⟩ := hybridSecurityImpl_bookkeeping kem hDet ecEk ecCt leak random t s z hz
  exact ⟨hc hs.1, fun he => hnew e he hs.2 hs.1⟩

/-! ## Agreement of adjacent hybrids -/

/-- Two selections give the same hybrid query computation from `s` whenever they agree at
every epoch eligible in `s`: not exposed, not challenged, and keyed in one of the tables. -/
lemma hybridSecurityImpl_run_eq_of_eligible (random random' : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : ∀ e, ¬(e ∈ s.exposed ∨ e ∈ s.challenged) →
      ((s.keyA e).isSome = true ∨ (s.keyB e).isSome = true) → random e = random' e)
    (t : (securitySpec leak Sym).Domain) :
    (hybridSecurityImpl kem hDet ecEk ecCt leak random t).run s =
      (hybridSecurityImpl kem hDet ecEk ecCt leak random' t).run s :=
  SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl)
    (fun e => SCKAScheme.oracleChall_run_eq_of_eligible_imp (random e) (random' e) s e (hs e)) t

/-- The thresholds `t + 1` and `t` select the same answers at every epoch other than `t`. -/
lemma hybridRandom_succ_eq_of_ne (t e : ℕ) (he : e ≠ t) :
    hybridRandom (t + 1) e = hybridRandom t e := by
  simp only [hybridRandom]
  by_cases h : e < t
  · simp [h, Nat.lt_succ_of_lt h]
  · have h' : ¬ e < t + 1 := by omega
    simp [h, h']

/-- From a state where epoch `t` is exposed, the hybrids with thresholds `t + 1` and `t` accept
every Boolean computation with equal probability. -/
lemma probOutput_hybrid_succ_eq_of_exposed (t : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : t ∈ s.exposed) (oa : OracleComp (securitySpec leak Sym) Bool) :
    Pr[= true | (simulateQ (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + 1)))
        oa).run' s] =
      Pr[= true | (simulateQ (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom t))
        oa).run' s] := by
  refine probOutput_run'_eq_of_run_eq _ _ _ (fun z => ?_) true
  refine OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
    (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + 1)))
    (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom t)) (fun u => t ∈ u.exposed) oa ?_
    (fun q u hu z hz =>
      hybridSecurityImpl_preserves_exposed kem hDet ecEk ecCt leak (hybridRandom t) t q u hu z hz)
    s hs z
  intro q u hu
  refine hybridSecurityImpl_run_eq_of_eligible kem hDet ecEk ecCt leak _ _ u ?_ q
  intro e hrej _
  rcases eq_or_ne e t with rfl | hne
  · exact absurd (Or.inl hu) hrej
  · exact hybridRandom_succ_eq_of_ne t e hne

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- An eligible epoch is neither rejected nor unavailable. -/
lemma ineligible_absurd
    {s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)} {e : ℕ}
    (helig : ¬(e ∈ s.exposed ∨ e ∈ s.challenged) ∧
      ((s.keyA e).isSome = true ∨ (s.keyB e).isSome = true))
    (h : (e ∈ s.exposed ∨ e ∈ s.challenged) ∨ (s.keyA e = none ∧ s.keyB e = none)) :
    False := by
  rcases h with h | ⟨hA, hB⟩
  · exact helig.1 h
  · rcases helig.2 with hk | hk
    · rw [hA] at hk; exact Bool.false_ne_true hk
    · rw [hB] at hk; exact Bool.false_ne_true hk

/-- Each query is answered identically by the hybrids with thresholds `t + 1` and `t`, or it is
an accepted challenge of epoch `t`, after which both hybrids are committed to `t`. -/
lemma hybrid_succ_query_eq_or_committed (t : ℕ) (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + 1)) q).run s =
        (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom t) q).run s ∨
      ((∀ z ∈ support ((hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + 1))
          q).run s), TargetCommitted t z.2) ∧
        (∀ z ∈ support ((hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom t)
          q).run s), TargetCommitted t z.2)) := by
  by_cases helig : ¬(t ∈ s.exposed ∨ t ∈ s.challenged) ∧
      ((s.keyA t).isSome = true ∨ (s.keyB t).isSome = true)
  · rcases q with (((((q | u) | u) | e) | u) | u)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · rcases eq_or_ne e t with rfl | hne
      · refine Or.inr ⟨fun z hz => ?_, fun z hz => ?_⟩
        · rcases SCKAScheme.oracleChall_support (hybridRandom (e + 1) e) s e z hz with
            ⟨-, h⟩ | ⟨-, -, h⟩
          · exact (ineligible_absurd helig h).elim
          · rw [h]; exact ⟨Finset.mem_insert_self _ _, fun h' => helig.1 (Or.inl h')⟩
        · rcases SCKAScheme.oracleChall_support (hybridRandom e e) s e z hz with
            ⟨-, h⟩ | ⟨-, -, h⟩
          · exact (ineligible_absurd helig h).elim
          · rw [h]; exact ⟨Finset.mem_insert_self _ _, fun h' => helig.1 (Or.inl h')⟩
      · exact Or.inl (SCKAScheme.oracleChall_run_eq_of_eligible_imp _ _ s e
          (fun _ _ => hybridRandom_succ_eq_of_ne t e hne))
    · exact Or.inl rfl
    · exact Or.inl rfl
  · refine Or.inl (hybridSecurityImpl_run_eq_of_eligible kem hDet ecEk ecCt leak _ _ s ?_ q)
    intro e hrej hkey
    rcases eq_or_ne e t with rfl | hne
    · exact absurd ⟨hrej, hkey⟩ helig
    · exact hybridRandom_succ_eq_of_ne t e hne

/-! ## Cancellation -/

/-- The hybrid experiment with threshold `T`, stopped with output `false` at the first query
after which the target epoch `t` is exposed. -/
def stoppedHybridExp (t T : ℕ) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  stoppedRun (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom T)) (targetExposed t) adv
    (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))

/-- Stopping both adjacent hybrids once the target epoch `t` is exposed leaves the signed
difference of their acceptance probabilities unchanged. -/
theorem hybridExp_sub_eq_stopped_sub (adv : SecurityAdversary leak Sym) (t : ℕ) :
    (Pr[= true | hybridExp kem hDet ecEk ecCt leak (t + 1) adv]).toReal -
        (Pr[= true | hybridExp kem hDet ecEk ecCt leak t adv]).toReal =
      (Pr[= true | stoppedHybridExp kem hDet ecEk ecCt leak t (t + 1) adv]).toReal -
        (Pr[= true | stoppedHybridExp kem hDet ecEk ecCt leak t t adv]).toReal :=
  signed_gap_stoppedRun_eq
    (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + 1)))
    (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom t))
    (fun _ => True) (TargetCommitted t) (targetExposed t)
    (fun _ _ _ _ _ => trivial)
    (hybridSecurityImpl_preserves_committed kem hDet ecEk ecCt leak _ t)
    (hybridSecurityImpl_preserves_committed kem hDet ecEk ecCt leak _ t)
    (targetExposed_eq_false_of_committed t)
    (fun q s _ => hybrid_succ_query_eq_or_committed kem hDet ecEk ecCt leak t q s)
    (fun s _ hs oa => probOutput_hybrid_succ_eq_of_exposed kem hDet ecEk ecCt leak t s
      (by simpa [targetExposed] using hs) oa)
    adv _ trivial

end Hybrid

end oppBiKemCKA
