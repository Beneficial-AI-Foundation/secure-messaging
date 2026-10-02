/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction

/-!
# Opp-BiKEM Send-A invariant

This file proves a structural invariant for the restricted reachability boundary containing only
the uniform-randomness and Send-A oracles. It makes no claim about Send-B, receive, or full-game
reachability.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

def Acknowledgements.sendingHorizon (ack : Acknowledgements) : ℕ :=
  (ack.ctRec.filter fun t => t - 1 ∈ ack.ctRec).sup Int.toNat

structure SendAInvariant
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop where
  correct : s.correct = true
  resEpoch_lower : -1 ≤ s.stA.res.resEpoch
  initial_ct_acks : (-1 : ℤ) ∈ s.stA.ack.ctRec ∧ (0 : ℤ) ∈ s.stA.ack.ctRec
  horizon : s.tcurA ≤ s.stA.ack.sendingHorizon
  knownPrefix : ∀ t : ℕ, 0 < t → t ≤ s.stA.ack.sendingHorizon →
    ∃ key : K, s.keyA t = some key
  keysCompatible : ∀ (t : ℕ) (keyA keyB : K),
    s.keyA t = some keyA → s.keyB t = some keyB → keyA = keyB
  futureKeys : ∀ t : ℕ, s.stA.res.resEpoch + 1 < (t : ℤ) →
    s.keyA t = none ∧ s.keyB t = none
  pendingFresh : s.stA.res.resEpoch ∉ s.stA.ack.ctRec → s.stA.res.ct = none →
    s.keyA s.stA.res.resEpoch.toNat = none ∧ s.keyB s.stA.res.resEpoch.toNat = none

theorem initGameState_sendAInvariant (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym))) :
    SendAInvariant (K := K) (SCKAScheme.initGameState stA stB) := by
  simp only [initA, init, support_pure, Set.mem_singleton_iff] at hA
  subst stA
  refine {
    correct := rfl
    resEpoch_lower := by norm_num [SCKAScheme.initGameState]
    initial_ct_acks := by simp [SCKAScheme.initGameState]
    horizon := by norm_num [SCKAScheme.initGameState, Acknowledgements.sendingHorizon]
    knownPrefix := ?_
    keysCompatible := by simp [SCKAScheme.initGameState]
    futureKeys := by simp [SCKAScheme.initGameState]
    pendingFresh := by simp [SCKAScheme.initGameState]
  }
  intro t ht hle
  have hhor : ({x ∈ ({-1, 0} : Finset ℤ) | x = 0 ∨ x - 1 = 0}.sup Int.toNat) = 0 := by
    decide
  change t ≤ {x ∈ ({-1, 0} : Finset ℤ) | x = 0 ∨ x - 1 = 0}.sup Int.toNat at hle
  rw [hhor] at hle
  omega

private theorem sendWith_support_facts
    {RKey REnc : Type} (keygen : ProbComp ((PK × SK) × RKey))
    (encaps : PK → ProbComp ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : StA PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : StA PK SK C Sym) (rand : SendRand RKey REnc)
    (hout : some (key?, ρ, tsnd, st', rand) ∈
      support (sendWith .A keygen encaps ecEk ecCt st)) :
    st'.ack = st.ack ∧ tsnd = st.ack.sendingHorizon ∧
    (st'.res.resEpoch = st.res.resEpoch ∨ st'.res.resEpoch = st.res.resEpoch + 2) ∧
    (key? = none → st'.res.ct = st.res.ct) ∧
    (∀ tI key, key? = some (tI, key) → tI = st'.res.resEpoch.toNat ∧
      st'.res.resEpoch ∉ st.ack.ctRec ∧ st.res.ct = none ∧ st'.res.ct.isSome) := by
  unfold sendWith at hout
  dsimp only at hout
  repeat' first
    | split at hout
    | (rw [mem_support_bind_iff] at hout; obtain ⟨x, _, hout⟩ := hout)
  all_goals simp only [support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hout
  all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hout
  all_goals simp_all [Acknowledgements.sendingHorizon, Role.offset]

theorem sendA_support_facts (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : StA PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : StA PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (sendA kem ecEk ecCt st)) :
    st'.ack = st.ack ∧ tsnd = st.ack.sendingHorizon ∧
    (st'.res.resEpoch = st.res.resEpoch ∨ st'.res.resEpoch = st.res.resEpoch + 2) ∧
    (key? = none → st'.res.ct = st.res.ct) ∧
    (∀ tI key, key? = some (tI, key) → tI = st'.res.resEpoch.toNat ∧
      st'.res.resEpoch ∉ st.ack.ctRec ∧ st.res.ct = none ∧ st'.res.ct.isSome) := by
  rw [sendA, send, mem_support_bind_iff] at hout
  obtain ⟨out, hout, hpure⟩ := hout
  cases out with
  | none => simp at hpure
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hpure
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpure
    exact sendWith_support_facts _ _ ecEk ecCt st _ _ _ _ rand hout

theorem sendA_supported_checks (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : SendAInvariant s) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : StA PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (sendA kem ecEk ecCt s.stA)) :
    s.tcurA ≤ tsnd ∧
    (List.range (tsnd + 1)).all (fun t => t = 0 || (s.keyA t).isSome) = true ∧
    (∀ tI key, key? = some (tI, key) → s.keyA tI = none ∧ s.keyB tI = none) := by
  have hfacts := sendA_support_facts kem ecEk ecCt s.stA key? ρ tsnd st' hout
  rcases hfacts with ⟨hack, htsnd, hepoch, hnone, hkey⟩
  refine ⟨htsnd ▸ hs.horizon, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro t ht
    simp only [List.mem_range] at ht
    by_cases ht0 : t = 0
    · simp [ht0]
    · have hpos : 0 < t := Nat.pos_of_ne_zero ht0
      have hle : t ≤ s.stA.ack.sendingHorizon := by omega
      obtain ⟨key, hsome⟩ := hs.knownPrefix t hpos hle
      simp [hsome]
  · intro tI key hkeyeq
    obtain ⟨htI, hfresh, hct, _⟩ := hkey tI key hkeyeq
    rcases hepoch with hepoch | hepoch
    · rw [hepoch] at htI hfresh
      simpa only [htI] using hs.pendingFresh hfresh hct
    · have hlower := hs.resEpoch_lower
      have hnonneg : 0 ≤ s.stA.res.resEpoch + 2 := by omega
      have hcast : ((s.stA.res.resEpoch + 2).toNat : ℤ) =
          s.stA.res.resEpoch + 2 := Int.toNat_of_nonneg hnonneg
      have hfuture : s.stA.res.resEpoch + 1 <
          ((s.stA.res.resEpoch + 2).toNat : ℤ) := by
        omega
      have hkeys := hs.futureKeys (s.stA.res.resEpoch + 2).toNat hfuture
      simpa only [htI, hepoch] using hkeys

theorem oracleUnif_preservesInv
    (Inv : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) → Prop) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) Inv := by
  intro t s hs z hz
  have hz' : ∃ y : unifSpec.Range t, (y, s) = z := by
    simpa [SCKAScheme.oracleUnif] using hz
  rcases hz' with ⟨_, rfl⟩
  simpa using hs

private theorem toNat_ne_of_add_one_lt {r : ℤ} (hlower : -1 ≤ r) {t : ℕ}
    (hlt : r + 1 < (t : ℤ)) : t ≠ r.toNat := by
  intro heq
  subst t
  by_cases hr : r < 0
  · have hr' : r = -1 := by omega
    simp [hr'] at hlt
  · have hcast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (le_of_not_gt hr)
    omega

theorem oracleSendA_preserves_sendAInvariant [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl.PreservesInv (SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak))
      (SendAInvariant (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  intro _ s hs z hz
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_liftM, bind_assoc] at hz
  obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
  cases out with
  | none =>
      simp at hz
      subst z
      exact hs
  | some out =>
      rcases out with ⟨key?, ρ, tsnd, st'⟩
      have hout' : some (key?, ρ, tsnd, st') ∈ support (sendA kem ecEk ecCt s.stA) := by
        simpa [scheme] using hout
      have hfacts := sendA_support_facts kem ecEk ecCt s.stA key? ρ tsnd st' hout'
      have hchecks := sendA_supported_checks kem ecEk ecCt s hs key? ρ tsnd st' hout'
      rcases hfacts with ⟨hack, htsnd, hepoch, hnone, hkey⟩
      rcases hchecks with ⟨hmono, hprefix, hfresh⟩
      have hlower' : -1 ≤ st'.res.resEpoch := by
        have hlower := hs.resEpoch_lower
        rcases hepoch with hepoch | hepoch <;> omega
      cases key? with
      | none =>
          simp at hz
          subst z
          dsimp only
          refine {
            correct := by simp [hs.correct, hmono, hprefix]
            resEpoch_lower := hlower'
            initial_ct_acks := by simpa only [hack] using hs.initial_ct_acks
            horizon := by
              simpa only [hack, htsnd] using (le_refl s.stA.ack.sendingHorizon)
            knownPrefix := ?_
            keysCompatible := hs.keysCompatible
            futureKeys := ?_
            pendingFresh := ?_
          }
          · intro t ht hle
            exact hs.knownPrefix t ht (by simpa only [hack] using hle)
          · intro t ht
            change st'.res.resEpoch + 1 < (t : ℤ) at ht
            change s.keyA t = none ∧ s.keyB t = none
            apply hs.futureKeys t
            rcases hepoch with hepoch | hepoch <;> omega
          · intro hfresh' hct'
            change st'.res.resEpoch ∉ st'.ack.ctRec at hfresh'
            change st'.res.ct = none at hct'
            change s.keyA st'.res.resEpoch.toNat = none ∧
              s.keyB st'.res.resEpoch.toNat = none
            have hct : st'.res.ct = s.stA.res.ct := hnone rfl
            rcases hepoch with hepoch | hepoch
            · rw [hepoch] at hfresh' ⊢
              apply hs.pendingFresh
              · simpa only [hack] using hfresh'
              · rw [← hct]
                exact hct'
            · have hnonneg : 0 ≤ s.stA.res.resEpoch + 2 := by
                have := hs.resEpoch_lower
                omega
              have hcast : ((s.stA.res.resEpoch + 2).toNat : ℤ) =
                  s.stA.res.resEpoch + 2 := Int.toNat_of_nonneg hnonneg
              have hfuture : s.stA.res.resEpoch + 1 <
                  ((s.stA.res.resEpoch + 2).toNat : ℤ) := by
                omega
              simpa only [hepoch] using
                hs.futureKeys (s.stA.res.resEpoch + 2).toNat hfuture
      | some keyOut =>
          rcases keyOut with ⟨tI, key⟩
          simp at hz
          subst z
          dsimp only
          have hold := hfresh tI key rfl
          rcases hold with ⟨holdA, holdB⟩
          obtain ⟨htI, _, _, hctSome⟩ := hkey tI key rfl
          have hprefix' :
              (List.range (tsnd + 1)).all
                (fun t => t = 0 || (Function.update s.keyA tI (some key) t).isSome) = true := by
            rw [List.all_eq_true] at hprefix ⊢
            intro t ht
            by_cases hti : t = tI
            · subst t
              simp
            · simpa only [Function.update_of_ne hti] using hprefix t ht
          refine {
            correct := by simp [hs.correct, hmono, hprefix', holdA, holdB]
            resEpoch_lower := hlower'
            initial_ct_acks := by simpa only [hack] using hs.initial_ct_acks
            horizon := by
              simpa only [hack, htsnd] using (le_refl s.stA.ack.sendingHorizon)
            knownPrefix := ?_
            keysCompatible := ?_
            futureKeys := ?_
            pendingFresh := ?_
          }
          · intro t ht hle
            by_cases hti : t = tI
            · subst t
              exact ⟨key, Function.update_self ..⟩
            · obtain ⟨oldKey, holdKey⟩ :=
                hs.knownPrefix t ht (by simpa only [hack] using hle)
              exact ⟨oldKey, by simpa only [Function.update_of_ne hti] using holdKey⟩
          · intro t keyA keyB hkeyA hkeyB
            change Function.update s.keyA tI (some key) t = some keyA at hkeyA
            change s.keyB t = some keyB at hkeyB
            by_cases hti : t = tI
            · subst t
              rw [Function.update_self] at hkeyA
              rw [holdB] at hkeyB
              simp at hkeyB
            · rw [Function.update_of_ne hti] at hkeyA
              exact hs.keysCompatible t keyA keyB hkeyA hkeyB
          · intro t hfuture'
            change st'.res.resEpoch + 1 < (t : ℤ) at hfuture'
            change Function.update s.keyA tI (some key) t = none ∧ s.keyB t = none
            have hne : t ≠ tI := by
              rw [htI]
              exact toNat_ne_of_add_one_lt hlower' hfuture'
            rw [Function.update_of_ne hne]
            apply hs.futureKeys t
            rcases hepoch with hepoch | hepoch <;> omega
          · intro _ hctNone
            change st'.res.ct = none at hctNone
            rw [hctNone] at hctSome
            simp at hctSome

theorem simulateQ_unif_sendA_invariant [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Option (ℕ × Option ℕ × Message Sym))) α)
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (z : α × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) +
        SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak)) oa).run
      (SCKAScheme.initGameState stA stB))) :
    SendAInvariant z.2 := by
  have hsum : QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) +
        SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak))
      (SendAInvariant (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
    intro t s hs z hz
    rcases t with t | t
    · exact oracleUnif_preservesInv _ t s hs z (by simpa using hz)
    · exact oracleSendA_preserves_sendAInvariant kem hDet ecEk ecCt leak
        t s hs z (by simpa using hz)
  exact simulateQ_run_preservesInv _ _ hsum oa _
    (initGameState_sendAInvariant stA stB hA) z hz

end oppBiKemCKA
