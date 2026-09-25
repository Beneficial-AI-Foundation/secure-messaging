/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.SendA

/-!
# Opp-BiKEM Send-B invariant

This file proves a structural invariant for the restricted reachability boundary containing only
the uniform-randomness and Send-B oracles. The initialized restricted execution remains at horizon
zero, while the conditional preservation theorem also covers aligned positive-horizon states. It
makes no claim about Send-A, receive, or full-game reachability.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

structure SendBInvariant
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop where
  correct : s.correct = true
  resEpoch_lower : 0 ≤ s.stB.res.resEpoch
  initial_ct_acks : (-1 : ℤ) ∈ s.stB.ack.ctRec ∧ (0 : ℤ) ∈ s.stB.ack.ctRec
  horizon : s.tcurB ≤ s.stB.ack.sendingHorizon
  knownPrefix : ∀ t : ℕ, 0 < t → t ≤ s.stB.ack.sendingHorizon →
    ∃ key : K, s.keyB t = some key
  keysCompatible : ∀ (t : ℕ) (keyA keyB : K),
    s.keyA t = some keyA → s.keyB t = some keyB → keyA = keyB
  futureKeys : ∀ t : ℕ, s.stB.res.resEpoch + 1 < (t : ℤ) →
    s.keyA t = none ∧ s.keyB t = none
  pendingFresh : s.stB.res.resEpoch ∉ s.stB.ack.ctRec → s.stB.res.ct = none →
    s.keyA s.stB.res.resEpoch.toNat = none ∧
      s.keyB s.stB.res.resEpoch.toNat = none

theorem initGameState_sendBInvariant
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym))) :
    SendBInvariant (K := K) (SCKAScheme.initGameState stA stB) := by
  simp only [initB, init, support_pure, Set.mem_singleton_iff] at hB
  subst stB
  refine {
    correct := rfl
    resEpoch_lower := by simp [SCKAScheme.initGameState]
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

private theorem sendWithB_support_facts
    {RKey REnc : Type}
    (keygen : ProbComp ((PK × SK) × RKey))
    (encaps : PK → ProbComp ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (rand : SendRand RKey REnc)
    (hout : some (key?, ρ, tsnd, st', rand) ∈
      support (sendWith .B keygen encaps ecEk ecCt st)) :
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

theorem send_support_facts
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (send role kem ecEk ecCt st)) :
    st'.ack = st.ack ∧ tsnd = st.ack.sendingHorizon ∧
    (st'.res.resEpoch = st.res.resEpoch ∨ st'.res.resEpoch = st.res.resEpoch + 2) ∧
    (key? = none → st'.res.ct = st.res.ct) ∧
    (∀ tI key, key? = some (tI, key) → tI = st'.res.resEpoch.toNat ∧
      st'.res.resEpoch ∉ st.ack.ctRec ∧ st.res.ct = none ∧ st'.res.ct.isSome) := by
  cases role with
  | A =>
      exact sendA_support_facts kem ecEk ecCt st key? ρ tsnd st' (by
        simpa only [sendA] using hout)
  | B =>
      rw [send, mem_support_bind_iff] at hout
      obtain ⟨out, hout, hpure⟩ := hout
      cases out with
      | none => simp at hpure
      | some out =>
        rcases out with ⟨key, msg, epoch, state, rand⟩
        simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at hpure
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpure
        exact sendWithB_support_facts _ _ ecEk ecCt st _ _ _ _ rand hout

theorem sendB_supported_checks
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : SendBInvariant s) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : StB PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (sendB kem ecEk ecCt s.stB)) :
    s.tcurB ≤ tsnd ∧
    (List.range (tsnd + 1)).all (fun t => t = 0 || (s.keyB t).isSome) = true ∧
    (∀ tI key, key? = some (tI, key) → s.keyB tI = none ∧ s.keyA tI = none) := by
  have hfacts := send_support_facts .B kem ecEk ecCt s.stB key? ρ tsnd st' (by
    simpa only [sendB] using hout)
  rcases hfacts with ⟨hack, htsnd, hepoch, hnone, hkey⟩
  refine ⟨htsnd ▸ hs.horizon, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro t ht
    simp only [List.mem_range] at ht
    by_cases ht0 : t = 0
    · simp [ht0]
    · have hpos : 0 < t := Nat.pos_of_ne_zero ht0
      have hle : t ≤ s.stB.ack.sendingHorizon := by omega
      obtain ⟨key, hsome⟩ := hs.knownPrefix t hpos hle
      simp [hsome]
  · intro tI key hkeyeq
    obtain ⟨htI, hfresh, hct, _⟩ := hkey tI key hkeyeq
    rcases hepoch with hepoch | hepoch
    · rw [hepoch] at htI hfresh
      have hkeys := hs.pendingFresh hfresh hct
      exact ⟨by simpa only [htI] using hkeys.2, by simpa only [htI] using hkeys.1⟩
    · have hlower := hs.resEpoch_lower
      have hnonneg : 0 ≤ s.stB.res.resEpoch + 2 := by omega
      have hcast : ((s.stB.res.resEpoch + 2).toNat : ℤ) =
          s.stB.res.resEpoch + 2 := Int.toNat_of_nonneg hnonneg
      have hfuture : s.stB.res.resEpoch + 1 <
          ((s.stB.res.resEpoch + 2).toNat : ℤ) := by
        omega
      have hkeys := hs.futureKeys (s.stB.res.resEpoch + 2).toNat hfuture
      exact ⟨by simpa only [htI, hepoch] using hkeys.2,
        by simpa only [htI, hepoch] using hkeys.1⟩

theorem oracleSendB_preserves_sendBInvariant
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak))
      (SendBInvariant (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  intro _ s hs z hz
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_liftM, bind_assoc] at hz
  obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
  cases out with
  | none =>
      simp at hz
      subst z
      exact hs
  | some out =>
      rcases out with ⟨key?, ρ, tsnd, st'⟩
      have hout' : some (key?, ρ, tsnd, st') ∈ support (sendB kem ecEk ecCt s.stB) := by
        simpa [scheme] using hout
      have hfacts := send_support_facts .B kem ecEk ecCt s.stB key? ρ tsnd st' (by
        simpa only [sendB] using hout')
      have hchecks := sendB_supported_checks kem ecEk ecCt s hs key? ρ tsnd st' hout'
      rcases hfacts with ⟨hack, htsnd, hepoch, hnone, hkey⟩
      rcases hchecks with ⟨hmono, hprefix, hfresh⟩
      have hlower' : 0 ≤ st'.res.resEpoch := by
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
              simpa only [hack, htsnd] using (le_refl s.stB.ack.sendingHorizon)
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
            have hct : st'.res.ct = s.stB.res.ct := hnone rfl
            rcases hepoch with hepoch | hepoch
            · rw [hepoch] at hfresh' ⊢
              apply hs.pendingFresh
              · simpa only [hack] using hfresh'
              · rw [← hct]
                exact hct'
            · have hnonneg : 0 ≤ s.stB.res.resEpoch + 2 := by
                have := hs.resEpoch_lower
                omega
              have hcast : ((s.stB.res.resEpoch + 2).toNat : ℤ) =
                  s.stB.res.resEpoch + 2 := Int.toNat_of_nonneg hnonneg
              have hfuture : s.stB.res.resEpoch + 1 <
                  ((s.stB.res.resEpoch + 2).toNat : ℤ) := by
                omega
              simpa only [hepoch] using
                hs.futureKeys (s.stB.res.resEpoch + 2).toNat hfuture
      | some keyOut =>
          rcases keyOut with ⟨tI, key⟩
          simp at hz
          subst z
          dsimp only
          have hold := hfresh tI key rfl
          rcases hold with ⟨holdB, holdA⟩
          obtain ⟨htI, _, _, hctSome⟩ := hkey tI key rfl
          have hprefix' :
              (List.range (tsnd + 1)).all
                (fun t => t = 0 || (Function.update s.keyB tI (some key) t).isSome) = true := by
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
              simpa only [hack, htsnd] using (le_refl s.stB.ack.sendingHorizon)
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
            change s.keyA t = some keyA at hkeyA
            change Function.update s.keyB tI (some key) t = some keyB at hkeyB
            by_cases hti : t = tI
            · subst t
              rw [Function.update_self] at hkeyB
              rw [holdA] at hkeyA
              simp at hkeyA
            · rw [Function.update_of_ne hti] at hkeyB
              exact hs.keysCompatible t keyA keyB hkeyA hkeyB
          · intro t hfuture'
            change st'.res.resEpoch + 1 < (t : ℤ) at hfuture'
            change s.keyA t = none ∧ Function.update s.keyB tI (some key) t = none
            have hne : t ≠ tI := by
              intro heq
              subst t
              rw [htI] at hfuture'
              have hcast : (st'.res.resEpoch.toNat : ℤ) = st'.res.resEpoch :=
                Int.toNat_of_nonneg hlower'
              omega
            rw [Function.update_of_ne hne]
            apply hs.futureKeys t
            rcases hepoch with hepoch | hepoch <;> omega
          · intro _ hctNone
            change st'.res.ct = none at hctNone
            rw [hctNone] at hctSome
            simp at hctSome

theorem simulateQ_unif_sendB_invariant
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    {α : Type}
    (oa : OracleComp
      (unifSpec + (Unit →ₒ Option (ℕ × Option ℕ × Message Sym))) α)
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym)))
    (z : α × SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.oracleUnif
          (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) +
        SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak)) oa).run
      (SCKAScheme.initGameState stA stB))) :
    SendBInvariant z.2 := by
  have hsum : QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) +
        SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak))
      (SendBInvariant (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
    intro t s hs z hz
    rcases t with t | t
    · exact oracleUnif_preservesInv _ t s hs z (by simpa using hz)
    · exact oracleSendB_preserves_sendBInvariant kem hDet ecEk ecCt leak
        t s hs z (by simpa using hz)
  exact simulateQ_run_preservesInv _ _ hsum oa _
    (initGameState_sendBInvariant stA stB hB) z hz

end oppBiKemCKA
