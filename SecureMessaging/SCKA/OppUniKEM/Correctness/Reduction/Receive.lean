/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Send

/-!
# Opp-UniKEM-CKA Receive Transitions

This module establishes how receive queries affect the KEM material stored in
the game state and the conditional failure probability `V`:

* source-shape lemmas — a receive either preserves the local KEM material or
  advances an epoch and erases it;
* preservation lemmas — a receive changes neither the potential `V` nor
  the absence of a realized current failure.
-/

open ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

open SCKAScheme.sckaCorrectnessSpec

namespace Reduction.Internal

/-- A successful receive by A either preserves its current KEM sources or
advances its epoch, erases those sources, and records the advancing message
shape. -/
lemma recvA_kem_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (stA : StA onoff Sym) (msg : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (stA' : StA onoff Sym)
    (hrecv : recvA kem onoff hDet ecCt0 ecCt1 stA msg =
      some (key?, trcv, stA')) :
    (stA'.t = stA.t ∧ stA'.ekA = stA.ekA ∧ stA'.dkA = stA.dkA) ∨
      (stA'.t = stA.t + 1 ∧ stA'.ekA = none ∧ stA'.dkA = none ∧
        msg.2.2.1 = stA.t ∧ msg.2.2.2 = some 1 ∧ msg.1.isSome) := by
  classical
  rcases msg with ⟨ch?, ack, t, b?⟩
  by_cases ht : stA.t = t
  · simp only [recvA, ht, if_true] at hrecv
    repeat' split at hrecv
    all_goals try simp_all only [Fin.isValue, Option.some.injEq, zero_ne_one,
      Option.isSome_some, and_true, and_false, or_false, and_self]
    all_goals (subst_vars; try simp_all only [Fin.isValue, imp_false,
      Prod.forall, BEq.rfl, Bool.and_true, Bool.not_eq_true, Prod.mk.injEq,
      and_self, Nat.left_eq_add, one_ne_zero, true_and, false_and, or_false,
      Bool.and_eq_true, beq_iff_eq, Nat.add_eq_left, and_false,
      not_false_eq_true])
    all_goals (rcases hrecv with ⟨_, _, hstate⟩; subst stA'; simp_all)
  · simp [recvA, ht] at hrecv
    simp_all

/-- A successful receive by B either preserves its KEM ciphertext sources or
advances its epoch and clears all offline and online ciphertext material. -/
lemma recvB_kem_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (stB : StB onoff Sym) (msg : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (stB' : StB onoff Sym)
    (hrecv : recvB kem onoff ecEk stB msg = some (key?, trcv, stB')) :
    (stB'.t = stB.t ∧ stB'.stCt = stB.stCt ∧ stB'.ct0 = stB.ct0 ∧
        stB'.ct1 = stB.ct1) ∨
      (stB'.t = stB.t + 1 ∧ stB'.stCt = none ∧ stB'.ct0 = none ∧
        stB'.ct1 = none ∧ stB.t < msg.2.2.1) := by
  classical
  rcases msg with ⟨ch?, ack, t, b?⟩
  by_cases ht : stB.t < t
  · right
    simp only [recvB, ht, if_true] at hrecv
    repeat' split at hrecv
    all_goals try simp_all only [Option.isNone_none, and_true, BEq.rfl,
      Bool.and_true, Bool.not_eq_true, insert_empty_eq, Option.some.injEq,
      Prod.mk.injEq, Bool.and_eq_true, beq_iff_eq, and_false,
      not_false_eq_true]
    all_goals (subst_vars; try simp_all only [Fin.isValue, imp_false,
      Prod.forall, BEq.rfl, Bool.and_true, Bool.not_eq_true, Prod.mk.injEq,
      and_self, Nat.left_eq_add, one_ne_zero, true_and, false_and, or_false,
      Bool.and_eq_true, beq_iff_eq, Nat.add_eq_left, and_false,
      not_false_eq_true])
    all_goals (rcases hrecv with ⟨_, _, hstate⟩; subst stB'; simp_all)
  · left
    simp only [recvB, ht, if_false] at hrecv
    repeat' split at hrecv
    all_goals try simp_all only [lt_self_iff_false, not_false_eq_true,
      Option.isNone_iff_eq_none, BEq.rfl, Bool.and_true, Bool.not_eq_true,
      Option.some.injEq, Prod.mk.injEq, not_lt, not_and, Bool.and_eq_true,
      beq_iff_eq, Std.le_refl, forall_const, and_self]
    all_goals (rcases hrecv with ⟨_, _, hstate⟩; subst stB'; simp_all)

/-- For every A-to-B message-table index `n`, `oracleRecvB` preserves the
residual KEM failure potential. -/
lemma oracleRecvB_preserves_failurePotential [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentFailurePotential kem onoff z.2 =
      currentFailurePotential kem onoff s := by
  rcases hs with ⟨T, hInv⟩
  cases hentry : s.msgA n with
  | none =>
      have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      rfl
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvB kem onoff ecEk s.stB msg with
      | none => simp [recvB] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stB'⟩
        have hkey : key? = none := by
          symm
          simpa [recvB] using congrArg (fun x => x.map (fun y => y.1)) hlocal
        subst key?
        have hz' : z =
            (some (trcv, none),
              { s with
                stB := stB'
                tcurB := max s.tcurB trcv
                correct := s.correct && decide (trcv = tsnd) }) := by
          simpa [SCKAScheme.oracleRecvB, hentry, scheme, hlocal,
            StateT.run_bind, StateT.run_get] using hz
        subst z
        rcases recvB_kem_source_shape kem onoff ecEk s.stB msg none trcv stB' hlocal with
          hsame | hadv
        · exact currentFailurePotential_congr kem onoff _ _ rfl hsame.1
            rfl rfl hsame.2.1 hsame.2.2.1 hsame.2.2.2
        · have htbound := hInv.msgAEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t + 1 := by
            have hltA : s.stB.t < s.stA.t := hadv.2.2.2.2.trans_le htbound
            have hle := hInv.epochs.2
            omega
          exact currentFailurePotential_recvB_advance kem onoff _ _ hepoch
            rfl rfl rfl hadv.1 hadv.2.1 hadv.2.2.1 hadv.2.2.2.1

/-- For every B-to-A message-table index `n`, `oracleRecvA` preserves the
residual KEM failure potential. -/
lemma oracleRecvA_preserves_failurePotential [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentFailurePotential kem onoff z.2 =
      currentFailurePotential kem onoff s := by
  rcases hs with ⟨T, hInv⟩
  cases hentry : s.msgB n with
  | none =>
      have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvA, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      rfl
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvA kem onoff hDet ecCt0 ecCt1 s.stA msg with
      | none => simp [recvA] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stA'⟩
        have hzA : z.2.stA = stA' := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        have hzB : z.2.stB = s.stB := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        rcases recvA_kem_source_shape kem onoff hDet ecCt0 ecCt1 s.stA msg
            key? trcv stA' hlocal with hsame | hadv
        · exact currentFailurePotential_congr kem onoff _ _
            ((congrArg (fun x => x.t) hzA).trans hsame.1)
            (congrArg (fun x => x.t) hzB)
            ((congrArg (fun x => x.ekA) hzA).trans hsame.2.1)
            ((congrArg (fun x => x.dkA) hzA).trans hsame.2.2)
            (congrArg (fun x => x.stCt) hzB)
            (congrArg (fun x => x.ct0) hzB)
            (congrArg (fun x => x.ct1) hzB)
        · have htbound := hInv.msgBEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t := by
            have : s.stA.t ≤ s.stB.t := by simpa [hadv.2.2.2.1] using htbound
            exact Nat.le_antisymm this hInv.epochs.1
          have hhon := hInv.msgB n (msg, tsnd) hentry
          have hon : (T s.stA.t).on.isSome := by
            rcases msg with ⟨ch?, ack, t, b?⟩
            simp only at hadv
            have ht : t = s.stA.t := hadv.2.2.2.1
            have hb : b? = some 1 := hadv.2.2.2.2.1
            have hch : ch?.isSome := hadv.2.2.2.2.2
            obtain ⟨ch, rfl⟩ := Option.isSome_iff_exists.mp hch
            obtain ⟨ct1, key, i, hon, _⟩ : ∃ ct1 key i,
                (T s.stA.t).on = some (ct1, key) ∧
                  ch = ecCt1.encode ct1 i := by
              simpa [HonestMessageB, ht, hb] using hhon.2
            rw [hon]
            rfl
          have hct1 : s.stB.ct1.isSome := by
            have hmap := hInv.onB
            rw [← hepoch] at hmap
            cases hT : (T s.stA.t).on with
            | none => simp [hT] at hon
            | some pair =>
                rw [hT] at hmap
                rw [← hmap]
                rfl
          exact currentFailurePotential_recvA_advance kem onoff _ _ hepoch hct1
            ((congrArg (fun x => x.t) hzA).trans hadv.1)
            ((congrArg (fun x => x.ekA) hzA).trans hadv.2.1)
            ((congrArg (fun x => x.dkA) hzA).trans hadv.2.2.1)
            (congrArg (fun x => x.t) hzB)
            (congrArg (fun x => x.stCt) hzB)
            (congrArg (fun x => x.ct0) hzB)
            (congrArg (fun x => x.ct1) hzB)

/-- For every A-to-B message-table index `n`, `oracleRecvB` preserves
`currentKEMFailure = false` from a reachable state. -/
lemma oracleRecvB_preserves_currentFailure [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentKEMFailure kem onoff hDet z.2 = false := by
  rcases hs with ⟨T, hInv⟩
  cases hentry : s.msgA n with
  | none =>
      have : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      exact hfail
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvB kem onoff ecEk s.stB msg with
      | none => simp [recvB] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stB'⟩
        have hkey : key? = none := by
          symm
          simpa [recvB] using congrArg (fun x => x.map (fun y => y.1)) hlocal
        subst key?
        have hz' : z =
            (some (trcv, none),
              { s with
                stB := stB'
                tcurB := max s.tcurB trcv
                correct := s.correct && decide (trcv = tsnd) }) := by
          simpa [SCKAScheme.oracleRecvB, hentry, scheme, hlocal,
            StateT.run_bind, StateT.run_get] using hz
        subst z
        rcases recvB_kem_source_shape kem onoff ecEk s.stB msg none trcv stB'
            hlocal with hsame | hadv
        · rw [← hfail]
          exact currentKEMFailure_congr kem onoff hDet _ _ rfl hsame.1 rfl
            hsame.2.2.1 hsame.2.2.2 (congrArg s.keyB hsame.1)
        · have htbound := hInv.msgAEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t + 1 := by
            have hltA : s.stB.t < s.stA.t := hadv.2.2.2.2.trans_le htbound
            have hle := hInv.epochs.2
            omega
          exact currentKEMFailure_recvB_advance_false kem onoff hDet _ _ hepoch
            rfl hadv.1 hadv.2.2.1

/-- For every B-to-A message-table index `n`, `oracleRecvA` preserves
`currentKEMFailure = false` from a reachable state. -/
lemma oracleRecvA_preserves_currentFailure [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    currentKEMFailure kem onoff hDet z.2 = false := by
  rcases hs with ⟨T, hInv⟩
  cases hentry : s.msgB n with
  | none =>
      have : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvA, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      exact hfail
  | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      cases hlocal : recvA kem onoff hDet ecCt0 ecCt1 s.stA msg with
      | none => simp [recvA] at hlocal
      | some out =>
        rcases out with ⟨key?, trcv, stA'⟩
        have hzA : z.2.stA = stA' := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        have hzB : z.2.stB = s.stB := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        have hzKeyB : z.2.keyB = s.keyB := by
          cases key? <;>
            simp [SCKAScheme.oracleRecvA, hentry, scheme, hlocal,
              StateT.run_bind, StateT.run_get] at hz <;> simp_all
        rcases recvA_kem_source_shape kem onoff hDet ecCt0 ecCt1 s.stA msg
            key? trcv stA' hlocal with hsame | hadv
        · rw [← hfail]
          exact currentKEMFailure_congr kem onoff hDet _ _
            ((congrArg (fun x => x.t) hzA).trans hsame.1)
            (congrArg (fun x => x.t) hzB)
            ((congrArg (fun x => x.dkA) hzA).trans hsame.2.2)
            (congrArg (fun x => x.ct0) hzB)
            (congrArg (fun x => x.ct1) hzB)
            (by rw [hzKeyB, hzB])
        · have htbound := hInv.msgBEpoch n msg tsnd hentry
          have hepoch : s.stA.t = s.stB.t := by
            have : s.stA.t ≤ s.stB.t := by simpa [hadv.2.2.2.1] using htbound
            exact Nat.le_antisymm this hInv.epochs.1
          exact currentKEMFailure_recvA_advance_false kem onoff hDet _ _ hepoch
            ((congrArg (fun x => x.t) hzA).trans hadv.1)
            (congrArg (fun x => x.t) hzB)

omit [DecidableEq Sym] in
/-- In a reachable state, absence of the explicit current KEM failure implies
the KEM material required by A's receive transition decapsulates correctly. -/
lemma currentKEMFailure_eq_false_implies_current [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hfail : currentKEMFailure kem onoff hDet s = false) :
    CurrentKEMCorrect kem onoff hDet s := by
  rcases hs with ⟨T, hInv⟩
  intro dk ct0 ct1 key hdk hct0A hct1 hkeyA
  have honSome : (T s.stB.t).on.isSome := by
    have hmap := hInv.onB
    rw [hct1] at hmap
    cases hon : (T s.stB.t).on with
    | none => simp [hon] at hmap
    | some pair => simp
  have htEq : s.stA.t = s.stB.t := by
    by_contra hne
    have hepochBounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hfuture := hInv.futureOn s.stA.t hlt
    have hTKey : (T s.stA.t).key.isSome := by
      rw [← hInv.keyB, hkeyA]
      simp
    simp [EpochTranscript.key, hfuture] at hTKey
  obtain ⟨st, hoffA⟩ := hInv.decodedCt0 ct0 hct0A
  have hoffB : (T s.stA.t).off = optionPair s.stB.stCt s.stB.ct0 := by
    simpa [htEq] using hInv.offB
  have hct0B : s.stB.ct0 = some ct0 := by
    rw [hoffA] at hoffB
    cases hst : s.stB.stCt with
    | none =>
      rw [hst] at hoffB
      change some (st, ct0) = none at hoffB
      exact (Option.some_ne_none _ hoffB).elim
    | some stB =>
      cases hct : s.stB.ct0 with
      | none =>
        rw [hst, hct] at hoffB
        change some (st, ct0) = none at hoffB
        exact (Option.some_ne_none _ hoffB).elim
      | some ct0B =>
        rw [hst, hct] at hoffB
        change some (st, ct0) = some (stB, ct0B) at hoffB
        have hpairs := Option.some.inj hoffB
        exact congrArg some (congrArg Prod.snd hpairs).symm
  have hkeyB : s.keyB s.stB.t = some key := by simpa [htEq] using hkeyA
  simpa [currentKEMFailure, htEq, hdk, hct0B, hct1, hkeyB] using hfail

end Reduction.Internal

end oppUniKemCKA
