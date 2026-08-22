/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant

/-!
# SendB Preserves the Reachability Invariant
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec
open ErasureCodePayload

section SendB

variable [DecidableEq Sym]

omit [DecidableEq Sym] in
/-- Recording B's next honest message without changing the transcript preserves
`reachableInv`. -/
private lemma reachableInv_after_sendB_same
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (T : Transcript kem onoff)
    (hInv : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (ich : ℕ) (msg : Message Sym)
    (hhon : HonestMessageB kem onoff ecCt0 ecCt1 T (msg, s.stB.t - 1)) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := { s.stB with ich := ich }
        tcurB := s.stB.t - 1
        msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
        nB := s.nB + 1
        correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) } := by
  refine ⟨T, ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurB]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact le_rfl
  · exact hInv.keypairAShape
  · exact hInv.offBShape
  · exact hInv.keypairA
  · exact hInv.offB
  · exact hInv.onB
  · exact hInv.decodedEk
  · exact hInv.decodedCt0
  · exact hInv.chunksA
  · exact hInv.chunksB
  · exact hInv.pastComplete
  · exact hInv.futureKeypair
  · exact hInv.futureOff
  · exact hInv.futureOn
  · exact hInv.keyA
  · exact hInv.keyB
  · exact hInv.msgA
  · intro n entry hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq] at hn
      subst entry
      exact hhon
    · simp only [Function.update_of_ne hnew] at hn
      exact hInv.msgB n entry hn
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact HonestMessageB.epoch_le hInv.epochPosB hhon
    · simp only [Function.update_of_ne hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

omit [DecidableEq Sym] in
/-- Adding a fresh offline encapsulation and recording B's honest message
preserves `reachableInv`. -/
private lemma reachableInv_after_sendB_newOff
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (T : Transcript kem onoff)
    (hInv : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (st : onoff.St) (ct0 : onoff.C₀)
    (hmem : (st, ct0) ∈ support onoff.encapsOff)
    (hct0 : s.stB.ct0 = none)
    (honNone : (T s.stB.t).on = none)
    (ich : ℕ) (msg : Message Sym)
    (hhon : let tr' := (T s.stB.t).setOff st ct0 hmem honNone
      let T' := Function.update T s.stB.t tr'
      HonestMessageB kem onoff ecCt0 ecCt1 T' (msg, s.stB.t - 1)) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := { s.stB with stCt := some st, ct0 := some ct0, ich := ich }
        tcurB := s.stB.t - 1
        msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
        nB := s.nB + 1
        correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) } := by
  dsimp only at hhon ⊢
  have hst : s.stB.stCt = none := by
    simpa [hct0] using hInv.offBShape
  have hoff : (T s.stB.t).off = none := by
    simpa [hct0, hst, optionPair] using hInv.offB
  let tr' := (T s.stB.t).setOff st ct0 hmem honNone
  let T' := Function.update T s.stB.t tr'
  have hTKey : ∀ t, (T' t).key = (T t).key := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t
      simp [T', tr', EpochTranscript.setOff, EpochTranscript.key, honNone]
    · simp [T', ht]
  have hTKp : ∀ t, (T' t).keypair = (T t).keypair := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [T', tr', EpochTranscript.setOff]
    · simp [T', ht]
  have hTOn : ∀ t, (T' t).on = (T t).on := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [T', tr', EpochTranscript.setOff]
    · simp [T', ht]
  refine ⟨T', ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurB]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact le_rfl
  · exact hInv.keypairAShape
  · simp
  · simpa [hTKp s.stA.t] using hInv.keypairA
  · simp [T', tr', EpochTranscript.setOff, optionPair]
  · simpa [hTOn s.stB.t] using hInv.onB
  · intro pk hpk
    obtain ⟨sk, htr⟩ := hInv.decodedEk pk hpk
    exact ⟨sk, by simpa [hTKp s.stB.t] using htr⟩
  · intro ct0' hct0'
    obtain ⟨st', htr⟩ := hInv.decodedCt0 ct0' hct0'
    refine ⟨st', ?_⟩
    by_cases ht : s.stA.t = s.stB.t
    · rw [ht, hoff] at htr
      contradiction
    · simpa [T', Function.update, ht] using htr
  · by_cases ht : s.stA.t = s.stB.t
    · cases hctA : s.stA.ct0 with
      | some ct0' =>
          obtain ⟨st', hbad⟩ := hInv.decodedCt0 ct0' hctA
          rw [ht] at hbad
          rw [hoff] at hbad
          contradiction
      | none =>
          have hlch : s.stA.lch = ∅ := by
            simpa [ChunksAConsistent, hctA, ht, hoff] using hInv.chunksA
          simp only [ChunksAConsistent, hctA, ht]
          have hcurrentOff : (T' s.stB.t).off = some (st, ct0) := by
            simp [T', tr', EpochTranscript.setOff]
          rw [hcurrentOff]
          exact ⟨∅,
            by simp [payloadChunks, ErasureCode.encodeChunks, hlch], hCt0Pos⟩
    · simpa [ChunksAConsistent, T', Function.update, ht] using hInv.chunksA
  · simpa [ChunksBConsistent, hTKp s.stB.t] using hInv.chunksB
  · intro t ht0 hlt
    simpa [hTKey t] using hInv.pastComplete t ht0 hlt
  · intro t hlt
    simpa [hTKp t] using hInv.futureKeypair t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [T', hne] using hInv.futureOff t hlt
  · intro t hlt
    simpa [hTOn t] using hInv.futureOn t hlt
  · intro t; simpa [hTKey t] using hInv.keyA t
  · intro t; simpa [hTKey t] using hInv.keyB t
  · intro n entry hn
    have hold := hInv.msgA n entry hn
    rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
    simp only [HonestMessageA] at hold ⊢
    rcases hold with ⟨htsnd, hb, hold⟩
    refine ⟨htsnd, hb, ?_⟩
    cases ch? with
    | none => trivial
    | some ch =>
        obtain ⟨pk, sk, i, htr, hch⟩ := hold
        exact ⟨pk, sk, i, by simpa [hTKp t] using htr, hch⟩
  · intro n entry hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq] at hn
      subst entry
      exact hhon
    · simp only [Function.update_of_ne hnew] at hn
      have hold := hInv.msgB n entry hn
      rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
      simp only [HonestMessageB] at hold ⊢
      rcases hold with ⟨htsnd, hold⟩
      refine ⟨htsnd, ?_⟩
      rcases ch? with _ | ch
      · trivial
      rcases b? with _ | b
      · exact hold
      fin_cases b
      · obtain ⟨st', ct0', i, htr, hch⟩ := hold
        by_cases ht : t = s.stB.t
        · subst t
          rw [hoff] at htr
          contradiction
        · exact ⟨st', ct0', i, by simpa [T', ht] using htr, hch⟩
      · obtain ⟨ct1, key, i, htr, hch⟩ := hold
        exact ⟨ct1, key, i, by simpa [hTOn t] using htr, hch⟩
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact HonestMessageB.epoch_le hInv.epochPosB hhon
    · simp only [Function.update_of_ne hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

omit [DecidableEq Sym] in
/-- Adding a fresh online encapsulation and derived key while recording B's
first online chunk preserves `reachableInv`. -/
private lemma reachableInv_after_sendB_newOn
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (T : Transcript kem onoff)
    (hInv : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (pk : PK) (sk : SK) (st : onoff.St) (ct0 : onoff.C₀)
    (ct1 : onoff.C₁) (key : K)
    (hkp : (T s.stB.t).keypair = some (pk, sk))
    (hoff : (T s.stB.t).off = some (st, ct0))
    (hon : (T s.stB.t).on = none)
    (_hek : s.stB.ekA = some pk) (_hst : s.stB.stCt = some st)
    (_hct0 : s.stB.ct0 = some ct0)
    (hmem : (ct1, key) ∈ support (onoff.encapsOn st pk)) :
    let msg : Message Sym :=
      (some (ecCt1.encode ct1 1), s.stB.ack, s.stB.t, some 1)
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := { s.stB with ct1 := some ct1, ich := 1 }
        tcurB := s.stB.t - 1
        keyB := Function.update s.keyB s.stB.t (some key)
        msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
        nB := s.nB + 1
        correct := s.correct
          && decide (s.tcurB ≤ s.stB.t - 1)
          && (s.keyB s.stB.t).isNone
          && ((s.keyA s.stB.t).isNone || s.keyA s.stB.t == some key)
          && (List.range (s.stB.t - 1 + 1)).all (fun t =>
            t = 0 || (Function.update s.keyB s.stB.t (some key) t).isSome) } := by
  dsimp only
  have htEq : s.stA.t = s.stB.t := by
    have hnlt : ¬ s.stB.t < s.stA.t := by
      intro hlt
      have hcomplete := hInv.pastComplete s.stB.t hInv.epochPosB hlt
      simp [EpochTranscript.key, hon] at hcomplete
    exact Nat.le_antisymm (Nat.le_of_not_gt hnlt) hInv.epochs.1
  -- `Nat.le_antisymm` above already closes the epoch equality; the following
  -- support fact determines the transcript installed at the current epoch.
  let tr' := (T s.stB.t).setOn ct1 key (by simp [hkp]) (by simp [hoff]) (by
    intro pk' sk' st' ct0' hkp' hoff'
    have hpairs := hkp'.symm.trans hkp
    have hoffs := hoff'.symm.trans hoff
    have hp : pk' = pk := congrArg Prod.fst (Option.some.inj hpairs)
    have hs : st' = st := congrArg Prod.fst (Option.some.inj hoffs)
    subst pk'; subst st'
    exact hmem)
  let T' := Function.update T s.stB.t tr'
  have hTKp : ∀ t, (T' t).keypair = (T t).keypair := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [T', tr', EpochTranscript.setOn]
    · simp [T', ht]
  have hTOff : ∀ t, (T' t).off = (T t).off := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [T', tr', EpochTranscript.setOn]
    · simp [T', ht]
  have hTKeyOther : ∀ t, t ≠ s.stB.t → (T' t).key = (T t).key := by
    intro t ht
    simp [T', ht]
  have hkeyCurrent : (T' s.stB.t).key = some key := by
    simp [T', tr', EpochTranscript.setOn, EpochTranscript.key]
  have hkeyBOld : s.keyB s.stB.t = none := by
    rw [hInv.keyB, EpochTranscript.key, hon]
    rfl
  have hkeyAOld : s.keyA s.stB.t = none := by
    simp [hInv.keyA, htEq]
  have hknown :
      (List.range (s.stB.t - 1 + 1)).all (fun t =>
        t = 0 || (Function.update s.keyB s.stB.t (some key) t).isSome) = true := by
    rw [List.all_eq_true]
    intro t htmem
    have hlt : t < s.stB.t := by
      have hlt' : t < s.stB.t - 1 + 1 := List.mem_range.mp htmem
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hInv.epochPosB))] at hlt'
      exact hlt'
    by_cases ht0 : t = 0
    · simp [ht0]
    · have hkey := hInv.pastComplete t (Nat.pos_of_ne_zero ht0)
          (lt_of_lt_of_le hlt hInv.epochs.1)
      have hne : t ≠ s.stB.t := Nat.ne_of_lt hlt
      simp [Function.update, hne, hInv.keyB, hkey]
  refine ⟨T', ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurB, hkeyBOld, hkeyAOld, hknown]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact le_rfl
  · exact hInv.keypairAShape
  · exact hInv.offBShape
  · simpa [hTKp s.stA.t] using hInv.keypairA
  · simpa [hTOff s.stB.t] using hInv.offB
  · simp [T', tr', EpochTranscript.setOn]
  · intro pk' hpk'
    obtain ⟨sk', htr⟩ := hInv.decodedEk pk' hpk'
    exact ⟨sk', by simpa [hTKp s.stB.t] using htr⟩
  · intro ct0' hct0'
    obtain ⟨st', htr⟩ := hInv.decodedCt0 ct0' hct0'
    exact ⟨st', by simpa [hTOff s.stA.t] using htr⟩
  · cases hctA : s.stA.ct0 with
    | none => simpa [ChunksAConsistent, hctA, htEq, hTOff s.stB.t] using hInv.chunksA
    | some ct0A =>
        have hlch : s.stA.lch = ∅ := by
          have hc : (∃ stA, (T s.stB.t).off = some (stA, ct0A)) ∧
              s.stA.lch = ∅ := by
            simpa [ChunksAConsistent, hctA, htEq, hon] using hInv.chunksA
          exact hc.2
        have hoffA := hInv.decodedCt0 ct0A hctA
        rw [htEq] at hoffA
        rcases hoffA with ⟨stA, hoffA⟩
        have hct : ct0A = ct0 := by
          exact congrArg Prod.snd (Option.some.inj (hoffA.symm.trans hoff))
        subst ct0A
        unfold ChunksAConsistent
        rw [hctA]
        constructor
        · exact ⟨st, by simpa [htEq, hTOff s.stB.t] using hoff⟩
        · have hon' : (T' s.stA.t).on = some (ct1, key) := by
            simp [htEq, T', tr', EpochTranscript.setOn]
          rw [hon']
          exact ⟨∅,
            by simp [payloadChunks, ErasureCode.encodeChunks, hlch], hCt1Pos⟩
  · simpa [ChunksBConsistent, hTKp s.stB.t] using hInv.chunksB
  · intro t ht0 hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_lt (by simpa [htEq] using hlt)
    simpa [hTKeyOther t hne] using hInv.pastComplete t ht0 hlt
  · intro t hlt
    simpa [hTKp t] using hInv.futureKeypair t hlt
  · intro t hlt
    simpa [hTOff t] using hInv.futureOff t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [T', hne] using hInv.futureOn t hlt
  · intro t
    by_cases ht0 : t = 0
    · simp [ht0, hInv.keyA]
    by_cases hlt : t < s.stA.t
    · have hne : t ≠ s.stB.t := by omega
      simpa [ht0, hlt, hTKeyOther t hne] using hInv.keyA t
    · simpa [ht0, hlt] using hInv.keyA t
  · intro t
    by_cases ht : t = s.stB.t
    · subst t
      simp [Function.update, hkeyCurrent]
    · simp [Function.update, ht, hTKeyOther t ht, hInv.keyB]
  · intro n entry hn
    have hold := hInv.msgA n entry hn
    rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
    simp only [HonestMessageA] at hold ⊢
    rcases hold with ⟨htsnd, hb, hold⟩
    refine ⟨htsnd, hb, ?_⟩
    cases ch? with
    | none => trivial
    | some ch =>
        obtain ⟨pk', sk', i, htr, hch⟩ := hold
        exact ⟨pk', sk', i, by simpa [hTKp t] using htr, hch⟩
  · intro n entry hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq] at hn
      subst entry
      change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ ct1' key' i,
        (T' s.stB.t).on = some (ct1', key') ∧
          ecCt1.encode ct1 1 = ecCt1.encode ct1' i
      exact ⟨rfl, ct1, key, 1, by simp [T', tr', EpochTranscript.setOn], rfl⟩
    · simp only [Function.update_of_ne hnew] at hn
      have hold := hInv.msgB n entry hn
      rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
      simp only [HonestMessageB] at hold ⊢
      rcases hold with ⟨htsnd, hold⟩
      refine ⟨htsnd, ?_⟩
      rcases ch? with _ | ch
      · trivial
      rcases b? with _ | b
      · exact hold
      fin_cases b
      · obtain ⟨st', ct0', i, htr, hch⟩ := hold
        exact ⟨st', ct0', i, by simpa [hTOff t] using htr, hch⟩
      · obtain ⟨ct1', key', i, htr, hch⟩ := hold
        by_cases ht : t = s.stB.t
        · subst t
          rw [hon] at htr
          contradiction
        · exact ⟨ct1', key', i, by simpa [T', ht] using htr, hch⟩
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      change s.stB.t ≤ s.stB.t
      exact le_rfl
    · simp only [Function.update_of_ne hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

omit [DecidableEq Sym] in
/-- Adding fresh offline and online encapsulations together with the derived key
preserves `reachableInv`. -/
private lemma reachableInv_after_sendB_newOffOn
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (T : Transcript kem onoff)
    (hInv : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (pk : PK) (sk : SK) (st : onoff.St) (ct0 : onoff.C₀)
    (ct1 : onoff.C₁) (key : K)
    (hkp : (T s.stB.t).keypair = some (pk, sk))
    (hct0none : s.stB.ct0 = none)
    (hoffmem : (st, ct0) ∈ support onoff.encapsOff)
    (honmem : (ct1, key) ∈ support (onoff.encapsOn st pk)) :
    let msg : Message Sym :=
      (some (ecCt1.encode ct1 1), s.stB.ack, s.stB.t, some 1)
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := { s.stB with
          stCt := some st
          ct0 := some ct0
          ct1 := some ct1
          ich := 1 }
        tcurB := s.stB.t - 1
        keyB := Function.update s.keyB s.stB.t (some key)
        msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
        nB := s.nB + 1
        correct := s.correct
          && decide (s.tcurB ≤ s.stB.t - 1)
          && (s.keyB s.stB.t).isNone
          && ((s.keyA s.stB.t).isNone || s.keyA s.stB.t == some key)
          && (List.range (s.stB.t - 1 + 1)).all (fun t =>
            t = 0 || (Function.update s.keyB s.stB.t (some key) t).isSome) } := by
  dsimp only
  have hstnone : s.stB.stCt = none := by
    simpa [hct0none] using hInv.offBShape
  have hoffnone : (T s.stB.t).off = none := by
    simpa [hct0none, hstnone, optionPair] using hInv.offB
  have honnone : (T s.stB.t).on = none := by
    by_contra hon
    simpa [hoffnone] using (T s.stB.t).on_off (Option.isSome_iff_ne_none.mpr hon)
  have htEq : s.stA.t = s.stB.t := by
    have hnlt : ¬ s.stB.t < s.stA.t := by
      intro hlt
      have hc := hInv.pastComplete s.stB.t hInv.epochPosB hlt
      simp [EpochTranscript.key, honnone] at hc
    exact Nat.le_antisymm (Nat.le_of_not_gt hnlt) hInv.epochs.1
  let offTr := (T s.stB.t).setOff st ct0 hoffmem honnone
  let tr' := offTr.setOn ct1 key (by simp [offTr, EpochTranscript.setOff, hkp])
    (by simp [offTr, EpochTranscript.setOff]) (by
      intro pk' sk' st' ct0' hkp' hoff'
      have hpairs : some (pk, sk) = some (pk', sk') := by
        simpa [offTr, EpochTranscript.setOff] using hkp.symm.trans hkp'
      have hoffs : some (st, ct0) = some (st', ct0') := by
        simpa [offTr, EpochTranscript.setOff] using hoff'
      have hp : pk' = pk := (congrArg Prod.fst (Option.some.inj hpairs)).symm
      have hs : st' = st := (congrArg Prod.fst (Option.some.inj hoffs)).symm
      subst pk'; subst st'
      exact honmem)
  let T' := Function.update T s.stB.t tr'
  have hTKp : ∀ t, (T' t).keypair = (T t).keypair := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [T', tr', offTr, EpochTranscript.setOn, EpochTranscript.setOff]
    · simp [T', ht]
  have hTKeyOther : ∀ t, t ≠ s.stB.t → (T' t).key = (T t).key := by
    intro t ht; simp [T', ht]
  have hkeyCurrent : (T' s.stB.t).key = some key := by
    simp [T', tr', EpochTranscript.setOn, EpochTranscript.key]
  have hkeyBOld : s.keyB s.stB.t = none := by
    simp [hInv.keyB, EpochTranscript.key, honnone]
  have hkeyAOld : s.keyA s.stB.t = none := by simp [hInv.keyA, htEq]
  have hknown :
      (List.range (s.stB.t - 1 + 1)).all (fun t =>
        t = 0 || (Function.update s.keyB s.stB.t (some key) t).isSome) = true := by
    rw [List.all_eq_true]
    intro t htmem
    have hlt : t < s.stB.t := by
      have hlt' : t < s.stB.t - 1 + 1 := List.mem_range.mp htmem
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hInv.epochPosB))] at hlt'
      exact hlt'
    by_cases ht0 : t = 0
    · simp [ht0]
    · have hk := hInv.pastComplete t (Nat.pos_of_ne_zero ht0)
          (lt_of_lt_of_le hlt hInv.epochs.1)
      simp [Function.update, Nat.ne_of_lt hlt, hInv.keyB, hk]
  refine ⟨T', ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurB, hkeyBOld, hkeyAOld, hknown]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact le_rfl
  · exact hInv.keypairAShape
  · simp
  · simpa [hTKp s.stA.t] using hInv.keypairA
  · simp [T', tr', offTr, EpochTranscript.setOn, EpochTranscript.setOff, optionPair]
  · simp [T', tr', EpochTranscript.setOn]
  · intro pk' hpk'
    obtain ⟨sk', htr⟩ := hInv.decodedEk pk' hpk'
    exact ⟨sk', by simpa [hTKp s.stB.t] using htr⟩
  · intro ct0A hct0A
    obtain ⟨stA, hbad⟩ := hInv.decodedCt0 ct0A hct0A
    rw [htEq, hoffnone] at hbad
    contradiction
  · cases hctA : s.stA.ct0 with
    | some ct0A =>
        obtain ⟨stA, hbad⟩ := hInv.decodedCt0 ct0A hctA
        rw [htEq] at hbad
        rw [hoffnone] at hbad
        contradiction
    | none =>
        have hlch : s.stA.lch = ∅ := by
          simpa [ChunksAConsistent, hctA, htEq, hoffnone] using hInv.chunksA
        simp only [ChunksAConsistent, hctA]
        have hcurrentOff : (T' s.stA.t).off = some (st, ct0) := by
          simp [htEq, T', tr', offTr, EpochTranscript.setOn,
            EpochTranscript.setOff]
        rw [hcurrentOff]
        exact ⟨∅,
          by simp [payloadChunks, ErasureCode.encodeChunks, hlch], hCt0Pos⟩
  · simpa [ChunksBConsistent, hTKp s.stB.t] using hInv.chunksB
  · intro t ht0 hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_lt (by simpa [htEq] using hlt)
    simpa [hTKeyOther t hne] using hInv.pastComplete t ht0 hlt
  · intro t hlt; simpa [hTKp t] using hInv.futureKeypair t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [T', hne] using hInv.futureOff t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [T', hne] using hInv.futureOn t hlt
  · intro t
    by_cases ht0 : t = 0
    · simp [ht0, hInv.keyA]
    by_cases hlt : t < s.stA.t
    · have hne : t ≠ s.stB.t := by omega
      simpa [ht0, hlt, hTKeyOther t hne] using hInv.keyA t
    · simpa [ht0, hlt] using hInv.keyA t
  · intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [Function.update, hkeyCurrent]
    · simp [Function.update, ht, hTKeyOther t ht, hInv.keyB]
  · intro n entry hn
    have hold := hInv.msgA n entry hn
    rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
    simp only [HonestMessageA] at hold ⊢
    rcases hold with ⟨htsnd, hb, hold⟩
    refine ⟨htsnd, hb, ?_⟩
    cases ch? with
    | none => trivial
    | some ch =>
        obtain ⟨pk', sk', i, htr, hch⟩ := hold
        exact ⟨pk', sk', i, by simpa [hTKp t] using htr, hch⟩
  · intro n entry hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq] at hn
      subst entry
      change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ ct1' key' i,
        (T' s.stB.t).on = some (ct1', key') ∧
          ecCt1.encode ct1 1 = ecCt1.encode ct1' i
      exact ⟨rfl, ct1, key, 1, by simp [T', tr', EpochTranscript.setOn], rfl⟩
    · simp only [Function.update_of_ne hnew] at hn
      have hold := hInv.msgB n entry hn
      rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
      simp only [HonestMessageB] at hold ⊢
      rcases hold with ⟨htsnd, hold⟩
      refine ⟨htsnd, ?_⟩
      rcases ch? with _ | ch
      · trivial
      rcases b? with _ | b
      · exact hold
      fin_cases b
      · obtain ⟨st', ct0', i, htr, hch⟩ := hold
        by_cases ht : t = s.stB.t
        · subst t; rw [hoffnone] at htr; contradiction
        · exact ⟨st', ct0', i, by simpa [T', ht] using htr, hch⟩
      · obtain ⟨ct1', key', i, htr, hch⟩ := hold
        by_cases ht : t = s.stB.t
        · subst t; rw [honnone] at htr; contradiction
        · exact ⟨ct1', key', i, by simpa [T', ht] using htr, hch⟩
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      change s.stB.t ≤ s.stB.t
      exact le_rfl
    · simp only [Function.update_of_ne hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

/-- B's send oracle preserves `reachableInv` across all transcript-update
cases. -/
lemma oracleSendB_preserves_reachableInv
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro _ s hs z hz
  rcases hs with ⟨T, hInv⟩
  have hknown := hInv.knownPrefixB (tcur := s.stB.t - 1) le_rfl
  cases hct0 : s.stB.ct0 with
  | some ct0 =>
      have hstSome : s.stB.stCt.isSome := by simpa [hct0] using hInv.offBShape
      obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hstSome
      have hoff : (T s.stB.t).off = some (st, ct0) := by
        simpa [hst, hct0, optionPair] using hInv.offB
      cases hack : !s.stB.ack.ctRec
      case true =>
        have hackFalse : s.stB.ack.ctRec = false := by
          cases h : s.stB.ack.ctRec <;> simp [h] at hack ⊢
        let ich := s.stB.ich + 1
        let msg : Message Sym :=
          (some (ecCt0.encode ct0 ich), s.stB.ack, s.stB.t, some 0)
        have hz' : z =
            (some (s.stB.t - 1, none, msg),
              { s with
                stB := { s.stB with ich := ich }
                tcurB := s.stB.t - 1
                msgB := Function.update s.msgB (s.nB + 1)
                  (some (msg, s.stB.t - 1))
                nB := s.nB + 1
                correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) &&
                  (List.range (s.stB.t - 1 + 1)).all
                    (fun t => t = 0 || (s.keyB t).isSome) }) := by
          rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
          simpa [scheme, sendB, hct0, hackFalse, ich, msg] using hz
        subst z
        simp only [hknown, Bool.and_true]
        apply reachableInv_after_sendB_same kem onoff ecEk ecCt0 ecCt1
          s T hInv ich msg
        change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ st' ct0' i,
          (T s.stB.t).off = some (st', ct0') ∧
            ecCt0.encode ct0 ich = ecCt0.encode ct0' i
        exact ⟨rfl, st, ct0, ich, hoff, rfl⟩
      case false =>
        have hackTrue : s.stB.ack.ctRec = true := by
          cases h : s.stB.ack.ctRec <;> simp [h] at hack ⊢
        cases hek : s.stB.ekA with
        | none =>
            let msg : Message Sym := (none, s.stB.ack, s.stB.t, none)
            have hz' : z =
                (some (s.stB.t - 1, none, msg),
                  { s with
                    tcurB := s.stB.t - 1
                    msgB := Function.update s.msgB (s.nB + 1)
                      (some (msg, s.stB.t - 1))
                    nB := s.nB + 1
                    correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) &&
                      (List.range (s.stB.t - 1 + 1)).all
                        (fun t => t = 0 || (s.keyB t).isSome) }) := by
              rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
              simpa [scheme, sendB, hct0, hackTrue, hek, msg] using hz
            subst z
            simp only [hknown, Bool.and_true]
            apply reachableInv_after_sendB_same kem onoff ecEk ecCt0 ecCt1
              s T hInv s.stB.ich msg
            simp [msg, HonestMessageB]
        | some pk =>
            have hkp := hInv.decodedEk pk hek
            obtain ⟨sk, hkp⟩ := hkp
            cases hct1 : s.stB.ct1 with
            | some ct1 =>
                have honSome : (T s.stB.t).on.isSome := by
                  by_contra hn
                  have hn' := Option.not_isSome_iff_eq_none.mp hn
                  simpa [hn', hct1] using hInv.onB
                obtain ⟨pair, hon⟩ := Option.isSome_iff_exists.mp honSome
                rcases pair with ⟨ct1', key⟩
                have hct1eq : ct1' = ct1 := by
                  simpa [hon, hct1] using hInv.onB
                subst ct1'
                let ich := s.stB.ich + 1
                let msg : Message Sym :=
                  (some (ecCt1.encode ct1 ich), s.stB.ack, s.stB.t, some 1)
                have hz' : z =
                    (some (s.stB.t - 1, none, msg),
                      { s with
                        stB := { s.stB with ich := ich }
                        tcurB := s.stB.t - 1
                        msgB := Function.update s.msgB (s.nB + 1)
                          (some (msg, s.stB.t - 1))
                        nB := s.nB + 1
                        correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) &&
                          (List.range (s.stB.t - 1 + 1)).all
                            (fun t => t = 0 || (s.keyB t).isSome) }) := by
                  rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
                  simpa [scheme, sendB, hct0, hackTrue, hek, hct1, msg, ich] using hz
                subst z
                simp only [hknown, Bool.and_true]
                apply reachableInv_after_sendB_same kem onoff ecEk ecCt0 ecCt1
                  s T hInv ich msg
                change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ ct1' key' i,
                  (T s.stB.t).on = some (ct1', key') ∧
                    ecCt1.encode ct1 ich = ecCt1.encode ct1' i
                exact ⟨rfl, ct1, key, ich, hon, rfl⟩
            | none =>
                have hon : (T s.stB.t).on = none := by
                  cases h : (T s.stB.t).on with
                  | none => rfl
                  | some pair =>
                      rcases pair with ⟨ct1, key⟩
                      have hbad := hInv.onB
                      simp [h, hct1] at hbad
                have hz' : ∃ ct1 key,
                    (ct1, key) ∈ support (onoff.encapsOn st pk) ∧
                    let msg : Message Sym :=
                      (some (ecCt1.encode ct1 1), s.stB.ack, s.stB.t, some 1)
                    (some (s.stB.t - 1, some s.stB.t, msg),
                      { s with
                        stB := { s.stB with ct1 := some ct1, ich := 1 }
                        tcurB := s.stB.t - 1
                        keyB := Function.update s.keyB s.stB.t (some key)
                        msgB := Function.update s.msgB (s.nB + 1)
                          (some (msg, s.stB.t - 1))
                        nB := s.nB + 1
                        correct := s.correct
                          && decide (s.tcurB ≤ s.stB.t - 1)
                          && (s.keyB s.stB.t).isNone
                          && ((s.keyA s.stB.t).isNone || s.keyA s.stB.t == some key)
                          && (List.range (s.stB.t - 1 + 1)).all (fun t =>
                            t = 0 ||
                              (Function.update s.keyB s.stB.t (some key) t).isSome) }) = z := by
                  rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
                  simpa [scheme, sendB, hct0, hackTrue, hek, hct1, hst] using hz
                obtain ⟨ct1, key, hmem, rfl⟩ := hz'
                exact reachableInv_after_sendB_newOn kem onoff ecEk ecCt0 ecCt1 hCt1Pos
                  s T hInv pk sk st ct0 ct1 key hkp hoff hon hek hst hct0 hmem
  | none =>
      have hstnone : s.stB.stCt = none := by
        simpa [hct0] using hInv.offBShape
      have hoffnone : (T s.stB.t).off = none := by
        simpa [hct0, hstnone, optionPair] using hInv.offB
      have honnone : (T s.stB.t).on = none := by
        by_contra hn
        simpa [hoffnone] using (T s.stB.t).on_off
          (Option.isSome_iff_ne_none.mpr hn)
      cases hack : !s.stB.ack.ctRec
      case true =>
        have hackFalse : s.stB.ack.ctRec = false := by
          cases h : s.stB.ack.ctRec <;> simp [h] at hack ⊢
        have hz' : ∃ st ct0,
            (st, ct0) ∈ support onoff.encapsOff ∧
            let msg : Message Sym :=
              (some (ecCt0.encode ct0 1), s.stB.ack, s.stB.t, some 0)
            (some (s.stB.t - 1, none, msg),
              { s with
                stB := { s.stB with stCt := some st, ct0 := some ct0, ich := 1 }
                tcurB := s.stB.t - 1
                msgB := Function.update s.msgB (s.nB + 1)
                  (some (msg, s.stB.t - 1))
                nB := s.nB + 1
                correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) &&
                  (List.range (s.stB.t - 1 + 1)).all
                    (fun t => t = 0 || (s.keyB t).isSome) }) = z := by
          rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
          simpa [scheme, sendB, hct0, hackFalse] using hz
        obtain ⟨st, ct0, hmem, rfl⟩ := hz'
        simp only [hknown, Bool.and_true]
        let old := T s.stB.t
        let tr' := old.setOff st ct0 hmem honnone
        let T' := Function.update T s.stB.t tr'
        apply reachableInv_after_sendB_newOff kem onoff ecEk ecCt0 hCt0Pos ecCt1
          s T hInv st ct0 hmem hct0 honnone 1
          (some (ecCt0.encode ct0 1), s.stB.ack, s.stB.t, some 0)
        change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ st' ct0' i,
          (T' s.stB.t).off = some (st', ct0') ∧
            ecCt0.encode ct0 1 = ecCt0.encode ct0' i
        exact ⟨rfl, st, ct0, 1,
          by simp [T', tr', EpochTranscript.setOff], rfl⟩
      case false =>
        have hackTrue : s.stB.ack.ctRec = true := by
          cases h : s.stB.ack.ctRec <;> simp [h] at hack ⊢
        cases hek : s.stB.ekA with
        | none =>
            have hz' : ∃ st ct0,
                (st, ct0) ∈ support onoff.encapsOff ∧
                let msg : Message Sym := (none, s.stB.ack, s.stB.t, none)
                (some (s.stB.t - 1, none, msg),
                  { s with
                    stB := { s.stB with
                      stCt := some st
                      ct0 := some ct0
                      ich := s.stB.ich }
                    tcurB := s.stB.t - 1
                    msgB := Function.update s.msgB (s.nB + 1)
                      (some (msg, s.stB.t - 1))
                    nB := s.nB + 1
                    correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) &&
                      (List.range (s.stB.t - 1 + 1)).all
                        (fun t => t = 0 || (s.keyB t).isSome) }) = z := by
              rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
              simpa [scheme, sendB, hct0, hackTrue, hek] using hz
            obtain ⟨st, ct0, hmem, rfl⟩ := hz'
            simp only [hknown, Bool.and_true]
            apply reachableInv_after_sendB_newOff kem onoff ecEk ecCt0 hCt0Pos ecCt1
              s T hInv st ct0 hmem hct0 honnone s.stB.ich
                (none, s.stB.ack, s.stB.t, none)
            simp [HonestMessageB]
        | some pk =>
            obtain ⟨sk, hkp⟩ := hInv.decodedEk pk hek
            have hct1none : s.stB.ct1 = none := by
              cases hct1 : s.stB.ct1 with
              | none => rfl
              | some ct1 => simpa [honnone, hct1] using hInv.onB
            have hz' : ∃ st ct0 ct1 key,
                (st, ct0) ∈ support onoff.encapsOff ∧
                (ct1, key) ∈ support (onoff.encapsOn st pk) ∧
                let msg : Message Sym :=
                  (some (ecCt1.encode ct1 1), s.stB.ack, s.stB.t, some 1)
                (some (s.stB.t - 1, some s.stB.t, msg),
                  { s with
                    stB := { s.stB with
                      stCt := some st
                      ct0 := some ct0
                      ct1 := some ct1
                      ich := 1 }
                    tcurB := s.stB.t - 1
                    keyB := Function.update s.keyB s.stB.t (some key)
                    msgB := Function.update s.msgB (s.nB + 1)
                      (some (msg, s.stB.t - 1))
                    nB := s.nB + 1
                    correct := s.correct
                      && decide (s.tcurB ≤ s.stB.t - 1)
                      && (s.keyB s.stB.t).isNone
                      && ((s.keyA s.stB.t).isNone || s.keyA s.stB.t == some key)
                      && (List.range (s.stB.t - 1 + 1)).all (fun t =>
                        t = 0 || (Function.update s.keyB s.stB.t (some key) t).isSome) }) = z := by
              rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
              simpa [scheme, sendB, hct0, hackTrue, hek, hct1none] using hz
            obtain ⟨st, ct0, ct1, key, hoffmem, honmem, rfl⟩ := hz'
            exact reachableInv_after_sendB_newOffOn kem onoff ecEk ecCt0 hCt0Pos
              ecCt1 s T hInv pk sk st ct0 ct1 key hkp hct0 hoffmem honmem

end SendB

end oppUniKemCKA
