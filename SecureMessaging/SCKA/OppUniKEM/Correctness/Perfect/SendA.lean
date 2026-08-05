/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.Invariant

/-!
# SendA Preserves the Perfect-Correctness Invariant

This module proves that A's send oracle preserves `reachableInv`.

There are two cases:

* if A already holds the current epoch's key pair, `sendA` emits the next
  public-key chunk without changing the transcript;
* otherwise, `sendA` samples a supported KEM key pair, records it in the
  current `EpochTranscript`, and emits its first public-key chunk.

In both cases the newly recorded message is honest, A's receive cursor is
updated monotonically, and every other component of `WorldInv` is preserved.
The exported result is `oracleSendA_preserves_reachableInv`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec
open oppUniKemCKA.Perfect.Internal

section SendA

variable [DecidableEq Sym]

/-- If A already holds the current epoch's key pair, sending its next encoded
public-key chunk preserves the same transcript and the reachable invariant. -/
private lemma reachableInv_after_sendA_existing
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (pk : PK) (sk : SK) (hek : s.stA.ekA = some pk) (hdk : s.stA.dkA = some sk) :
    let ich := if s.stA.ack.ekRec then s.stA.ich else s.stA.ich + 1
    let ch? := if s.stA.ack.ekRec then none else some (ecEk.encode pk ich)
    let msg : Message Sym := (ch?, s.stA.ack, s.stA.t, none)
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stA := { s.stA with ich := ich }
        tcurA := s.stA.t - 1
        msgA := Function.update s.msgA (s.nA + 1) (some (msg, s.stA.t - 1))
        nA := s.nA + 1
        correct := s.correct && decide (s.tcurA ≤ s.stA.t - 1) } := by
  dsimp only
  refine ⟨world, ?_⟩
  have hmono : s.tcurA ≤ s.stA.t - 1 := hInv.tcurA
  have hkp : (world s.stA.t).keypair = some (pk, sk) := by
    simpa [hek, hdk] using hInv.keypairA
  constructor
  · simp [hInv.correct, hmono]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact le_rfl
  · exact hInv.tcurB
  · simp [hek, hdk]
  · exact hInv.offBShape
  · simpa [hek, hdk] using hInv.keypairA
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
  · intro n entry hn
    by_cases hnew : n = s.nA + 1
    · subst n
      simp [Function.update] at hn
      subst entry
      by_cases hack : s.stA.ack.ekRec
      · simp [HonestMessageA, hack]
      · simp [HonestMessageA, hack, hkp]
    · simp only [Function.update, hnew, ↓reduceDIte] at hn
      exact hInv.msgA n entry hn
  · exact hInv.msgB
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nA + 1
    · subst n
      simp only [Function.update, ↓reduceDIte, Option.some.injEq,
        Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact le_rfl
    · simp only [Function.update, hnew, ↓reduceDIte] at hn
      exact hInv.msgAEpoch n ρ tsnd hn
  · exact hInv.msgBEpoch

/-- If A has no current key pair, sampling and recording a supported key pair,
then sending its first encoded public-key chunk, preserves `reachableInv`. -/
private lemma reachableInv_after_sendA_new
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (pk : PK) (sk : SK) (hmem : (pk, sk) ∈ support kem.keygen)
    (hdk : s.stA.dkA = none) :
    let ich := if s.stA.ack.ekRec then 0 else 1
    let ch? := if s.stA.ack.ekRec then none else some (ecEk.encode pk ich)
    let msg : Message Sym := (ch?, s.stA.ack, s.stA.t, none)
    let old := world s.stA.t
    let _world' := Function.update world s.stA.t (old.setKeypair pk sk hmem (by
      have hkpnone : old.keypair = none := by
        have hekNone : s.stA.ekA = none := by
          have := hInv.keypairAShape
          simp only [hdk, Option.isSome_none, Option.isSome_eq_false_iff,
            Option.isNone_iff_eq_none] at this
          exact this
        simpa [old, hekNone, hdk] using hInv.keypairA
      by_contra hon
      have : old.on.isSome := Option.isSome_iff_ne_none.mpr hon
      simpa [hkpnone] using old.on_keypair this))
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stA := { s.stA with dkA := some sk, ekA := some pk, ich := ich }
        tcurA := s.stA.t - 1
        msgA := Function.update s.msgA (s.nA + 1) (some (msg, s.stA.t - 1))
        nA := s.nA + 1
        correct := s.correct && decide (s.tcurA ≤ s.stA.t - 1) } := by
  dsimp only
  have hekNone : s.stA.ekA = none := by
    have hshape := hInv.keypairAShape
    simp only [hdk, Option.isSome_none, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hshape
    exact hshape
  have hkpnone : (world s.stA.t).keypair = none := by
    simpa [hekNone, hdk] using hInv.keypairA
  have honnone : (world s.stA.t).on = none := by
    by_contra hon
    have his : (world s.stA.t).on.isSome := Option.isSome_iff_ne_none.mpr hon
    simpa [hkpnone] using (world s.stA.t).on_keypair his
  let tr' := (world s.stA.t).setKeypair pk sk hmem honnone
  let world' := Function.update world s.stA.t tr'
  have hworldKey : ∀ t, (world' t).key = (world t).key := by
    intro t
    by_cases ht : t = s.stA.t
    · subst t
      simp [world', tr', EpochTranscript.setKeypair, EpochTranscript.key, honnone]
    · simp [world', ht]
  have hworldOff : ∀ t, (world' t).off = (world t).off := by
    intro t
    by_cases ht : t = s.stA.t
    · subst t
      simp [world', tr', EpochTranscript.setKeypair]
    · simp [world', ht]
  have hworldOn : ∀ t, (world' t).on = (world t).on := by
    intro t
    by_cases ht : t = s.stA.t
    · subst t
      simp [world', tr', EpochTranscript.setKeypair]
    · simp [world', ht]
  refine ⟨world', ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurA]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact le_rfl
  · exact hInv.tcurB
  · simp
  · exact hInv.offBShape
  · simp [world', tr', EpochTranscript.setKeypair]
  · simpa [hworldOff s.stB.t] using hInv.offB
  · simpa [hworldOn s.stB.t] using hInv.onB
  · intro pk' hpk'
    obtain ⟨sk', htr⟩ := hInv.decodedEk pk' hpk'
    refine ⟨sk', ?_⟩
    by_cases ht : s.stB.t = s.stA.t
    · rw [ht] at htr
      rw [hkpnone] at htr
      contradiction
    · simpa [world', ht] using htr
  · intro ct0 hct0
    obtain ⟨st, htr⟩ := hInv.decodedCt0 ct0 hct0
    exact ⟨st, by simpa [hworldOff s.stA.t] using htr⟩
  · simpa [ChunksA, hworldOff s.stA.t, hworldOn s.stA.t] using hInv.chunksA
  · by_cases ht : s.stB.t = s.stA.t
    · have hchunks : s.stB.ekA = none ∧ s.stB.lch = ∅ := by
        simpa [ChunksB, ht, hkpnone] using hInv.chunksB
      rcases hchunks with ⟨hekB, hlch⟩
      simp only [ChunksB, EpochTranscript.setKeypair, ht, Function.update_self,
        hekB, hlch, world', tr']
      exact ⟨∅, by simp [payloadChunks, ErasureCode.encodeChunks], hEkPos⟩
    · simpa [ChunksB, world', ht] using hInv.chunksB
  · intro t ht0 hlt
    simpa [hworldKey t] using hInv.pastComplete t ht0 hlt
  · intro t hlt
    have hne : t ≠ s.stA.t := Nat.ne_of_gt hlt
    simpa [world', hne] using hInv.futureKeypair t hlt
  · intro t hlt
    simpa [hworldOff t] using hInv.futureOff t hlt
  · intro t hlt
    simpa [hworldOn t] using hInv.futureOn t hlt
  · intro t
    simpa [hworldKey t] using hInv.keyA t
  · intro t
    simpa [hworldKey t] using hInv.keyB t
  · intro n entry hn
    by_cases hnew : n = s.nA + 1
    · subst n
      simp [Function.update] at hn
      subst entry
      by_cases hack : s.stA.ack.ekRec
      · simp [HonestMessageA, hack]
      · simp [HonestMessageA, hack, world', tr', EpochTranscript.setKeypair]
    · simp only [Function.update, hnew, ↓reduceDIte] at hn
      have hold := hInv.msgA n entry hn
      rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
      simp only [HonestMessageA] at hold ⊢
      rcases hold with ⟨htsnd, hb, hold⟩
      refine ⟨htsnd, hb, ?_⟩
      cases ch? with
      | none => trivial
      | some ch =>
          obtain ⟨pk', sk', i, htr, hch⟩ := hold
          refine ⟨pk', sk', i, ?_, hch⟩
          by_cases ht : t = s.stA.t
          · subst t
            rw [hkpnone] at htr
            contradiction
          · simpa [world', ht] using htr
  · intro n entry hn
    have hold := hInv.msgB n entry hn
    rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
    simp only [HonestMessageB] at hold ⊢
    rcases hold with ⟨htsnd, hold⟩
    refine ⟨htsnd, ?_⟩
    rcases ch? with _ | ch
    · exact trivial
    rcases b? with _ | b
    · exact hold
    fin_cases b
    · obtain ⟨st, ct0, i, htr, hch⟩ := hold
      exact ⟨st, ct0, i, by simpa [hworldOff t] using htr, hch⟩
    · obtain ⟨ct1, key, i, htr, hch⟩ := hold
      exact ⟨ct1, key, i, by simpa [hworldOn t] using htr, hch⟩
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nA + 1
    · subst n
      simp only [Function.update, ↓reduceDIte, Option.some.injEq,
        Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact le_rfl
    · simp only [Function.update, hnew, ↓reduceDIte] at hn
      exact hInv.msgAEpoch n ρ tsnd hn
  · exact hInv.msgBEpoch

/-- A's send oracle preserves `reachableInv`: it either reuses the current
supported key pair or samples and records a new supported key pair. -/
lemma oracleSendA_preserves_reachableInv
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (hEkPos : 0 < ecEk.ec.nchunk) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro _ s hs z hz
  rcases hs with ⟨world, hInv⟩
  cases hdk : s.stA.dkA with
  | none =>
      have hz' : ∃ pk sk,
          (pk, sk) ∈ support kem.keygen ∧
          let ich := if s.stA.ack.ekRec then 0 else 1
          let ch? := if s.stA.ack.ekRec then none else some (ecEk.encode pk ich)
          let msg : Message Sym := (ch?, s.stA.ack, s.stA.t, none)
          (some (s.stA.t - 1, none, msg),
            { s with
              stA := { s.stA with dkA := some sk, ekA := some pk, ich := ich }
              tcurA := s.stA.t - 1
              msgA := Function.update s.msgA (s.nA + 1)
                (some (msg, s.stA.t - 1))
              nA := s.nA + 1
              correct := s.correct && decide (s.tcurA ≤ s.stA.t - 1) }) = z := by
        rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
        simpa [scheme, sendA, hdk] using hz
      obtain ⟨pk, sk, hmem, rfl⟩ := hz'
      exact reachableInv_after_sendA_new kem onoff ecEk ecCt0 ecCt1 hEkPos
        s world hInv pk sk hmem hdk
  | some sk =>
      have hekSome : s.stA.ekA.isSome := by simpa [hdk] using hInv.keypairAShape
      obtain ⟨pk, hek⟩ := Option.isSome_iff_exists.mp hekSome
      have hz' :
          let ich := if s.stA.ack.ekRec then s.stA.ich else s.stA.ich + 1
          let ch? := if s.stA.ack.ekRec then none else some (ecEk.encode pk ich)
          let msg : Message Sym := (ch?, s.stA.ack, s.stA.t, none)
          z = (some (s.stA.t - 1, none, msg),
            { s with
              stA := { s.stA with ich := ich }
              tcurA := s.stA.t - 1
              msgA := Function.update s.msgA (s.nA + 1)
                (some (msg, s.stA.t - 1))
              nA := s.nA + 1
              correct := s.correct && decide (s.tcurA ≤ s.stA.t - 1) }) := by
        rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
        simpa [scheme, sendA, hdk, hek] using hz
      subst z
      exact reachableInv_after_sendA_existing kem onoff ecEk ecCt0 ecCt1
        s world hInv pk sk hek hdk

end SendA

end oppUniKemCKA
