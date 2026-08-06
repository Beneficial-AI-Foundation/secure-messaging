/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.Invariant

/-!
# RecvA Preserves the Perfect-Correctness Invariant

`oracleRecvA_preserves_reachableInv`: A's receive oracle preserves
`reachableInv` for every recorded B-to-A message.  Cases, by the delivered
message:

* missing — the state is unchanged;
* stale epoch — only A's receive cursor moves, monotonically;
* current epoch, no usable chunk — only the acknowledgement is processed;
* current epoch, `ct₀` chunk — accumulated until decoding records the
  offline ciphertext;
* current epoch, `ct₁` chunk — accumulated until decoding completes the
  epoch: A decapsulates, `CurrentKEMCorrect` identifies the result with
  B's recorded key, A's epoch-local state is cleared, and its epoch
  advances.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec
open oppUniKemCKA.Perfect.Internal

section RecvA

variable [DecidableEq Sym]

/-- Receiving a stale B-to-A message only advances A's receive cursor and
preserves the existing transcript witness. -/
private lemma reachableInv_after_recvA_stale
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (t : ℕ) (ht : t < s.stA.t) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        tcurA := max s.tcurA (t - 1)
        correct := s.correct && decide (t - 1 = t - 1) } := by
  have hrecv : t - 1 ≤ s.stA.t - 1 := by omega
  have hmax : max s.tcurA (t - 1) ≤ s.stA.t - 1 := max_le hInv.tcurA hrecv
  refine ⟨world, ?_⟩
  constructor
  · simp [hInv.correct]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hmax
  · exact hInv.tcurB
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
  · exact hInv.msgB
  · exact hInv.msgAEpoch
  · exact hInv.msgBEpoch

/-- Replacing A's current-epoch local state while preserving its key material,
decoded ciphertext witness, and honest chunk buffer preserves reachability. -/
private lemma reachableInv_after_recvA_same
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (stA' : StA onoff Sym)
    (ht : stA'.t = s.stA.t) (hdk : stA'.dkA = s.stA.dkA)
    (hek : stA'.ekA = s.stA.ekA)
    (hdecoded : ∀ ct0, stA'.ct0 = some ct0 →
      ∃ st, (world stA'.t).off = some (st, ct0))
    (hchunks : ChunksA kem onoff ecCt0 ecCt1 world stA') :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stA := stA'
        tcurA := max s.tcurA (s.stA.t - 1)
        correct := s.correct && decide (s.stA.t - 1 = s.stA.t - 1) } := by
  have htcur : max s.tcurA (s.stA.t - 1) = s.stA.t - 1 :=
    Nat.max_eq_right hInv.tcurA
  refine ⟨world, ?_⟩
  constructor
  · simp [hInv.correct]
  · simpa [ht] using hInv.epochs
  · simpa [ht] using hInv.epochPosA
  · exact hInv.epochPosB
  · simp [ht, htcur]
  · exact hInv.tcurB
  · simpa [hdk, hek] using hInv.keypairAShape
  · exact hInv.offBShape
  · simpa [ht, hdk, hek] using hInv.keypairA
  · exact hInv.offB
  · exact hInv.onB
  · exact hInv.decodedEk
  · exact hdecoded
  · exact hchunks
  · exact hInv.chunksB
  · simpa [ht] using hInv.pastComplete
  · simpa [ht] using hInv.futureKeypair
  · exact hInv.futureOff
  · exact hInv.futureOn
  · intro t; simpa [ht] using hInv.keyA t
  · exact hInv.keyB
  · exact hInv.msgA
  · exact hInv.msgB
  · intro n ρ tsnd hn
    simpa [ht] using hInv.msgAEpoch n ρ tsnd hn
  · exact hInv.msgBEpoch

/-- Apply the public-key acknowledgement from a current-epoch B-to-A message
to A without changing any other local state. -/
private def recvAAckStep
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) : StA onoff Sym :=
  if ack.ekRec && stA.t == t then
    { stA with ack := { stA.ack with ekRec := true } }
  else stA

omit [DecidableEq Sym] in
/-- `recvAAckStep` preserves A's epoch. -/
@[simp] private lemma recvAAckStep_t
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).t = stA.t := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

omit [DecidableEq Sym] in
/-- `recvAAckStep` preserves A's decapsulation key. -/
@[simp] private lemma recvAAckStep_dkA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).dkA = stA.dkA := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

omit [DecidableEq Sym] in
/-- `recvAAckStep` preserves A's encapsulation key. -/
@[simp] private lemma recvAAckStep_ekA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).ekA = stA.ekA := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

omit [DecidableEq Sym] in
/-- `recvAAckStep` preserves A's decoded offline ciphertext. -/
@[simp] private lemma recvAAckStep_ct0
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).ct0 = stA.ct0 := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

omit [DecidableEq Sym] in
/-- `recvAAckStep` preserves A's ciphertext chunk buffer. -/
@[simp] private lemma recvAAckStep_lch
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).lch = stA.lch := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

/-- Completing current-epoch decapsulation records A's shared key, clears its
epoch-local receive state, and advances A while preserving `reachableInv`. -/
private lemma reachableInv_after_recvA_advance
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (key : K) (htAB : s.stA.t = s.stB.t)
    (hkey : (world s.stA.t).key = some key) :
    let stA' : StA onoff Sym :=
      { s.stA with
        dkA := none
        ekA := none
        ct0 := none
        t := s.stA.t + 1
        lch := ∅
        ack := { ekRec := false, ctRec := false } }
    let tcurA' := max s.tcurA (s.stA.t - 1)
    let keyA' := Function.update s.keyA s.stA.t (some key)
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stA := stA'
        tcurA := tcurA'
        keyA := keyA'
        correct := s.correct
          && decide (s.stA.t - 1 = s.stA.t - 1)
          && (s.keyA s.stA.t).isNone
          && ((s.keyB s.stA.t).isNone || s.keyB s.stA.t == some key)
          && (List.range (tcurA' + 1)).all (fun t =>
            t = 0 || (keyA' t).isSome) } := by
  dsimp only
  have htcur : max s.tcurA (s.stA.t - 1) = s.stA.t - 1 :=
    Nat.max_eq_right hInv.tcurA
  have hkeyAOld : s.keyA s.stA.t = none := by simp [hInv.keyA]
  have hkeyBOld : s.keyB s.stA.t = some key := by simpa [hInv.keyB] using hkey
  have hknown :
      (List.range (max s.tcurA (s.stA.t - 1) + 1)).all (fun t =>
        t = 0 || (Function.update s.keyA s.stA.t (some key) t).isSome) = true := by
    rw [List.all_eq_true]
    intro t htmem
    have hlt : t < s.stA.t := by
      have hlt' : t < max s.tcurA (s.stA.t - 1) + 1 := List.mem_range.mp htmem
      rw [htcur, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hInv.epochPosA))] at hlt'
      exact hlt'
    by_cases ht0 : t = 0
    · simp [ht0]
    · have hk := hInv.pastComplete t (Nat.pos_of_ne_zero ht0) hlt
      have hne : t ≠ s.stA.t := Nat.ne_of_lt hlt
      have hkeyAt := hInv.keyA t
      have hkeySome : (s.keyA t).isSome = true := by
        rw [hkeyAt]
        simpa [ht0, hlt] using hk
      simpa [Function.update, hne, ht0] using hkeySome
  have hkpNext : (world (s.stA.t + 1)).keypair = none :=
    hInv.futureKeypair _ (by omega)
  have hoffNext : (world (s.stA.t + 1)).off = none := by
    apply hInv.futureOff
    omega
  have honNext : (world (s.stA.t + 1)).on = none := by
    apply hInv.futureOn
    omega
  refine ⟨world, ?_⟩
  constructor
  · simp [hInv.correct, hkeyAOld, hkeyBOld, hknown]
  · change s.stB.t ≤ s.stA.t + 1 ∧ s.stA.t + 1 ≤ s.stB.t + 1
    omega
  · change 0 < s.stA.t + 1
    omega
  · exact hInv.epochPosB
  · change max s.tcurA (s.stA.t - 1) ≤ (s.stA.t + 1) - 1
    rw [htcur]
    omega
  · exact hInv.tcurB
  · simp
  · exact hInv.offBShape
  · simp [hkpNext, optionPair]
  · exact hInv.offB
  · exact hInv.onB
  · exact hInv.decodedEk
  · simp
  · simp [ChunksA, hoffNext]
  · exact hInv.chunksB
  · intro t ht0 hlt
    rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with hltOld | rfl
    · exact hInv.pastComplete t ht0 hltOld
    · simp [hkey]
  · intro t hlt
    change s.stA.t + 1 < t at hlt
    exact hInv.futureKeypair t (by omega)
  · exact hInv.futureOff
  · exact hInv.futureOn
  · intro t
    change Function.update s.keyA s.stA.t (some key) t =
      if t = 0 then none
      else if t < s.stA.t + 1 then (world t).key else none
    have hcur0 : s.stA.t ≠ 0 := Nat.ne_of_gt hInv.epochPosA
    by_cases ht : t = s.stA.t
    · subst t
      simp [Function.update, hcur0, hkey]
    · by_cases ht0 : t = 0
      · subst t
        have hzeroCur : (0 : ℕ) ≠ s.stA.t := Ne.symm hcur0
        simpa [Function.update, hzeroCur] using hInv.keyA 0
      by_cases hlt : t < s.stA.t
      · have hltNext : t < s.stA.t + 1 := by omega
        simpa [Function.update, ht, ht0, hlt, hltNext] using hInv.keyA t
      · have hgt : s.stA.t < t := by omega
        have hnltNext : ¬t < s.stA.t + 1 := by omega
        simpa [Function.update, ht, ht0, hlt, hnltNext] using hInv.keyA t
  · exact hInv.keyB
  · exact hInv.msgA
  · exact hInv.msgB
  · intro n ρ tsnd hn
    change ρ.2.2.1 ≤ s.stA.t + 1
    exact (hInv.msgAEpoch n ρ tsnd hn).trans (Nat.le_succ _)
  · exact hInv.msgBEpoch

/-- Processing a current-epoch message with no usable ciphertext chunk updates
only A's acknowledgement and receive cursor while preserving reachability. -/
private lemma reachableInv_after_recvA_ackOnly
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (ack : Ack) :
    let stA' := recvAAckStep kem onoff s.stA ack s.stA.t
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stA := stA'
        tcurA := max s.tcurA (s.stA.t - 1)
        correct := s.correct && decide (s.stA.t - 1 = s.stA.t - 1) } := by
  dsimp only
  apply reachableInv_after_recvA_same kem onoff ecEk ecCt0 ecCt1
    s world hInv (recvAAckStep kem onoff s.stA ack s.stA.t)
  · simp
  · simp
  · simp
  · intro ct0 hct0
    simpa using hInv.decodedCt0 ct0 (by simpa using hct0)
  · simpa [ChunksA] using hInv.chunksA

/-- Assuming correctness of the current KEM material, every result of A's
receive oracle preserves the reachable transcript invariant. -/
lemma oracleRecvA_preserves_reachableInv_of_current
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hCurrent : CurrentKEMCorrect kem onoff hDet s)
    (z : Option (ℕ × Option ℕ) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleRecvA (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s)) :
    reachableInv kem onoff ecEk ecCt0 ecCt1 z.2 := by
  rcases hs with ⟨world, hInv⟩
  cases hentry : s.msgB n with
  | none =>
      have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvA, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      exact ⟨world, hInv⟩
  | some entry =>
      rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
      have hhon := hInv.msgB n ((ch?, ack, t, b?), tsnd) hentry
      have htsnd : tsnd = t - 1 := by
        have hparts := hhon
        simp only [HonestMessageB] at hparts
        exact hparts.1
      have htbound := hInv.msgBEpoch n (ch?, ack, t, b?) tsnd hentry
      change t ≤ s.stB.t at htbound
      by_cases ht : t = s.stA.t
      · subst t
        have htAB : s.stA.t = s.stB.t :=
          Nat.le_antisymm htbound hInv.epochs.1
        cases ch? with
        | none =>
            have hz' : z =
                (some (s.stA.t - 1, none),
                  { s with
                    stA := recvAAckStep kem onoff s.stA ack s.stA.t
                    tcurA := max s.tcurA (s.stA.t - 1)
                    correct := s.correct && decide (s.stA.t - 1 = s.stA.t - 1) }) := by
              simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                hentry, scheme, recvA, recvAAckStep, htsnd] using hz
            subst z
            exact reachableInv_after_recvA_ackOnly kem onoff ecEk ecCt0 ecCt1
              s world hInv ack
        | some ch =>
          cases b? with
          | none =>
              have hz' : z =
                  (some (s.stA.t - 1, none),
                    { s with
                      stA := recvAAckStep kem onoff s.stA ack s.stA.t
                      tcurA := max s.tcurA (s.stA.t - 1)
                      correct := s.correct && decide (s.stA.t - 1 = s.stA.t - 1) }) := by
                simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                  hentry, scheme, recvA, recvAAckStep, htsnd] using hz
              subst z
              exact reachableInv_after_recvA_ackOnly kem onoff ecEk ecCt0 ecCt1
                s world hInv ack
          | some b =>
            fin_cases b
            · cases hct0 : s.stA.ct0 with
              | some ct0 =>
                  have hz' : z =
                      (some (s.stA.t - 1, none),
                        { s with
                          stA := recvAAckStep kem onoff s.stA ack s.stA.t
                          tcurA := max s.tcurA (s.stA.t - 1)
                          correct := s.correct && decide
                            (s.stA.t - 1 = s.stA.t - 1) }) := by
                    simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                      hentry, scheme, recvA, recvAAckStep, htsnd, hct0] using hz
                  subst z
                  exact reachableInv_after_recvA_ackOnly kem onoff ecEk ecCt0 ecCt1
                    s world hInv ack
              | none =>
                  obtain ⟨st, ct0, i, hoff, hch⟩ : ∃ st ct0 i,
                      (world s.stA.t).off = some (st, ct0) ∧
                        ch = ecCt0.encode ct0 i := by
                    simpa [HonestMessageB, htsnd] using hhon
                  obtain ⟨I, hlch, hcard⟩ : ∃ I,
                      s.stA.lch = payloadChunks ecCt0 ct0 I ∧
                        I.card < ecCt0.ec.nchunk := by
                    simpa [ChunksA, hct0, hoff] using hInv.chunksA
                  have hstep := decode_insert_honest ecCt0 hCt0Correct ct0 I i hcard
                  rcases hstep with ⟨hcard', hdec⟩ | ⟨hcard', hdec⟩
                  · let stA0 : StA onoff Sym :=
                        { s.stA with ct0 := none, lch := insert ch s.stA.lch }
                    let stA' := recvAAckStep kem onoff stA0 ack s.stA.t
                    have hz' : z =
                        (some (s.stA.t - 1, none),
                          { s with
                            stA := stA'
                            tcurA := max s.tcurA (s.stA.t - 1)
                            correct := s.correct && decide
                              (s.stA.t - 1 = s.stA.t - 1) }) := by
                      simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                        hentry, scheme, recvA, recvAAckStep, htsnd, hct0, hch,
                        hlch, hdec, stA0, stA'] using hz
                    subst z
                    apply reachableInv_after_recvA_same kem onoff ecEk ecCt0 ecCt1
                      s world hInv stA'
                    · simp [stA', stA0]
                    · simp [stA', stA0]
                    · simp [stA', stA0]
                    · intro ct0' hct0'
                      simp [stA', stA0] at hct0'
                    · unfold ChunksA
                      rw [show stA'.ct0 = none by
                        simp only [stA', recvAAckStep_ct0, stA0]]
                      rw [show stA'.t = s.stA.t by
                        simp only [stA', recvAAckStep_t, stA0], hoff]
                      refine ⟨insert (counterIndex ecCt0 i) I, ?_, hcard'⟩
                      rw [show stA'.lch = insert ch s.stA.lch by
                        simp only [stA', recvAAckStep_lch, stA0], hch, hlch]
                      exact insert_payloadChunks ecCt0 ct0 I i
                  · let stA0 : StA onoff Sym :=
                        { s.stA with
                          ct0 := some ct0
                          lch := ∅
                          ack := { s.stA.ack with ctRec := true } }
                    let stA' := recvAAckStep kem onoff stA0 ack s.stA.t
                    have hz' : z =
                        (some (s.stA.t - 1, none),
                          { s with
                            stA := stA'
                            tcurA := max s.tcurA (s.stA.t - 1)
                            correct := s.correct && decide
                              (s.stA.t - 1 = s.stA.t - 1) }) := by
                      simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                        hentry, scheme, recvA, recvAAckStep, htsnd, hct0, hch,
                        hlch, hdec, stA0, stA'] using hz
                    subst z
                    apply reachableInv_after_recvA_same kem onoff ecEk ecCt0 ecCt1
                      s world hInv stA'
                    · simp [stA', stA0]
                    · simp [stA', stA0]
                    · simp [stA', stA0]
                    · intro ct0' hct0'
                      have : ct0' = ct0 := by
                        have hback : ct0 = ct0' := by
                          simpa [stA', stA0] using hct0'
                        exact hback.symm
                      subst ct0'
                      exact ⟨st, by simpa [stA', stA0] using hoff⟩
                    · cases hon : (world s.stA.t).on with
                      | none => simp [stA', stA0, ChunksA, hoff, hon]
                      | some pair =>
                          rcases pair with ⟨ct1, key⟩
                          unfold ChunksA
                          rw [show stA'.ct0 = some ct0 by
                            simp only [stA', recvAAckStep_ct0, stA0]]
                          rw [show stA'.t = s.stA.t by
                            simp only [stA', recvAAckStep_t, stA0], hon]
                          refine ⟨⟨st, hoff⟩, ∅, ?_, hCt1Pos⟩
                          rw [show stA'.lch = ∅ by
                            simp only [stA', recvAAckStep_lch, stA0]]
                          simp [payloadChunks, ErasureCode.encodeChunks]
            · cases hdk : s.stA.dkA with
              | none =>
                  have hz' : z =
                      (some (s.stA.t - 1, none),
                        { s with
                          stA := recvAAckStep kem onoff s.stA ack s.stA.t
                          tcurA := max s.tcurA (s.stA.t - 1)
                          correct := s.correct && decide
                            (s.stA.t - 1 = s.stA.t - 1) }) := by
                    simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                      hentry, scheme, recvA, recvAAckStep, htsnd, hdk] using hz
                  subst z
                  exact reachableInv_after_recvA_ackOnly kem onoff ecEk ecCt0 ecCt1
                    s world hInv ack
              | some dk =>
                cases hct0 : s.stA.ct0 with
                | none =>
                    have hz' : z =
                        (some (s.stA.t - 1, none),
                          { s with
                            stA := recvAAckStep kem onoff s.stA ack s.stA.t
                            tcurA := max s.tcurA (s.stA.t - 1)
                            correct := s.correct && decide
                              (s.stA.t - 1 = s.stA.t - 1) }) := by
                      simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                        hentry, scheme, recvA, recvAAckStep, htsnd, hdk, hct0] using hz
                    subst z
                    exact reachableInv_after_recvA_ackOnly kem onoff ecEk ecCt0 ecCt1
                      s world hInv ack
                | some ct0 =>
                  obtain ⟨ct1, key, i, hon, hch⟩ : ∃ ct1 key i,
                      (world s.stA.t).on = some (ct1, key) ∧
                        ch = ecCt1.encode ct1 i := by
                    simpa [HonestMessageB, htsnd] using hhon
                  obtain ⟨hoffWitness, I, hlch, hcard⟩ :
                      (∃ st, (world s.stA.t).off = some (st, ct0)) ∧
                      ∃ I, s.stA.lch = payloadChunks ecCt1 ct1 I ∧
                        I.card < ecCt1.ec.nchunk := by
                    simpa [ChunksA, hct0, hon] using hInv.chunksA
                  obtain ⟨st, hoff⟩ := hoffWitness
                  have hstep := decode_insert_honest ecCt1 hCt1Correct ct1 I i hcard
                  rcases hstep with ⟨hcard', hdec⟩ | ⟨hcard', hdec⟩
                  · let stA0 : StA onoff Sym :=
                        { s.stA with lch := insert ch s.stA.lch }
                    let stA' := recvAAckStep kem onoff stA0 ack s.stA.t
                    have hz' : z =
                        (some (s.stA.t - 1, none),
                          { s with
                            stA := stA'
                            tcurA := max s.tcurA (s.stA.t - 1)
                            correct := s.correct && decide
                              (s.stA.t - 1 = s.stA.t - 1) }) := by
                      simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                        hentry, scheme, recvA, recvAAckStep, htsnd, hdk, hct0,
                        hch, hlch, hdec, stA0, stA'] using hz
                    subst z
                    apply reachableInv_after_recvA_same kem onoff ecEk ecCt0 ecCt1
                      s world hInv stA'
                    · simp [stA', stA0]
                    · simp [stA', stA0]
                    · simp [stA', stA0]
                    · intro ct0' hct0'
                      have : ct0' = ct0 := by
                        have hold : s.stA.ct0 = some ct0' := by
                          simpa [stA', stA0] using hct0'
                        exact (Option.some.inj (hct0.symm.trans hold)).symm
                      subst ct0'
                      exact ⟨st, by simpa [stA', stA0] using hoff⟩
                    · unfold ChunksA
                      rw [show stA'.ct0 = some ct0 by
                        simp only [stA', recvAAckStep_ct0, stA0, hct0]]
                      rw [show stA'.t = s.stA.t by
                        simp only [stA', recvAAckStep_t, stA0], hon]
                      refine ⟨⟨st, hoff⟩, insert (counterIndex ecCt1 i) I, ?_, hcard'⟩
                      rw [show stA'.lch = insert ch s.stA.lch by
                        simp only [stA', recvAAckStep_lch, stA0], hch, hlch]
                      exact insert_payloadChunks ecCt1 ct1 I i
                  · have hct1B : s.stB.ct1 = some ct1 := by
                      have hmap := hInv.onB
                      rw [← htAB, hon] at hmap
                      exact hmap.symm
                    have hkeyB : s.keyB s.stA.t = some key := by
                      rw [hInv.keyB]
                      simp [EpochTranscript.key, hon]
                    have hdecaps := hCurrent dk ct0 ct1 key hdk hct0 hct1B hkeyB
                    have hkey : (world s.stA.t).key = some key := by
                      simp [EpochTranscript.key, hon]
                    have hz' :
                        let stA' : StA onoff Sym :=
                          { s.stA with
                            dkA := none
                            ekA := none
                            ct0 := none
                            t := s.stA.t + 1
                            lch := ∅
                            ack := { ekRec := false, ctRec := false } }
                        let tcurA' := max s.tcurA (s.stA.t - 1)
                        let keyA' := Function.update s.keyA s.stA.t (some key)
                        z = (some (s.stA.t - 1, some s.stA.t),
                          { s with
                            stA := stA'
                            tcurA := tcurA'
                            keyA := keyA'
                            correct := s.correct
                              && decide (s.stA.t - 1 = s.stA.t - 1)
                              && (s.keyA s.stA.t).isNone
                              && ((s.keyB s.stA.t).isNone ||
                                s.keyB s.stA.t == some key)
                              && (List.range (tcurA' + 1)).all (fun t =>
                                t = 0 || (keyA' t).isSome) }) := by
                      simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
                        hentry, scheme, recvA, htsnd, hdk, hct0, hch, hlch,
                        hdec, hdecaps] using hz
                    subst z
                    exact reachableInv_after_recvA_advance kem onoff ecEk ecCt0 ecCt1
                      s world hInv key htAB hkey
      · have htle : t ≤ s.stA.t := htbound.trans hInv.epochs.1
        have htlt : t < s.stA.t := by omega
        have hne : s.stA.t ≠ t := Ne.symm ht
        have hz' : z =
            (some (t - 1, none),
              { s with
                tcurA := max s.tcurA (t - 1)
                correct := s.correct && decide (t - 1 = t - 1) }) := by
          simpa [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
            hentry, scheme, recvA, ht, hne, htsnd] using hz
        subst z
        exact reachableInv_after_recvA_stale kem onoff ecEk ecCt0 ecCt1
          s world hInv t htlt

/-- Perfect KEM correctness discharges the current-material assumption, so the
full A-receive query implementation preserves `reachableInv`. This lemma is
public because the parent `Perfect` module composes it with the other oracles. -/
lemma oracleRecvA_preserves_reachableInv
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro n s hs z hz
  exact oracleRecvA_preserves_reachableInv_of_current kem onoff hDet ecEk ecCt0
    hCt0Correct ecCt1 hCt1Correct hCt1Pos leak n s hs
    (currentKEMCorrect_of_perfect kem onoff hDet hkem ecEk ecCt0 ecCt1 s hs) z hz

end RecvA

end oppUniKemCKA
