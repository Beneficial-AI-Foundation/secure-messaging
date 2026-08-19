/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant

/-!
# RecvB Preserves the Reachability Invariant

The main result, `oracleRecvB_preserves_reachableInv`, proves that B's receive
oracle preserves `reachableInv`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec
open ErasureCodePayload

/-- Propagate A's ciphertext-received acknowledgement when it refers to B's
current epoch. -/
private def recvBAckStep
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) : StB onoff Sym :=
  if ack.ctRec && stB.t == t then
    { stB with ack := { stB.ack with ctRec := true } }
  else stB

/-- `recvBAckStep` preserves B's epoch. -/
@[simp] private lemma recvBAckStep_t
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).t = stB.t := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

/-- `recvBAckStep` preserves B's offline ciphertext. -/
@[simp] private lemma recvBAckStep_ct0
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).ct0 = stB.ct0 := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

/-- `recvBAckStep` preserves B's online ciphertext. -/
@[simp] private lemma recvBAckStep_ct1
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).ct1 = stB.ct1 := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

/-- `recvBAckStep` preserves B's offline encapsulation state. -/
@[simp] private lemma recvBAckStep_stCt
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).stCt = stB.stCt := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

section RecvB

variable [DecidableEq Sym]

/-- If B's public-key field is `none`, insert an optional public-key chunk into
the current buffer and apply the decoder. -/
private def recvBEkStep
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym)
    (ch? : Option (ℕ × Sym)) : StB onoff Sym :=
  if stB.ekA.isNone then
    let lch := match ch? with | none => stB.lch | some ch => insert ch stB.lch
    let ekA? := ecEk.decode lch
    { stB with
      ekA := ekA?
      lch := lch
      ack := { stB.ack with ekRec := ekA?.isSome } }
  else stB

/-- `recvBEkStep` preserves B's epoch. -/
@[simp] private lemma recvBEkStep_t
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).t = stB.t := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

/-- `recvBEkStep` preserves B's offline ciphertext. -/
@[simp] private lemma recvBEkStep_ct0
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).ct0 = stB.ct0 := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

/-- `recvBEkStep` preserves B's online ciphertext. -/
@[simp] private lemma recvBEkStep_ct1
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).ct1 = stB.ct1 := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

/-- `recvBEkStep` preserves B's offline encapsulation state. -/
@[simp] private lemma recvBEkStep_stCt
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).stCt = stB.stCt := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

/-- Inserting an honest optional public-key chunk preserves B's honest-buffer
predicate, decoding exactly when the reconstruction threshold is reached. -/
private lemma chunksB_recvBEkStep
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (hcorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (T : Transcript kem onoff) (stB : StB onoff Sym)
    (ch? : Option (ℕ × Sym))
    (hchunks : ChunksBConsistent kem onoff ecEk T stB)
    (hmsg : ∀ ch, ch? = some ch → ∃ pk sk i,
      (T stB.t).keypair = some (pk, sk) ∧ ch = ecEk.encode pk i) :
    ChunksBConsistent kem onoff ecEk T (recvBEkStep kem onoff ecEk stB ch?) := by
  cases htr : (T stB.t).keypair with
  | none =>
      have hs : stB.ekA = none ∧ stB.lch = ∅ := by
        simpa [ChunksBConsistent, htr] using hchunks
      rcases hs with ⟨hek, hlch⟩
      cases ch? with
      | none =>
          have hdec : ecEk.decode ∅ = none := by
            cases hd : ecEk.decode ∅ with
            | none => rfl
            | some pk =>
                have := decode_payloadChunks_none ecEk hcorrect pk ∅ hEkPos
                have hencempty : ecEk.ec.encodeChunks (ecEk.serialize pk) ∅ = ∅ := by
                  ext chunk
                  simp [ErasureCode.encodeChunks]
                have hempty : payloadChunks ecEk pk ∅ = ∅ := by
                  simp [payloadChunks, hencempty]
                rw [hempty, hd] at this
                contradiction
          simp [recvBEkStep, hek, hlch, hdec, ChunksBConsistent, htr]
      | some ch =>
          obtain ⟨pk, sk, i, hkp, _⟩ := hmsg ch rfl
          rw [htr] at hkp
          contradiction
  | some pair =>
      rcases pair with ⟨pk, sk⟩
      cases hek : stB.ekA with
      | some pk' =>
          simpa [recvBEkStep, hek, ChunksBConsistent, htr] using hchunks
      | none =>
          obtain ⟨I, hlch, hcard⟩ : ∃ I,
              stB.lch = payloadChunks ecEk pk I ∧ I.card < ecEk.ec.nchunk := by
            simpa [ChunksBConsistent, htr, hek] using hchunks
          cases ch? with
          | none =>
              have hdec := decode_payloadChunks_none ecEk hcorrect pk I hcard
              have hstepEk :
                  (recvBEkStep kem onoff ecEk stB none).ekA = none := by
                simp [recvBEkStep, hek, hlch, hdec]
              have hstepLch :
                  (recvBEkStep kem onoff ecEk stB none).lch =
                    payloadChunks ecEk pk I := by
                simp [recvBEkStep, hek, hlch]
              unfold ChunksBConsistent
              rw [recvBEkStep_t, htr, hstepEk]
              exact ⟨I, hstepLch, hcard⟩
          | some ch =>
              obtain ⟨pk', sk', i, hkp, hch⟩ := hmsg ch rfl
              have hpk : pk' = pk := by
                have hpairs : some (pk, sk) = some (pk', sk') := htr.symm.trans hkp
                exact (congrArg Prod.fst (Option.some.inj hpairs)).symm
              subst pk'
              have hstep := decode_insert_honest ecEk hcorrect pk I i hcard
              subst ch
              rcases hstep with ⟨hlt, hdec⟩ | ⟨heq, hdec⟩
              · have hstepEk :
                    (recvBEkStep kem onoff ecEk stB
                      (some (ecEk.encode pk i))).ekA = none := by
                  simp [recvBEkStep, hek, hlch, hdec]
                have hstepLch :
                    (recvBEkStep kem onoff ecEk stB
                      (some (ecEk.encode pk i))).lch =
                        payloadChunks ecEk pk (insert (counterIndex ecEk i) I) := by
                  calc
                    _ = insert (ecEk.encode pk i) stB.lch := by
                      simp [recvBEkStep, hek]
                    _ = insert (ecEk.encode pk i) (payloadChunks ecEk pk I) := by
                      rw [hlch]
                    _ = _ := insert_payloadChunks ecEk pk I i
                unfold ChunksBConsistent
                rw [recvBEkStep_t, htr, hstepEk]
                exact ⟨insert (counterIndex ecEk i) I, hstepLch, hlt⟩
              · have hstepEk :
                    (recvBEkStep kem onoff ecEk stB
                      (some (ecEk.encode pk i))).ekA = some pk := by
                  simp [recvBEkStep, hek, hlch, hdec]
                have hstepLch :
                    (recvBEkStep kem onoff ecEk stB
                      (some (ecEk.encode pk i))).lch =
                        payloadChunks ecEk pk (insert (counterIndex ecEk i) I) := by
                  calc
                    _ = insert (ecEk.encode pk i) stB.lch := by
                      simp [recvBEkStep, hek]
                    _ = insert (ecEk.encode pk i) (payloadChunks ecEk pk I) := by
                      rw [hlch]
                    _ = _ := insert_payloadChunks ecEk pk I i
                unfold ChunksBConsistent
                rw [recvBEkStep_t, htr, hstepEk]
                exact ⟨rfl, insert (counterIndex ecEk i) I, hstepLch, heq⟩

omit [DecidableEq Sym] in
/-- If an honest B-side chunk buffer decodes to `pk`, then the current epoch
transcript contains `(pk, sk)` for some `sk`. -/
private lemma ChunksBConsistent.decodedEk
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (T : Transcript kem onoff) (stB : StB onoff Sym)
    (hchunks : ChunksBConsistent kem onoff ecEk T stB) :
    ∀ pk, stB.ekA = some pk → ∃ sk, (T stB.t).keypair = some (pk, sk) := by
  intro pk hpk
  cases htr : (T stB.t).keypair with
  | none => simp [ChunksBConsistent, htr, hpk] at hchunks
  | some pair =>
      rcases pair with ⟨pk', sk⟩
      have hc : pk = pk' ∧ ∃ I,
          stB.lch = payloadChunks ecEk pk' I ∧ I.card = ecEk.ec.nchunk := by
        simpa [ChunksBConsistent, htr, hpk] using hchunks
      have : pk = pk' := hc.1
      subst pk'
      exact ⟨sk, rfl⟩

/-- Processing an honest message for B's current epoch preserves
`reachableInv`. -/
private lemma reachableInv_after_recvB_current
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (hcorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (T : Transcript kem onoff)
    (hInv : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (ch? : Option (ℕ × Sym)) (ack : Ack) (b? : Option Bit)
    (hmsg : HonestMessageA kem onoff ecEk T
      ((ch?, ack, s.stB.t, b?), s.stB.t - 1)) :
    let stB' := recvBAckStep kem onoff
      (recvBEkStep kem onoff ecEk s.stB ch?) ack s.stB.t
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := stB'
        tcurB := max s.tcurB (s.stB.t - 1)
        correct := s.correct && decide (s.stB.t - 1 = s.stB.t - 1) } := by
  dsimp only
  have hchunkMsg : ∀ ch, ch? = some ch → ∃ pk sk i,
      (T s.stB.t).keypair = some (pk, sk) ∧ ch = ecEk.encode pk i := by
    intro ch hch
    subst ch?
    simpa [HonestMessageA] using hmsg.2.2
  have hchunks := chunksB_recvBEkStep kem onoff ecEk hcorrect hEkPos
    T s.stB ch? hInv.chunksB hchunkMsg
  let stB0 := recvBEkStep kem onoff ecEk s.stB ch?
  let stB' := recvBAckStep kem onoff stB0 ack s.stB.t
  have htB0 : stB0.t = s.stB.t := by simp [stB0]
  have htB' : stB'.t = s.stB.t := by simp [stB', htB0]
  have hchunks' : ChunksBConsistent kem onoff ecEk T stB' := by
    by_cases hack : ack.ctRec && stB0.t == s.stB.t
    · simpa [stB', recvBAckStep, hack] using hchunks
    · simpa [stB', recvBAckStep, hack] using hchunks
  refine ⟨T, ?_⟩
  constructor
  · simp [hInv.correct]
  · rw [htB']
    exact hInv.epochs
  · exact hInv.epochPosA
  · simpa [htB'] using hInv.epochPosB
  · exact hInv.tcurA
  · rw [htB', Nat.max_eq_right hInv.tcurB]
  · exact hInv.keypairAShape
  · simpa [stB', stB0] using hInv.offBShape
  · exact hInv.keypairA
  · simpa [stB', stB0, htB'] using hInv.offB
  · simpa [stB', stB0, htB'] using hInv.onB
  · exact ChunksBConsistent.decodedEk kem onoff ecEk T stB' hchunks'
  · exact hInv.decodedCt0
  · exact hInv.chunksA
  · exact hchunks'
  · exact hInv.pastComplete
  · exact hInv.futureKeypair
  · simpa [htB'] using hInv.futureOff
  · simpa [htB'] using hInv.futureOn
  · exact hInv.keyA
  · exact hInv.keyB
  · exact hInv.msgA
  · exact hInv.msgB
  · exact hInv.msgAEpoch
  · simpa [htB'] using hInv.msgBEpoch

omit [DecidableEq Sym] in
/-- Delivering a stale A-to-B message changes only B's receive index and
preserves `reachableInv`. -/
private lemma reachableInv_after_recvB_stale
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (T : Transcript kem onoff)
    (hInv : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (t : ℕ) (ht : t < s.stB.t) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        tcurB := max s.tcurB (t - 1)
        correct := s.correct && decide (t - 1 = t - 1) } := by
  have hrecv : t - 1 ≤ s.stB.t - 1 := by omega
  have hmax : max s.tcurB (t - 1) ≤ s.stB.t - 1 :=
    max_le hInv.tcurB hrecv
  refine ⟨T, ?_⟩
  constructor
  · simp [hInv.correct]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact hmax
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

/-- Reset B's epoch-local state before processing a message for the next
epoch. -/
private def recvBNextBase
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) : StB onoff Sym :=
  { stB with
    t := stB.t + 1
    ct0 := none
    ct1 := none
    stCt := none
    ekA := none
    lch := ∅
    ack := { ekRec := false, ctRec := false } }

/-- Advancing B by one epoch and processing the first honest message of that
epoch preserves `reachableInv`. -/
private lemma reachableInv_after_recvB_next
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (hcorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (T : Transcript kem onoff)
    (hInv : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (ch? : Option (ℕ × Sym)) (ack : Ack) (t : ℕ) (b? : Option Bit)
    (ht : t = s.stB.t + 1) (htA : s.stA.t = t)
    (hmsg : HonestMessageA kem onoff ecEk T ((ch?, ack, t, b?), t - 1)) :
    let base := recvBNextBase kem onoff s.stB
    let stB' := recvBAckStep kem onoff
      (recvBEkStep kem onoff ecEk base ch?) ack t
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := stB'
        tcurB := max s.tcurB (t - 1)
        correct := s.correct && decide (t - 1 = t - 1) } := by
  dsimp only
  let base := recvBNextBase kem onoff s.stB
  have hbaseT : base.t = t := by simp [base, recvBNextBase, ht]
  have hoff : (T t).off = none := hInv.futureOff t (by omega)
  have hon : (T t).on = none := hInv.futureOn t (by omega)
  have hbaseChunks : ChunksBConsistent kem onoff ecEk T base := by
    cases hkp : (T t).keypair with
    | none =>
        unfold ChunksBConsistent
        rw [hbaseT, hkp]
        simp [base, recvBNextBase]
    | some pair =>
        rcases pair with ⟨pk, sk⟩
        unfold ChunksBConsistent
        rw [hbaseT, hkp]
        have hbaseEk : base.ekA = none := by
          simp [base, recvBNextBase]
        rw [hbaseEk]
        refine ⟨∅, ?_, hEkPos⟩
        simp [base, recvBNextBase, payloadChunks, ErasureCode.encodeChunks]
  have hchunkMsg : ∀ ch, ch? = some ch → ∃ pk sk i,
      (T t).keypair = some (pk, sk) ∧ ch = ecEk.encode pk i := by
    intro ch hch
    subst ch?
    simpa [HonestMessageA] using hmsg.2.2
  have hchunks0 := chunksB_recvBEkStep kem onoff ecEk hcorrect hEkPos
    T base ch? hbaseChunks (by
      intro ch hch
      simpa [hbaseT] using hchunkMsg ch hch)
  let stB0 := recvBEkStep kem onoff ecEk base ch?
  let stB' := recvBAckStep kem onoff stB0 ack t
  have htB' : stB'.t = t := by simp [stB', stB0, hbaseT]
  have hchunks' : ChunksBConsistent kem onoff ecEk T stB' := by
    by_cases hack : ack.ctRec && stB0.t == t
    · simpa [stB', recvBAckStep, hack] using hchunks0
    · simpa [stB', recvBAckStep, hack] using hchunks0
  have htcur : max s.tcurB (t - 1) = t - 1 := by
    apply Nat.max_eq_right
    exact hInv.tcurB.trans (by omega)
  refine ⟨T, ?_⟩
  constructor
  · simp [hInv.correct]
  · change stB'.t ≤ s.stA.t ∧ s.stA.t ≤ stB'.t + 1
    simp [htB', htA]
  · exact hInv.epochPosA
  · change 0 < stB'.t
    simpa [htB'] using hInv.epochPosA.trans_eq htA
  · exact hInv.tcurA
  · change max s.tcurB (t - 1) ≤ stB'.t - 1
    rw [htB', htcur]
  · exact hInv.keypairAShape
  · simp [recvBNextBase]
  · simpa [htA] using hInv.keypairA
  · change (T stB'.t).off = optionPair stB'.stCt stB'.ct0
    rw [htB']
    simp [stB', stB0, base, recvBNextBase, hoff]
  · change (T stB'.t).on.map Prod.fst = stB'.ct1
    rw [htB']
    simp [stB', stB0, base, recvBNextBase, hon]
  · exact ChunksBConsistent.decodedEk kem onoff ecEk T stB' hchunks'
  · exact hInv.decodedCt0
  · exact hInv.chunksA
  · exact hchunks'
  · exact hInv.pastComplete
  · exact hInv.futureKeypair
  · intro x hx
    apply hInv.futureOff x
    rw [htB'] at hx
    exact (hInv.epochs.1.trans_eq htA).trans_lt hx
  · intro x hx
    apply hInv.futureOn x
    rw [htB'] at hx
    exact (hInv.epochs.1.trans_eq htA).trans_lt hx
  · exact hInv.keyA
  · exact hInv.keyB
  · exact hInv.msgA
  · exact hInv.msgB
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    change ρ.2.2.1 ≤ stB'.t
    rw [htB']
    exact (hInv.msgBEpoch n ρ tsnd hn).trans (by omega)

/-- B's receive oracle preserves `reachableInv` for missing, stale, current,
and next-epoch message deliveries. -/
lemma oracleRecvB_preserves_reachableInv
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hcorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro n s hs z hz
  rcases hs with ⟨T, hInv⟩
  cases hentry : s.msgA n with
  | none =>
      have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      exact ⟨T, hInv⟩
  | some entry =>
      rcases entry with ⟨⟨ch?, ack, t, b?⟩, tsnd⟩
      have hhon := hInv.msgA n ((ch?, ack, t, b?), tsnd) hentry
      have htsnd : tsnd = t - 1 := by
        have hparts := hhon
        simp only [HonestMessageA] at hparts
        exact hparts.1
      have htbound := hInv.msgAEpoch n (ch?, ack, t, b?) tsnd hentry
      change t ≤ s.stA.t at htbound
      rcases lt_trichotomy t s.stB.t with ht | ht | ht
      · have hne : s.stB.t ≠ t := Nat.ne_of_gt ht
        have hz' :
            z = (some (t - 1, none),
              { s with
                tcurB := max s.tcurB (t - 1)
                correct := s.correct && decide (t - 1 = t - 1) }) := by
          simpa [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, hentry,
            scheme, recvB, htsnd, Nat.not_lt_of_ge (Nat.le_of_lt ht), hne] using hz
        subst z
        exact reachableInv_after_recvB_stale kem onoff ecEk ecCt0 ecCt1
          s T hInv t ht
      · subst t
        have hz' :
            let stB' := recvBAckStep kem onoff
              (recvBEkStep kem onoff ecEk s.stB ch?) ack s.stB.t
            z = (some (s.stB.t - 1, none),
              { s with
                stB := stB'
                tcurB := max s.tcurB (s.stB.t - 1)
                correct := s.correct && decide (s.stB.t - 1 = s.stB.t - 1) }) := by
          simpa [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, hentry,
            scheme, recvB, recvBEkStep, recvBAckStep, htsnd] using hz
        subst z
        exact reachableInv_after_recvB_current kem onoff ecEk hcorrect hEkPos
          ecCt0 ecCt1 s T hInv ch? ack b? (by simpa [htsnd] using hhon)
      · have htNext : t = s.stB.t + 1 := by
          have := hInv.epochs.2
          omega
        have htA : s.stA.t = t := by
          apply Nat.le_antisymm
          · simpa [htNext] using hInv.epochs.2
          · exact htbound
        have hz' :
            let base := recvBNextBase kem onoff s.stB
            let stB' := recvBAckStep kem onoff
              (recvBEkStep kem onoff ecEk base ch?) ack t
            z = (some (t - 1, none),
              { s with
                stB := stB'
                tcurB := max s.tcurB (t - 1)
                correct := s.correct && decide (t - 1 = t - 1) }) := by
          simpa [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, hentry,
            scheme, recvB, recvBNextBase, recvBEkStep, recvBAckStep,
            htsnd, ht, htNext] using hz
        subst z
        exact reachableInv_after_recvB_next kem onoff ecEk hcorrect hEkPos
          ecCt0 ecCt1 s T hInv ch? ack t b? htNext htA (by simpa [htsnd] using hhon)

end RecvB

end oppUniKemCKA
