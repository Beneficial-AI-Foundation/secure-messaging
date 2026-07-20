/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Opp-UniKEM-CKA — Perfect Correctness

This file proves correctness when the underlying KEM is perfectly correct.
The argument is organized around an honest transcript indexed by protocol
epoch.  For every epoch the transcript records the key pair, the offline
encapsulation, and the online encapsulation, together with the assertion that
each value belongs to the support of its prescribed distribution.

The main invariant relates this mathematical transcript to both parties'
local states, the public message history, the accumulated erasure-code
chunks, and the tables of established keys.  It asserts in particular that:

1. the parties' epochs differ by at most one;
2. every stored or transmitted object comes from its epoch transcript;
3. a payload is reconstructed exactly when sufficiently many distinct honest
   chunks have been accumulated;
4. all completed epochs contain matching keys; and
5. every assertion made by the correctness experiment remains true.

The proof first establishes exact reconstruction lemmas for honest encoded
subsets.  It then proves that initialization and each of the five kinds of
interaction—random-index sampling, the two sends, and the two receives—preserve
the invariant.  Receive preservation is proved without an ordering or
freshness assumption, so delayed, reordered, duplicated, and replayed honest
messages are covered.  Perfect KEM correctness is used only when a completed
online encapsulation is decapsulated.  Invariance under an arbitrary adaptive
interaction then implies that the experiment returns `true` with probability
one.

The imperfect-KEM analysis is separated into `KEM` and `Reduction`: the former
develops the conditional KEM error, while the latter replaces the pointwise
KEM assertion above by an expected-error argument.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {m : Type → Type u} {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec

/-- `recvB` reports the epoch carried by the delivered message, independently
of B's current local epoch.  In particular, a delayed old message does not get
mislabelled with the current epoch. -/
theorem recvB_receivingEpoch
    [Monad m] (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
    [DecidableEq Sym]
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym)
    (ch? : Option (ℕ × Sym)) (ack : Ack) (t : ℕ) (b? : Option Bit) :
    (recvB kem onoff ecEk stB (ch?, ack, t, b?)).map (fun out => out.2.1) =
      some (t - 1) := by
  simp [recvB]

/-- Perfect KEM correctness specialized to deterministic decapsulation. -/
private lemma decapsDet_eq_some_of_mem_support [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    {pk : PK} {sk : SK} {c : C} {key : K}
    (hks : (pk, sk) ∈ support kem.keygen)
    (hck : (c, key) ∈ support (kem.encaps pk)) :
    hDet.decapsDet sk c = some key := by
  have hsup : support kem.CorrectExp = {true} :=
    (probOutput_eq_one_iff (mx := kem.CorrectExp) (x := true)).mp hkem |>.2
  rw [KEMScheme.CorrectExp] at hsup
  simp only [hDet.decaps_eq, bind_pure_comp, map_pure, support_bind, support_map] at hsup
  have hin : decide (hDet.decapsDet sk c = some key) ∈
      ⋃ x ∈ support kem.keygen,
        (fun a => decide (hDet.decapsDet x.2 a.1 = some a.2)) '' support (kem.encaps x.1) := by
    exact Set.mem_iUnion.2 ⟨(pk, sk), Set.mem_iUnion.2 ⟨hks, ⟨(c, key), hck, rfl⟩⟩⟩
  exact of_decide_eq_true (by simpa [hsup] using hin)

/-- Honest offline and online samples reassemble to a sample of ordinary KEM
encapsulation. -/
private lemma mem_support_encaps_of_onoff
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    {pk : PK} {st : onoff.St} {ct0 : onoff.C₀} {ct1 : onoff.C₁} {key : K}
    (hoff : (st, ct0) ∈ support onoff.encapsOff)
    (hon : (ct1, key) ∈ support (onoff.encapsOn st pk)) :
    (onoff.split.symm (ct0, ct1), key) ∈ support (kem.encaps pk) := by
  rw [onoff.factor pk, mem_support_bind_iff]
  exact ⟨(st, ct0), hoff, by simpa [mem_support_pure_iff] using hon⟩

section ErasureCode

variable [DecidableEq Sym]

/-- Forget the bound on an encoded chunk index. -/
private def chunkToNat {ec : ErasureCode Sym} :
    (Fin ec.N × Sym) ↪ (ℕ × Sym) where
  toFun chunk := (chunk.1.val, chunk.2)
  inj' := by
    intro a b h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h))
      (congrArg (fun chunk : ℕ × Sym => chunk.2) h)

/-- The natural-index representation used by the Opp-UniKEM message format for
an honest subset of a payload's codeword. -/
private noncomputable def payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) : Finset (ℕ × Sym) :=
  (ecp.ec.encodeChunks (ecp.serialize payload) I).map chunkToNat

private lemma payloadChunks_valid {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    ∀ chunk ∈ payloadChunks ecp payload I, chunk.1 < ecp.ec.N := by
  intro chunk hchunk
  rw [payloadChunks, Finset.mem_map] at hchunk
  obtain ⟨bounded, _, rfl⟩ := hchunk
  exact bounded.1.isLt

private def chunkToFin {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    {chunk // chunk ∈ payloadChunks ecp payload I} ↪ (Fin ecp.ec.N × Sym) where
  toFun chunk :=
    (⟨chunk.1.1, payloadChunks_valid ecp payload I chunk.1 chunk.2⟩, chunk.1.2)
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact Prod.ext
      (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.1.val) hab)
      (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.2) hab)

private lemma payloadChunks_roundtrip {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) :
    (payloadChunks ecp payload I).attach.map (chunkToFin ecp payload I) =
      ecp.ec.encodeChunks (ecp.serialize payload) I := by
  apply Finset.ext
  intro chunk
  constructor
  · intro hchunk
    rw [Finset.mem_map] at hchunk
    obtain ⟨natChunk, _, hnatChunk⟩ := hchunk
    have hmem := natChunk.property
    change natChunk.1 ∈
      (ecp.ec.encodeChunks (ecp.serialize payload) I).map chunkToNat at hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨bounded, hbounded, hboundedEq⟩ := hmem
    have hback : chunkToFin ecp payload I natChunk = bounded := by
      apply Prod.ext
      · apply Fin.ext
        exact (congrArg Prod.fst hboundedEq).symm
      · exact (congrArg Prod.snd hboundedEq).symm
    rw [← hnatChunk, hback]
    exact hbounded
  · intro hchunk
    have hnat : chunkToNat chunk ∈ payloadChunks ecp payload I := by
      rw [payloadChunks, Finset.mem_map]
      exact ⟨chunk, hchunk, rfl⟩
    let natChunk : {chunk // chunk ∈ payloadChunks ecp payload I} :=
      ⟨chunkToNat chunk, hnat⟩
    rw [Finset.mem_map]
    refine ⟨natChunk, by simp, ?_⟩
    exact Prod.ext (Fin.ext rfl) rfl

private lemma payloadChunks_boundedMap {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N))
    (hvalid : ∀ chunk ∈ payloadChunks ecp payload I, chunk.1 < ecp.ec.N) :
    let toBounded : {chunk // chunk ∈ payloadChunks ecp payload I} ↪
        (Fin ecp.ec.N × Sym) :=
      { toFun := fun chunk =>
          (⟨chunk.1.1, hvalid chunk.1 chunk.2⟩, chunk.1.2)
        inj' := by
          intro a b hab
          apply Subtype.ext
          exact Prod.ext
            (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.1.val) hab)
            (congrArg (fun chunk : Fin ecp.ec.N × Sym => chunk.2) hab) }
    (payloadChunks ecp payload I).attach.map toBounded =
      ecp.ec.encodeChunks (ecp.serialize payload) I := by
  dsimp only
  apply Finset.ext
  intro chunk
  constructor
  · intro hchunk
    rw [Finset.mem_map] at hchunk
    obtain ⟨natChunk, _, hnatChunk⟩ := hchunk
    have hmem := natChunk.property
    change natChunk.1 ∈
      (ecp.ec.encodeChunks (ecp.serialize payload) I).map chunkToNat at hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨bounded, hbounded, hboundedEq⟩ := hmem
    rw [← hnatChunk]
    have : (⟨natChunk.1.1, hvalid natChunk.1 natChunk.2⟩, natChunk.1.2) = bounded := by
      apply Prod.ext
      · apply Fin.ext
        exact (congrArg Prod.fst hboundedEq).symm
      · exact (congrArg Prod.snd hboundedEq).symm
    change (⟨natChunk.1.1, hvalid natChunk.1 natChunk.2⟩, natChunk.1.2) ∈
      ecp.ec.encodeChunks (ecp.serialize payload) I
    rw [this]
    exact hbounded
  · intro hchunk
    have hnat : chunkToNat chunk ∈ payloadChunks ecp payload I := by
      rw [payloadChunks, Finset.mem_map]
      exact ⟨chunk, hchunk, rfl⟩
    let natChunk : {chunk // chunk ∈ payloadChunks ecp payload I} :=
      ⟨chunkToNat chunk, hnat⟩
    rw [Finset.mem_map]
    refine ⟨natChunk, by simp, ?_⟩
    exact Prod.ext (Fin.ext rfl) rfl

private lemma decode_payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : I.card = ecp.ec.nchunk) :
    ecp.decode (payloadChunks ecp payload I) = some payload := by
  rw [ErasureCodePayload.decode]
  split
  next hvalid =>
    dsimp only
    rw [payloadChunks_boundedMap ecp payload I hvalid]
    rw [(hcorrect (ecp.serialize payload) I).1 hcard]
    exact ecp.parse_serialize payload
  next hvalid => exact False.elim (hvalid (payloadChunks_valid ecp payload I))

private lemma decode_payloadChunks_none {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : I.card < ecp.ec.nchunk) :
    ecp.decode (payloadChunks ecp payload I) = none := by
  rw [ErasureCodePayload.decode]
  split
  next hvalid =>
    dsimp only
    rw [payloadChunks_boundedMap ecp payload I hvalid]
    simp [(hcorrect (ecp.serialize payload) I).2 hcard]
  next hvalid => exact False.elim (hvalid (payloadChunks_valid ecp payload I))

private def counterIndex {M : Type} (ecp : ErasureCodePayload M Sym) (i : ℕ) :
    Fin ecp.ec.N :=
  ⟨i % ecp.ec.N, Nat.mod_lt i ecp.ec.N_pos⟩

private lemma encode_eq_chunkToNat {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M) (i : ℕ) :
    ecp.encode payload i =
      chunkToNat (counterIndex ecp i, ecp.ec.encode (ecp.serialize payload) (counterIndex ecp i)) :=
  rfl

private lemma encodeChunks_insert (ec : ErasureCode Sym)
    (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)) (i : Fin ec.N) :
    ec.encodeChunks M (insert i I) = insert (i, ec.encode M i) (ec.encodeChunks M I) := by
  ext chunk
  simp [ErasureCode.encodeChunks, eq_comm]

private lemma insert_payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    insert (ecp.encode payload i) (payloadChunks ecp payload I) =
      payloadChunks ecp payload (insert (counterIndex ecp i) I) := by
  rw [payloadChunks, payloadChunks, encodeChunks_insert, Finset.map_insert,
    encode_eq_chunkToNat]

/-- Inserting one honest chunk into an honest sub-threshold set either leaves a
strictly sub-threshold honest set, or reaches the threshold and decodes the
original payload. -/
private lemma decode_insert_honest {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N)) (i : ℕ)
    (hcard : I.card < ecp.ec.nchunk) :
    let I' := insert (counterIndex ecp i) I
    (I'.card < ecp.ec.nchunk ∧
        ecp.decode (insert (ecp.encode payload i) (payloadChunks ecp payload I)) = none) ∨
      (I'.card = ecp.ec.nchunk ∧
        ecp.decode (insert (ecp.encode payload i) (payloadChunks ecp payload I)) =
          some payload) := by
  dsimp only
  have hle : (insert (counterIndex ecp i) I).card ≤ ecp.ec.nchunk := by
    calc
      (insert (counterIndex ecp i) I).card ≤ I.card + 1 :=
        Finset.card_insert_le (counterIndex ecp i) I
      _ ≤ ecp.ec.nchunk := hcard
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · left
    exact ⟨hlt, by
      rw [insert_payloadChunks]
      exact decode_payloadChunks_none ecp hcorrect payload _ hlt⟩
  · right
    exact ⟨heq, by
      rw [insert_payloadChunks]
      exact decode_payloadChunks ecp hcorrect payload _ heq⟩

end ErasureCode

section Invariant

variable [DecidableEq Sym]

/-- Ghost record of the honest randomized choices made for one protocol epoch. -/
structure EpochTranscript
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) where
  /-- The honest public/secret key pair sampled for this epoch, when present. -/
  keypair : Option (PK × SK)
  /-- The honest offline state and ciphertext sampled for this epoch, when present. -/
  off : Option (onoff.St × onoff.C₀)
  /-- The honest online ciphertext and shared key sampled for this epoch, when present. -/
  on : Option (onoff.C₁ × K)
  keypair_mem : ∀ pk sk, keypair = some (pk, sk) → (pk, sk) ∈ support kem.keygen
  off_mem : ∀ st ct0, off = some (st, ct0) → (st, ct0) ∈ support onoff.encapsOff
  on_mem : ∀ pk sk st ct0 ct1 key,
    keypair = some (pk, sk) → off = some (st, ct0) → on = some (ct1, key) →
      (ct1, key) ∈ support (onoff.encapsOn st pk)
  on_keypair : on.isSome → keypair.isSome
  on_off : on.isSome → off.isSome

private def EpochTranscript.empty
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    EpochTranscript kem onoff where
  keypair := none
  off := none
  on := none
  keypair_mem := by simp
  off_mem := by simp
  on_mem := by simp
  on_keypair := by simp
  on_off := by simp

/-- The shared key recorded by an epoch transcript once its online stage has
completed. -/
def EpochTranscript.key
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (tr : EpochTranscript kem onoff) : Option K := tr.on.map Prod.snd

private def EpochTranscript.setKeypair
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (tr : EpochTranscript kem onoff) (pk : PK) (sk : SK)
    (hmem : (pk, sk) ∈ support kem.keygen) (hon : tr.on = none) :
    EpochTranscript kem onoff where
  keypair := some (pk, sk)
  off := tr.off
  on := tr.on
  keypair_mem := by simpa using hmem
  off_mem := tr.off_mem
  on_mem := by simp [hon]
  on_keypair := by simpa [hon]
  on_off := tr.on_off

private def EpochTranscript.setOff
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (tr : EpochTranscript kem onoff) (st : onoff.St) (ct0 : onoff.C₀)
    (hmem : (st, ct0) ∈ support onoff.encapsOff) (hon : tr.on = none) :
    EpochTranscript kem onoff where
  keypair := tr.keypair
  off := some (st, ct0)
  on := tr.on
  keypair_mem := tr.keypair_mem
  off_mem := by simpa using hmem
  on_mem := by simp [hon]
  on_keypair := tr.on_keypair
  on_off := by simpa [hon]

private def EpochTranscript.setOn
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (tr : EpochTranscript kem onoff) (ct1 : onoff.C₁) (key : K)
    (hkeypair : tr.keypair.isSome) (hoffSome : tr.off.isSome)
    (hmem : ∀ pk sk st ct0,
      tr.keypair = some (pk, sk) → tr.off = some (st, ct0) →
        (ct1, key) ∈ support (onoff.encapsOn st pk)) :
    EpochTranscript kem onoff where
  keypair := tr.keypair
  off := tr.off
  on := some (ct1, key)
  keypair_mem := tr.keypair_mem
  off_mem := tr.off_mem
  on_mem := by
    intro pk sk st ct0 ct1' key' hkp hoff hon
    simp only [Option.some.injEq, Prod.mk.injEq] at hon
    obtain ⟨rfl, rfl⟩ := hon
    exact hmem pk sk st ct0 hkp hoff
  on_keypair := by
    intro _
    exact hkeypair
  on_off := by
    intro _
    exact hoffSome

/-- Pair two optional values exactly when both are present.  This operation is
part of the small state-invariant interface used by the quantitative proof. -/
@[simp, nolint simpNF] def optionPair {A B : Type} : Option A → Option B → Option (A × B)
  | some a, some b => some (a, b)
  | _, _ => none

attribute [nolint simpNF] optionPair.eq_2

private def HonestMessageA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (world : ℕ → EpochTranscript kem onoff)
    (entry : Message Sym × ℕ) : Prop :=
  let (ρ, tsnd) := entry
  let (ch?, _ack, t, b?) := ρ
  tsnd = t - 1 ∧ b? = none ∧
    match ch? with
    | none => True
    | some ch => ∃ pk sk i,
        (world t).keypair = some (pk, sk) ∧ ch = ecEk.encode pk i

/-- A B-to-A message is honest when its chunks and acknowledgement fields are
drawn from the recorded epoch transcript and its reported receiving epoch is
the predecessor of its sending epoch. -/
def HonestMessageB
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (world : ℕ → EpochTranscript kem onoff) (entry : Message Sym × ℕ) : Prop :=
  let (ρ, tsnd) := entry
  let (ch?, _ack, t, b?) := ρ
  tsnd = t - 1 ∧
    match ch?, b? with
    | none, _ => True
    | some ch, some 0 => ∃ st ct0 i,
        (world t).off = some (st, ct0) ∧ ch = ecCt0.encode ct0 i
    | some ch, some 1 => ∃ ct1 key i,
        (world t).on = some (ct1, key) ∧ ch = ecCt1.encode ct1 i
    | some _, none => False

private lemma HonestMessageB.epoch_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (world : ℕ → EpochTranscript kem onoff) (msg : Message Sym) (tcur : ℕ)
    (hpos : 0 < tcur)
    (hmsg : HonestMessageB kem onoff ecCt0 ecCt1 world (msg, tcur - 1)) :
    msg.2.2.1 ≤ tcur := by
  rcases msg with ⟨ch?, ack, t, b?⟩
  simp only [HonestMessageB] at hmsg
  change t ≤ tcur
  omega

private def ChunksB
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (world : ℕ → EpochTranscript kem onoff)
    (stB : StB onoff Sym) : Prop :=
  match (world stB.t).keypair with
  | none => stB.ekA = none ∧ stB.lch = ∅
  | some (pk, _sk) =>
      match stB.ekA with
      | none => ∃ I, stB.lch = payloadChunks ecEk pk I ∧ I.card < ecEk.ec.nchunk
      | some pk' => pk' = pk ∧ ∃ I,
          stB.lch = payloadChunks ecEk pk I ∧ I.card = ecEk.ec.nchunk

private def ChunksA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (world : ℕ → EpochTranscript kem onoff) (stA : StA onoff Sym) : Prop :=
  match stA.ct0 with
  | none =>
      match (world stA.t).off with
      | none => stA.lch = ∅
      | some (_st, ct0) => ∃ I,
          stA.lch = payloadChunks ecCt0 ct0 I ∧ I.card < ecCt0.ec.nchunk
  | some ct0 =>
      (∃ st, (world stA.t).off = some (st, ct0)) ∧
      match (world stA.t).on with
      | none => stA.lch = ∅
      | some (ct1, _key) => ∃ I,
          stA.lch = payloadChunks ecCt1 ct1 I ∧ I.card < ecCt1.ec.nchunk

/-- Reachability invariant for the Opp-UniKEM correctness game. -/
structure WorldInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (world : ℕ → EpochTranscript kem onoff)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop where
  correct : s.correct = true
  epochs : s.stB.t ≤ s.stA.t ∧ s.stA.t ≤ s.stB.t + 1
  epochPosA : 0 < s.stA.t
  epochPosB : 0 < s.stB.t
  tcurA : s.tcurA ≤ s.stA.t - 1
  tcurB : s.tcurB ≤ s.stB.t - 1
  keypairAShape : s.stA.ekA.isSome = s.stA.dkA.isSome
  offBShape : s.stB.stCt.isSome = s.stB.ct0.isSome
  keypairA : (world s.stA.t).keypair = optionPair s.stA.ekA s.stA.dkA
  offB : (world s.stB.t).off = optionPair s.stB.stCt s.stB.ct0
  onB : (world s.stB.t).on.map Prod.fst = s.stB.ct1
  decodedEk : ∀ pk, s.stB.ekA = some pk → ∃ sk, (world s.stB.t).keypair = some (pk, sk)
  decodedCt0 : ∀ ct0, s.stA.ct0 = some ct0 → ∃ st, (world s.stA.t).off = some (st, ct0)
  chunksA : ChunksA kem onoff ecCt0 ecCt1 world s.stA
  chunksB : ChunksB kem onoff ecEk world s.stB
  pastComplete : ∀ t, 0 < t → t < s.stA.t → (world t).key.isSome
  futureKeypair : ∀ t, s.stA.t < t → (world t).keypair = none
  futureOff : ∀ t, s.stB.t < t → (world t).off = none
  futureOn : ∀ t, s.stB.t < t → (world t).on = none
  keyA : ∀ t, s.keyA t = if t = 0 then none else if t < s.stA.t then (world t).key else none
  keyB : ∀ t, s.keyB t = (world t).key
  msgA : ∀ n entry, s.msgA n = some entry → HonestMessageA kem onoff ecEk world entry
  msgB : ∀ n entry, s.msgB n = some entry → HonestMessageB kem onoff ecCt0 ecCt1 world entry
  msgAEpoch : ∀ n ρ tsnd, s.msgA n = some (ρ, tsnd) → ρ.2.2.1 ≤ s.stA.t
  msgBEpoch : ∀ n ρ tsnd, s.msgB n = some (ρ, tsnd) → ρ.2.2.1 ≤ s.stB.t

/-- A protocol state is reachable when it admits an honest epoch transcript
satisfying all state, message-history, erasure-code, epoch, and key-agreement
relations collected in `WorldInv`. -/
def reachableInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  ∃ world, WorldInv kem onoff ecEk ecCt0 ecCt1 world s

/-- The KEM material currently held by A and the key currently recorded for B
decapsulate consistently.  This is the only KEM-correctness fact needed by
`recvA`; all remaining protocol correctness obligations are deterministic. -/
def CurrentKEMCorrect
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  ∀ dk ct0 ct1 key,
    s.stA.dkA = some dk → s.stA.ct0 = some ct0 →
    s.stB.ct1 = some ct1 → s.keyB s.stA.t = some key →
    hDet.decapsDet dk (onoff.split.symm (ct0, ct1)) = some key

private lemma currentKEMCorrect_of_perfect [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) :
    CurrentKEMCorrect kem onoff hDet s := by
  rcases hs with ⟨world, hInv⟩
  intro dk ct0 ct1 key hdk hct0 hct1 hkeyB
  have hekSome : s.stA.ekA.isSome := by
    simpa [hdk] using hInv.keypairAShape
  obtain ⟨pk, hek⟩ := Option.isSome_iff_exists.mp hekSome
  have hkp : (world s.stA.t).keypair = some (pk, dk) := by
    simpa [hek, hdk, optionPair] using hInv.keypairA
  obtain ⟨st, hoff⟩ := hInv.decodedCt0 ct0 hct0
  have hworldKey : (world s.stA.t).key = some key := by
    simpa [hInv.keyB] using hkeyB
  have honSome : (world s.stA.t).on.isSome := by
    cases hon : (world s.stA.t).on with
    | some pair => simp [hon]
    | none => simp [EpochTranscript.key, hon] at hworldKey
  have htEq : s.stA.t = s.stB.t := by
    by_contra hne
    have hle : s.stB.t ≤ s.stA.t := hInv.epochs.1
    have hlt : s.stB.t < s.stA.t := by omega
    have hfuture := hInv.futureOn s.stA.t hlt
    simp [hfuture] at honSome
  obtain ⟨pair, hon⟩ := Option.isSome_iff_exists.mp honSome
  rcases pair with ⟨ct1', key'⟩
  have hct1eq : ct1' = ct1 := by
    have hmap := hInv.onB
    rw [← htEq, hon] at hmap
    simpa [hct1] using hmap
  subst ct1'
  have hkeyeq : key' = key := by
    have hworldKey : (world s.stA.t).key = some key' := by
      simp [EpochTranscript.key, hon]
    rw [hInv.keyB, hworldKey] at hkeyB
    exact Option.some.inj hkeyB
  subst key'
  have hks := (world s.stA.t).keypair_mem pk dk hkp
  have hoffmem := (world s.stA.t).off_mem st ct0 hoff
  have honmem := (world s.stA.t).on_mem pk dk st ct0 ct1 key hkp hoff hon
  exact decapsDet_eq_some_of_mem_support kem hDet hkem hks
    (mem_support_encaps_of_onoff kem onoff hoffmem honmem)

lemma reachableInv_init
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (hEkPos : 0 < ecEk.ec.nchunk) (hCt0Pos : 0 < ecCt0.ec.nchunk) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      (SCKAScheme.initGameState
        { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
          ack := { ekRec := false, ctRec := false } }
        { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
          lch := ∅, ack := { ekRec := false, ctRec := false } }) := by
  let world : ℕ → EpochTranscript kem onoff := fun _ => .empty kem onoff
  refine ⟨world, ?_⟩
  constructor <;> simp [world, EpochTranscript.empty, EpochTranscript.key,
    ChunksA, ChunksB, payloadChunks, hEkPos, hCt0Pos, SCKAScheme.initGameState] <;>
    omega

lemma oracleUnif_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif (StA onoff Sym) (StB onoff Sym) K (Message Sym))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro t σ hσ z hz
  have hz' : ∃ y : unifSpec.Range t, (y, σ) = z := by
    simpa [SCKAScheme.oracleUnif] using hz
  rcases hz' with ⟨_, rfl⟩
  simpa using hσ

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
  · simpa [hek, hdk] using hInv.keypairAShape
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
    · simp [Function.update, hnew] at hn
      exact hInv.msgA n entry hn
  · exact hInv.msgB
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nA + 1
    · subst n
      simp [Function.update] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact le_rfl
    · simp [Function.update, hnew] at hn
      exact hInv.msgAEpoch n ρ tsnd hn
  · exact hInv.msgBEpoch

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
    let world' := Function.update world s.stA.t (old.setKeypair pk sk hmem (by
      have hkpnone : old.keypair = none := by
        have hekNone : s.stA.ekA = none := by
          have := hInv.keypairAShape
          simp [hdk] at this
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
    simp [hdk] at hshape
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
      simp [ChunksB, world', ht, tr', EpochTranscript.setKeypair, hekB, hlch]
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
    · simp [Function.update, hnew] at hn
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
      simp [Function.update] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact le_rfl
    · simp [Function.update, hnew] at hn
      exact hInv.msgAEpoch n ρ tsnd hn
  · exact hInv.msgBEpoch

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

@[simp] private lemma recvBEkStep_t
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).t = stB.t := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

@[simp] private lemma recvBEkStep_ct0
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).ct0 = stB.ct0 := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

@[simp] private lemma recvBEkStep_ct1
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).ct1 = stB.ct1 := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

@[simp] private lemma recvBEkStep_stCt
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (stB : StB onoff Sym) (ch?) :
    (recvBEkStep kem onoff ecEk stB ch?).stCt = stB.stCt := by
  by_cases h : stB.ekA = none <;> simp [recvBEkStep, h]

private lemma chunksB_recvBEkStep
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (hcorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (world : ℕ → EpochTranscript kem onoff) (stB : StB onoff Sym)
    (ch? : Option (ℕ × Sym))
    (hchunks : ChunksB kem onoff ecEk world stB)
    (hmsg : ∀ ch, ch? = some ch → ∃ pk sk i,
      (world stB.t).keypair = some (pk, sk) ∧ ch = ecEk.encode pk i) :
    ChunksB kem onoff ecEk world (recvBEkStep kem onoff ecEk stB ch?) := by
  cases htr : (world stB.t).keypair with
  | none =>
      have hs : stB.ekA = none ∧ stB.lch = ∅ := by
        simpa [ChunksB, htr] using hchunks
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
          simp [recvBEkStep, hek, hlch, hdec, ChunksB, htr]
      | some ch =>
          obtain ⟨pk, sk, i, hkp, _⟩ := hmsg ch rfl
          rw [htr] at hkp
          contradiction
  | some pair =>
      rcases pair with ⟨pk, sk⟩
      cases hek : stB.ekA with
      | some pk' =>
          simpa [recvBEkStep, hek, ChunksB, htr] using hchunks
      | none =>
          obtain ⟨I, hlch, hcard⟩ : ∃ I,
              stB.lch = payloadChunks ecEk pk I ∧ I.card < ecEk.ec.nchunk := by
            simpa [ChunksB, htr, hek] using hchunks
          cases ch? with
          | none =>
              have hdec := decode_payloadChunks_none ecEk hcorrect pk I hcard
              simp [recvBEkStep, hek, hlch, hdec, ChunksB, htr]
              exact ⟨I, rfl, hcard⟩
          | some ch =>
              obtain ⟨pk', sk', i, hkp, hch⟩ := hmsg ch rfl
              have hpk : pk' = pk := by
                have hpairs : some (pk, sk) = some (pk', sk') := htr.symm.trans hkp
                exact (congrArg Prod.fst (Option.some.inj hpairs)).symm
              subst pk'
              have hstep := decode_insert_honest ecEk hcorrect pk I i hcard
              subst ch
              rcases hstep with ⟨hlt, hdec⟩ | ⟨heq, hdec⟩
              · simp [recvBEkStep, hek, hlch, hdec, ChunksB, htr]
                exact ⟨insert (counterIndex ecEk i) I,
                  insert_payloadChunks ecEk pk I i, hlt⟩
              · simp [recvBEkStep, hek, hlch, hdec, ChunksB, htr]
                exact ⟨insert (counterIndex ecEk i) I,
                  insert_payloadChunks ecEk pk I i, heq⟩

private lemma ChunksB.decodedEk
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (world : ℕ → EpochTranscript kem onoff) (stB : StB onoff Sym)
    (hchunks : ChunksB kem onoff ecEk world stB) :
    ∀ pk, stB.ekA = some pk → ∃ sk, (world stB.t).keypair = some (pk, sk) := by
  intro pk hpk
  cases htr : (world stB.t).keypair with
  | none => simp [ChunksB, htr, hpk] at hchunks
  | some pair =>
      rcases pair with ⟨pk', sk⟩
      have hc : pk = pk' ∧ ∃ I,
          stB.lch = payloadChunks ecEk pk' I ∧ I.card = ecEk.ec.nchunk := by
        simpa [ChunksB, htr, hpk] using hchunks
      have : pk = pk' := hc.1
      subst pk'
      exact ⟨sk, by simpa using htr⟩

private def recvBAckStep
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) : StB onoff Sym :=
  if ack.ctRec && stB.t == t then
    { stB with ack := { stB.ack with ctRec := true } }
  else stB

@[simp] private lemma recvBAckStep_t
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).t = stB.t := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

@[simp] private lemma recvBAckStep_ct0
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).ct0 = stB.ct0 := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

@[simp] private lemma recvBAckStep_ct1
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).ct1 = stB.ct1 := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

@[simp] private lemma recvBAckStep_stCt
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stB : StB onoff Sym) (ack : Ack) (t : ℕ) :
    (recvBAckStep kem onoff stB ack t).stCt = stB.stCt := by
  by_cases h : ack.ctRec && stB.t == t <;> simp [recvBAckStep, h]

private lemma reachableInv_after_recvB_current
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (hcorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (ch? : Option (ℕ × Sym)) (ack : Ack) (b? : Option Bit)
    (hmsg : HonestMessageA kem onoff ecEk world
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
      (world s.stB.t).keypair = some (pk, sk) ∧ ch = ecEk.encode pk i := by
    intro ch hch
    subst ch?
    simpa [HonestMessageA] using hmsg.2.2
  have hchunks := chunksB_recvBEkStep kem onoff ecEk hcorrect hEkPos
    world s.stB ch? hInv.chunksB hchunkMsg
  let stB0 := recvBEkStep kem onoff ecEk s.stB ch?
  let stB' := recvBAckStep kem onoff stB0 ack s.stB.t
  have htB0 : stB0.t = s.stB.t := by simp [stB0]
  have htB' : stB'.t = s.stB.t := by simp [stB', htB0]
  have hchunks' : ChunksB kem onoff ecEk world stB' := by
    by_cases hack : ack.ctRec && stB0.t == s.stB.t
    · simpa [stB', recvBAckStep, hack] using hchunks
    · simpa [stB', recvBAckStep, hack] using hchunks
  refine ⟨world, ?_⟩
  constructor
  · simp [hInv.correct]
  · simpa [htB'] using hInv.epochs
  · exact hInv.epochPosA
  · simpa [htB'] using hInv.epochPosB
  · exact hInv.tcurA
  · simpa [htB', Nat.max_eq_right hInv.tcurB]
  · exact hInv.keypairAShape
  · simpa [stB', stB0] using hInv.offBShape
  · exact hInv.keypairA
  · simpa [stB', stB0, htB'] using hInv.offB
  · simpa [stB', stB0, htB'] using hInv.onB
  · exact ChunksB.decodedEk kem onoff ecEk world stB' hchunks'
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

private lemma reachableInv_after_recvB_stale
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (t : ℕ) (ht : t < s.stB.t) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        tcurB := max s.tcurB (t - 1)
        correct := s.correct && decide (t - 1 = t - 1) } := by
  have hrecv : t - 1 ≤ s.stB.t - 1 := by omega
  have hmax : max s.tcurB (t - 1) ≤ s.stB.t - 1 :=
    max_le hInv.tcurB hrecv
  refine ⟨world, ?_⟩
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

private lemma reachableInv_after_recvB_next
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (hcorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (ch? : Option (ℕ × Sym)) (ack : Ack) (t : ℕ) (b? : Option Bit)
    (ht : t = s.stB.t + 1) (htA : s.stA.t = t)
    (hmsg : HonestMessageA kem onoff ecEk world ((ch?, ack, t, b?), t - 1)) :
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
  have hoff : (world t).off = none := hInv.futureOff t (by omega)
  have hon : (world t).on = none := hInv.futureOn t (by omega)
  have hbaseChunks : ChunksB kem onoff ecEk world base := by
    cases hkp : (world t).keypair with
    | none =>
        unfold ChunksB
        rw [hbaseT, hkp]
        simp [base, recvBNextBase]
    | some pair =>
        rcases pair with ⟨pk, sk⟩
        unfold ChunksB
        rw [hbaseT, hkp]
        simp [base, recvBNextBase]
        exact ⟨∅, by simp [payloadChunks, ErasureCode.encodeChunks], hEkPos⟩
  have hchunkMsg : ∀ ch, ch? = some ch → ∃ pk sk i,
      (world t).keypair = some (pk, sk) ∧ ch = ecEk.encode pk i := by
    intro ch hch
    subst ch?
    simpa [HonestMessageA] using hmsg.2.2
  have hchunks0 := chunksB_recvBEkStep kem onoff ecEk hcorrect hEkPos
    world base ch? hbaseChunks (by
      intro ch hch
      simpa [hbaseT] using hchunkMsg ch hch)
  let stB0 := recvBEkStep kem onoff ecEk base ch?
  let stB' := recvBAckStep kem onoff stB0 ack t
  have htB' : stB'.t = t := by simp [stB', stB0, hbaseT]
  have hchunks' : ChunksB kem onoff ecEk world stB' := by
    by_cases hack : ack.ctRec && stB0.t == t
    · simpa [stB', recvBAckStep, hack] using hchunks0
    · simpa [stB', recvBAckStep, hack] using hchunks0
  have htcur : max s.tcurB (t - 1) = t - 1 := by
    apply Nat.max_eq_right
    exact hInv.tcurB.trans (by omega)
  refine ⟨world, ?_⟩
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
  · simp [stB', stB0, base, recvBNextBase]
  · simpa [htA] using hInv.keypairA
  · change (world stB'.t).off = optionPair stB'.stCt stB'.ct0
    rw [htB']
    simp [stB', stB0, base, recvBNextBase, hoff]
  · change (world stB'.t).on.map Prod.fst = stB'.ct1
    rw [htB']
    simp [stB', stB0, base, recvBNextBase, hon]
  · exact ChunksB.decodedEk kem onoff ecEk world stB' hchunks'
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
  rcases hs with ⟨world, hInv⟩
  cases hentry : s.msgA n with
  | none =>
      have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst z
      exact ⟨world, hInv⟩
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
          s world hInv t ht
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
          ecCt0 ecCt1 s world hInv ch? ack b? (by simpa [htsnd] using hhon)
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
          ecCt0 ecCt1 s world hInv ch? ack t b? htNext htA (by simpa [htsnd] using hhon)

private lemma reachableInv_after_sendB_same
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (ich : ℕ) (msg : Message Sym)
    (hhon : HonestMessageB kem onoff ecCt0 ecCt1 world (msg, s.stB.t - 1)) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := { s.stB with ich := ich }
        tcurB := s.stB.t - 1
        msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
        nB := s.nB + 1
        correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) } := by
  refine ⟨world, ?_⟩
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
      simp [Function.update] at hn
      subst entry
      exact hhon
    · simp [Function.update, hnew] at hn
      exact hInv.msgB n entry hn
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp [Function.update] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact HonestMessageB.epoch_le kem onoff ecCt0 ecCt1 world msg s.stB.t
        hInv.epochPosB hhon
    · simp [Function.update, hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

private lemma reachableInv_after_sendB_newOff
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (st : onoff.St) (ct0 : onoff.C₀)
    (hmem : (st, ct0) ∈ support onoff.encapsOff)
    (hct0 : s.stB.ct0 = none) (ich : ℕ) (msg : Message Sym)
    (hhon : let tr' := (world s.stB.t).setOff st ct0 hmem (by
        have hoff : (world s.stB.t).off = none := by
          have hst : s.stB.stCt = none := by
            have hshape := hInv.offBShape
            simp [hct0] at hshape
            exact hshape
          simpa [hct0, hst, optionPair] using hInv.offB
        by_contra hon
        have his := (world s.stB.t).on_off (Option.isSome_iff_ne_none.mpr hon)
        simpa [hoff] using his)
      let world' := Function.update world s.stB.t tr'
      HonestMessageB kem onoff ecCt0 ecCt1 world' (msg, s.stB.t - 1)) :
    let old := world s.stB.t
    let world' := Function.update world s.stB.t (old.setOff st ct0 hmem (by
      have hst : s.stB.stCt = none := by
        have hshape := hInv.offBShape
        simp [hct0] at hshape
        exact hshape
      have hoff : old.off = none := by
        simpa [old, hct0, hst, optionPair] using hInv.offB
      by_contra hon
      exact (by simpa [hoff] using old.on_off (Option.isSome_iff_ne_none.mpr hon))))
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with
        stB := { s.stB with stCt := some st, ct0 := some ct0, ich := ich }
        tcurB := s.stB.t - 1
        msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
        nB := s.nB + 1
        correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) } := by
  dsimp only at hhon ⊢
  have hst : s.stB.stCt = none := by
    have hshape := hInv.offBShape
    simp [hct0] at hshape
    exact hshape
  have hoff : (world s.stB.t).off = none := by
    simpa [hct0, hst, optionPair] using hInv.offB
  have hon : (world s.stB.t).on = none := by
    by_contra hne
    simpa [hoff] using (world s.stB.t).on_off (Option.isSome_iff_ne_none.mpr hne)
  let tr' := (world s.stB.t).setOff st ct0 hmem hon
  let world' := Function.update world s.stB.t tr'
  have hworldKey : ∀ t, (world' t).key = (world t).key := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t
      simp [world', tr', EpochTranscript.setOff, EpochTranscript.key, hon]
    · simp [world', ht]
  have hworldKp : ∀ t, (world' t).keypair = (world t).keypair := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [world', tr', EpochTranscript.setOff]
    · simp [world', ht]
  have hworldOn : ∀ t, (world' t).on = (world t).on := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [world', tr', EpochTranscript.setOff]
    · simp [world', ht]
  refine ⟨world', ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurB]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact le_rfl
  · exact hInv.keypairAShape
  · simp
  · simpa [hworldKp s.stA.t] using hInv.keypairA
  · simp [world', tr', EpochTranscript.setOff, optionPair]
  · simpa [hworldOn s.stB.t] using hInv.onB
  · intro pk hpk
    obtain ⟨sk, htr⟩ := hInv.decodedEk pk hpk
    exact ⟨sk, by simpa [hworldKp s.stB.t] using htr⟩
  · intro ct0' hct0'
    obtain ⟨st', htr⟩ := hInv.decodedCt0 ct0' hct0'
    refine ⟨st', ?_⟩
    by_cases ht : s.stA.t = s.stB.t
    · rw [ht, hoff] at htr
      contradiction
    · simpa [world', Function.update, ht] using htr
  · by_cases ht : s.stA.t = s.stB.t
    · cases hctA : s.stA.ct0 with
      | some ct0' =>
          obtain ⟨st', hbad⟩ := hInv.decodedCt0 ct0' hctA
          rw [ht] at hbad
          rw [hoff] at hbad
          contradiction
      | none =>
          have hlch : s.stA.lch = ∅ := by
            simpa [ChunksA, hctA, ht, hoff] using hInv.chunksA
          simp [ChunksA, hctA, ht, world', tr', EpochTranscript.setOff, hlch]
          exact ⟨∅, by simp [payloadChunks, ErasureCode.encodeChunks], hCt0Pos⟩
    · simpa [ChunksA, world', Function.update, ht] using hInv.chunksA
  · simpa [ChunksB, hworldKp s.stB.t] using hInv.chunksB
  · intro t ht0 hlt
    simpa [hworldKey t] using hInv.pastComplete t ht0 hlt
  · intro t hlt
    simpa [hworldKp t] using hInv.futureKeypair t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [world', hne] using hInv.futureOff t hlt
  · intro t hlt
    simpa [hworldOn t] using hInv.futureOn t hlt
  · intro t; simpa [hworldKey t] using hInv.keyA t
  · intro t; simpa [hworldKey t] using hInv.keyB t
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
        exact ⟨pk, sk, i, by simpa [hworldKp t] using htr, hch⟩
  · intro n entry hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp [Function.update] at hn
      subst entry
      exact hhon
    · simp [Function.update, hnew] at hn
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
        · exact ⟨st', ct0', i, by simpa [world', ht] using htr, hch⟩
      · obtain ⟨ct1, key, i, htr, hch⟩ := hold
        exact ⟨ct1, key, i, by simpa [hworldOn t] using htr, hch⟩
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp [Function.update] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact HonestMessageB.epoch_le kem onoff ecCt0 ecCt1 world' msg s.stB.t
        hInv.epochPosB hhon
    · simp [Function.update, hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

private lemma reachableInv_after_sendB_newOn
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (pk : PK) (sk : SK) (st : onoff.St) (ct0 : onoff.C₀)
    (ct1 : onoff.C₁) (key : K)
    (hkp : (world s.stB.t).keypair = some (pk, sk))
    (hoff : (world s.stB.t).off = some (st, ct0))
    (hon : (world s.stB.t).on = none)
    (hek : s.stB.ekA = some pk) (hst : s.stB.stCt = some st)
    (hct0 : s.stB.ct0 = some ct0)
    (hmem : (ct1, key) ∈ support (onoff.encapsOn st pk)) :
    let tr' := (world s.stB.t).setOn ct1 key (by simp [hkp]) (by simp [hoff])
      (by
        intro pk' sk' st' ct0' hkp' hoff'
        have hp : pk' = pk := by
          exact congrArg Prod.fst (Option.some.inj (hkp'.symm.trans hkp))
        have hs : st' = st := by
          exact congrArg Prod.fst (Option.some.inj (hoff'.symm.trans hoff))
        subst pk'; subst st'
        exact hmem)
    let world' := Function.update world s.stB.t tr'
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
  -- support fact determines the ghost transcript installed at the current epoch.
  let tr' := (world s.stB.t).setOn ct1 key (by simp [hkp]) (by simp [hoff]) (by
    intro pk' sk' st' ct0' hkp' hoff'
    have hpairs := hkp'.symm.trans hkp
    have hoffs := hoff'.symm.trans hoff
    have hp : pk' = pk := congrArg Prod.fst (Option.some.inj hpairs)
    have hs : st' = st := congrArg Prod.fst (Option.some.inj hoffs)
    subst pk'; subst st'
    exact hmem)
  let world' := Function.update world s.stB.t tr'
  have hworldKp : ∀ t, (world' t).keypair = (world t).keypair := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [world', tr', EpochTranscript.setOn]
    · simp [world', ht]
  have hworldOff : ∀ t, (world' t).off = (world t).off := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [world', tr', EpochTranscript.setOn]
    · simp [world', ht]
  have hworldKeyOther : ∀ t, t ≠ s.stB.t → (world' t).key = (world t).key := by
    intro t ht
    simp [world', ht]
  have hkeyCurrent : (world' s.stB.t).key = some key := by
    simp [world', tr', EpochTranscript.setOn, EpochTranscript.key]
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
  refine ⟨world', ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurB, hkeyBOld, hkeyAOld, hknown]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact le_rfl
  · exact hInv.keypairAShape
  · exact hInv.offBShape
  · simpa [hworldKp s.stA.t] using hInv.keypairA
  · simpa [hworldOff s.stB.t] using hInv.offB
  · simp [world', tr', EpochTranscript.setOn]
  · intro pk' hpk'
    obtain ⟨sk', htr⟩ := hInv.decodedEk pk' hpk'
    exact ⟨sk', by simpa [hworldKp s.stB.t] using htr⟩
  · intro ct0' hct0'
    obtain ⟨st', htr⟩ := hInv.decodedCt0 ct0' hct0'
    exact ⟨st', by simpa [hworldOff s.stA.t] using htr⟩
  · cases hctA : s.stA.ct0 with
    | none => simpa [ChunksA, hctA, htEq, hworldOff s.stB.t] using hInv.chunksA
    | some ct0A =>
        have hlch : s.stA.lch = ∅ := by
          have hc : (∃ stA, (world s.stB.t).off = some (stA, ct0A)) ∧
              s.stA.lch = ∅ := by
            simpa [ChunksA, hctA, htEq, hon] using hInv.chunksA
          exact hc.2
        have hoffA := hInv.decodedCt0 ct0A hctA
        rw [htEq] at hoffA
        rcases hoffA with ⟨stA, hoffA⟩
        have hct : ct0A = ct0 := by
          exact congrArg Prod.snd (Option.some.inj (hoffA.symm.trans hoff))
        subst ct0A
        unfold ChunksA
        rw [hctA]
        constructor
        · exact ⟨st, by simpa [htEq, hworldOff s.stB.t] using hoff⟩
        · have hon' : (world' s.stA.t).on = some (ct1, key) := by
            simpa [htEq, world', tr', EpochTranscript.setOn]
          rw [hon']
          exact ⟨∅,
            by simpa [payloadChunks, ErasureCode.encodeChunks] using hlch, hCt1Pos⟩
  · simpa [ChunksB, hworldKp s.stB.t] using hInv.chunksB
  · intro t ht0 hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_lt (by simpa [htEq] using hlt)
    simpa [hworldKeyOther t hne] using hInv.pastComplete t ht0 hlt
  · intro t hlt
    simpa [hworldKp t] using hInv.futureKeypair t hlt
  · intro t hlt
    simpa [hworldOff t] using hInv.futureOff t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [world', hne] using hInv.futureOn t hlt
  · intro t
    by_cases ht0 : t = 0
    · simp [ht0, hInv.keyA]
    by_cases hlt : t < s.stA.t
    · have hne : t ≠ s.stB.t := by omega
      simpa [ht0, hlt, hworldKeyOther t hne] using hInv.keyA t
    · simpa [ht0, hlt] using hInv.keyA t
  · intro t
    by_cases ht : t = s.stB.t
    · subst t
      simp [Function.update, hkeyCurrent]
    · simp [Function.update, ht, hworldKeyOther t ht, hInv.keyB]
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
        exact ⟨pk', sk', i, by simpa [hworldKp t] using htr, hch⟩
  · intro n entry hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp [Function.update] at hn
      subst entry
      change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ ct1' key' i,
        (world' s.stB.t).on = some (ct1', key') ∧
          ecCt1.encode ct1 1 = ecCt1.encode ct1' i
      exact ⟨rfl, ct1, key, 1, by simp [world', tr', EpochTranscript.setOn], rfl⟩
    · simp [Function.update, hnew] at hn
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
        exact ⟨st', ct0', i, by simpa [hworldOff t] using htr, hch⟩
      · obtain ⟨ct1', key', i, htr, hch⟩ := hold
        by_cases ht : t = s.stB.t
        · subst t
          rw [hon] at htr
          contradiction
        · exact ⟨ct1', key', i, by simpa [world', ht] using htr, hch⟩
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp [Function.update] at hn
      obtain ⟨rfl, rfl⟩ := hn
      change s.stB.t ≤ s.stB.t
      exact le_rfl
    · simp [Function.update, hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

private lemma reachableInv_after_sendB_newOffOn
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (world : ℕ → EpochTranscript kem onoff)
    (hInv : WorldInv kem onoff ecEk ecCt0 ecCt1 world s)
    (pk : PK) (sk : SK) (st : onoff.St) (ct0 : onoff.C₀)
    (ct1 : onoff.C₁) (key : K)
    (hkp : (world s.stB.t).keypair = some (pk, sk))
    (hct0none : s.stB.ct0 = none)
    (hoffmem : (st, ct0) ∈ support onoff.encapsOff)
    (honmem : (ct1, key) ∈ support (onoff.encapsOn st pk)) :
    let old := world s.stB.t
    let offTr := old.setOff st ct0 hoffmem (by
      have hst : s.stB.stCt = none := by
        have hs := hInv.offBShape
        simp [hct0none] at hs
        exact hs
      have hoff : old.off = none := by
        simpa [old, hct0none, hst, optionPair] using hInv.offB
      by_contra hon
      simpa [hoff] using old.on_off (Option.isSome_iff_ne_none.mpr hon))
    let tr' := offTr.setOn ct1 key (by
      simp [offTr, old, EpochTranscript.setOff, hkp])
      (by simp [offTr, EpochTranscript.setOff]) (by
        intro pk' sk' st' ct0' hkp' hoff'
        have hp : pk' = pk := by
          have hpairs : some (pk', sk') = some (pk, sk) := by
            calc
              some (pk', sk') = old.keypair := by
                simpa [offTr, EpochTranscript.setOff] using hkp'.symm
              _ = some (pk, sk) := by simpa [old] using hkp
          exact congrArg Prod.fst (Option.some.inj hpairs)
        have hs : st' = st := by
          have hoffs : some (st', ct0') = some (st, ct0) := by
            simpa [offTr, EpochTranscript.setOff] using hoff'.symm
          exact congrArg Prod.fst (Option.some.inj hoffs)
        subst pk'; subst st'
        exact honmem)
    let world' := Function.update world s.stB.t tr'
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
    have hs := hInv.offBShape
    simp [hct0none] at hs
    exact hs
  have hoffnone : (world s.stB.t).off = none := by
    simpa [hct0none, hstnone, optionPair] using hInv.offB
  have honnone : (world s.stB.t).on = none := by
    by_contra hon
    simpa [hoffnone] using (world s.stB.t).on_off (Option.isSome_iff_ne_none.mpr hon)
  have htEq : s.stA.t = s.stB.t := by
    have hnlt : ¬ s.stB.t < s.stA.t := by
      intro hlt
      have hc := hInv.pastComplete s.stB.t hInv.epochPosB hlt
      simp [EpochTranscript.key, honnone] at hc
    exact Nat.le_antisymm (Nat.le_of_not_gt hnlt) hInv.epochs.1
  let offTr := (world s.stB.t).setOff st ct0 hoffmem honnone
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
  let world' := Function.update world s.stB.t tr'
  have hworldKp : ∀ t, (world' t).keypair = (world t).keypair := by
    intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [world', tr', offTr, EpochTranscript.setOn, EpochTranscript.setOff]
    · simp [world', ht]
  have hworldKeyOther : ∀ t, t ≠ s.stB.t → (world' t).key = (world t).key := by
    intro t ht; simp [world', ht]
  have hkeyCurrent : (world' s.stB.t).key = some key := by
    simp [world', tr', EpochTranscript.setOn, EpochTranscript.key]
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
  refine ⟨world', ?_⟩
  constructor
  · simp [hInv.correct, hInv.tcurB, hkeyBOld, hkeyAOld, hknown]
  · exact hInv.epochs
  · exact hInv.epochPosA
  · exact hInv.epochPosB
  · exact hInv.tcurA
  · exact le_rfl
  · exact hInv.keypairAShape
  · simp
  · simpa [hworldKp s.stA.t] using hInv.keypairA
  · simp [world', tr', offTr, EpochTranscript.setOn, EpochTranscript.setOff, optionPair]
  · simp [world', tr', EpochTranscript.setOn]
  · intro pk' hpk'
    obtain ⟨sk', htr⟩ := hInv.decodedEk pk' hpk'
    exact ⟨sk', by simpa [hworldKp s.stB.t] using htr⟩
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
          simpa [ChunksA, hctA, htEq, hoffnone] using hInv.chunksA
        simp [ChunksA, hctA, htEq, world', tr', offTr, EpochTranscript.setOn,
          EpochTranscript.setOff, hlch]
        exact ⟨∅, by simp [payloadChunks, ErasureCode.encodeChunks], hCt0Pos⟩
  · simpa [ChunksB, hworldKp s.stB.t] using hInv.chunksB
  · intro t ht0 hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_lt (by simpa [htEq] using hlt)
    simpa [hworldKeyOther t hne] using hInv.pastComplete t ht0 hlt
  · intro t hlt; simpa [hworldKp t] using hInv.futureKeypair t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [world', hne] using hInv.futureOff t hlt
  · intro t hlt
    have hne : t ≠ s.stB.t := Nat.ne_of_gt hlt
    simpa [world', hne] using hInv.futureOn t hlt
  · intro t
    by_cases ht0 : t = 0
    · simp [ht0, hInv.keyA]
    by_cases hlt : t < s.stA.t
    · have hne : t ≠ s.stB.t := by omega
      simpa [ht0, hlt, hworldKeyOther t hne] using hInv.keyA t
    · simpa [ht0, hlt] using hInv.keyA t
  · intro t
    by_cases ht : t = s.stB.t
    · subst t; simp [Function.update, hkeyCurrent]
    · simp [Function.update, ht, hworldKeyOther t ht, hInv.keyB]
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
        exact ⟨pk', sk', i, by simpa [hworldKp t] using htr, hch⟩
  · intro n entry hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp [Function.update] at hn
      subst entry
      change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ ct1' key' i,
        (world' s.stB.t).on = some (ct1', key') ∧
          ecCt1.encode ct1 1 = ecCt1.encode ct1' i
      exact ⟨rfl, ct1, key, 1, by simp [world', tr', EpochTranscript.setOn], rfl⟩
    · simp [Function.update, hnew] at hn
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
        · exact ⟨st', ct0', i, by simpa [world', ht] using htr, hch⟩
      · obtain ⟨ct1', key', i, htr, hch⟩ := hold
        by_cases ht : t = s.stB.t
        · subst t; rw [honnone] at htr; contradiction
        · exact ⟨ct1', key', i, by simpa [world', ht] using htr, hch⟩
  · exact hInv.msgAEpoch
  · intro n ρ tsnd hn
    by_cases hnew : n = s.nB + 1
    · subst n
      simp [Function.update] at hn
      obtain ⟨rfl, rfl⟩ := hn
      change s.stB.t ≤ s.stB.t
      exact le_rfl
    · simp [Function.update, hnew] at hn
      exact hInv.msgBEpoch n ρ tsnd hn

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
  rcases hs with ⟨world, hInv⟩
  cases hct0 : s.stB.ct0 with
  | some ct0 =>
      have hstSome : s.stB.stCt.isSome := by simpa [hct0] using hInv.offBShape
      obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hstSome
      have hoff : (world s.stB.t).off = some (st, ct0) := by
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
                correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) }) := by
          rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
          simpa [scheme, sendB, hct0, hackFalse, ich, msg] using hz
        subst z
        apply reachableInv_after_sendB_same kem onoff ecEk ecCt0 ecCt1
          s world hInv ich msg
        change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ st' ct0' i,
          (world s.stB.t).off = some (st', ct0') ∧
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
                    correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) }) := by
              rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
              simpa [scheme, sendB, hct0, hackTrue, hek, msg] using hz
            subst z
            apply reachableInv_after_sendB_same kem onoff ecEk ecCt0 ecCt1
              s world hInv s.stB.ich msg
            simp [msg, HonestMessageB]
        | some pk =>
            have hkp := hInv.decodedEk pk hek
            obtain ⟨sk, hkp⟩ := hkp
            cases hct1 : s.stB.ct1 with
            | some ct1 =>
                have honSome : (world s.stB.t).on.isSome := by
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
                        correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) }) := by
                  rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
                  simpa [scheme, sendB, hct0, hackTrue, hek, hct1, msg, ich] using hz
                subst z
                apply reachableInv_after_sendB_same kem onoff ecEk ecCt0 ecCt1
                  s world hInv ich msg
                change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ ct1' key' i,
                  (world s.stB.t).on = some (ct1', key') ∧
                    ecCt1.encode ct1 ich = ecCt1.encode ct1' i
                exact ⟨rfl, ct1, key, ich, hon, rfl⟩
            | none =>
                have hon : (world s.stB.t).on = none := by
                  cases h : (world s.stB.t).on with
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
                            t = 0 || (Function.update s.keyB s.stB.t (some key) t).isSome) }) = z := by
                  rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
                  simpa [scheme, sendB, hct0, hackTrue, hek, hct1, hst] using hz
                obtain ⟨ct1, key, hmem, rfl⟩ := hz'
                exact reachableInv_after_sendB_newOn kem onoff ecEk ecCt0 ecCt1 hCt1Pos
                  s world hInv pk sk st ct0 ct1 key hkp hoff hon hek hst hct0 hmem
  | none =>
      have hstnone : s.stB.stCt = none := by
        have hs := hInv.offBShape
        simp [hct0] at hs
        exact hs
      have hoffnone : (world s.stB.t).off = none := by
        simpa [hct0, hstnone, optionPair] using hInv.offB
      have honnone : (world s.stB.t).on = none := by
        by_contra hn
        simpa [hoffnone] using (world s.stB.t).on_off
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
                correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) }) = z := by
          rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
          simpa [scheme, sendB, hct0, hackFalse] using hz
        obtain ⟨st, ct0, hmem, rfl⟩ := hz'
        let old := world s.stB.t
        let tr' := old.setOff st ct0 hmem honnone
        let world' := Function.update world s.stB.t tr'
        apply reachableInv_after_sendB_newOff kem onoff ecEk ecCt0 hCt0Pos ecCt1
          s world hInv st ct0 hmem hct0 1
          (some (ecCt0.encode ct0 1), s.stB.ack, s.stB.t, some 0)
        change s.stB.t - 1 = s.stB.t - 1 ∧ ∃ st' ct0' i,
          (world' s.stB.t).off = some (st', ct0') ∧
            ecCt0.encode ct0 1 = ecCt0.encode ct0' i
        exact ⟨rfl, st, ct0, 1,
          by simp [world', tr', EpochTranscript.setOff], rfl⟩
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
                    correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) }) = z := by
              rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
              simpa [scheme, sendB, hct0, hackTrue, hek] using hz
            obtain ⟨st, ct0, hmem, rfl⟩ := hz'
            apply reachableInv_after_sendB_newOff kem onoff ecEk ecCt0 hCt0Pos ecCt1
              s world hInv st ct0 hmem hct0 s.stB.ich
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
              ecCt1 s world hInv pk sk st ct0 ct1 key hkp hct0 hoffmem honmem

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

private def recvAAckStep
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) : StA onoff Sym :=
  if ack.ekRec && stA.t == t then
    { stA with ack := { stA.ack with ekRec := true } }
  else stA

@[simp] private lemma recvAAckStep_t
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).t = stA.t := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

@[simp] private lemma recvAAckStep_dkA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).dkA = stA.dkA := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

@[simp] private lemma recvAAckStep_ekA
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).ekA = stA.ekA := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

@[simp] private lemma recvAAckStep_ct0
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).ct0 = stA.ct0 := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

@[simp] private lemma recvAAckStep_lch
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (stA : StA onoff Sym) (ack : Ack) (t : ℕ) :
    (recvAAckStep kem onoff stA ack t).lch = stA.lch := by
  by_cases h : ack.ekRec && stA.t == t <;> simp [recvAAckStep, h]

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
    · simpa [hkey]
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
                    · simp [stA', stA0, ChunksA, hoff, hct0, hch, hlch, hdec]
                      exact ⟨insert (counterIndex ecCt0 i) I,
                        insert_payloadChunks ecCt0 ct0 I i, hcard'⟩
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
                          simp [stA', stA0, ChunksA, hoff, hon]
                          exact ⟨∅,
                            by simp [payloadChunks, ErasureCode.encodeChunks], hCt1Pos⟩
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
                    · simp [stA', stA0, ChunksA, hct0, hoff, hon, hch, hlch, hdec]
                      exact ⟨insert (counterIndex ecCt1 i) I,
                        insert_payloadChunks ecCt1 ct1 I i, hcard'⟩
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

private lemma oracleRecvA_preserves_reachableInv
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

private lemma correctnessImpl_preserves
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro t s hs z hz
  match t with
  | OUnif n =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleUnif_preserves_reachableInv kem onoff ecEk ecCt0 ecCt1 n s hs z hz
  | OSendA =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1
          leak hEkPos () s hs z hz
  | OSendB =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0Pos
          ecCt1 hCt1Pos leak () s hs z hz
  | ORecvA n =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleRecvA_preserves_reachableInv kem onoff hDet hkem ecEk ecCt0
          hCt0Correct ecCt1 hCt1Correct hCt1Pos leak n s hs z hz
  | ORecvB n =>
      simpa [SCKAScheme.sckaCorrectnessImpl] using
        oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEkCorrect hEkPos
          ecCt0 ecCt1 leak n s hs z hz

/-- Perfect correctness of Opp-UniKEM-CKA in the full SCKA correctness game.

The adversary may delay, reorder, duplicate, and replay honest protocol
messages.  Perfect KEM correctness, deterministic decapsulation, and the
three erasure-code correctness assumptions suffice to make every game
assertion hold on every supported execution. -/
-- ANCHOR: correctness
theorem correctness [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEkCorrect : ecEk.ec.Correct) (hCt0Correct : ecCt0.ec.Correct)
    (hCt1Correct : ecCt1.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] = 1
-- ANCHOR_END: correctness
    := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  refine ⟨probFailure_eq_zero, ?_⟩
  intro b hb
  unfold SCKAScheme.correctnessExp at hb
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨ik, hik, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stA, hstA, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stB, hstB, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨out, hout, hb⟩
  have hik' : ik = () := by simpa [scheme, initKeyGen, mem_support_pure_iff] using hik
  subst ik
  have hstA' : stA =
      ({ dkA := none
         ekA := none
         ct0 := none
         t := 1
         ich := 0
         lch := ∅
         ack := { ekRec := false, ctRec := false } } : StA onoff Sym) := by
    simpa [scheme, initA, mem_support_pure_iff] using hstA
  subst stA
  have hstB' : stB =
      ({ ekA := none
         ct0 := none
         ct1 := none
         stCt := none
         t := 1
         ich := 0
         lch := ∅
         ack := { ekRec := false, ctRec := false } } : StB onoff Sym) := by
    simpa [scheme, initB, mem_support_pure_iff] using hstB
  subst stB
  have hInv : reachableInv kem onoff ecEk ecCt0 ecCt1 out.2 := by
    exact OracleComp.simulateQ_run_preservesInv
      (impl := SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (Inv := reachableInv kem onoff ecEk ecCt0 ecCt1)
      (correctnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
        ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak hkem)
      adv
      (SCKAScheme.initGameState
        ({ dkA := none
           ekA := none
           ct0 := none
           t := 1
           ich := 0
           lch := ∅
           ack := { ekRec := false, ctRec := false } } : StA onoff Sym)
        ({ ekA := none
           ct0 := none
           ct1 := none
           stCt := none
           t := 1
           ich := 0
           lch := ∅
           ack := { ekRec := false, ctRec := false } } : StB onoff Sym))
      (reachableInv_init kem onoff ecEk ecCt0 ecCt1 hEkPos hCt0Pos)
      out hout
  have hb' : b = out.2.correct := by simpa [mem_support_pure_iff] using hb
  rcases hInv with ⟨_world, hWorld⟩
  exact hb'.trans hWorld.correct

end Invariant

end oppUniKemCKA
