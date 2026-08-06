/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.ErasureCode
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Opp-UniKEM-CKA — Game Invariant

Each epoch of the SCKA correctness game of
`Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` runs one KEM instance:
A samples `(pk, sk) ← kem.keygen`; B samples `(st, ct₀) ← onoff.encapsOff`
and, once it has decoded `pk`, `(ct₁, k) ← onoff.encapsOn st pk`.

* `EpochTranscript` — the samples an epoch has drawn, each with a proof of
  membership in the support of its sampler.
* `WorldInv T s` — the game state `s` is consistent with the transcript
  `T : ℕ → EpochTranscript` and `s.correct = true`; the clauses are
  documented on the fields.  `reachableInv s := ∃ T, WorldInv T s`.
* `CurrentKEMCorrect s` — A's current KEM material and B's recorded key
  decapsulate consistently: the one KEM fact the `RecvA` proof needs.  For
  a perfectly correct KEM it holds in every reachable state
  (`currentKEMCorrect_of_perfect`), because every sample lies in the
  support of its honest sampler.

`reachableInv` holds initially (`reachableInv_init`) and is preserved by
the uniform oracle (`oracleUnif_preserves_reachableInv`); the send and
receive oracles are handled in the sibling modules.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {m : Type → Type u} {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec

/-- Bridge lemma: deterministic KEM decapsulation is correct when both
`(pk, sk)` and `(c, key)` are in the support of the corresponding samplers. -/
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

/-- Bridge lemma: honest offline and online OnOff samples reassemble to a
sample of ordinary KEM encapsulation. -/
private lemma mem_support_encaps_of_onoff
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    {pk : PK} {st : onoff.St} {ct0 : onoff.C₀} {ct1 : onoff.C₁} {key : K}
    (hoff : (st, ct0) ∈ support onoff.encapsOff)
    (hon : (ct1, key) ∈ support (onoff.encapsOn st pk)) :
    (onoff.split.symm (ct0, ct1), key) ∈ support (kem.encaps pk) := by
  rw [onoff.factor pk, mem_support_bind_iff]
  exact ⟨(st, ct0), hoff, by simpa [mem_support_pure_iff] using hon⟩

open oppUniKemCKA.Perfect.Internal

section Invariant

variable [DecidableEq Sym]

/-- The samples drawn so far for one protocol epoch: A's key pair, B's
offline encapsulation part, and B's online encapsulation part, each with a
proof of membership in the support of its sampler.  The online part
presupposes the other two. -/
structure EpochTranscript
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) where
  /-- The honest public/secret key pair sampled for this epoch, when present. -/
  keypair : Option (PK × SK)
  /-- The honest offline state and ciphertext sampled for this epoch, when present. -/
  off : Option (onoff.St × onoff.C₀)
  /-- The honest online ciphertext and shared key sampled for this epoch, when present. -/
  on : Option (onoff.C₁ × K)
  /-- Proof that each sampled key pair lies in the support of key generation. -/
  keypair_mem : ∀ pk sk, keypair = some (pk, sk) → (pk, sk) ∈ support kem.keygen
  /-- Proof that each sampled offline part lies in the support of offline encapsulation. -/
  off_mem : ∀ st ct0, off = some (st, ct0) → (st, ct0) ∈ support onoff.encapsOff
  /-- Proof that each sampled online part lies in the support of online encapsulation. -/
  on_mem : ∀ pk sk st ct0 ct1 key,
    keypair = some (pk, sk) → off = some (st, ct0) → on = some (ct1, key) →
      (ct1, key) ∈ support (onoff.encapsOn st pk)
  /-- The online part requires a key pair. -/
  on_keypair : on.isSome → keypair.isSome
  /-- The online part requires the offline part. -/
  on_off : on.isSome → off.isSome

/-- Empty epoch transcript with no samples drawn. -/
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

/-- Update a transcript by installing a key pair, provided the online stage
has not yet begun. -/
def EpochTranscript.setKeypair
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (tr : EpochTranscript kem onoff) (pk : PK) (sk : SK)
    (hmem : (pk, sk) ∈ support kem.keygen) (hon : tr.on = none) :
    EpochTranscript kem onoff where
  keypair := some (pk, sk)
  off := tr.off
  on := tr.on
  keypair_mem := by simp [hmem]
  off_mem := tr.off_mem
  on_mem := by simp [hon]
  on_keypair := by simp [hon]
  on_off := tr.on_off

/-- Update a transcript by installing the offline encapsulation, provided the
online stage has not yet begun. -/
def EpochTranscript.setOff
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (tr : EpochTranscript kem onoff) (st : onoff.St) (ct0 : onoff.C₀)
    (hmem : (st, ct0) ∈ support onoff.encapsOff) (hon : tr.on = none) :
    EpochTranscript kem onoff where
  keypair := tr.keypair
  off := some (st, ct0)
  on := tr.on
  keypair_mem := tr.keypair_mem
  off_mem := by simp [hmem]
  on_mem := by simp [hon]
  on_keypair := tr.on_keypair
  on_off := by simp [hon]

/-- Complete a transcript by installing the online encapsulation, provided both
the key pair and offline part are present. -/
def EpochTranscript.setOn
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
@[simp] def optionPair {A B : Type} : Option A → Option B → Option (A × B)
  | some a, some b => some (a, b)
  | _, _ => none

/-- Internal helper: an A-to-B message is honest when its chunk and receiving
epoch fields are drawn from the recorded epoch transcript. -/
def HonestMessageA
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

omit [DecidableEq Sym] in
/-- Internal helper: an honest message's sending epoch is at most the
current epoch. -/
lemma HonestMessageB.epoch_le {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure}
    {ecCt0 : ErasureCodePayload onoff.C₀ Sym}
    {ecCt1 : ErasureCodePayload onoff.C₁ Sym}
    {world : ℕ → EpochTranscript kem onoff} {msg : Message Sym} {tcur : ℕ}
    (hpos : 0 < tcur)
    (hmsg : HonestMessageB kem onoff ecCt0 ecCt1 world (msg, tcur - 1)) :
    msg.2.2.1 ≤ tcur := by
  rcases msg with ⟨ch?, ack, t, b?⟩
  simp only [HonestMessageB] at hmsg
  change t ≤ tcur
  omega

/-- Internal helper: B's chunk buffer is an honest chunk set of the public
key in transit. -/
def ChunksB
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

/-- Internal helper: A's chunk buffer is an honest chunk set of the
ciphertext in transit. -/
def ChunksA
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

/-- The game state `s` is the honest protocol state determined by the
transcript `world`: epochs, key material, chunk buffers, message histories,
and key tables are those of `world`, and the correctness flag is set. -/
structure WorldInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (world : ℕ → EpochTranscript kem onoff)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop where
  /-- The correctness flag is set. -/
  correct : s.correct = true
  /-- Epochs are monotone and differ by at most one. -/
  epochs : s.stB.t ≤ s.stA.t ∧ s.stA.t ≤ s.stB.t + 1
  /-- A's epoch is positive. -/
  epochPosA : 0 < s.stA.t
  /-- B's epoch is positive. -/
  epochPosB : 0 < s.stB.t
  /-- A's current receiving epoch is at most the last completed epoch. -/
  tcurA : s.tcurA ≤ s.stA.t - 1
  /-- B's current receiving epoch is at most the last completed epoch. -/
  tcurB : s.tcurB ≤ s.stB.t - 1
  /-- A's key-pair components are synchronized. -/
  keypairAShape : s.stA.ekA.isSome = s.stA.dkA.isSome
  /-- B's offline components are synchronized. -/
  offBShape : s.stB.stCt.isSome = s.stB.ct0.isSome
  /-- A's key pair matches the transcript. -/
  keypairA : (world s.stA.t).keypair = optionPair s.stA.ekA s.stA.dkA
  /-- B's offline part matches the transcript. -/
  offB : (world s.stB.t).off = optionPair s.stB.stCt s.stB.ct0
  /-- B's online ciphertext matches the transcript. -/
  onB : (world s.stB.t).on.map Prod.fst = s.stB.ct1
  /-- B's decoded public key comes from the transcript. -/
  decodedEk : ∀ pk, s.stB.ekA = some pk → ∃ sk, (world s.stB.t).keypair = some (pk, sk)
  /-- A's decoded offline ciphertext comes from the transcript. -/
  decodedCt0 : ∀ ct0, s.stA.ct0 = some ct0 → ∃ st, (world s.stA.t).off = some (st, ct0)
  /-- A's chunk buffer is an honest chunk set. -/
  chunksA : ChunksA kem onoff ecCt0 ecCt1 world s.stA
  /-- B's chunk buffer is an honest chunk set. -/
  chunksB : ChunksB kem onoff ecEk world s.stB
  /-- Past epochs have completed their online stage. -/
  pastComplete : ∀ t, 0 < t → t < s.stA.t → (world t).key.isSome
  /-- Future epochs have no key pair. -/
  futureKeypair : ∀ t, s.stA.t < t → (world t).keypair = none
  /-- Future epochs (for B) have no offline part. -/
  futureOff : ∀ t, s.stB.t < t → (world t).off = none
  /-- Future epochs (for B) have no online part. -/
  futureOn : ∀ t, s.stB.t < t → (world t).on = none
  /-- A's key table matches the transcript. -/
  keyA : ∀ t, s.keyA t = if t = 0 then none else if t < s.stA.t then (world t).key else none
  /-- B's key table matches the transcript. -/
  keyB : ∀ t, s.keyB t = (world t).key
  /-- All A-to-B messages are honest. -/
  msgA : ∀ n entry, s.msgA n = some entry → HonestMessageA kem onoff ecEk world entry
  /-- All B-to-A messages are honest. -/
  msgB : ∀ n entry, s.msgB n = some entry → HonestMessageB kem onoff ecCt0 ecCt1 world entry
  /-- A-to-B message sending epochs are at most A's current epoch. -/
  msgAEpoch : ∀ n ρ tsnd, s.msgA n = some (ρ, tsnd) → ρ.2.2.1 ≤ s.stA.t
  /-- B-to-A message sending epochs are at most B's current epoch. -/
  msgBEpoch : ∀ n ρ tsnd, s.msgB n = some (ρ, tsnd) → ρ.2.2.1 ≤ s.stB.t

/-- The game state admits a transcript of honest epoch samples satisfying
`WorldInv`. -/
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

/-- Internal: the reachable invariant implies KEM material decapsulates
correctly for a perfect KEM. -/
lemma currentKEMCorrect_of_perfect [DecidableEq K]
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
    | some _pair => simp
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

/-- The initial game state admits a trivial transcript with empty epochs. -/
lemma reachableInv_init
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (_hEkPos : 0 < ecEk.ec.nchunk) (_hCt0Pos : 0 < ecCt0.ec.nchunk) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      (SCKAScheme.initGameState
        { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
          ack := { ekRec := false, ctRec := false } }
        { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0,
          lch := ∅, ack := { ekRec := false, ctRec := false } }) := by
  let world : ℕ → EpochTranscript kem onoff := fun _ => .empty kem onoff
  refine ⟨world, ?_⟩
  (constructor <;> simp [world, EpochTranscript.empty, EpochTranscript.key,
    ChunksA, ChunksB, SCKAScheme.initGameState]; omega)

/-- The uniform oracle preserves the reachable invariant. -/
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

end Invariant

end oppUniKemCKA
