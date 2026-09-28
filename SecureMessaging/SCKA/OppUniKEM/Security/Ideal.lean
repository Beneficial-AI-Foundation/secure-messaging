/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Core

/-!
# Receive using the encapsulated key

**Construction.** For `key : Option K`, `keyDecapsKEM kem key` retains the
original samplers and returns `key` on every decapsulation. In a game state
`s`, `oracleRecvAIdeal` uses this KEM with `key = s.keyB s.stA.t`, B's recorded
key for A's current epoch. The existing receive algorithm handles decoding,
acknowledgements, and erasure.

**Result.** With correct ciphertext erasure codes, for every state `s`
satisfying `reachableInv`, message index `n`, and supported successor `s'`
of the auxiliary receive, `reachableInv s'` holds.

**Proof.** The unchanged samplers transport the on/off witness, leakage
marginals, and correctness transcript to constant decapsulation. Its chosen
result agrees with B's recorded key. `IdealReceive` compares this operation
with real decapsulation; `IdealGame` supplies the other security oracles.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}

/-- Auxiliary KEM with the original key generation and encapsulation but
constant decapsulation result `key`, used by the auxiliary receive algorithm. -/
abbrev keyDecapsKEM (kem : KEMScheme ProbComp K PK SK C) (key : Option K) :
    KEMScheme ProbComp K PK SK C :=
  { kem with decaps := fun _ _ => pure key }

/-- Constant decapsulation is deterministic, with result `key` on every
secret key and ciphertext. -/
abbrev keyDecapsDet (kem : KEMScheme ProbComp K PK SK C) (key : Option K) :
    (keyDecapsKEM kem key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- Changing decapsulation leaves the original on/off encapsulation
factorization and its ciphertext and offline-state spaces unchanged. -/
abbrev keyDecapsOnOff (kem : KEMScheme ProbComp K PK SK C)
    (onoff : kem.OnOffStructure) (key : Option K) :
    (keyDecapsKEM kem key).OnOffStructure where
  St := onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := onoff.encapsOff
  encapsOn := onoff.encapsOn
  factor := onoff.factor

/-- The original leakage witness also witnesses the unchanged samplers
of the constant-decapsulation auxiliary KEM. -/
abbrev keyDecapsLeak (kem : KEMScheme ProbComp K PK SK C)
    (onoff : kem.OnOffStructure) (leak : kem.OnOffRandLeak onoff) (key : Option K) :
    (keyDecapsKEM kem key).OnOffRandLeak (keyDecapsOnOff kem onoff key) where
  KeygenRand := leak.KeygenRand
  OffRand := leak.OffRand
  OnRand := leak.OnRand
  keygenRleak := leak.keygenRleak
  encapsOffRleak := leak.encapsOffRleak
  encapsOnRleak := leak.encapsOnRleak
  keygen_fst := leak.keygen_fst
  encapsOff_fst := leak.encapsOff_fst
  encapsOn_fst := leak.encapsOn_fst

/-- Reinterpret one honest epoch transcript under constant decapsulation.
Every sampled value and support witness is unchanged. -/
def EpochTranscript.toKeyDecaps
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (T : oppUniKemCKA.EpochTranscript kem onoff) (key : Option K) :
    oppUniKemCKA.EpochTranscript (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key) where
  keypair := T.keypair
  off := T.off
  on := T.on
  keypair_mem := T.keypair_mem
  off_mem := T.off_mem
  on_mem := T.on_mem
  on_keypair := T.on_keypair
  on_off := T.on_off

/-- Reinterpret an auxiliary epoch transcript as an original transcript.
Each transcript entry retains its key-generation and encapsulation samples. -/
def EpochTranscript.ofKeyDecaps
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure} {key : Option K}
    (T : oppUniKemCKA.EpochTranscript (keyDecapsKEM kem key)
      (keyDecapsOnOff kem onoff key)) : oppUniKemCKA.EpochTranscript kem onoff where
  keypair := T.keypair
  off := T.off
  on := T.on
  keypair_mem := T.keypair_mem
  off_mem := T.off_mem
  on_mem := T.on_mem
  on_keypair := T.on_keypair
  on_off := T.on_off

/-- Transcript consistency is unaffected by replacing decapsulation,
because it constrains the sampled KEM material, keys, chunks, and messages. -/
theorem transcriptConsistent_toKeyDecaps
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {ecEk : ErasureCodePayload PK Sym}
    {ecCt0 : ErasureCodePayload onoff.C₀ Sym}
    {ecCt1 : ErasureCodePayload onoff.C₁ Sym}
    {T : Transcript kem onoff}
    {s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)}
    (h : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s) (key : Option K) :
    TranscriptConsistent (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key)
      ecEk ecCt0 ecCt1 (fun t => EpochTranscript.toKeyDecaps (T t) key) s := by
  have hchunks := h.chunksA
  cases h
  constructor <;> try assumption
  cases hct : s.stA.ct0 <;> cases hoff : (T s.stA.t).off <;> cases hon : (T s.stA.t).on <;>
    simpa only [ChunksAConsistent, EpochTranscript.toKeyDecaps, keyDecapsOnOff,
      hct, hoff, hon] using hchunks

/-- Auxiliary transcript consistency implies original transcript
consistency when all samplers are retained and only decapsulation changes. -/
theorem transcriptConsistent_ofKeyDecaps
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure} {key : Option K}
    {ecEk : ErasureCodePayload PK Sym}
    {ecCt0 : ErasureCodePayload onoff.C₀ Sym}
    {ecCt1 : ErasureCodePayload onoff.C₁ Sym}
    {T : Transcript (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key)}
    {s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)}
    (h : TranscriptConsistent (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key)
      ecEk ecCt0 ecCt1 T s) :
    TranscriptConsistent kem onoff ecEk ecCt0 ecCt1
      (fun t => EpochTranscript.ofKeyDecaps (T t)) s := by
  have hchunks := h.chunksA
  cases h
  constructor <;> try assumption
  cases hct : s.stA.ct0 <;> cases hoff : (T s.stA.t).off <;> cases hon : (T s.stA.t).on <;>
    simpa only [ChunksAConsistent, EpochTranscript.ofKeyDecaps, keyDecapsOnOff,
      hct, hoff, hon] using hchunks

/-- On completion of an online ciphertext, auxiliary A records B's
encapsulated key for A's current epoch. All chunk processing and erasure
are performed by the existing receive algorithm. -/
-- ANCHOR: oracleRecvAIdeal
def oracleRecvAIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  fun n s =>
    let key := s.keyB s.stA.t
    (SCKAScheme.oracleRecvA (scheme (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key)
      (keyDecapsDet kem key) ecEk ecCt0 ecCt1 (keyDecapsLeak kem onoff leak key)) n).run s
-- ANCHOR_END: oracleRecvAIdeal

/-- For every transcript-consistent state and delivered index, auxiliary
receive preserves transcript consistency when the ciphertext erasure codes
are correct. Its decapsulation result is B's recorded encapsulated key. -/
theorem oracleRecvAIdeal_preserves_reachableInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (oracleRecvAIdeal kem onoff ecEk ecCt0 ecCt1 leak)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro n s hs z hz
  let key := s.keyB s.stA.t
  have hs' : reachableInv (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key)
      ecEk ecCt0 ecCt1 s := by
    obtain ⟨T, hT⟩ := hs
    exact ⟨_, transcriptConsistent_toKeyDecaps hT key⟩
  have hc : CurrentKEMCorrect (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key)
      (keyDecapsDet kem key) s := by
    intro dk ct0 ct1 k _ _ _ hk
    exact hk
  obtain ⟨T, hT⟩ := oracleRecvA_preserves_reachableInv (keyDecapsKEM kem key)
    (keyDecapsOnOff kem onoff key) (keyDecapsDet kem key) ecEk ecCt0 hCt0
    ecCt1 hCt1 ecCt1.ec.nchunk_pos (keyDecapsLeak kem onoff leak key)
    n s hs' hc z hz
  exact ⟨_, transcriptConsistent_ofKeyDecaps hT⟩

end oppUniKemCKA.Security
