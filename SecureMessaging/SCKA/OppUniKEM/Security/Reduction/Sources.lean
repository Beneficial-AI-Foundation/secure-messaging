/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Receive
import SecureMessaging.SCKA.Security

/-!
# The stored source material

**Definition.** For material `m` and an epoch `e`, `pinnedSources m e s` states that A's key
pair, when present while A is in epoch `e`, is `m.keygen.1`, and that B's offline state and
offline ciphertext, when B holds an offline state while in epoch `e`, are `m.off.1`.

**Results.**

- `honestCorrectness_preserves_pinnedSources`: the correctness oracles of `honestScheme m e`
  preserve `pinnedSources m e`.
- `oracleSendA_pinned_support`, `oracleSendB_pinned_support`: let
  `m ∈ support (sampleMaterial leak)`. For every state `s`, satisfying `reachableInv` and
  `pinnedSources m e` in B's case, every possible response/state pair of a send oracle of
  `honestScheme m e s` from `s` is a possible response/state pair of the same send oracle of
  Opp-UniKEM over `base` from `s`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Predicate on game states: if A is in epoch `e` and holds a decapsulation key, then A's
key pair `(ekA, dkA)` is `m.keygen.1`; if B is in epoch `e` and holds an offline state, then
B's offline state and offline ciphertext `(stCt, ct0)` are `m.off.1`. -/
def pinnedSources {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  (s.stA.t = e → s.stA.dkA.isSome →
    s.stA.ekA = some m.keygen.1.1 ∧ s.stA.dkA = some m.keygen.1.2) ∧
  (s.stB.t = e → s.stB.stCt.isSome →
    s.stB.stCt = some m.off.1.1 ∧ s.stB.ct0 = some m.off.1.2)

/-- In every state satisfying `reachableInv`, if B holds no online ciphertext, then A and B
are in the same epoch. -/
theorem epochs_eq_before_online
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hc : s.stB.ct1 = none) :
    s.stA.t = s.stB.t := by
  obtain ⟨T, hT⟩ := hs
  have hon : (T s.stB.t).on = none := by
    have h := hT.onB
    rw [hc] at h
    simpa using h
  have hn : ¬s.stB.t < s.stA.t := by
    intro hlt
    have h := hT.pastComplete s.stB.t hT.epochPosB hlt
    simp [EpochTranscript.key, hon] at h
  have := hT.epochs
  omega

/-- In every state satisfying `reachableInv` and `pinnedSources m e`, if B is in epoch `e`,
holds the public key `pk` and the offline state `st`, and holds no online ciphertext, then
`pk = m.keygen.1.1` and `st = m.off.1.1`. -/
theorem pinned_online_inputs
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hm : pinnedSources m e s)
    (he : s.stB.t = e) (pk : PK) (st : onoff.St)
    (hp : s.stB.ekA = some pk) (hst : s.stB.stCt = some st) (hc : s.stB.ct1 = none) :
    pk = m.keygen.1.1 ∧ st = m.off.1.1 := by
  have ht := epochs_eq_before_online base onoff ecEk ecCt0 ecCt1 s hs hc
  obtain ⟨T, hT⟩ := hs
  obtain ⟨sk, hpk⟩ := hT.decodedEk pk hp
  have hpair := hT.keypairA
  rw [ht, hpk] at hpair
  have ha : s.stA.ekA = some pk ∧ s.stA.dkA = some sk := by
    cases hpA : s.stA.ekA <;> cases hsA : s.stA.dkA <;>
      simp_all [Option.map₂]
  have hsrcA := hm.1 (ht.trans he) (by simp [ha.2])
  have hsrcB := hm.2 he (by simp [hst])
  exact ⟨Option.some.inj (ha.1.symm.trans hsrcA.1),
    Option.some.inj (hst.symm.trans hsrcB.1)⟩

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Let `s` satisfy `pinnedSources m e`. For every possible successful output of A's send in
`honestScheme m e s` from `s.stA`, with successor local state `next`, the state
`{ s with stA := next }` satisfies `pinnedSources m e`. -/
theorem sendA_preserves_pinnedSources
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StA onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendA (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
              (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        ecEk s.stA)) :
    pinnedSources m e { s with stA := next } := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [sendA, hd, hp, ha, Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    try dsimp only [Pinned.kem, Pinned.onOff] at hout
    simp only [Pinned.keygen, he, decide_true, decide_false, ↓reduceIte, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [pinnedSources] <;> aesop

/-- The version of `sendA_preserves_pinnedSources` for B. -/
theorem sendB_preserves_pinnedSources
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StB onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendB (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
              (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB)) :
    pinnedSources m e { s with stB := next } := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    try dsimp only [Pinned.kem, Pinned.onOff] at hout
    simp only [Pinned.encapsOff, Pinned.encapsOn, he, decide_true, decide_false,
      ↓reduceIte, pure_bind, mem_support_bind_iff, mem_support_pure_iff,
      Prod.exists, Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [pinnedSources] <;> aesop

/-- Let `s` satisfy `pinnedSources m e`. If B's receive of `msg` from `s.stB` succeeds with
successor local state `next`, then `{ s with stB := next }` satisfies `pinnedSources m e`. -/
theorem recvB_preserves_pinnedSources [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StB onoff Sym)
    (hout : recvB base onoff ecEk s.stB msg = some (key, t, next)) :
    pinnedSources m e { s with stB := next } := by
  obtain h | h := oppUniKemCKA.Reduction.Internal.recvB_kem_source_shape
    base onoff ecEk s.stB msg key t next hout
  · exact ⟨hs.1, by simpa only [h.1, h.2.1, h.2.2.1] using hs.2⟩
  · exact ⟨hs.1, by simp [h.2.1]⟩

/-- The version of `recvB_preserves_pinnedSources` for A's receive in `honestScheme m e s`. -/
theorem recvA_preserves_pinnedSources [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StA onoff Sym)
    (hout : (honestScheme ecEk ecCt0 ecCt1 m e s).recvA s.stA msg = some (key, t, next)) :
    pinnedSources m e { s with stA := next } := by
  rcases oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
    (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
      (s.keyB s.stA.t))
    (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
      (s.keyB s.stA.t))
    (Pinned.deterministic m (decide (s.stA.t = e)) (decide (s.stB.t = e))
      (decide (s.stB.t = e)) (s.keyB s.stA.t)).decapsDet
    ecCt0 ecCt1 s.stA msg key t next hout with h | h
  · exact ⟨by simpa only [h.1, h.2.1, h.2.2] using hs.1, hs.2⟩
  · exact ⟨by simp [h.2.2.1], hs.2⟩

/-- For every state `s` satisfying `pinnedSources m e` and every correctness query, each
possible successor state of the correctness oracles of `honestScheme m e s` satisfies
`pinnedSources m e`. -/
theorem honestCorrectness_preserves_pinnedSources [DecidableEq K] [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s)) :
    pinnedSources m e z.2 := by
  apply SCKAScheme.correctnessImpl_preserves_localInv_at _
    (fun a b => pinnedSources m e { s with stA := a, stB := b }) s hs ?_ ?_ ?_ ?_ t z hz
  · exact fun key msg t next hout =>
      sendA_preserves_pinnedSources ecEk m e s hs key msg t next hout
  · exact fun key msg t next hout =>
      sendB_preserves_pinnedSources ecCt0 ecCt1 m e s hs key msg t next hout
  · exact fun msg key t next hout =>
      recvA_preserves_pinnedSources ecEk ecCt0 ecCt1 m e s hs msg key t next hout
  · exact fun msg key t next hout =>
      recvB_preserves_pinnedSources base onoff ecEk leak m e s hs msg key t next hout

/-- The initial game state, in which neither party holds private keys or offline state,
satisfies `pinnedSources m e`. -/
theorem pinnedSources_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (m : Material leak) (e : ℕ) :
    pinnedSources (Sym := Sym) m e
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff) := by
  simp [pinnedSources, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- For `m ∈ support (sampleMaterial leak)` and every flag `selected`, every possible output of
`Pinned.keygen m selected` is a possible output of `base.keygen`. -/
theorem pinned_keygen_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) (selected : Bool)
    (pair : PK × SK) (h : pair ∈ support (Pinned.keygen m selected)) :
    pair ∈ support base.keygen := by
  cases selected
  · exact h
  · obtain rfl := (mem_support_pure_iff _ _).mp h
    exact (sampleMaterial_ordinary_support leak m hm).1

/-- For `m ∈ support (sampleMaterial leak)` and every state `s`, every possible output of A's
send in `honestScheme m e s` from `s.stA` is a possible output of `sendA base onoff ecEk`
from `s.stA`. -/
theorem sendA_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym))
    (hout : out ∈ support
      (sendA (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
              (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        ecEk s.stA)) :
    out ∈ support (sendA base onoff ecEk s.stA) := by
  cases hd : s.stA.dkA with
  | none =>
    simp only [sendA, hd, pure_bind, mem_support_bind_iff] at hout ⊢
    obtain ⟨pair, hpair, hout⟩ := hout
    exact ⟨pair, pinned_keygen_support leak m hm _ pair hpair, hout⟩
  | some sk => simpa only [sendA, hd] using hout

/-- The version of `sendA_pinned_support` for B, for states `s` satisfying `reachableInv`
and `pinnedSources m e`. -/
theorem sendB_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym))
    (hout : out ∈ support
      (sendB (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
              (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB)) :
    out ∈ support (sendB base onoff ecCt0 ecCt1 s.stB) := by
  have hoff := (sampleMaterial_ordinary_support leak m hm).2.1
  have hon := (sampleMaterial_ordinary_support leak m hm).2.2
  by_cases he : s.stB.t = e
  · cases hc0 : s.stB.ct0 with
    | none =>
      obtain ⟨T, hT⟩ := hs
      have hack := hT.ctRecB_eq_false_of_ct0_eq_none hc0
      simp only [sendB, hc0, hack, Bool.not_false, Pinned.onOff, Pinned.encapsOff,
        he, decide_true, ↓reduceIte, pure_bind] at hout
      simp only [sendB, hc0, hack, he, Bool.not_false, ↓reduceIte, pure_bind,
        mem_support_bind_iff]
      exact ⟨m.off.1, hoff, hout⟩
    | some ct0 =>
      simp only [sendB, hc0, pure_bind] at hout ⊢
      cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
        cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
      all_goals
        simp only [hp, hc1, hst, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.onOff, Pinned.encapsOn, he, decide_true] at hout ⊢
        first
        | exact hout
        | have hinputs := pinned_online_inputs base onoff ecEk ecCt0 ecCt1
            leak m e s hs hsrc he _ _ hp hst hc1
          apply (mem_support_bind_iff _ _ _).mpr
          refine ⟨m.on.1, ?_, hout⟩
          simpa only [hinputs.1, hinputs.2] using hon
  · cases hc0 : s.stB.ct0 with
    | none =>
      obtain ⟨T, hT⟩ := hs
      have hack := hT.ctRecB_eq_false_of_ct0_eq_none hc0
      simpa only [sendB, hc0, hack, Bool.not_false, pure_bind,
        Pinned.onOff, Pinned.encapsOff, he, decide_false, Bool.false_eq_true,
        ↓reduceIte] using hout
    | some ct0 =>
      cases ha : s.stB.ack.ctRec
      all_goals
        simp only [sendB, hc0, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.onOff, Pinned.encapsOn, he, decide_false] at hout ⊢
        first
        | exact hout
        | cases hp : s.stB.ekA <;> simp only [hp] at hout ⊢
          all_goals first
          | exact hout
          | cases hc1 : s.stB.ct1 <;> simp only [hc1] at hout ⊢
            all_goals first
            | exact hout
            | cases hst : s.stB.stCt <;> simpa only [hst] using hout

/-- For `m ∈ support (sampleMaterial leak)` and every state `s`, every possible response/state
pair of A's send oracle of `honestScheme m e s` from `s` is a possible response/state pair of
A's send oracle of `scheme base …` from `s`. -/
theorem oracleSendA_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendA (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendA (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  rw [SCKAScheme.mem_support_oracleSendA_run_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  exact ⟨out, sendA_pinned_support base onoff ecEk leak m hm e s out hout, hz⟩

/-- The version of `oracleSendA_pinned_support` for B, for states `s` satisfying
`reachableInv` and `pinnedSources m e`. -/
theorem oracleSendB_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendB (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendB (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  rw [SCKAScheme.mem_support_oracleSendB_run_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  exact ⟨out, sendB_pinned_support base onoff ecEk ecCt0 ecCt1 leak
    m hm e s hs hsrc out hout, hz⟩

end oppUniKemCKA.Security.Embedding
