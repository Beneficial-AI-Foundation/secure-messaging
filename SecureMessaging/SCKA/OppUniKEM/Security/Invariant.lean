/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.SendA
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.SendB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.RecvA
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.RecvB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Core
import SecureMessaging.SCKA.Security.Family

/-!
# Transcript and epoch invariants

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM.
For a game state `s`, let:

- `reachableInv s` assert consistency with a transcript of sampled KEM material;
- `CurrentKEMCorrect s` assert agreement of current decapsulation with B's recorded key;
- `n := s.nA` be the number of successful sends by A.

The predicate `sendEpochInv s` asserts
`s.stA.t ≤ n + 1` and `s.stA.dkA.isSome → s.stA.t ≤ n`.

With correct erasure codes, each security query from a state satisfying `reachableInv`
and `CurrentKEMCorrect` preserves `reachableInv`. Each correctness query preserves
`sendEpochInv`. If `reachableInv s` and `sendEpochInv s` hold and either key table records
epoch `t`, then `recorded_epoch_le_sends` gives `t ≤ n`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- Replacing the exposed and challenged sets preserves consistency with the same transcript. -/
theorem TranscriptConsistent.with_security_bookkeeping
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {ecEk : ErasureCodePayload PK Sym}
    {ecCt0 : ErasureCodePayload onoff.C₀ Sym}
    {ecCt1 : ErasureCodePayload onoff.C₁ Sym}
    {T : Transcript kem onoff}
    {s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)}
    (h : TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T s)
    (exposed challenged : Finset ℕ) :
    TranscriptConsistent kem onoff ecEk ecCt0 ecCt1 T
      { s with exposed := exposed, challenged := challenged } := by
  cases h
  constructor <;> assumption

/-- Replacing the exposed and challenged sets preserves `reachableInv`. -/
theorem reachableInv_with_security_bookkeeping
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {ecEk : ErasureCodePayload PK Sym}
    {ecCt0 : ErasureCodePayload onoff.C₀ Sym}
    {ecCt1 : ErasureCodePayload onoff.C₁ Sym}
    {s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)}
    (h : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (exposed challenged : Finset ℕ) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      { s with exposed := exposed, challenged := challenged } := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, hT.with_security_bookkeeping exposed challenged⟩

/-- The initial game state satisfies `reachableInv`. -/
theorem reachableInv_initialGame
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) :
    reachableInv kem onoff ecEk ecCt0 ecCt1
      (Reduction.Internal.initialGame (Sym := Sym) kem onoff) := by
  simpa [Reduction.Internal.initialGame, Reduction.Internal.initialA,
    Reduction.Internal.initialB] using
      reachableInv_init kem onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos

/-- With correct erasure codes, every correctness query of `Π` from a state satisfying
`reachableInv` and `CurrentKEMCorrect` has only successors satisfying `reachableInv`. -/
theorem correctnessImpl_preserves_reachableInv_at [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((SCKAScheme.sckaCorrectnessImpl
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run s)) :
    reachableInv kem onoff ecEk ecCt0 ecCt1 z.2 := by
  rcases t with ((((n | u) | u) | n) | n)
  · exact SCKAScheme.oracleUnif_preservesInv _ n s hs z hz
  · exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos u s hs z hz
  · exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak u s hs z hz
  · exact oracleRecvA_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0
      ecCt1 hCt1 ecCt1.ec.nchunk_pos leak n s hs hc z hz
  · exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEk ecEk.ec.nchunk_pos
      ecCt0 ecCt1 leak n s hs z hz

/-- With correct erasure codes, every security query of `Π` from a state satisfying
`reachableInv` and `CurrentKEMCorrect` has only successors satisfying `reachableInv`. -/
theorem securityImpl_preserves_reachableInv
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
      (exposureB kem onoff leak) (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run s)) :
    reachableInv kem onoff ecEk ecCt0 ecCt1 z.2 :=
  SCKAScheme.securityImplOf_preserves_at_of_book _ _ _ _ _
    (reachableInv kem onoff ecEk ecCt0 ecCt1)
    (fun _ E C h => reachableInv_with_security_bookkeeping h E C)
    (sendArleak_forget kem onoff ecEk leak) (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
    (SCKAScheme.challOf_recordsChallenges _) s hs
    (correctnessImpl_preserves_reachableInv_at kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak s hs hc)
    (oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos () s hs)
    (oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak () s hs) t z hz

end oppUniKemCKA

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}

/-- A game state `s` satisfies `sendEpochInv` if `s.stA.t ≤ s.nA + 1` and
`s.stA.t ≤ s.nA` whenever A holds a decapsulation key. Here `s.nA` counts successful A-sends. -/
def sendEpochInv {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  s.stA.t ≤ s.nA + 1 ∧ (s.stA.dkA.isSome → s.stA.t ≤ s.nA)

/-- The empty epoch-one state satisfies the send/epoch accounting invariant. -/
theorem sendEpochInv_init
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    sendEpochInv (Reduction.Internal.initialGame (Sym := Sym) kem onoff) := by
  simp [sendEpochInv, Reduction.Internal.initialGame, Reduction.Internal.initialA,
    SCKAScheme.initGameState]

/-- If `reachableInv s` and `sendEpochInv s` hold, every epoch `t` recorded in either
key table satisfies `t ≤ s.nA`. -/
theorem recorded_epoch_le_sends
    {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {ecEk : ErasureCodePayload PK Sym}
    {ecCt0 : ErasureCodePayload onoff.C₀ Sym}
    {ecCt1 : ErasureCodePayload onoff.C₁ Sym}
    {s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)}
    (hr : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hs : sendEpochInv s)
    (t : ℕ) (hk : (s.keyA t).isSome ∨ (s.keyB t).isSome) : t ≤ s.nA := by
  obtain ⟨T, hT⟩ := hr
  rcases hk with hk | hk
  · rw [hT.keyA] at hk
    split at hk
    · simp at hk
    · split at hk
      · have := hs.1
        omega
      · simp at hk
  · rw [hT.keyB] at hk
    have hle : t ≤ s.stB.t := by
      by_contra hn
      have ht : s.stB.t < t := by omega
      simp [EpochTranscript.key, hT.futureOn t ht] at hk
    by_cases hlt : t < s.stA.t
    · have := hs.1
      omega
    · have ht : t = s.stA.t := by have := hT.epochs; omega
      have hon : (T s.stA.t).on.isSome := by
        simpa [EpochTranscript.key, ht] using hk
      have hkp := (T s.stA.t).on_keypair hon
      rw [hT.keypairA] at hkp
      have hdk : s.stA.dkA.isSome := by
        cases hd : s.stA.dkA <;> cases he : s.stA.ekA <;> simp_all [Option.map₂]
      exact ht ▸ hs.2 hdk

/-- For every local state, message, and decapsulation function, A's receive either
retains its epoch and decapsulation key, or advances one epoch and erases an existing key. -/
theorem recvA_epoch_shape [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (decapsDet : SK → C → Option K)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : StA onoff Sym) (msg : Message Sym)
    (key : Option (ℕ × K)) (epoch : ℕ) (s' : StA onoff Sym)
    (h : recvA kem onoff decapsDet ecCt0 ecCt1 s msg = some (key, epoch, s')) :
    (s'.t = s.t ∧ s'.dkA = s.dkA) ∨
      (s'.t = s.t + 1 ∧ s.dkA.isSome ∧ s'.dkA = none) := by
  rcases msg with ⟨ch, ack, t, b⟩
  dsimp only [recvA] at h
  repeat' (split at * <;> try simp_all only [Bool.and_eq_true, beq_iff_eq,
    Option.some.injEq, Prod.mk.injEq, and_self, Nat.left_eq_add, one_ne_zero, false_and,
    or_false, Fin.isValue, imp_false, Prod.forall, and_true, Bool.not_eq_true,
    Option.isSome_some, true_and, Nat.add_eq_left, and_false, ↓reduceIte, reduceCtorEq])
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp_all

/-- A's ordinary send preserves `sendEpochInv`. -/
theorem oracleSendA_preserves_sendEpochInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (SCKAScheme.oracleSendA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) sendEpochInv := by
  intro _ s hs z hz
  cases hd : s.stA.dkA <;>
    simp only [SCKAScheme.oracleSendA, scheme, sendA, hd, zero_add,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, StateT.run_set, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff, Prod.exists] at hz
  · obtain ⟨pk, sk, _, rfl⟩ := hz
    constructor <;> dsimp
    · exact hs.1.trans (Nat.le_succ _)
    · intro _
      exact hs.1
  · obtain rfl := hz
    constructor <;> dsimp
    · exact hs.1.trans (Nat.le_succ _)
    · intro _
      exact hs.1

/-- If `scka.recvA` is Opp-UniKEM's receive with any decapsulation function,
then `oracleRecvA scka` preserves `sendEpochInv`. -/
theorem oracleRecvA_preserves_sendEpochInv_of_recv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    {Rand : Type}
    (scka : SCKAScheme ProbComp Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym) Rand)
    (decapsDet : SK → C → Option K)
    (hRecv : scka.recvA = recvA kem onoff decapsDet ecCt0 ecCt1) :
    QueryImpl.PreservesInv (SCKAScheme.oracleRecvA scka) sendEpochInv := by
  intro n s hs z hz
  simp only [SCKAScheme.oracleRecvA, hRecv, StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hm : s.msgB n with
  | none =>
    have hz' : z = (none, s) := by simpa [hm] using hz
    obtain rfl := hz'
    exact hs
  | some entry =>
    rcases entry with ⟨msg, epoch⟩
    rw [hm] at hz
    dsimp only at hz
    cases hr : recvA kem onoff decapsDet ecCt0 ecCt1 s.stA msg with
    | none =>
      simp only [hr, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
    | some out =>
      rcases out with ⟨key, epoch', state⟩
      have hshape := recvA_epoch_shape kem onoff decapsDet ecCt0 ecCt1 s.stA msg key epoch' state hr
      simp only [hr] at hz
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals
        obtain rfl := hz
        rcases hshape with ⟨ht, hd⟩ | ⟨ht, hd, hnone⟩
        · simpa only [sendEpochInv, ht, hd] using hs
        · constructor
          · dsimp
            rw [ht]
            exact Nat.add_le_add_right (hs.2 hd) 1
          · simp only [hnone, Option.isSome_none, Bool.false_eq_true, false_implies]

/-- B's ordinary send preserves `sendEpochInv`. -/
theorem oracleSendB_preserves_sendEpochInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (SCKAScheme.oracleSendB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) sendEpochInv := by
  intro _ s hs z hz
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
    rcases out with ⟨key, msg, epoch, state⟩
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
    all_goals obtain rfl := hz; exact hs

/-- B's receive preserves `sendEpochInv`. -/
theorem oracleRecvB_preserves_sendEpochInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (SCKAScheme.oracleRecvB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) sendEpochInv := by
  intro n s hs z hz
  simp only [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  repeat' split at hz
  all_goals
    simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      mem_support_pure_iff] at hz
    obtain rfl := hz
    exact hs

end oppUniKemCKA.Security
