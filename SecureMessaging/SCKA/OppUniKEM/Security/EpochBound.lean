/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Core

/-!
# Bounding recorded epochs by sends

**Invariant.** For a game state `s`, write `a = s.stA.t` for A's current
epoch, `d = s.stA.dkA` for its optional secret key, and `n = s.nA` for its
successful-send count. Define `sendEpochInv s` by
`a ≤ n + 1 ∧ (d ≠ none → a ≤ n)`.

**Results.** The initial state satisfies this invariant, and every supported
successor of every security query preserves it. Moreover, for every state
`s` and epoch `t : ℕ`,
`reachableInv s ∧ sendEpochInv s ∧ (keyA_s(t) ≠ none ∨ keyB_s(t) ≠ none) → t ≤ s.nA`.
Here `reachableInv` asserts existence of a consistent correctness transcript.

**Proof.** Key generation occurs in a send, which increments `n`. For every
successful receive, either `(a', d') = (a, d)`, or
`a' = a + 1 ∧ d ≠ none ∧ d' = none`; the latter preserves `a' ≤ n + 1`.
Transcript consistency then relates each recorded key to a generated key
pair. `CounterBound` supplies the remaining inequality `s.nA ≤ q`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}

/-- For a game state `s`, require `s.stA.t ≤ s.nA + 1`, and require
`s.stA.t ≤ s.nA` whenever `s.stA.dkA` is present. Here `s.nA` counts successful
A sends and `s.stA.t` is A's current epoch. -/
def sendEpochInv {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  s.stA.t ≤ s.nA + 1 ∧ (s.stA.dkA.isSome → s.stA.t ≤ s.nA)

/-- The empty epoch-one state satisfies the send/epoch accounting invariant. -/
theorem sendEpochInv_init
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure) :
    sendEpochInv (Reduction.Internal.initialGame (Sym := Sym) kem onoff) := by
  simp [sendEpochInv, Reduction.Internal.initialGame, Reduction.Internal.initialA,
    SCKAScheme.initGameState]

/-- For every game state `s` satisfying `reachableInv` and `sendEpochInv`,
and every epoch `t`, a present entry in `s.keyA t` or `s.keyB t` implies
`t ≤ s.nA`, where `s.nA` counts successful A sends. -/
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

/-- A raw receive either keeps A's epoch and decapsulation key unchanged,
or advances one epoch from an existing key and erases that key. This
property holds for every local state, message, and choice of erasure codes. -/
theorem recvA_epoch_shape [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : StA onoff Sym) (msg : Message Sym)
    (key : Option (ℕ × K)) (epoch : ℕ) (s' : StA onoff Sym)
    (h : recvA kem onoff hDet ecCt0 ecCt1 s msg = some (key, epoch, s')) :
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

/-- A successful ordinary send consumes one counter unit and either
creates or retains the current key pair, preserving epoch accounting. -/
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

/-- For every state `s` satisfying `sendEpochInv`, delivered index `n`,
and supported successor `s'` of A's receive, `sendEpochInv s'` holds.
An epoch-advancing receive requires a present secret key and erases it. -/
theorem oracleRecvA_preserves_sendEpochInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (SCKAScheme.oracleRecvA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) sendEpochInv := by
  intro n s hs z hz
  simp only [SCKAScheme.oracleRecvA, scheme, StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hm : s.msgB n with
  | none =>
    have hz' : z = (none, s) := by simpa [hm] using hz
    obtain rfl := hz'
    exact hs
  | some entry =>
    rcases entry with ⟨msg, epoch⟩
    rw [hm] at hz
    dsimp only at hz
    cases hr : recvA kem onoff hDet ecCt0 ecCt1 s.stA msg with
    | none =>
      simp only [hr, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
    | some out =>
      rcases out with ⟨key, epoch', state⟩
      have hshape := recvA_epoch_shape kem onoff hDet ecCt0 ecCt1 s.stA msg key epoch' state hr
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

/-- For every state satisfying `sendEpochInv`, every supported successor
of B's ordinary send satisfies it: A's local state and send counter are retained. -/
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

/-- For every state satisfying `sendEpochInv` and every delivery index,
each supported successor of B's receive satisfies it. A's state and counter
retain their values. -/
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

/-- Every full-security oracle preserves the epoch/send accounting
invariant. Leaking sends inherit preservation from their ordinary
marginals, including rejection; bookkeeping updates preserve both inequalities. -/
theorem securityImpl_preserves_sendEpochInv
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl.PreservesInv (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
      (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) sendEpochInv := by
  intro t s hs z hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · have hz' : ∃ r, (r, s) = z := by
        simpa [SCKAScheme.sckaSecurityImpl, SCKAScheme.sckaCorrectnessImpl,
          SCKAScheme.oracleUnif] using hz
      obtain ⟨_, rfl⟩ := hz'
      exact hs
    · exact oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
    · exact oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
    · exact oracleRecvA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs z hz
    · exact oracleRecvB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs z hz
  · exact SCKAScheme.oracleSendArleak_preservesInv _ _ (sendArleak_forget kem onoff ecEk leak)
      sendEpochInv (fun _ _ h => h)
      (oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak) u s hs z hz
  · exact SCKAScheme.oracleSendBrleak_preservesInv _ _
      (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
      sendEpochInv (fun _ _ h => h)
      (oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak) u s hs z hz
  · exact SCKAScheme.oracleChall_preservesInv b sendEpochInv (fun _ _ h => h) t s hs z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff) sendEpochInv
      (fun _ _ h => h) u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff) sendEpochInv
      (fun _ _ h => h) u s hs z hz

end oppUniKemCKA.Security
