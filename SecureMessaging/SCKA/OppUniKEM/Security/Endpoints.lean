/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Projection
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Composition
import ToVCVio.OracleComp.SimSemantics.StateT.ExpectedPayoffBound
import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant

/-!
# Replacing decapsulation in the Opp-UniKEM security game

Let:

- `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be the Opp-UniKEM protocol,
- `adv : SecurityAdversary leak Sym` be an SCKA adversary that makes
  at most `q` send oracle calls (`SecuritySendQueryBound adv q`), and
- `ε` be the KEM correctness error.

Assume:

- the KEM scheme has deterministic decapsulation;
- the erasure codes are correct.

For a fixed challenge bit `b`, define the following games for `Π`.
Each runs `adv` and returns its output bit.

- `G_b`: the original SCKA game (`SCKAScheme.securityExpFixedBit`).
  It answers eligible challenges with recorded keys for `b = false` and independent uniform keys
  for `b = true`.
- `I_b`: the ideal game (`idealSecurityExp`). It differs from `G_b` only in A's receive:
  when A completes an online ciphertext, it uses B's recorded key directly instead of decapsulating
  the received ciphertext.

Main result:

For every `b`, `security_correctness_endpoint_le` bounds the difference between the probability of
`G_b` and `I_b` returning `true`: `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`.
-/

open OracleSpec OracleComp KEMScheme ErasureCodePayload ENNReal

universe u

namespace oppUniKemCKA

/-! ## Ideal game -/

section

variable {m : Type → Type u} [Monad m] {K PK SK C Sym : Type}

/-- The Opp-UniKEM scheme with A's receive using `decapsDet : SK → C → Option K`.
All other algorithms are those of `scheme`. -/
def schemeWithDecaps (kem : KEMScheme m K PK SK C) (onoff : kem.OnOffStructure)
  [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (decapsDet : SK → C → Option K) :
    SCKAScheme m Unit (StA onoff Sym) (StB onoff Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.OffRand leak.OnRand) :=
  { scheme kem onoff hDet ecEk ecCt0 ecCt1 leak with
    recvA := recvA kem onoff decapsDet ecCt0 ecCt1 }

end

namespace Security

open Reduction.Internal

variable {K PK SK C Sym : Type}

section IdealGame

/-- A's receive oracle in the ideal game `I_b`.

Let `Key[B, t]` be the key recorded by the game for B at epoch `t` (`none` if absent),
and let `t_A` be A's epoch before the receive. On input B's message index `n`, execute
the ordinary `O-Recv-A(n)`, replacing decapsulation by the lookup `Key[B, t_A]`. -/
def oracleRecvAIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  fun n => do
    let s ← (get : StateT
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)))
    (SCKAScheme.oracleRecvA (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak
      (fun _ _ => s.keyB s.stA.t)) n)

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The SCKA correctness oracles using the ideal receive oracle for A. -/
def idealCorrectnessImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  let scka := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak
  SCKAScheme.oracleUnif (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    + SCKAScheme.oracleSendA scka + SCKAScheme.oracleSendB scka
    + oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak + SCKAScheme.oracleRecvB scka

/-- The SCKA security oracles for the ideal game `I_b`. -/
def idealSecurityImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  SCKAScheme.securityImplOf (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.oracleChall b _ _ _ _)
    (exposureA kem onoff leak) (exposureB kem onoff leak)
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)

/-- The experiment `I_b`: run `adv` against `idealSecurityImpl … b` and return its output bit. -/
def idealSecurityExp
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (b : Bool) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run'
    (Reduction.Internal.initialGame kem onoff)

end

/-- Two decapsulation functions give equal A-receive computations on a fixed state and
message if they agree on every decapsulation reached by that receive. -/
theorem recvA_eq_of_decaps_agrees [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (decaps decaps' : SK → C → Option K)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : StA onoff Sym) (msg : Message Sym)
    (hdec : ∀ dk ct0 ch ct1 ack,
      s.dkA = some dk → s.ct0 = some ct0 →
      msg = (some ch, ack, s.t, some 1) →
      ecCt1.decode (insert ch s.lch) = some ct1 →
      decaps dk (onoff.split.symm (ct0, ct1)) = decaps' dk (onoff.split.symm (ct0, ct1))) :
    recvA kem onoff decaps ecCt0 ecCt1 s msg =
      recvA kem onoff decaps' ecCt0 ecCt1 s msg := by
  rcases msg with ⟨ch, ack, t, bit⟩
  by_cases ht : t = s.t
  · subst t
    cases hc : ch with
    | none =>
      cases hct : s.ct0 <;> simp [recvA, hct]
    | some chunk =>
      cases hb : bit with
      | none =>
        cases hct : s.ct0 <;> simp [recvA, hct]
      | some bit =>
        fin_cases bit
        · cases hct : s.ct0 <;> cases hdecode : ecCt0.decode (insert chunk s.lch) <;>
            simp [recvA, hct, hdecode]
        · cases hd : s.dkA with
          | none => cases hct : s.ct0 <;> simp [recvA, hd, hct]
          | some dk =>
            cases hct : s.ct0 with
            | none => simp [recvA, hd, hct]
            | some ct0 =>
              cases hct1 : ecCt1.decode (insert chunk s.lch) with
              | none => simp [recvA, hd, hct, hct1]
              | some ct1 =>
                have heq := hdec dk ct0 chunk ct1 ack hd hct
                  (by simp [hc, hb]) hct1
                simp [recvA, hd, hct, hct1, heq]
  · have ht' : s.t ≠ t := Ne.symm ht
    simp [recvA, ht']

/-- Conditions for replacing A's decapsulation by B's recorded key in a game state `s`:

- the online ciphertext erasure code is correct;
- `s` is consistent with a transcript of sampled KEM material (`reachableInv`);
- whenever A's secret key and offline ciphertext, B's online ciphertext, and B's recorded key
  for A's epoch are present, decapsulation of those ciphertext components under that secret
  key returns the recorded key (`CurrentKEMCorrect`). -/
def IdealReceiveConditions
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  ecCt1.ec.Correct ∧ reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧
    CurrentKEMCorrect kem onoff hDet s

/-- Suppose the game state `s` satisfies `IdealReceiveConditions`.
If a recorded message from B completes A's online ciphertext, A's decapsulation result equals
B's recorded key for A's current epoch. -/
theorem honest_recvA_decapsulation_eq_recorded [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : IdealReceiveConditions kem onoff hDet ecEk ecCt0 ecCt1 s)
    (n : ℕ) (msg : Message Sym) (epoch : ℕ) (hentry : s.msgB n = some (msg, epoch))
    (dk : SK) (ct0 : onoff.C₀) (ch : ℕ × Sym) (ct1 : onoff.C₁) (ack : Ack)
    (hdk : s.stA.dkA = some dk) (hct0 : s.stA.ct0 = some ct0)
    (hmsg : msg = (some ch, ack, s.stA.t, some 1))
    (hdecode : ecCt1.decode (insert ch s.stA.lch) = some ct1) :
    hDet.decapsDet dk (onoff.split.symm (ct0, ct1)) = s.keyB s.stA.t := by
  rcases hs with ⟨hCt1, hs, hc⟩
  obtain ⟨T, hT⟩ := hs
  subst msg
  have hhon := hT.msgB n _ hentry
  obtain ⟨online, key, i, hon, hch⟩ : ∃ online key i,
      (T s.stA.t).on = some (online, key) ∧ ch = ecCt1.encode online i := by
    simpa [HonestMessageB] using hhon.2
  obtain ⟨_, I, hlch, hcard⟩ :
      (∃ st, (T s.stA.t).off = some (st, ct0)) ∧
      ∃ I, s.stA.lch = payloadChunks ecCt1 online I ∧ I.card < ecCt1.ec.nchunk := by
    simpa [ChunksAConsistent, hct0, hon] using hT.chunksA
  have hstep := decode_insert_honest ecCt1 hCt1 online I i hcard
  have heq : online = ct1 := by
    rw [hch, hlch] at hdecode
    rcases hstep with ⟨_, hn⟩ | ⟨_, hsome⟩
    · simp [hn] at hdecode
    · exact Option.some.inj (hsome.symm.trans hdecode)
  subst ct1
  have htbound := hT.msgBEpoch n _ epoch hentry
  change s.stA.t ≤ s.stB.t at htbound
  have htAB := Nat.le_antisymm htbound hT.epochs.1
  have hct1B : s.stB.ct1 = some online := by
    have h := hT.onB
    rw [← htAB, hon] at h
    exact h.symm
  have hk : s.keyB s.stA.t = some key := by
    rw [hT.keyB]
    simp [EpochTranscript.key, hon]
  exact (hc dk ct0 online key hdk hct0 hct1B hk).trans hk.symm

/-- Suppose the game state `s` satisfies `IdealReceiveConditions`.
For every delivery index `n`, A's receive oracles in `G_b` and `I_b` have equal response/state
computations from `s`. -/
theorem oracleRecvA_eq_ideal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff)
    (n : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : IdealReceiveConditions kem onoff hDet ecEk ecCt0 ecCt1 s) :
    (SCKAScheme.oracleRecvA (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s =
      (oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak n).run s := by
  change (SCKAScheme.oracleRecvA _ n).run s =
    (SCKAScheme.oracleRecvA (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak
      (fun _ _ => s.keyB s.stA.t)) n).run s
  cases hentry : s.msgB n with
  | none => simp [SCKAScheme.oracleRecvA, hentry]
  | some entry =>
    rcases entry with ⟨msg, epoch⟩
    have heq := recvA_eq_of_decaps_agrees kem onoff hDet.decapsDet (fun _ _ => s.keyB s.stA.t)
      ecCt0 ecCt1 s.stA msg
      (honest_recvA_decapsulation_eq_recorded kem onoff hDet ecEk ecCt0 ecCt1
        s hs n msg epoch hentry)
    simp only [SCKAScheme.oracleRecvA, scheme, schemeWithDecaps, StateT.run_bind,
      StateT.run_get, pure_bind, hentry, heq]

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Suppose the game state `s` satisfies `IdealReceiveConditions`.
For every query `t`, the oracles of `G_b` and `I_b` have equal response/state computations
from `s`. -/
theorem securityImpl_eq_ideal_of_current
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : IdealReceiveConditions kem onoff hDet ecEk ecCt0 ecCt1 s) :
    (SCKAScheme.sckaSecurityImpl b (exposureA (Sym := Sym) kem onoff leak)
      (exposureB (Sym := Sym) kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run s =
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b t).run s := by
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s ?_ (fun _ => rfl) t
  intro t
  rcases t with ((((n | u) | u) | n) | n)
  all_goals simp only [idealCorrectnessImpl, SCKAScheme.sckaCorrectnessImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  exact oracleRecvA_eq_ideal kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs

end IdealGame

/-! ## KEM failure probability

We extend the original game `G_b` and ideal game `I_b` with a Boolean flag `bad`, initially
`false`. Their oracle implementations are `trackedSecurityImpl` and `trackedIdealImpl`,
respectively.
The flag records whether `currentKEMFailure` has detected completed KEM material whose
decapsulation disagrees with B's recorded key.

Let `V(s) := currentFailurePotential s` be the conditional KEM failure probability for the
current partially sampled epoch, or zero if sampling has not started or online encapsulation
is complete.

Let `Φ(s, bad) := if bad then 1 else V(s)` (`trackedFailureScore`).
It equals `1` once a KEM failure has been recorded, and the current failure
potential `V(s)` otherwise.
-/

section FailureProbability

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The oracles of `G_b` with a flag recording whether a KEM failure has occurred. -/
def trackedSecurityImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
        ProbComp) :=
  -- VCVio's `extendState` adds a flag, updated by its second argument after each query.
  QueryImpl.extendState
    (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
    (fun _ _ _ s' bad => bad || currentKEMFailure kem onoff hDet s')

/-- Discarding the failure flag after running `trackedSecurityImpl` gives the same computation
as the original security oracles, including the adversary's output and final game state.
This holds for any initial state and flag. -/
theorem trackedSecurity_run_project
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    -- Run with tracking from `p = (s, bad)`, then discard the final flag:
    -- `Prod.map id Prod.fst` maps `(a, (s', bad'))` to `(a, s')`.
    Prod.map id Prod.fst <$>
        (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run p
      =
      -- Run the original game from `s = p.1`, retaining its output and final state.
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
        (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run p.1 :=
  -- VCVio's projection theorem for `extendState` gives this equality.
  extendState_run_proj_eq _ _ adv p.1 p.2

/-- Once the failure flag is set, every tracked successor has it set. -/
theorem trackedSecurityImpl_preserves_bad
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (fun p => p.2 = true) := by
  intro t p hp z hz
  rw [trackedSecurityImpl, QueryImpl.extendState_apply, mem_support_bind_iff] at hz
  obtain ⟨y, _, hz⟩ := hz
  obtain rfl := (mem_support_pure_iff _ _).mp hz
  simp [hp]

/-- Assume the three erasure codes are correct. Every query of `trackedSecurityImpl` preserves
`trackedInv`: either `bad = true`, or `reachableInv` holds and `currentKEMFailure` is false. -/
theorem trackedSecurityImpl_preserves
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1) := by
  intro t p hp z hz
  change z ∈ support (do
    let y ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p.1
    pure (y.1, (y.2, p.2 || currentKEMFailure kem onoff hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst z
  rcases hp with hbad | ⟨hreach, hfail⟩
  · left
    simp [hbad]
  have hc := currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
    p.1 hreach hfail
  have hreach' := securityImpl_preserves_reachableInv kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak b t p.1 hreach hc y hy
  cases hbad : currentKEMFailure kem onoff hDet y.2
  · exact Or.inr ⟨hreach', hbad⟩
  · exact Or.inl (by simp)

/-- Fix a bit `b` and a state `s` satisfying `reachableInv` and `currentKEMFailure s = false`.
If `(s', bad')` is the state after A's tracked leaking-send query from `(s, false)`, then
we have the following bound on the expected failure score `Φ`:
`E[Φ(s', bad')] ≤ Φ(s, false) + ε`. -/
theorem tracked_sendArleak_score_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendArleak).run (s, false))
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change expectedPayoff (do
    let y ← (SCKAScheme.oracleSendArleak vulnRleakA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendArleak_expectedPayoff_le
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) vulnRleakA
      (sendArleak_forget kem onoff ecEk leak) s (leakEpochsA s.stA)
      (score := fun state => trackedFailureScore kem onoff
        (state, false || currentKEMFailure kem onoff hDet state))
      (c := trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff)
  · intro key msg epoch state coins hout
    exact sendArleak_exposure kem onoff ecEk leak s.stA
      key msg epoch state coins hout
  · intro state exposed
    rfl
  · simp [hf]
  · have h := tracked_sendA_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak s hs hf
    change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, expectedPayoff_map] using h

/-- The version of `tracked_sendArleak_score_le` for B. -/
theorem tracked_sendBrleak_score_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendBrleak).run (s, false))
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change expectedPayoff (do
    let y ← (SCKAScheme.oracleSendBrleak vulnRleakB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendBrleak_expectedPayoff_le
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) vulnRleakB
      (sendBrleak_forget kem onoff ecCt0 ecCt1 leak) s (leakEpochsB s.stB)
      (score := fun state => trackedFailureScore kem onoff
        (state, false || currentKEMFailure kem onoff hDet state))
      (c := trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff)
  · intro key msg epoch state coins hout
    exact sendBrleak_exposure kem onoff ecCt0 ecCt1 leak s.stB
      key msg epoch state coins hout
  · intro state exposed
    rfl
  · simp [hf]
  · have h := tracked_sendB_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak s hs hf
    change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, expectedPayoff_map] using h

/-- Fix a bit `b`, a query `t`, and a state `p` satisfying `trackedInv`.
Let `p'` be the state after `trackedSecurityImpl b` answers `t` from `p`.
Then we have the following bounds on the tracked failure score:
- `E[Φ(p')] ≤ Φ(p) + ε` for an ordinary or leaking send, and
- `E[Φ(p')] ≤ Φ(p)` otherwise. -/
theorem trackedSecurity_score_step_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
    (hp : trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p) :
    expectedPayoff ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b t).run p)
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff p +
        if SCKAScheme.sckaSecuritySpec.isSendQuery t then factorCorrectnessError kem onoff
        else 0 := by
  by_cases hbad : p.2 = true
  · refine (expectedPayoff_le_one _ _ ?_).trans ?_
    · intro z
      exact trackedFailureScore_le_one kem onoff z.2
    · simp [trackedFailureScore, hbad]
  have hfalse : p.2 = false := Bool.eq_false_iff.mpr hbad
  have hgood : reachableInv kem onoff ecEk ecCt0 ecCt1 p.1 ∧
      currentKEMFailure kem onoff hDet p.1 = false := by
    rcases hp with hp | hp
    · exact False.elim (hbad hp)
    · exact hp
  have hpEq : p = (p.1, false) := Prod.ext rfl hfalse
  rw [hpEq]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [SCKAScheme.sckaSecuritySpec.isSendQuery_OCorrectness]
    exact tracked_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak t (p.1, false)
      (Or.inr hgood)
  · cases u
    simpa only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte] using
      tracked_sendArleak_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak b p.1 hgood.1 hgood.2
  · cases u
    simpa only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte] using
      tracked_sendBrleak_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak b p.1 hgood.1 hgood.2
  all_goals
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    apply expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
    intro z hz
    change z ∈ support (do
      let y ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) _).run p.1
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    simp only [mem_support_pure_iff] at hz
    subst z
    let J := fun s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) =>
      currentKEMFailure kem onoff hDet s = false ∧
      currentFailurePotential kem onoff s = currentFailurePotential kem onoff p.1
    have hj : J p.1 := ⟨hgood.2, rfl⟩
    suffices hout : J y.2 by
      exact le_of_eq (by simp [trackedFailureScore, hout.1, hout.2])
  · apply (SCKAScheme.oracleChall_recordsChallenges b).preservesInv J ?_ t p.1 hj y hy
    intro state challenged hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptA_preservesInv (vulnCorrA kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptB_preservesInv (vulnCorrB kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate

/-- Under the module's assumptions, for every bit `b` and SCKA adversary `adv` satisfying
`SecuritySendQueryBound adv q`, the tracked execution of `G_b` from `(initialGame, false)`
satisfies `Pr[bad_final = true] ≤ q · ε`, where `bad_final` is its final failure flag. -/
theorem kem_failure_probability_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    Pr[fun z => z.2.2 = true |
      (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run
        (initialGame (Sym := Sym) kem onoff, false)] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  have hpres := trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0
    ecCt1 hCt1 leak b
  have hinit := tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1
    ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos
  have hscore₀ : trackedFailureScore kem onoff
      (initialGame (Sym := Sym) kem onoff, false) = 0 := by
    simp [trackedFailureScore, currentFailurePotential, initialGame, initialA, initialB,
      SCKAScheme.initGameState, Option.map₂]
  have hscore := expectedPayoff_simulateQ_run_le
    (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    (trackedInv kem onoff hDet ecEk ecCt0 ecCt1)
    (trackedFailureScore kem onoff) (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
    (factorCorrectnessError kem onoff) hpres
    (trackedSecurity_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    adv q hq (initialGame kem onoff, false) hinit
  rw [hscore₀, zero_add, factorCorrectnessError_eq] at hscore
  exact (tracked_bad_probability_le_score kem onoff _).trans hscore

end FailureProbability

/-! ## Comparison bound -/

section ComparisonBound

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The oracles of the ideal game `I_b` with failure tracking, using the same flag update as
`trackedSecurityImpl`. -/
def trackedIdealImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) ProbComp) :=
  QueryImpl.extendState (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    (fun _ _ _ s' bad => bad || currentKEMFailure kem onoff hDet s')

/-- The version of `trackedSecurity_run_project` for the ideal game `I_b`:
discarding the failure flag recovers the ideal execution, for any initial state and flag. -/
theorem trackedIdeal_run_project
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ (trackedIdealImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run p =
      (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
        adv).run p.1 :=
  extendState_run_proj_eq _ _ adv p.1 p.2

/-- The original game `G_b` equals the security-oracle simulation from `initialGame`,
projected to the adversary's output. -/
theorem securityExpFixedBit_eq_run'
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) :
    SCKAScheme.securityExpFixedBit (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
      (exposureA kem onoff leak) (exposureB kem onoff leak) =
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
        (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run' (initialGame kem onoff) := by
  simp [SCKAScheme.securityExpFixedBit, scheme, initKeyGen, initA, initB,
    initialGame, initialA, initialB, StateT.run'_eq, map_eq_bind_pure_comp]

/-- Under the module's assumptions, for every bit `b` and SCKA adversary `adv` satisfying
`SecuritySendQueryBound adv q`, the original game `G_b` and ideal game `I_b` satisfy
`|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`. -/
theorem security_correctness_endpoint_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    |(Pr[= true | SCKAScheme.securityExpFixedBit
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
        (exposureA kem onoff leak) (exposureB kem onoff leak)]).toReal -
      (Pr[= true | idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak
        b adv]).toReal| ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  let left := trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
  let right := trackedIdealImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let s₀ := initialGame (Sym := Sym) kem onoff
  have hagree : ∀ t p, Inv p → ¬p.2 = true → (left t).run p = (right t).run p := by
    intro t p hp hgood
    rcases hp with hbad | ⟨hr, hf⟩
    · exact False.elim (hgood hbad)
    · have hc := currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
        p.1 hr hf
      have heq := securityImpl_eq_ideal_of_current kem onoff hDet ecEk ecCt0 ecCt1
        leak b t p.1 ⟨hCt1, hr, hc⟩
      simp only [left, right, trackedSecurityImpl, trackedIdealImpl, QueryImpl.extendState_apply]
      rw [heq]
  have hbound := abs_probEvent_simulateQ_run_sub_le_bad_of_inv left right Inv
    (fun p => p.2 = true)
    (trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak b)
    (trackedSecurityImpl_preserves_bad kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    hagree adv (fun guess => guess = true) (s₀, false)
    (tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
  have hl : Pr[= true | SCKAScheme.securityExpFixedBit
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b (exposureA kem onoff leak)
        (exposureB kem onoff leak)] =
      Pr[fun z => z.1 = true | (simulateQ left adv).run (s₀, false)] := by
    rw [securityExpFixedBit_eq_run', ← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map]
    rw [← trackedSecurity_run_project kem onoff hDet ecEk ecCt0 ecCt1 leak b adv (s₀, false),
      probEvent_map]
    rfl
  have hr : Pr[= true | idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak b adv] =
      Pr[fun z => z.1 = true | (simulateQ right adv).run (s₀, false)] := by
    rw [idealSecurityExp, ← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map]
    rw [← trackedIdeal_run_project kem onoff hDet ecEk ecCt0 ecCt1 leak b adv (s₀, false),
      probEvent_map]
    rfl
  rw [hl, hr]
  refine hbound.trans ?_
  have hbad := kem_failure_probability_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak b adv q hq
  have hfinite : (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))
  have hreal := ENNReal.toReal_mono hfinite hbad
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

end ComparisonBound

end Security

end oppUniKemCKA
