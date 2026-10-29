/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.CorrectnessOracles
import SecureMessaging.SCKA.OppUniKEM.Security.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Projection
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Composition
import ToVCVio.OracleComp.SimSemantics.StateT.BadFlag
import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant

/-!
# Opp-UniKEM correctness-error endpoints

**Setting.** Throughout this module, we consider:

- the Opp-UniKEM protocol (`scheme`) over a KEM `kem`;
- an SCKA security adversary `adv` making at most `q` send queries
  (`SecuritySendQueryBound adv q`);
- the KEM correctness error `ε`, that is, `kem.correctnessError` (Def. A.1 of [SCKA]).

**Main result.** For a challenge bit `b`, the *ideal game* `I_b` is the real game `G_b`
(`SCKAScheme.securityExpFixedBit`) in which party A, upon completing an online ciphertext, outputs
party B's recorded key instead of decapsulating (`I_b := idealSecurityExp … (fun _ => b) adv`).
More generally, under a challenge mode `mode`, it answers an eligible challenge at epoch `t` with a
uniform key exactly when `mode t = true` (`idealSecurityExp … mode adv`).

The real and ideal games differ in acceptance probability by at most the cumulative KEM correctness
error over `q` sends: `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`
(`security_correctness_endpoint_le`).
-/

open OracleSpec OracleComp KEMScheme ErasureCodePayload ENNReal
open OracleComp.ProgramLogic

universe u

namespace oppUniKemCKA

/-! ## Ideal game -/

section

variable {m : Type → Type u} [Monad m] {K PK SK C Sym : Type}

/-- Variant of the Opp-UniKEM scheme `scheme` in which party A's receive algorithm invokes a
given deterministic decapsulation function `decapsDet : SK → C → Option K`; all other protocol
algorithms are unchanged. -/
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
variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

section IdealGame

include hDet in
/-- Party A's receive oracle in the ideal game.

When invoked on message index `n` in game state `s`, this oracle executes `SCKAScheme.oracleRecvA`
except that decapsulation is replaced by looking up party B's recorded key `s.keyB s.stA.t` for
A's current epoch (`none` if no key is recorded). -/
def oracleRecvAIdeal [DecidableEq K] [DecidableEq Sym] :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (GameState onoff Sym) ProbComp) :=
  fun n => do
    let s ← (get : StateT
      (GameState onoff Sym) ProbComp
      (GameState onoff Sym))
    (SCKAScheme.oracleRecvA (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak
      (fun _ _ => s.keyB s.stA.t)) n)

include hCt0 hCt1 in
/-- Assuming the ciphertext erasure codes are correct, party A's ideal receive oracle
`oracleRecvAIdeal` preserves `reachableInv`. -/
theorem oracleRecvAIdeal_preserves_reachableInv [DecidableEq K] [DecidableEq Sym] :
    QueryImpl.PreservesInv (oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro n s hs res hres
  exact oracleRecvA_preserves_reachableInv_of_recv kem onoff ecEk ecCt0 hCt0
    ecCt1 hCt1 ecCt1.ec.nchunk_pos
    (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ _ => s.keyB s.stA.t))
    (fun _ _ => s.keyB s.stA.t) rfl n s hs (fun _ _ _ _ _ _ _ hk => hk) res hres

/-- Party A's ideal receive oracle `oracleRecvAIdeal` preserves `sendEpochInv`. -/
theorem oracleRecvAIdeal_preserves_sendEpochInv [DecidableEq K] [DecidableEq Sym] :
    QueryImpl.PreservesInv (oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak)
      sendEpochInv := by
  intro n s hs res hres
  exact oracleRecvA_preserves_sendEpochInv_of_recv kem onoff ecCt0 ecCt1
    (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ _ => s.keyB s.stA.t))
    (fun _ _ => s.keyB s.stA.t) rfl n s hs res hres

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

include hDet in
/-- The SCKA correctness oracle implementation in which party A's receive oracle is replaced by
`oracleRecvAIdeal`. -/
def idealCorrectnessImpl :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (GameState onoff Sym) ProbComp) :=
  let scka := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak
  SCKAScheme.oracleUnif (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    + SCKAScheme.oracleSendA scka + SCKAScheme.oracleSendB scka
    + oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak + SCKAScheme.oracleRecvB scka

include hDet in
/-- Security oracle implementation for the ideal game under challenge mode `mode : ℕ → Bool`. -/
def idealSecurityImpl
    (mode : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (GameState onoff Sym) ProbComp) :=
  SCKAScheme.securityImplOf (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf mode)
    (exposureA kem onoff leak) (exposureB kem onoff leak)
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)

include hDet in
/-- The ideal security experiment: executes `adv` against `idealSecurityImpl … mode` starting from
the initial game state. -/
def idealSecurityExp
    (mode : ℕ → Bool) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode) adv).run'
    (Reduction.Internal.initialGame kem onoff)

omit [SampleableType K] in
/-- Evaluated at state `s`, `idealCorrectnessImpl` coincides with `sckaCorrectnessImpl` instantiated
on `schemeWithDecaps` using the constant lookup `fun _ _ => s.keyB s.stA.t`. -/
private theorem idealCorrectnessImpl_run_eq
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : GameState onoff Sym) :
    (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak t).run s =
      (SCKAScheme.sckaCorrectnessImpl (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak
        (fun _ _ => s.keyB s.stA.t)) t).run s := by
  rcases t with ((((n | u) | u) | n) | n) <;> rfl

omit [SampleableType K] in
/-- Every query of `idealCorrectnessImpl` leaves the `exposed` and `challenged` epoch sets
unchanged. -/
theorem idealCorrectnessImpl_securitySets_eq
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : GameState onoff Sym)
    (res : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      GameState onoff Sym)
    (hres : res ∈ support ((idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak t).run s)) :
    res.2.exposed = s.exposed ∧ res.2.challenged = s.challenged := by
  rw [idealCorrectnessImpl_run_eq] at hres
  exact SCKAScheme.correctnessImpl_securitySets_eq _ t s res hres

omit [SampleableType K] in
/-- Every successor state `res.2` of an ideal correctness query `t` from `s` satisfies
`res.2.nA ≤ s.nA + 1` when `t` is a send query and `res.2.nA ≤ s.nA` otherwise. -/
theorem idealCorrectnessImpl_nA_step
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : GameState onoff Sym)
    (res : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      GameState onoff Sym)
    (hres : res ∈ support ((idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak t).run s)) :
    res.2.nA ≤ s.nA + if SCKAScheme.isSendQuery t then 1 else 0 := by
  rw [idealCorrectnessImpl_run_eq] at hres
  exact SCKAScheme.correctnessImpl_nA_step _ t s res hres

omit [SampleableType K] in
include hEk hCt0 hCt1 in
/-- Assuming the erasure codes are correct, every query of `idealCorrectnessImpl` preserves
`reachableInv`. -/
theorem idealCorrectnessImpl_preserves_reachableInv :
    QueryImpl.PreservesInv (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro t s hs res hres
  rcases t with ((((n | u) | u) | n) | n)
  · exact SCKAScheme.oracleUnif_preservesInv _ n s hs res hres
  · exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos u s hs res hres
  · exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak u s hs res hres
  · exact oracleRecvAIdeal_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0 ecCt1 hCt1
      leak n s hs res hres
  · exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEk ecEk.ec.nchunk_pos
      ecCt0 ecCt1 leak n s hs res hres

end

/-- Two decapsulation functions give equal A-receive computations on a fixed state and
message if they agree on every decapsulation reached by that receive. -/
theorem recvA_eq_of_decaps_agrees [DecidableEq Sym]
    (decaps decaps' : SK → C → Option K)
    (stA : StA onoff Sym) (msg : Message Sym)
    (hdec : ∀ dk ct0 ch ct1 ack,
      stA.dkA = some dk → stA.ct0 = some ct0 →
      msg = (some ch, ack, stA.t, some 1) →
      ecCt1.decode (insert ch stA.lch) = some ct1 →
      decaps dk (onoff.split.symm (ct0, ct1)) = decaps' dk (onoff.split.symm (ct0, ct1))) :
    recvA kem onoff decaps ecCt0 ecCt1 stA msg =
      recvA kem onoff decaps' ecCt0 ecCt1 stA msg := by
  rcases msg with ⟨ch, ack, t, bit⟩
  by_cases ht : t = stA.t
  · subst t
    cases hc : ch with
    | none =>
      cases hct : stA.ct0 <;> simp [recvA, hct]
    | some chunk =>
      cases hb : bit with
      | none =>
        cases hct : stA.ct0 <;> simp [recvA, hct]
      | some bit =>
        fin_cases bit
        · cases hct : stA.ct0 <;> cases hdecode : ecCt0.decode (insert chunk stA.lch) <;>
            simp [recvA, hct, hdecode]
        · cases hct1 : ecCt1.decode (insert chunk stA.lch) with
          | none => cases hct : stA.ct0 <;> simp [recvA, hct, hct1]
          | some ct1 =>
            cases hd : stA.dkA with
            | none => cases hct : stA.ct0 <;> simp [recvA, hd, hct, hct1]
            | some dk =>
              cases hct : stA.ct0 with
              | none => simp [recvA, hd, hct, hct1]
              | some ct0 =>
                have heq := hdec dk ct0 chunk ct1 ack hd hct
                  (by simp [hc, hb]) hct1
                simp [recvA, hd, hct, hct1, heq]
  · have ht' : stA.t ≠ t := Ne.symm ht
    simp [recvA, ht']

include hDet in
/-- Conditions for replacing A's decapsulation by B's recorded key in a game state `s`:

- the online ciphertext erasure code is correct;
- `s` is consistent with a transcript of sampled KEM material (`reachableInv`);
- whenever A's secret key and offline ciphertext, B's online ciphertext, and B's recorded key
  for A's epoch are present, decapsulation of those ciphertext components under that secret
  key returns the recorded key (`CurrentKEMCorrect`). -/
def IdealReceiveConditions
    (s : GameState onoff Sym) : Prop :=
  ecCt1.ec.Correct ∧ reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧
    CurrentKEMCorrect kem onoff hDet s

/-- Suppose the game state `s` satisfies `IdealReceiveConditions`.
If a recorded message from B completes A's online ciphertext, A's decapsulation result equals
B's recorded key for A's current epoch. -/
theorem honest_recvA_decapsulation_eq_recorded [DecidableEq Sym]
    (s : GameState onoff Sym)
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
    (n : ℕ) (s : GameState onoff Sym)
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
    have heq := recvA_eq_of_decaps_agrees kem onoff ecCt0 ecCt1 hDet.decapsDet
      (fun _ _ => s.keyB s.stA.t) s.stA msg
      (honest_recvA_decapsulation_eq_recorded kem onoff hDet ecEk ecCt0 ecCt1
        s hs n msg epoch hentry)
    simp only [SCKAScheme.oracleRecvA, scheme, schemeWithDecaps, StateT.run_bind,
      StateT.run_get, pure_bind, hentry, heq]

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Suppose the game state `s` satisfies `IdealReceiveConditions`.
For every query `t`, the oracles of `G_b` and `I_b` have equal response/state computations
from `s`. -/
theorem securityImpl_eq_ideal_of_current (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : GameState onoff Sym)
    (hs : IdealReceiveConditions kem onoff hDet ecEk ecCt0 ecCt1 s) :
    (SCKAScheme.sckaSecurityImpl b (exposureA (Sym := Sym) kem onoff leak)
      (exposureB (Sym := Sym) kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run s =
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b) t).run s := by
  rw [SCKAScheme.sckaSecurityImpl_eq_securityImplOf]
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s ?_ (fun _ => rfl) t
  intro t
  rcases t with ((((n | u) | u) | n) | n)
  all_goals simp only [idealCorrectnessImpl, SCKAScheme.sckaCorrectnessImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  exact oracleRecvA_eq_ideal kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs

end IdealGame

/-! ## KEM failure probability

The instrumented oracle implementations `trackedSecurityImpl` and `trackedIdealImpl` augment the
states of `G_b` and `I_b` with a boolean failure flag `bad` (initially `false`), which is set to
`true` as soon as `currentKEMFailure` detects completed KEM material whose decapsulation disagrees
with party B's recorded key.

- `V(s) := currentFailurePotential s`: the conditional KEM failure probability of the current
  partially sampled epoch (`0` before sampling begins and after online encapsulation completes).
- `Φ(s, bad) := if bad then 1 else V(s)` (`trackedFailureScore`): the supermartingale score used to
  bound the probability of setting `bad`.
-/

section FailureProbability

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

include hDet in
/-- The security oracle implementation of `G_b` augmented with a boolean flag recording whether a
KEM decapsulation failure has occurred. -/
def trackedSecurityImpl (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (GameState onoff Sym × Bool)
        ProbComp) :=
  trackedImpl
    (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
    (currentKEMFailure kem onoff hDet)

/-- Discarding the failure flag after running `trackedSecurityImpl` gives the same computation
as the security oracles of `G_b`, including the adversary's output and final game state.
This holds for any initial state and flag. -/
theorem trackedSecurity_run_project (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (p : GameState onoff Sym × Bool) :
    -- Run with tracking from `p = (s, bad)`, then discard the final flag:
    -- `Prod.map id Prod.fst` maps `(a, (s', bad'))` to `(a, s')`.
    Prod.map id Prod.fst <$>
        (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run p
      =
      -- Run the real game from `s = p.1`, retaining its output and final state.
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
        (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run p.1 :=
  OracleComp.tracked_run_project _ _ adv p

/-- Once the failure flag is set, every tracked successor has it set. -/
theorem trackedSecurityImpl_preserves_bad (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (fun p => p.2 = true) := by
  intro t p hp res hres
  unfold trackedSecurityImpl trackedImpl StateT.run at hres
  rw [mem_support_bind_iff] at hres
  obtain ⟨y, _, hres⟩ := hres
  obtain rfl := (mem_support_pure_iff _ _).mp hres
  simp [hp]

include hEk hCt0 hCt1 in
/-- Assume the three erasure codes are correct. Every query of `trackedSecurityImpl` preserves
`trackedInv`: either `bad = true`, or `reachableInv` holds and `currentKEMFailure` is false. -/
theorem trackedSecurityImpl_preserves (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1) := by
  apply OracleComp.trackedImpl_preserves _ _ (reachableInv kem onoff ecEk ecCt0 ecCt1)
  intro t s hreach hfail res hres
  have hc := currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
    s hreach hfail
  exact securityImpl_preserves_reachableInv kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak b t s hreach hc res hres

/-- In any state `s` satisfying `reachableInv s` and `currentKEMFailure s = false`, executing party
A's instrumented leaking-send oracle from `(s, false)` increases the expected failure score
`trackedFailureScore` by at most `factorCorrectnessError kem onoff`. -/
theorem tracked_sendArleak_score_le (b : Bool)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    wp
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendArleak).run (s, false))
      (fun res => trackedFailureScore kem onoff res.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change wp (do
    let y ← (SCKAScheme.oracleSendArleak vulnRleakA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, wp_map, Function.comp_def]
  apply SCKAScheme.oracleSendArleak_wp_le
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
    change wp (do
      let y ← (SCKAScheme.oracleSendA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, wp_map, Function.comp_def] using h

/-- Counterpart of `tracked_sendArleak_score_le` for party B's leaking-send oracle. -/
theorem tracked_sendBrleak_score_le (b : Bool)
    (s : GameState onoff Sym)
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    wp
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendBrleak).run (s, false))
      (fun res => trackedFailureScore kem onoff res.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change wp (do
    let y ← (SCKAScheme.oracleSendBrleak vulnRleakB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, wp_map, Function.comp_def]
  apply SCKAScheme.oracleSendBrleak_wp_le
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
    change wp (do
      let y ← (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, wp_map, Function.comp_def] using h

/-- For any state `p` satisfying `trackedInv`, executing a query `t` of `trackedSecurityImpl`
increases the expected failure score `Φ` by at most `factorCorrectnessError kem onoff` when `t` is
an ordinary or leaking send query, and does not increase `E[Φ]` otherwise. -/
theorem trackedSecurity_score_step_le (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (p : GameState onoff Sym × Bool)
    (hp : trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p) :
    wp ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b t).run p)
      (fun res => trackedFailureScore kem onoff res.2) ≤
      trackedFailureScore kem onoff p +
        if SCKAScheme.sckaSecuritySpec.isSendQuery t then factorCorrectnessError kem onoff
        else 0 := by
  by_cases hbad : p.2 = true
  · refine (wp_le_const_of_support (c := 1) _ fun res _ => ?_).trans ?_
    · exact trackedFailureScore_le_one kem onoff res.2
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
    apply wp_le_const_of_support _
    intro res hres
    change res ∈ support (do
      let y ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) _).run p.1
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) at hres
    rw [mem_support_bind_iff] at hres
    obtain ⟨y, hy, hres⟩ := hres
    simp only [mem_support_pure_iff] at hres
    subst res
    let J := fun s : GameState onoff Sym =>
      currentKEMFailure kem onoff hDet s = false ∧
      currentFailurePotential kem onoff s = currentFailurePotential kem onoff p.1
    have hj : J p.1 := ⟨hgood.2, rfl⟩
    suffices hout : J y.2 by
      exact le_of_eq (by simp [trackedFailureScore, hout.1, hout.2])
  · apply SCKAScheme.oracleChall_preservesInv b J ?_ t p.1 hj y hy
    intro state challenged hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptA_preservesInv (vulnCorrA kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptB_preservesInv (vulnCorrB kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate

include hEk hCt0 hCt1 in
/-- Assuming the erasure codes are correct, for every bit `b` and SCKA adversary `adv` satisfying
`SecuritySendQueryBound adv q`, the tracked execution of `G_b` from `(initialGame, false)`
satisfies `Pr[bad_final = true] ≤ q · ε`, where `bad_final` is its final failure flag. -/
theorem kem_failure_probability_le (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    Pr{let res ← ((simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run
        (initialGame (Sym := Sym) kem onoff, false))}[res.2.2 = true] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  have hpres := trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0
    ecCt1 hCt1 leak b
  have hinit := tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1
    ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos
  have hscore₀ : trackedFailureScore kem onoff
      (initialGame (Sym := Sym) kem onoff, false) = 0 := by
    simp [trackedFailureScore, currentFailurePotential, initialGame, initialA, initialB,
      SCKAScheme.initGameState, Option.map₂]
  have hbound := OracleComp.tracked_bad_le_of_score_step
    (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
    (currentKEMFailure kem onoff hDet) (reachableInv kem onoff ecEk ecCt0 ecCt1)
    (trackedFailureScore kem onoff) (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
    (factorCorrectnessError kem onoff)
    (by intro p hp; simp [trackedFailureScore, hp]) hpres
    (trackedSecurity_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    adv q hq (initialGame kem onoff) hinit
  simpa only [trackedSecurityImpl, hscore₀, zero_add, factorCorrectnessError_eq] using hbound

end FailureProbability

/-! ## Comparison bound -/

section ComparisonBound

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

include hDet in
/-- The oracle implementation of the ideal game `I_b` augmented with the same boolean failure flag
update as `trackedSecurityImpl`. -/
def trackedIdealImpl (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (GameState onoff Sym × Bool) ProbComp) :=
  trackedImpl (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b))
    (currentKEMFailure kem onoff hDet)

/-- The version of `trackedSecurity_run_project` for the ideal game `I_b`:
discarding the failure flag recovers the ideal execution, for any initial state and flag. -/
theorem trackedIdeal_run_project (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (p : GameState onoff Sym × Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ (trackedIdealImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run p =
      (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b))
        adv).run p.1 :=
  OracleComp.tracked_run_project _ _ adv p

/-- The real game `G_b` equals the security-oracle simulation from `initialGame`,
projected to the adversary's output. -/
theorem securityExpFixedBit_eq_run' (b : Bool)
    (adv : SecurityAdversary leak Sym) :
    SCKAScheme.securityExpFixedBit (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
      (exposureA kem onoff leak) (exposureB kem onoff leak) =
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
        (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run' (initialGame kem onoff) := by
  simp [SCKAScheme.securityExpFixedBit, scheme, initKeyGen, initA, initB,
    initialGame, initialA, initialB, StateT.run'_eq, map_eq_bind_pure_comp]

include hEk hCt0 hCt1 in
/-- Assuming the erasure codes are correct, for every bit `b` and SCKA adversary `adv` satisfying
`SecuritySendQueryBound adv q`, that is, making at most `q` ordinary and leaking send queries,
the real game `G_b` and ideal game `I_b` satisfy
`|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`. -/
theorem security_correctness_endpoint_le (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    |(Pr{let x ← (SCKAScheme.securityExpFixedBit
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b
        (exposureA kem onoff leak) (exposureB kem onoff leak))}[x = true]).toReal -
      (Pr{let x ← (idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak
        (fun _ => b) adv)}[x = true]).toReal| ≤
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
      unfold left right trackedSecurityImpl trackedIdealImpl trackedImpl StateT.run
      rw [heq]
  have hbound := abs_prEvent_simulateQ_run_sub_le_bad_of_inv left right Inv
    (fun p => p.2 = true)
    (trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak b)
    (trackedSecurityImpl_preserves_bad kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    hagree adv (fun guess => guess = true) (s₀, false)
    (tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
  have hl : Pr{let x ← (SCKAScheme.securityExpFixedBit
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv b (exposureA kem onoff leak)
        (exposureB kem onoff leak))}[x = true] =
      Pr{let res ← (simulateQ left adv).run (s₀, false)}[res.1 = true] := by
    rw [securityExpFixedBit_eq_run', StateT.run'_eq, prEvent_map]
    rw [← trackedSecurity_run_project kem onoff hDet ecEk ecCt0 ecCt1 leak b adv (s₀, false),
      prEvent_map]
    rfl
  have hr : Pr{let x ← (idealSecurityExp kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b)
      adv)}[x = true] =
      Pr{let res ← (simulateQ right adv).run (s₀, false)}[res.1 = true] := by
    rw [idealSecurityExp, StateT.run'_eq, prEvent_map]
    rw [← trackedIdeal_run_project kem onoff hDet ecEk ecCt0 ecCt1 leak b adv (s₀, false),
      prEvent_map]
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
