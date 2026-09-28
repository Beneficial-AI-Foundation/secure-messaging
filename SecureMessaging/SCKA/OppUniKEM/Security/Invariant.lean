/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.SendA
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.SendB
import SecureMessaging.SCKA.Security.Leakage
import SecureMessaging.SCKA.Security.Exposure
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.RecvA
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant.RecvB

/-!
# Correctness-transcript preservation in the security game

**Predicates.** `TranscriptConsistent T s` relates the sampled KEM material
in transcript `T` to state `s`, its message history, and its key tables.
`reachableInv s` asserts existence of such a transcript. `CurrentKEMCorrect s`
asserts agreement of decapsulation and encapsulation for the current
completed epoch.

**Result.** Given correct erasure codes and deterministic decapsulation,
for every challenge bit `b`, query `t`, state `s` satisfying both predicates,
and supported response/state pair `(a, s')`, `reachableInv s'` holds.

**Proof.** Ordinary queries use the correctness preservation lemmas. Leaking
sends use their coin-forgetting marginals. Changes to `exposed` and
`challenged` preserve transcript consistency. `Tracked` records violations
of `CurrentKEMCorrect` with a persistent failure flag.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- Changing only the exposed and challenged epoch sets preserves the same
honest transcript, including all key, chunk, and epoch consistency facts. -/
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

/-- The correctness reachability invariant is independent of security-game
bookkeeping: replacing exposed/challenged sets retains its transcript witness. -/
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

/-- The set of previously exposed epochs is disjoint from the set of
successfully challenged epochs. Failed queries change neither set. -/
def exposureInv {StA StB I Rho : Type} (s : SCKAScheme.GameState StA StB I Rho) : Prop :=
  Disjoint s.exposed s.challenged

/-- The initial exposed and challenged sets are empty and hence disjoint. -/
theorem exposureInv_init {StA StB I Rho : Type} (stA : StA) (stB : StB) :
    exposureInv (SCKAScheme.initGameState (I := I) (Rho := Rho) stA stB) := by
  simp [exposureInv, SCKAScheme.initGameState]

/-- A's leaking-send oracle preserves the existing correctness transcript.
The proof uses the key-generation marginal law and the ordinary-send
preservation theorem; rejected sends retain the old transcript. -/
theorem oracleSendArleak_preserves_reachableInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleSendArleak sendExposureA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  apply SCKAScheme.oracleSendArleak_preservesInv
  · exact sendArleak_forget kem onoff ecEk leak
  · intro s exposed hs
    simpa using reachableInv_with_security_bookkeeping hs exposed s.challenged
  · exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos

/-- B's leaking-send oracle preserves the same correctness transcript as
its ordinary send. Offline, online, and combined sampling use their
marginal laws, including the deterministic retransmission branch. -/
theorem oracleSendBrleak_preserves_reachableInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleSendBrleak sendExposureB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  apply SCKAScheme.oracleSendBrleak_preservesInv
  · exact sendBrleak_forget kem onoff ecCt0 ecCt1 leak
  · intro s exposed hs
    simpa using reachableInv_with_security_bookkeeping hs exposed s.challenged
  · exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak

/-- Assume correct erasure codes. For every fixed bit, security query,
and state `s` satisfying `reachableInv` and `CurrentKEMCorrect`, every
supported successor state satisfies `reachableInv`. -/
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
    reachableInv kem onoff ecEk ecCt0 ecCt1 z.2 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · exact oracleUnif_preserves_reachableInv kem onoff ecEk ecCt0 ecCt1 n s hs z hz
    · exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
        ecEk.ec.nchunk_pos () s hs z hz
    · exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
        ecCt1 ecCt1.ec.nchunk_pos leak () s hs z hz
    · exact oracleRecvA_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0
        ecCt1 hCt1 ecCt1.ec.nchunk_pos leak n s hs hc z hz
    · exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEk ecEk.ec.nchunk_pos
        ecCt0 ecCt1 leak n s hs z hz
  · exact oracleSendArleak_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1
      leak u s hs z hz
  · exact oracleSendBrleak_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1
      leak u s hs z hz
  · apply SCKAScheme.oracleChall_preservesInv b
      (reachableInv kem onoff ecEk ecCt0 ecCt1) ?_ t s hs z hz
    intro state challenged hstate
    simpa using reachableInv_with_security_bookkeeping hstate state.exposed challenged
  · apply SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) ?_ u s hs z hz
    intro state exposed hstate
    simpa using reachableInv_with_security_bookkeeping hstate exposed state.challenged
  · apply SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) ?_ u s hs z hz
    intro state exposed hstate
    simpa using reachableInv_with_security_bookkeeping hstate exposed state.challenged

end oppUniKemCKA
