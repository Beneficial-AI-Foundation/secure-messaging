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
# Transcript consistency in the security game

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM, and let `s` be a
game state. The predicate `reachableInv s` asserts consistency with a transcript of sampled
KEM material. The predicate `CurrentKEMCorrect s` requires decapsulation to return B's
recorded key whenever the current decapsulation key, ciphertext components, and key are present.

Assume the erasure codes are correct. Every supported successor of a security query from a state
satisfying `reachableInv` and `CurrentKEMCorrect` also satisfies `reachableInv`.
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

/-- Assume the three erasure codes are correct. For every correctness query of `Π` from a
state satisfying `reachableInv` and `CurrentKEMCorrect`, all supported successor states
satisfy `reachableInv`. -/
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

/-- Assume the three erasure codes are correct. For every security query of `Π` from a
state satisfying `reachableInv` and `CurrentKEMCorrect`, all supported successor states
satisfy `reachableInv`. -/
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
    (SCKAScheme.oracleChall_recordsChallenges b) s hs
    (correctnessImpl_preserves_reachableInv_at kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak s hs hc)
    (oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos () s hs)
    (oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak () s hs) t z hz

end oppUniKemCKA
