/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant

/-!
# Opp-BiKEM main invariant: initialisation and the KEM-correctness bridge

The honest initial game state satisfies `GameInv` with the empty transcript. The second half
of the file isolates the only KEM fact the invariant's receive step needs: decapsulation
recovers the encapsulated key on every honestly generated tuple, which follows from perfect
correctness of the KEM.
-/

open OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The transcript with no samples drawn. -/
def Transcript.empty (kem : KEMScheme ProbComp K PK SK C) : Transcript kem :=
  fun _ => EpochTranscript.empty kem

/-- The honest initial game state satisfies the main invariant with the empty transcript. -/
theorem gameInv_init (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym))) :
    GameInv kem ecEk ecCt (SCKAScheme.initGameState stA stB) := by
  simp only [initA, initB, init, support_pure, Set.mem_singleton_iff] at hA hB
  subst stA
  subst stB
  refine ⟨rfl, Transcript.empty kem, ?_, ?_⟩
  all_goals
    constructor
  all_goals
    simp only [SCKAScheme.initGameState, Transcript.empty, EpochTranscript.empty,
      EpochTranscript.key, BufferConsistent, Acknowledgements.sendingHorizon,
      Role.reqParity, Role.resParity, Role.offset, Finset.mem_insert, Finset.mem_singleton,
      reduceCtorEq, if_true, if_false, List.not_mem_nil, Option.isSome_none, Option.map_none,
      Bool.false_eq_true, implies_true, true_and, Finset.notMem_empty, IsEmpty.forall_iff]
  all_goals try omega
  all_goals try (intro t sk ht; simp at ht)
  all_goals try simp

/-- Decapsulation recovers the encapsulated key on every honestly generated tuple. -/
def DecapsCorrectOnSupport (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps) : Prop :=
  ∀ pk sk c k, (pk, sk) ∈ support kem.keygen → (c, k) ∈ support (kem.encaps pk) →
    hDet.decapsDet sk c = some k

/-- A perfectly correct KEM decapsulates correctly on every honestly generated tuple. -/
theorem decapsCorrectOnSupport_of_perfectlyCorrect [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    DecapsCorrectOnSupport kem hDet := by
  intro pk sk c k hkp henc
  have hone : Pr[= true | kem.CorrectExp] = 1 := hkem
  rw [probOutput_eq_one_iff] at hone
  obtain ⟨-, hsupp⟩ := hone
  by_contra hne
  have hfalse : false ∈ support kem.CorrectExp := by
    unfold KEMScheme.CorrectExp
    rw [mem_support_bind_iff]
    refine ⟨(pk, sk), hkp, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨(c, k), henc, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨hDet.decapsDet sk c, ?_, ?_⟩
    · rw [hDet.decaps_eq]
      simp
    · simp [hne]
  rw [hsupp] at hfalse
  simp at hfalse

end oppBiKemCKA
