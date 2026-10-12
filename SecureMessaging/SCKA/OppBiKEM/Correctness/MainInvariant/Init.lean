/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant

/-!
# Opp-BiKEM-CKA — Initialization

The initial game state satisfies `GameInv`, witnessed by the empty transcript (`gameInv_init`).
-/

open OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The transcript with no samples drawn. -/
def Transcript.empty (kem : KEMScheme ProbComp K PK SK C) : Transcript kem :=
  fun _ => EpochTranscript.empty kem

/-- Every initial game state, built from outputs of `initA` and `initB`, satisfies `GameInv`,
witnessed by the empty transcript. -/
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

end oppBiKemCKA
