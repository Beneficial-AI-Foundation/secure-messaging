/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Numerical
public import ToVCVio.CryptoFoundations.KeyEncapMech
public import ToVCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# FrodoKEM as a KEM in the random-oracle model

`romKem ps gen` runs the generic FrodoKEM algorithms `KEM.keygenM`, `KEM.encapsM` and
`KEM.decapsM` with `romOperations ps gen`, so every SHAKE call is a query to one hash oracle,
shared by key generation, encapsulation and decapsulation. The oracle `hashSpec ps` maps each
covered input to `outputBits ps` bits, and a call asking for `n` bits reads the first `n` of
them. This matches `FiniteXOF.answer`, so answering the queries from a fixed table `H` gives
exactly the KEM with `operations ps gen H` (`simulateQ_correctnessExperiment`). This follows from
`KEM.mmap_keygenM`, `KEM.mmap_encapsM` and `KEM.mmap_decapsM`, since answering from a table is a
monad morphism that fixes uniform sampling. The public-matrix generator `gen` is a fixed
function, not an oracle.

Run in VCVio's random-oracle runtime `ProbCompRuntime.rom (hashSpec ps)`, the standard correctness
error of `romKem` is `honestFailureProb ps gen` (`romKem_correctnessError`). So `romKem` is
`Certificate.failureBound ps`-correct (`romKem_deltaCorrect`).

The step from the lazily sampled oracle to one uniformly sampled table is
`OracleComp.rom_evalDist_empty_eq_uniformTable`.
-/

@[expose] public section

namespace FrodoKEM.ROM

open OracleComp OracleSpec LatticeCrypto ToVCVio
open scoped ENNReal

/-- The hash oracle: each input whose length is covered gets `outputBits ps` bits. -/
abbrev hashSpec (ps : ParameterSet) :=
  FiniteXOF.Input (inputLengths ps) →ₒ Bits (outputBits ps)

/-- Computations with uniform sampling and access to the hash oracle. -/
abbrev RomComp (ps : ParameterSet) := OracleComp (unifSpec + hashSpec ps)

/-- A SHAKE call asking for `n` bits, made as an oracle query. A covered input is queried and the
first `n` bits of the answer are kept. Any other input gets zeros, as in `FiniteXOF.answer`. -/
def shakeQuery (ps : ParameterSet) (x : List Bool) (n : ℕ) : RomComp ps (Bits n) :=
  if h : x.length ∈ inputLengths ps then
    (fun v => FiniteXOF.«prefix» v n) <$>
      ((hashSpec ps).query (FiniteXOF.encode _ x h) : RomComp ps (Bits (outputBits ps)))
  else pure (Vector.replicate n false)

/-- Answer the hash queries from the fixed table `H`, keeping uniform sampling. -/
abbrev tableImpl (ps : ParameterSet) (H : Table ps) :
    QueryImpl (unifSpec + hashSpec ps) ProbComp :=
  unifFwdAnswerImpl (QueryImpl.ofFn H)

/-- Uniform sampling is unchanged by answering the hash queries from a table. -/
theorem simulateQ_liftM (ps : ParameterSet) (H : Table ps) {α : Type} (mx : ProbComp α) :
    simulateQ (tableImpl ps H) (liftM mx : RomComp ps α) = mx := by
  rw [tableImpl, unifFwdAnswerImpl, QueryImpl.passthrough_add,
    QueryImpl.simulateQ_add_liftM_left, QueryImpl.liftTarget_self, simulateQ_id']

/-- Answered from the table `H`, an oracle SHAKE call returns `FiniteXOF.answer H`. -/
theorem simulateQ_shakeQuery (ps : ParameterSet) (H : Table ps) (x : List Bool) (n : ℕ) :
    simulateQ (tableImpl ps H) (shakeQuery ps x n) = pure (FiniteXOF.answer H x n) := by
  unfold shakeQuery FiniteXOF.answer
  split
  · rw [simulateQ_map, tableImpl, unifFwdAnswerImpl]
    exact congrArg _ (QueryImpl.simulateQ_add_liftM_query_right _ _ _)
  · simp

/-- The operations of FrodoKEM in the random-oracle model: `gen` is fixed, and each SHAKE call is
the oracle query `shakeQuery`. -/
def romOperations (ps : ParameterSet) (gen : Generator ps) : OperationsM (RomComp ps) ps where
  gen := gen
  shake := shakeQuery ps

/-- FrodoKEM as a KEM in the random-oracle model: the generic algorithms `KEM.keygenM`,
`KEM.encapsM` and `KEM.decapsM` run with `romOperations ps gen`, so every SHAKE call is a query
to the one hash oracle `hashSpec ps`, and `gen` is fixed. As in `KEM.asKEMScheme`, decapsulation
always returns `some`. -/
def romKem (ps : ParameterSet) (gen : Generator ps) :
    KEMScheme (RomComp ps) (SharedSecretBits ps)
      (PublicKey ps) (SecretKey ps) (Ciphertext ps) :=
  KEM.asKEMSchemeM (romOperations ps gen)

section tableEquivalence

variable (ps : ParameterSet) (gen : Generator ps) (H : Table ps)

/-- Answering the oracle SHAKE calls from the table `H` turns `romOperations ps gen` into the
deterministic operations `operations ps gen H`. -/
theorem romOperations_map_tableImpl :
    (romOperations ps gen).map (simulateQ' (tableImpl ps H)) =
      (operations ps gen H).toM ProbComp := by
  simp only [OperationsM.map, romOperations, simulateQ_shakeQuery,
    Operations.toM, operations]

/-- Answered from a table, oracle key generation is `KEM.keygen` for that table. -/
theorem simulateQ_keygen :
    simulateQ (tableImpl ps H) (KEM.keygenM (romOperations ps gen)) =
      KEM.keygen (operations ps gen H) := by
  rw [← simulateQ'_apply, KEM.mmap_keygenM _ _ (simulateQ_liftM ps H),
    romOperations_map_tableImpl, KEM.keygen]

/-- Answered from a table, oracle encapsulation is `KEM.encaps` for that table. -/
theorem simulateQ_encaps (pk : PublicKey ps) :
    simulateQ (tableImpl ps H) (KEM.encapsM (romOperations ps gen) pk) =
      KEM.encaps (operations ps gen H) pk := by
  rw [← simulateQ'_apply, KEM.mmap_encapsM _ _ (simulateQ_liftM ps H),
    romOperations_map_tableImpl, KEM.encaps]

/-- Answered from a table, oracle decapsulation is `KEM.decaps` for that table. -/
theorem simulateQ_decaps (sk : SecretKey ps) (c : Ciphertext ps) :
    simulateQ (tableImpl ps H) (KEM.decapsM (romOperations ps gen) sk c) =
      pure (KEM.decaps (operations ps gen H) sk c) := by
  rw [← simulateQ'_apply, KEM.mmap_decapsM, romOperations_map_tableImpl, KEM.decapsM_toM]

/-- Answered from the table `H`, the correctness experiment of `romKem` is the correctness
experiment of FrodoKEM with `operations ps gen H`. -/
theorem simulateQ_correctnessExperiment :
    simulateQ (tableImpl ps H) (romKem ps gen).correctnessExperiment =
      (KEM.asKEMScheme (operations ps gen H)).correctnessExperiment := by
  simp only [KEMScheme.correctnessExperiment, romKem, KEM.asKEMSchemeM, KEM.asKEMScheme,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_keygen, simulateQ_encaps,
    simulateQ_decaps, map_pure]

end tableEquivalence

/-- Any uniform sampler of the tables has the same distribution as `FiniteXOF.sampleTable`. Both are
uniform on a finite type; only the sampler instances differ. -/
theorem uniformSample_evalDistEq_sampleTable (lengths : Finset ℕ) (O : ℕ)
    [SampleableType (FiniteXOF.Table lengths O)] :
    $ᵗ (FiniteXOF.Table lengths O) =ᵈ FiniteXOF.sampleTable lengths O := by
  let : MeasurableSpace (FiniteXOF.Table lengths O) := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  rw [FiniteXOF.sampleTable, SampleableType.evalDist_uniformSample,
    @SampleableType.evalDist_uniformSample _ (SampleableType.ofFintype _)]

/-- In the random-oracle model, the correctness error of `romKem` is the honest failure probability
`honestFailureProb ps gen`. -/
theorem romKem_correctnessError (ps : ParameterSet) (gen : Generator ps) :
    (romKem ps gen).correctnessError (ProbCompRuntime.rom (hashSpec ps)) =
      honestFailureProb ps gen := by
  have hExp : ($ᵗ (Table ps) >>= fun g =>
        simulateQ (tableImpl ps g) (romKem ps gen).correctnessExperiment) =ᵈ
      (FiniteXOF.sampleTable (inputLengths ps) (outputBits ps) >>= fun H =>
        (KEM.asKEMScheme (operations ps gen H)).correctnessExperiment) :=
    EvalDistEq.bind (uniformSample_evalDistEq_sampleTable _ _) fun g => by
      rw [simulateQ_correctnessExperiment]
  rw [KEMScheme.correctnessError_eq_evalDist_false_of_prFail_eq_zero]
  · rw [OracleComp.rom_evalDist_empty_eq_uniformTable]
    rw [hExp.evalDist_eq, ← prEvent_eq_evalDist_singleton, honestFailureProb]
    congr 1
    simp [KEMScheme.correctnessExperiment, KEM.asKEMScheme, map_bind]
  · rw [ProbCompRuntime.prFail, SemanticsVia.prFail, ← ProbCompRuntime.evalDist,
      OracleComp.rom_evalDist_empty_eq_uniformTable, MeasureTheory.measure_univ, tsub_self]

/-- In the random-oracle model, `romKem` is `Certificate.failureBound ps`-correct. -/
-- ANCHOR: frodoKEM_rom_deltaCorrect
theorem romKem_deltaCorrect (ps : ParameterSet) (gen : Generator ps) :
    (romKem ps gen).deltaCorrect (ProbCompRuntime.rom (hashSpec ps))
      (Certificate.failureBound ps)
-- ANCHOR_END: frodoKEM_rom_deltaCorrect
    :=
  (romKem_correctnessError ps gen).trans_le (honestFailureProb_le_failureBound ps gen)

end FrodoKEM.ROM
