/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Basic
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Deterministic
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Sampling
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.IndepNoise
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.FailureProbability
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Numerical
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Numerical

/-!
# FrodoKEM correctness

A decapsulation failure occurs when honest decapsulation returns a different shared secret
from the one that encapsulation produced. In the random-oracle model, a table of uniformly random
answers replaces SHAKE. In this model, the failure probability, averaged over the table, is at
most `2^-138.7`, `2^-199.6` and `2^-252.5` for sizes 640, 976 and 1344. `[CiC25]` publishes the
same values. The bound holds for FrodoKEM and for eFrodoKEM.

This file restates the theorem of each proof step with `recall`. Lean rejects a `recall` command
if the statement differs from the statement of the theorem. Thus this outline always agrees with
the proofs, which are in the files under `Correctness/`. The FrodoKEM chapter of the docs explains
each step.

## Scope

The bound is an average over the random table. It does not apply to concrete SHAKE, to one fixed
table, or to many encapsulations with one key. The function that makes the public matrix `A` does
not read the table.

## References

* `[CiC25]`, Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
  Communications in Cryptology 2:3, <https://cic.iacr.org/p/2/3/25>.
-/

namespace FrodoKEM

open OracleComp LatticeCrypto
open scoped ENNReal

/-! Step 1: if the noise is small, decoding returns the message. `[CiC25]` proves this for one
entry (§4.1, Lemma 1), and this theorem applies it to each entry of the matrix. -/
recall Decode_Encode_add (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    Decode p (Encode p b + E) = b

/-! Step 2: for each function in place of SHAKE, failure implies large noise. -/
recall KEM.honestFailureProb_le_honestNoiseBadProb {ps : ParameterSet} (ops : Operations ps) :
    KEM.honestFailureProb ops ≤ KEM.honestNoiseBadProb ops

/-! Step 3: the probability of large noise, averaged over all tables, is equal to the probability
of large noise when the five noise matrices are independent samples. -/
recall ROM.honestNoiseBadProb_eq_indepNoise (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestNoiseBadProb ps gen = IndepNoise.noiseBadProb ps

/-! Step 4: the union bound over the `8 × 8` entries of the noise matrix. -/
recall IndepNoise.noiseBadProb_le (ps : ParameterSet) :
    IndepNoise.noiseBadProb ps ≤ 64 * IndepNoise.entryFailureProb ps

/-! Step 5: the distribution of one entry is the `2n`-fold convolution of the distribution of a
product of two errors, convolved once more with the error distribution. -/
recall Certificate.probOutput_entryNoiseExp (ps : ParameterSet) (z : ℤ) :
    Pr{let x ← IndepNoise.entryNoiseExp ps}[x = z] =
      (((ToVCVio.productMeasure
          (FailureCertificate.RoundedConvolution.counts (Certificate.config ps))
          (FailureCertificate.RoundedConvolution.counts (Certificate.config ps))) ^
          (2 * ps.params.n) *
        FailureCertificate.RoundedConvolution.counts (Certificate.config ps)) z :
          ℝ≥0∞) /
        (2 ^ lenChi) ^ (4 * ps.params.n + 1)

/-! Step 6: the Lean kernel bounds this distribution with whole-number arithmetic. -/
recall Certificate.noiseBadProb_le_failureBound (ps : ParameterSet) :
    IndepNoise.noiseBadProb ps ≤ Certificate.failureBound ps

/-! Result: the average failure probability `p` satisfies `p ^ 10 · 2 ^ (10 e) ≤ 1`, that is,
`p ≤ 2 ^ (-e)` for the published exponent `e`. -/
recall ROM.honestFailureProb_tenth_power_le (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestFailureProb ps gen ^ 10 * 2 ^ Certificate.exponentTenths ps ≤ 1

end FrodoKEM
