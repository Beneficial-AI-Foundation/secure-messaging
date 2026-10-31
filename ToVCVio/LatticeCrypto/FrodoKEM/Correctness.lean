/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Basic
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Deterministic
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Sampling
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Ideal
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.FailureProbability
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Numerical
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Numerical

/-!
# FrodoKEM correctness

A decapsulation failure occurs when honest decapsulation returns a different shared secret
from the one that encapsulation produced. This module bounds the probability of a failure for
the three FrodoKEM families. The bound uses a random-oracle model, in which a table of uniformly
random answers replaces SHAKE. The bounds are `2^-138.7`, `2^-199.6` and `2^-252.5` for
FrodoKEM-640, -976 and -1344. `[CiC25]` publishes the same values.

The proof has six steps, and each section below gives one step. Each section ends with `recall`
commands that restate its main theorems. Lean rejects a `recall` command if the statement differs
from the statement of the theorem. Thus the outline always agrees with the proofs.

The proofs are in the files under `Correctness/`. The algorithms are in the parent directory.
-/

namespace FrodoKEM

open OracleComp LatticeCrypto
open scoped ENNReal

/-!
## Step 1: small noise does not change the decoded message

Encoding puts the `2 ^ B` possible chunk values at equal distances around `ZMod q`. Decoding
rounds to the nearest of these values. If the added noise is less than half the distance,
decoding returns the original chunk. This is Lemma 1 of Section 4.1 of `[CiC25]`.

`dc_ec_add` proves this result for one entry, and `Decode_Encode_add` proves it for a matrix.
The noise condition has no division: `-q ≤ 2 ^ (B + 1) · e < q`. Here `e` is the noise as an
integer between `-q/2` and `q/2`.
-/

recall Decode_Encode_add (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    Decode p (Encode p b + E) = b

/-!
## Step 2: decapsulation fails only when the noise is large

Honest decryption computes the encoded message plus the noise matrix `S′ E + E″ - E′ S`. Key
generation and encryption sample the secret and error matrices in this sum. If the noise satisfies
the condition of step 1, decryption returns the message. Encryption of that message then gives
the same ciphertext again, and decapsulation returns the honest shared secret.

Thus a failure is at most as probable as large noise. This step uses no property of SHAKE.
-/

recall KEM.honestFailureProb_le_honestNoiseBadProb {ps : ParameterSet} (ops : Operations ps) :
    KEM.honestFailureProb ops ≤ KEM.honestNoiseBadProb ops

/-!
## Step 3: in the random-oracle model, the noise is sampled independently

From this step on, a table of uniformly random answers replaces SHAKE (`ROM.operations`).
Before the noise is known, the KEM reads five entries of the table. These five inputs differ in
length or in prefix, so each answer is a new uniform bit string. Two of these answers go to the
error sampler.

The proof cuts these two answers at the matrix boundaries. The five noise matrices that result
have the joint distribution of five independent samples (`ROM.finiteLaw_samplesFromCoins`).
The ideal experiment `Ideal.noiseBadProb` samples the five matrices independently. Thus, on
average over the table, large noise has the same probability as in the ideal experiment.
-/

recall ROM.honestNoiseBadProb_eq_ideal (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestNoiseBadProb ps gen = Ideal.noiseBadProb ps

/-!
## Step 4: from the noise matrix to one entry

The noise matrix has `8 × 8 = 64` entries. As an integer, each entry has the distribution of
`Ideal.entryNoiseExp`. This distribution is two sums of `n` products of independent errors,
plus one more error.

The noise is large only if an entry is outside the interval `[-threshold, threshold)`. The union
bound gives the result: the probability for the matrix is at most 64 times the probability for
one entry.
-/

recall Ideal.noiseBadProb_le (ps : ParameterSet) :
    Ideal.noiseBadProb ps ≤ 64 * Ideal.entryFailureProb ps

/-!
## Step 5: the exact distribution of one entry

One sampled error has the value `z` with probability `noiseCount z / 2 ^ 16`
(`probOutput_sampleError`). The error distribution is symmetric. Thus the subtraction of a
product has the same distribution as the addition of a product. One entry is the sum of `2n`
independent products of two errors, plus one more error.

A counting measure gives the number of inputs for each integer value. The distribution of one
entry is a power of a counting measure, divided by `2 ^ (16 · (4n + 1))`.
-/

recall Certificate.probOutput_entryNoiseExp (ps : ParameterSet) (z : ℤ) :
    Pr{let x ← Ideal.entryNoiseExp ps}[x = z] =
      (((ToVCVio.productMeasure
          (FailureCertificate.RoundedConvolution.counts (Certificate.config ps))
          (FailureCertificate.RoundedConvolution.counts (Certificate.config ps))) ^
          (2 * ps.params.n) *
        FailureCertificate.RoundedConvolution.counts (Certificate.config ps)) z :
          ℝ≥0∞) /
        (2 ^ lenChi) ^ (4 * ps.params.n + 1)

/-!
## Step 6: a computed bound on one entry

The exact distribution of step 5 has too many terms to compute. `RoundedConvolution` computes
an approximate distribution with two changes:
* After each of the `2n` steps, it rounds each count down to the fixed-point precision `p`.
* It removes the mass outside a window of width `2w + 1` around zero.

Rounding down never increases a count (`lowerCounts_domination`). The proof counts all removed
mass as failure. Thus the probability of a large entry is at most `v₁ / 2 ^ (p + 16) + v₂ / 2 ^ p`
(`probEvent_le_certificate`). Here `v₁` is the approximate mass outside the decoding interval,
and `v₂` is the total removed mass.

The computation keeps a distribution in one natural number, with each count in its own block of
bits. Thus one step is one multiplication, one shift and one mask. `ClosedForm.lean` proves that
the long sums for the mask and the failure weights equal short geometric-series formulas.

For each family, one `decide +kernel` command then computes `(v₁, v₂)`. It runs all `2n` steps
in the Lean kernel. The proof stores no precomputed values. It does not use `native_decide` or
additional axioms.
-/

recall Certificate.certificate640 :
    FailureCertificate.RoundedConvolution.certificateValues
      (Certificate.config .FrodoKEM640) (Certificate.badWeight .FrodoKEM640) =
        (10891243206164296039, 4220411)

recall Certificate.noiseBadProb_le_failureBound (ps : ParameterSet) :
    Ideal.noiseBadProb ps ≤ Certificate.failureBound ps

/-!
## Result

Steps 2 to 6 together bound the failure probability of the KEM in the random-oracle model.
The second theorem compares the bound with the published exponents. It raises the two sides to
the tenth power. Thus a bound such as `2^-138.7` becomes a comparison of whole numbers.
-/

recall ROM.honestFailureProb_le_failureBound (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestFailureProb ps gen ≤ Certificate.failureBound ps

recall ROM.honestFailureProb_tenth_power_le (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestFailureProb ps gen ^ 10 * 2 ^ Certificate.exponentTenths ps ≤ 1

/-!
## Scope

* The bound is an average over the random table that replaces SHAKE. The bound does not apply
  to concrete SHAKE, to one fixed table, or to many encapsulations with one key.
* The function that makes the public matrix `A` does not depend on the table.
* `Certificate.pkeFailureProb_le_failureBound` gives the same bound for FrodoPKE with
  independently sampled errors. It applies to each message and each public matrix.
-/

end FrodoKEM
