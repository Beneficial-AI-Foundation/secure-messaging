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

The random inputs of the KEM are the fallback secret, the seeds `seedSE` and `z`, the message `μ`
and the salt. The KEM samples no matrix. It computes the five matrices from these inputs with
SHAKE:
* `S` and `E` come from `SHAKE(0x5F ‖ seedSE)`.
* The public matrix is `A = gen(SHAKE(z))`. The public key contains `A Sᵀ + E`, and `pkh` is
  `SHAKE(pk)`.
* The encryption seed is the first part of `SHAKE(pkh ‖ μ ‖ salt)`.
* `S′`, `E′` and `E″` come from `SHAKE(0x96 ‖ encryption seed)`.

Honest decryption computes the encoded message plus the noise matrix `S′ E + E″ - E′ S`. If the
noise satisfies the condition of step 1, decryption returns the message. Encryption of that
message then gives the same ciphertext again. Thus decapsulation returns the honest shared secret
(`KEM.decaps_encapsFromCoins_of_noiseBound`).

This result holds for each choice of the random inputs and for any `Gen` and `SHAKE` functions.
Thus a failure is at most as probable as large noise (`KEM.honestNoiseBadProb`).

For a fixed SHAKE, this step does not give the probability of large noise. There are two
problems:
* The seeds are short. For FrodoKEM-640, SHAKE expands the 256 bits of `seedSE` to 163,840 bits
  for `S` and `E`. Thus `(S, E)` takes at most `2 ^ 256` values. Independent samples take far
  more values.
* The encryption seed depends on the public key, and thus on `S`, `E` and `A`. Thus `S′`, `E′`
  and `E″` depend on `S` and `E`.

No bound holds for every SHAKE. For example, a function in place of SHAKE can give the same
error matrices for each input, with `E′ = 0` and the other matrices at their largest values.
Then `S′ E` is large, and the noise is always large.
-/

recall KEM.honestFailureProb_le_honestNoiseBadProb {ps : ParameterSet} (ops : Operations ps) :
    KEM.honestFailureProb ops ≤ KEM.honestNoiseBadProb ops

/-!
## Step 3: in the random-oracle model, the noise is sampled independently

From this step on, a table `H` of uniformly random answers replaces SHAKE (`ROM.operations`).
The function `gen` that makes the public matrix does not depend on the table. Step 2 holds for
each table, so it also holds on average over the table. The result of this step is about the
average over the table and the random inputs together. It does not apply to one fixed table.

**The randomness comes from the table.** The proof fixes the random inputs of the KEM and takes
the probability over the table only. For a fixed `seedSE`, the entry at `0x5F ‖ seedSE` is a
uniform string, because the table is random. The seed only selects the entry. Thus the length of
the seed has no effect on the result. This step needs a random table: with a fixed SHAKE and fixed
inputs, nothing random is left.

**The proof of this step.** For fixed random inputs, the proof has four parts:
1. The computation of the five matrices is a program that asks five questions of an oracle
   (`fixedCoinsProgram`).
2. A VCVio theorem replaces the full table with a lazy oracle
   (`evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable`). The lazy oracle gives a new
   uniform answer to each new input, and it remembers that answer. The two oracles give the same
   distribution.
3. Only the first two inputs are fixed. The other three depend on earlier answers. For example,
   `pkh` depends on the public key. But the five inputs of one run are all different. They
   differ in length, or, for the two noise queries, in their first 8 bits (`ROM.domain_disjoint`).
   Thus the lazy oracle gives five independent uniform answers. An earlier answer selects where
   the oracle looks, but the value at that place is new.
4. Each query reads only a prefix of its answer, and a prefix of a uniform string is uniform
   (`ToVCVio.FiniteXOF.finiteLaw_prefix_uniform`). The proof cuts answer 2 into `S` and `E`, and
   answer 5 into `S′`, `E′` and `E″`. The cut is a bijection (`splitBitsEquiv`), so the parts are
   uniform and independent. The other three answers only select later inputs.

Thus the five matrices have the distribution of `IndepNoise.sampleNoise`
(`ROM.finiteLaw_samplesFromCoins`). This experiment samples the five matrices independently. Each
choice of the random inputs gives the same probability `IndepNoise.noiseBadProb ps`. Thus the
average over the random inputs has the same value.
-/

recall ROM.honestNoiseBadProb_eq_indepNoise (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestNoiseBadProb ps gen = IndepNoise.noiseBadProb ps

recall ROM.honestFailureProb_le_indepNoiseBadProb (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestFailureProb ps gen ≤ IndepNoise.noiseBadProb ps

/-!
## Step 4: from the noise matrix to one entry

The noise matrix has `8 × 8 = 64` entries. As an integer, each entry has the distribution of
`IndepNoise.entryNoiseExp`. This distribution is two sums of `n` products of independent errors,
plus one more error.

The noise is large only if an entry is outside the interval `[-threshold, threshold)`. The union
bound gives the result: the probability for the matrix is at most 64 times the probability for
one entry.
-/

recall IndepNoise.noiseBadProb_le (ps : ParameterSet) :
    IndepNoise.noiseBadProb ps ≤ 64 * IndepNoise.entryFailureProb ps

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
    Pr{let x ← IndepNoise.entryNoiseExp ps}[x = z] =
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
    IndepNoise.noiseBadProb ps ≤ Certificate.failureBound ps

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
