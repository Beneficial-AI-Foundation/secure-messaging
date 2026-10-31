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

Honest FrodoKEM decapsulation can return a different shared secret from the one encapsulation
produced. This module bounds the probability of that failure for the three FrodoKEM families,
in a model where SHAKE is a random oracle. The bounds are `2^-138.7`, `2^-199.6` and
`2^-252.5` for FrodoKEM-640, -976 and -1344, the values published in `[CiC25]`.

The proof has six steps, one section each below. Each section ends with `recall` commands that
restate its main theorems. Lean checks that each restated theorem exists and has exactly the
statement shown, so the outline cannot drift from the proofs.

All proofs live in the files under `Correctness/`. The algorithms are in the parent directory.
-/

namespace FrodoKEM

open OracleComp LatticeCrypto
open scoped ENNReal

/-!
## Step 1: small noise does not change the decoded message

Encoding spaces the `2 ^ B` possible chunk values evenly around `ZMod q`. Decoding rounds to the
nearest of them, so it returns the original chunk whenever the added noise is less than half the
spacing. This is Lemma 1 of Section 4.1 of `[CiC25]`. `dc_ec_add` proves it for one entry and
`Decode_Encode_add` for a whole matrix. The noise condition is written without division, as
`-q ≤ 2 ^ (B + 1) · e < q`, where `e` is the noise as an integer between `-q/2` and `q/2`.
-/

recall Decode_Encode_add (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    Decode p (Encode p b + E) = b

/-!
## Step 2: decapsulation fails only when the noise is large

When honest decryption runs, it computes the encoded message plus the noise matrix
`S′ E + E″ - E′ S`, built from the secret and error matrices of key generation and
encryption. If that noise satisfies the bound of step 1, decryption returns the message.
Re-encrypting it then gives back the same ciphertext, and decapsulation returns the honest
shared secret. So the failure probability is at most the probability that the noise is too
large. This step uses no property of SHAKE.
-/

recall KEM.honestFailureProb_le_honestNoiseBadProb {ps : ParameterSet} (ops : Operations ps) :
    KEM.honestFailureProb ops ≤ KEM.honestNoiseBadProb ops

/-!
## Step 3: in the random-oracle model, the noise is sampled independently

From here on, SHAKE is replaced by a table of uniformly random answers (`ROM.operations`).
The KEM asks the table five questions before the noise is fixed. Their inputs differ in length
or prefix, so every answer is a fresh uniform string. The two answers that feed the error
sampler are therefore independent uniform bit strings. Cutting them at the matrix boundaries
gives the five noise matrices with exactly the joint distribution of five independent samples
(`ROM.finiteLaw_samplesFromCoins`). Averaging over the table, the probability of large noise
equals that of the ideal experiment `Ideal.noiseBadProb`, where all five matrices are sampled
independently.
-/

recall ROM.honestNoiseBadProb_eq_ideal (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestNoiseBadProb ps gen = Ideal.noiseBadProb ps

/-!
## Step 4: from the noise matrix to one entry

The noise matrix has `8 × 8 = 64` entries. Each one, viewed as an integer, has the
distribution of `Ideal.entryNoiseExp`: two sums of `n` products of independent errors, plus one
more error. The matrix is too noisy only if some entry leaves the interval
`[-threshold, threshold)`, so by the union bound the matrix probability is at most 64 times the
probability for one entry.
-/

recall Ideal.noiseBadProb_le (ps : ParameterSet) :
    Ideal.noiseBadProb ps ≤ 64 * Ideal.entryFailureProb ps

/-!
## Step 5: the exact distribution of one entry

One sampled error takes the value `z` with probability `noiseCount z / 2 ^ 16`
(`probOutput_sampleError`). The error distribution is symmetric, so subtracting a product has
the same effect as adding one. One entry is therefore the sum of `2n` independent products of
two errors and one more error. Its distribution is a power of a counting measure on the
integers, divided by `2 ^ (16 · (4n + 1))`.
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
a rounded version instead:
* after each of the `2n` steps, every count is rounded down to fixed-point precision `p`;
* any mass that leaves a window of width `2w + 1` around zero is dropped.

Rounding down never increases a count (`lowerCounts_domination`), and all dropped mass is
counted as failure. So the probability that one entry is too large is at most
`v₁ / 2 ^ (p + 16) + v₂ / 2 ^ p` (`probEvent_le_certificate`). Here `v₁` is the rounded mass
outside the decoding interval and `v₂` is the total mass dropped.

The computation stores a whole distribution in one natural number, each count in its own block
of bits, so that one convolution step is one multiplication, one shift and one mask.
`ClosedForm.lean` proves that the long sums defining the mask and the failure weights equal
short geometric-series formulas. Each family's numbers `(v₁, v₂)` are then found by a single
`decide +kernel`, which runs all `2n` steps inside Lean's kernel. The proof stores no
precomputed values and uses neither `native_decide` nor extra axioms.
-/

recall Certificate.certificate640 :
    FailureCertificate.RoundedConvolution.certificateValues
      (Certificate.config .FrodoKEM640) (Certificate.badWeight .FrodoKEM640) =
        (10891243206164296039, 4220411)

recall Certificate.noiseBadProb_le_failureBound (ps : ParameterSet) :
    Ideal.noiseBadProb ps ≤ Certificate.failureBound ps

/-!
## Result

Chaining steps 2 to 6 bounds the failure probability of the KEM in the random-oracle model.
The second theorem compares the bound with the published exponents. It raises both sides to
the tenth power, so that a bound like `2^-138.7` becomes a comparison of whole numbers.
-/

recall ROM.honestFailureProb_le_failureBound (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestFailureProb ps gen ≤ Certificate.failureBound ps

recall ROM.honestFailureProb_tenth_power_le (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestFailureProb ps gen ^ 10 * 2 ^ Certificate.exponentTenths ps ≤ 1

/-!
## Scope

* The bound is an average over the random table that stands in for SHAKE. It says nothing
  about concrete SHAKE, about any one fixed table, or about many encapsulations to one key.
* The function that generates the public matrix `A` does not depend on that table.
* `Certificate.pkeFailureProb_le_failureBound` gives the same bound for FrodoPKE with
  independently sampled errors, for every message and public matrix.
-/

end FrodoKEM
