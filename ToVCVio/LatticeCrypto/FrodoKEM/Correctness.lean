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
## The role of SHAKE in steps 2 and 3

Write `F` for the function that the KEM uses in place of SHAKE. Steps 2 and 3 use three numbers:
* `fail(F)`, the probability of a failure with `F` (`KEM.honestFailureProb`).
* `noise(F)`, the probability of large noise with `F` (`KEM.honestNoiseBadProb`).
* `indep`, the probability of large noise when the five matrices are independent samples
  (`IndepNoise.noiseBadProb`). This number does not depend on any `F`.

Each probability is over the five random inputs (the coins) of the KEM. Steps 2 and 3 prove
different kinds of claim, and the table gives them in order.

| Claim                                            | For which `F`                 | Proof      |
|--------------------------------------------------|-------------------------------|------------|
| For each coin value, failure implies large noise | each `F`                      | step 2     |
| `fail(F) ≤ noise(F)`                             | each `F`                      | step 2     |
| The value of `noise(F)`                          | depends on `F`, can be `1`    | none       |
| The average of `noise(F)` over `F` is `indep`    | `F` is a uniform random table | step 3     |
| The average of `fail(F)` is at most `indep`      | `F` is a uniform random table | steps 2, 3 |
| `fail(SHAKE)` is at most about `indep`           | `F` is SHAKE                  | not proved |

Step 2 is about events. It says that only large noise causes a failure, for each `F`. It does not
say how often the noise is large. That number depends on `F`, so step 2 does not bound it. Step 3
is about this number. It does not compute `noise(F)` for one `F`. It computes the average of
`noise(F)` over all `F`. The last row needs the assumption that SHAKE acts like a random table.

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

This implication holds for each value of the coins and for each `F` and `gen`. Thus, for each
`F`, the failure event is contained in the large-noise event, and `fail(F) ≤ noise(F)`.

Step 2 gives no value for `noise(F)`. For one fixed `F`, the five matrices are not independent
samples, for two reasons:
* The seeds are short. For FrodoKEM-640, `F` expands the 256 bits of `seedSE` to 163,840 bits
  for `S` and `E`. Thus `(S, E)` takes at most `2 ^ 256` values. Independent samples take far
  more values.
* The encryption seed depends on the public key, and thus on `S`, `E` and `A`. Thus `S′`, `E′`
  and `E″` depend on `S` and `E`.

Thus `noise(F)` depends on `F`, and no bound holds for each `F`. For example, an `F` can give the
same error matrices for each input, with `E′ = 0` and the other matrices at their largest
values. Then `S′ E` is large, and `noise(F) = 1`. Step 2 still holds for this `F`: it gives
`fail(F) ≤ 1`.
-/

recall KEM.honestFailureProb_le_honestNoiseBadProb {ps : ParameterSet} (ops : Operations ps) :
    KEM.honestFailureProb ops ≤ KEM.honestNoiseBadProb ops

/-!
## Step 3: in the random-oracle model, the noise is sampled independently

From this step on, `F` is a table `H` of uniformly random answers. For each table `H`, step 2
gives `fail(H) ≤ noise(H)`. Thus the average of `fail(H)` over `H` is at most the average of
`noise(H)` over `H`. This step proves that the average of `noise(H)` is exactly `indep`. It does
not prove that `noise(H)` is near `indep` for one fixed `H`.

In the Lean statements, `ROM.honestFailureProb` and `ROM.honestNoiseBadProb` are these averages.
Each one samples `H` and the coins together.

### Where the proof is

The proof of this step is in four files. The first three paths start at `ToVCVio/`, and the last
path starts at `VCVio/OracleComp/QueryTracking/`.

| File                              | Content                                                     |
|-----------------------------------|-------------------------------------------------------------|
| `Probability/FiniteXOF.lean`      | A general table that answers SHAKE calls                    |
| `…/RandomOracle/Model.lean`       | The table in FrodoKEM, the six kinds of call, their domains |
| `…/RandomOracle/Correctness.lean` | The proof of this step                                      |
| `RandomOracle/EagerTable.lean`    | Lazy sampling equals full-table sampling                    |

Here `…` is `LatticeCrypto/FrodoKEM/Correctness`.

### The table

SHAKE takes an input bit string `x` and a length `n`, and returns `n` bits. The KEM calls SHAKE
with inputs of six lengths only, one for each kind of call (`ROM.inputLength`).

A table `H` (`ToVCVio.FiniteXOF.Table`) gives one bit string of `outputBits` bits to each input
of these six lengths. `outputBits` is the length of the longest stream that the KEM reads, the
encryption-noise stream. The table answers the call `SHAKE(x, n)` with the first `n` bits of
`H(x)` (`ToVCVio.FiniteXOF.answer`). It answers inputs of other lengths with zeros, but the KEM
makes no such call. `ROM.operations ps gen H` is the KEM with this answer function in place of
SHAKE.

There are finitely many tables. `ToVCVio.FiniteXOF.sampleTable` selects one uniformly. This is
the same as an independent uniform choice of each entry. This uniform table is the random oracle.
-/

recall ToVCVio.FiniteXOF.Table (lengths : Finset ℕ) (outBits : ℕ) : Type

recall ToVCVio.FiniteXOF.answer {lengths : Finset ℕ} {O : ℕ}
    (H : ToVCVio.FiniteXOF.Table lengths O) (x : List Bool) (n : ℕ) : Vector Bool n

recall ROM.inputLength (ps : ParameterSet) : ROM.QueryRole → ℕ
  | .seedA => lenZ
  | .keygenNoise => 8 + ps.params.lenSeedSE
  | .publicKeyHash => lenSeedA + ps.params.n * nbar * ps.params.D
  | .seedAndKey => ps.params.ell + ps.params.ell + ps.params.lenSalt
  | .encryptionNoise => 8 + ps.params.lenSeedSE
  | .sharedSecret =>
      mbar * ps.params.n * ps.params.D + mbar * nbar * ps.params.D +
        ps.params.lenSalt + ps.params.ell

recall ROM.operations (ps : ParameterSet) (gen : ROM.Generator ps) (H : ROM.Table ps) :
    Operations ps :=
  { gen := gen
    shake := ToVCVio.FiniteXOF.answer H }

/-!
### The coins and the experiment

"Coins" are the random inputs of an algorithm. The honest KEM samples five coins: the fallback
secret, `seedSE` (`keySeed` in the code), `z`, the message `μ` and the salt. These five coins are
not the five queries below.

`ROM.honestNoiseBadProb` is the following experiment:
1. Select a table `H` uniformly.
2. Select the five coins uniformly.
3. Run key generation and encryption with `H` in place of SHAKE.
4. Check if the noise is large.

The function `gen` that makes the public matrix does not depend on the table.
-/

recall ROM.honestNoiseBadProb (ps : ParameterSet) (gen : ROM.Generator ps) : ℝ≥0∞ :=
  Pr{
    let H ← ToVCVio.FiniteXOF.sampleTable (ROM.inputLengths ps) (ROM.outputBits ps)
    let fallback ← $ᵗ (SharedSecretBits ps)
    let keySeed ← $ᵗ (SeedSEBits ps)
    let z ← $ᵗ (Bits lenZ)
    let message ← $ᵗ (MessageBits ps)
    let salt ← $ᵗ (SaltBits ps)
  }[
    ¬ NoiseBound ps.params
      (PKE.decryptionNoise (ROM.operations ps gen H) keySeed
        (KEM.deriveSeedAndKey (ROM.operations ps gen H)
          (KEM.hashPublicKey (ROM.operations ps gen H)
            (KEM.keygenFromCoins (ROM.operations ps gen H) fallback keySeed z).1)
          message salt).1)
  ]

/-!
### The five queries

When the coins and `H` are fixed, the KEM reads five entries of `H` before the noise is known. The
private program `fixedCoinsProgram` makes these five queries in this order.

| # | Input                    | Depends on                   | Use of the answer              |
|---|--------------------------|------------------------------|--------------------------------|
| 0 | `z`                      | coin `z`                     | `seedA`, then `A = gen(seedA)` |
| 1 | `0x5F ‖ seedSE`          | coin `seedSE`                | `S` and `E`                    |
| 2 | `pk`                     | answers 0 and 1              | `pkh`                          |
| 3 | `pkh ‖ μ ‖ salt`         | answer 2, coins `μ` and salt | the encryption seed            |
| 4 | `0x96 ‖ encryption seed` | answer 3                     | `S′`, `E′` and `E″`            |

A sixth query gives the shared secret. It comes after the noise is known, so it has no effect on
the noise.

### The proof

**(a) Fix the coins.** The coins are independent of `H`. Thus the proof can fix the coins and
take the probability over `H` only. If each value of the coins gives the same number, then the
full experiment gives that number too. The private lemma `five_coin_average` does this last
average.

For fixed coins, the randomness comes from the table only. For a fixed `seedSE`, the entry at
`0x5F ‖ seedSE` is a uniform string, because the table is random. The seed only selects the
entry. Thus the length of the seed has no effect on the result. With a fixed SHAKE and fixed coins,
nothing random is left. Thus this step needs a random table.

**(b) The problem.** For fixed coins, the five matrices are a function of `H` only. Queries 0
and 1 have fixed inputs, so their answers are uniform and independent. The inputs of queries 2, 3
and 4 depend on earlier entries of `H`. An entry at a place that `H` itself selects is not always
uniform. For example, the entry at "the first `x` where `H(x)` starts with 0" always starts
with 0.

**(c) The lazy oracle.** A lazy oracle selects an entry only when the KEM asks for it:
* If the input is new, the oracle selects a uniform answer and records it.
* If the input is not new, the oracle gives the recorded answer again.

A VCVio theorem shows that this oracle gives the same distribution as the full uniform table. An
entry that nobody has read is uniform, if the oracle selects it at the start or later.
-/

recall OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable
    {D R : Type} [DecidableEq D] [SampleableType R] [SampleableType (D → R)] [Finite D]
    {α : Type} [MeasurableSpace α] (oa : OracleComp (D →ₒ R) α) :
    𝒟[(simulateQ OracleSpec.randomOracle oa).run' ∅] =
      𝒟[do let g ← $ᵗ (D → R); pure (evalWithAnswerFn (QueryImpl.ofFn g) oa)]

/-!
**(d) The five inputs are all different.** The kinds of call have different input lengths,
except the two noise calls. These two have the same length, and their first 8 bits `0x5F` and
`0x96` are different (`ROM.domain_disjoint`). Thus each of the five queries is new to the lazy
oracle, and each one gets a new uniform answer. The oracle selects that answer after the input is
known, so the input cannot bias the answer. The private lemma `fiveQueryProgram_run_eq` proves
that the five answers `u₀, …, u₄` are five independent uniform strings.
-/

recall ROM.domain_disjoint (ps : ParameterSet) {r s : ROM.QueryRole} (hrs : r ≠ s)
    (x : List Bool) : ¬ (ROM.InDomain ps r x ∧ ROM.InDomain ps s x)

/-!
**(e) From the five answers to the five matrices.** The matrices use only the prefixes of `u₁`
and `u₄`. A prefix of a uniform string is uniform (`ToVCVio.FiniteXOF.finiteLaw_prefix_uniform`).
The proof cuts `u₁` into `S` and `E`, and `u₄` into `S′`, `E′` and `E″`. The cut is a bijection
(`splitBitsEquiv`), so the parts are uniform and independent
(`ROM.finiteLaw_samplesFromStreams_uniform`).
The answers `u₀`, `u₂` and `u₃` only select later inputs, and the matrices do not use them.
-/

recall ToVCVio.FiniteXOF.finiteLaw_prefix_uniform (O n : ℕ) (h : n ≤ O) :
    ToVCVio.finiteLaw ((fun v => ToVCVio.FiniteXOF.prefix v n) <$> ($ᵗ (Vector Bool O))) =
      ToVCVio.finiteLaw ($ᵗ (Vector Bool n))

/-!
**(f) The result.** For each value of the coins, the five matrices have the distribution of
`IndepNoise.sampleNoise` (`ROM.finiteLaw_samplesFromCoins`). This experiment samples the five
matrices independently. Thus each value of the coins gives the probability
`IndepNoise.noiseBadProb ps`, and by (a) the full experiment gives the same value. Step 2 then
gives the bound on the failure probability of the KEM.
-/

recall ROM.finiteLaw_samplesFromCoins
    (ps : ParameterSet) (gen : ROM.Generator ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    ToVCVio.finiteLaw
      ((fun H => ROM.samplesFromCoins ps gen H fallback keySeed z message salt) <$>
        ToVCVio.FiniteXOF.sampleTable (ROM.inputLengths ps) (ROM.outputBits ps)) =
      ToVCVio.finiteLaw (IndepNoise.sampleNoise ps)

recall ROM.honestNoiseBadProb_eq_indepNoise (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestNoiseBadProb ps gen = IndepNoise.noiseBadProb ps

recall ROM.honestFailureProb_le_indepNoiseBadProb (ps : ParameterSet) (gen : ROM.Generator ps) :
    ROM.honestFailureProb ps gen ≤ IndepNoise.noiseBadProb ps

/-!
### Comparison with the paper

`[CiC25]` does not prove steps 2 and 3.
* Section 4.1 computes the failure probability of FrodoPKE. It assumes that each entry of the
  noise is "the sum of 2n products of two independent samples from χ, and one more independent
  sample". Steps 4 to 6 formalize this computation.
* Section 5 states that "the failure probability δ of FrodoKEM is the same as the failure
  probability of the underlying FrodoPKE". It gives no proof. In the KEM, SHAKE computes the
  errors from seeds that depend on each other. Thus the errors are not independent samples.
* Section 5.1 models the uses of SHAKE as independent random oracles. It uses domain separation,
  by input length and by the bytes `0x5F` and `0x96`, to make "each distinct use of SHAKE"
  independent.

Steps 2 and 3 close the gap in Section 5 with the model of Section 5.1. There is one difference.
This proof uses one table with domain separation, not independent oracles. It then proves that
the domain separation makes the answers independent. The paper assumes this.
-/

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
