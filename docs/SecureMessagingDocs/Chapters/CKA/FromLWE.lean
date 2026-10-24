import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromLWE.Construction
import SecureMessaging.CKA.FromLWE.Correctness
import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.Correctness

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "CKA from LWE" =>

*References:*

- {Informal.citet ACD19}[]. [The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol](https://eprint.iacr.org/2018/1037). EUROCRYPT 2019, §4.1.2.
- {Informal.citet BCDMNNRS16}[]. [Frodo: Take off the ring! Practical, Quantum-Secure Key Exchange from LWE](https://www.douglas.stebila.ca/files/research/papers/CCS-BCDMNNRS16-full.pdf). CCS 2016, §3.2 of the full version dated February 23, 2017.

:::group "cka_cka_from_lwe"
CKA from LWE.
:::

:::defTitle "cka_from_lwe_spec" "CKA from LWE construction"
:::

::::definition "cka_from_lwe_spec" (parent := "cka_cka_from_lwe") (lean := "lweCKA.scheme") (tags := "gh-12") (uses := "cka")
The type `Params` contains four natural-number fields.

:::table +header (align := left)
*
  * Field
  * Symbol
  * Meaning
*
  * `n`
  * $`n`
  * Number of rows and columns in the public base matrix.
*
  * `nbar`
  * $`\bar n`
  * Number of rows and columns in each shared-key matrix.
*
  * `logQ`
  * $`D`
  * Exponent defining the modulus $`q = 2^D`.
*
  * `keyBits`
  * $`B`
  * Number of key bits extracted from each shared-matrix entry.
:::

A parameter record `p : Params` is *well-formed* (`p.WellFormed`) when
$`0 < n`, $`0 < \bar n`, and $`0 < B < D - 1`.

The noise distribution $`χ` assigns probabilities to values in $`\mathbb{Z}_q`, the integers modulo $`q`.
The construction samples each secret and error entry independently from this distribution.
The input `χ : ProbComp (Scalar p)` supplies the sampling procedure. This specification does not fix a particular distribution.

With these inputs, `lweCKA.scheme` defines the construction of {Informal.citet ACD19}[], §4.1.2,
using reconciliation from {Informal.citet BCDMNNRS16}[], §3.2.
Party labels are swapped relative to {Informal.citet ACD19}[] so that A sends first.

:::table +header (align := left)
*
  * Lean type
  * Dimensions
  * Entries
*
  * `BaseMatrix`
  * $`n \times n`
  * Modulo $`q`
*
  * `RightMatrix`
  * $`n \times \bar n`
  * Modulo $`q`
*
  * `LeftMatrix`
  * $`\bar n \times n`
  * Modulo $`q`
*
  * `SharedMatrix`
  * $`\bar n \times \bar n`
  * Modulo $`q`
*
  * `HintMatrix`
  * $`\bar n \times \bar n`
  * One bit
*
  * `Key`
  * $`\bar n \times \bar n`
  * Modulo $`2^B`
:::

The protocol order is: initialization → A sends → B receives → B sends → A receives.
The send and receive cycle then repeats.

Before the first message, the parties share initial material `ik = (baseMatrix, S₀, E₀)`.
It contains the public base matrix `baseMatrix`, the initial secret matrix `S₀`, and the error matrix `E₀`.
The public base matrix is sampled uniformly from $`\mathbb{Z}_q^{n \times n}`.
Every entry of `S₀` and `E₀` is sampled independently from $`χ`.
Both matrices have dimensions $`n \times \bar n`.
The CKA specification does not specify how the parties obtain this shared material.

From these samples, `initA` sets A’s state to `(baseMatrix, baseMatrix * S₀ + E₀)`, ready to send.
The function `initB` sets B’s state to `(baseMatrix, S₀)`, ready to receive.

A sends first. The displayed variant `sendArleak` returns a key, message, next state, and sampled randomness.

```anchor sendArleak (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
/-- Send from party A and also return the sampled matrices as leaked randomness. -/
def sendArleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .aSend baseMatrix pub => do
      let r ← sampleSendACoins p χ
      let nextPub := r.secret * baseMatrix + r.error
      let value := r.secret * pub + r.extra
      return some (extract p value, .fromA nextPub (makeHint p value),
        .aRecv baseMatrix r.secret, .fromA r)
  | _ => pure none
```

B receives A’s message, recovers the key, and updates its state.

```anchor recvB (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
/-- Party B receives A's message. -/
def recvB {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .bRecv baseMatrix secret, .fromA pub hint =>
      some (reconcile p (pub * secret) hint, .bSend baseMatrix pub)
  | _, _ => none
```

B then sends its reply, with fresh randomness.

```anchor sendBrleak (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
/-- Send from party B and also return the sampled matrices as leaked randomness. -/
def sendBrleak {p : Params} (χ : ProbComp (Scalar p)) (st : State p) :
    ProbComp (Option (Key p × Message p × State p × Rand p)) :=
  match st with
  | .bSend baseMatrix pub => do
      let r ← sampleSendBCoins p χ
      let nextPub := baseMatrix * r.secret + r.error
      let value := pub * r.secret + r.extra
      return some (extract p value, .fromB nextPub (makeHint p value),
        .bRecv baseMatrix r.secret, .fromB r)
  | _ => pure none
```

A receives B’s message, recovers the key, and updates its state.

```anchor recvA (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
/-- Party A receives B's message. -/
def recvA {p : Params} (st : State p) (msg : Message p) :
    Option (Key p × State p) :=
  match st, msg with
  | .aRecv baseMatrix secret, .fromB pub hint =>
      some (reconcile p (secret * pub) hint, .aSend baseMatrix pub)
  | _, _ => none
```

A send returns `none` if its state is not ready to send.
A receive returns `none` if its state and message do not match the receiving party.

The displayed variants `sendArleak` and `sendBrleak` return the sampled secret and error matrices.
The ordinary operations `sendA` and `sendB` omit these matrices from their outputs.
The definition `lweCKA.scheme` supplies both send variants, initialization, and receive operations to the CKA interface.

```anchor scheme (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
def scheme (p : Params) (_h : p.WellFormed) (χ : ProbComp (Scalar p)) :
    CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p) where
  initKeyGen := initKeyGen p χ
  initA := fun ik => pure (initA ik)
  initB := fun ik => pure (initB ik)
  sendA := fun st => eraseCoins <$> sendArleak χ st
  sendArleak := sendArleak χ
  recvA := recvA
  sendB := fun st => eraseCoins <$> sendBrleak χ st
  sendBrleak := sendBrleak χ
  recvB := recvB
```

::::

:::defTitle "cka_from_lwe_correctness" "CKA from LWE correctness"
:::

::::theorem "cka_from_lwe_correctness" (parent := "cka_cka_from_lwe") (lean := "lweCKA.correctness_failure_le, lweCKA.correctness_failure_challenge_le") (tags := "gh-13") (uses := "cka_from_lwe_spec, cka_correctness")
Correctness means that the sender and receiver obtain the same key.
We prove a bound on disagreement for one exchange, then extend it to any bounded sequence of exchanges.
The numerical bounds use the four historical parameter sets from the original Frodo key-exchange paper {Informal.citet BCDMNNRS16}[].

Let $`\varepsilon` be the probability that the complete keys differ in the first honest exchange.
This is `lweCKA.firstExchangeFailureProb`, which counts disagreement in any of the 64 key entries.
A completed exchange consists of a send and its matching receive.
If every run completes at most $`T` exchanges, `lweCKA.correctness_failure_le` proves

$$`\Pr[\,\textsf{correctnessExp} = \mathsf{false}\,] \leq \min(1,T\varepsilon).`

The condition `lweCKA.HasExchangeBound` states this limit on completed exchanges.
It counts exchanges with $`\min(t_A,t_B)`, where the two counters record each party's progress.
A final send without its matching receive does not increase this count.
The proof does not assume that failures in different exchanges are independent.

The experiment samples the public base matrix uniformly.
It samples every secret and error entry independently from the noise distribution specified below.
The construction does not use the paper's optional public-message truncation.
These results concern the original 2016 parameters, not later FrodoKEM parameter sets.

The following table gives the dimensions and key sizes from Table 2 of the paper.
Here $`n` is the large matrix dimension and $`q` is the modulus.
Every instance uses an $`8\times8` matrix of key entries.

:::table +header (align := left)
*
  * Parameter set
  * $`n`
  * $`q`
  * Bits per key entry
  * Total key bits
*
  * Challenge
  * 352
  * $`2^{11}`
  * 1
  * 64
*
  * Classical
  * 592
  * $`2^{12}`
  * 2
  * 128
*
  * Recommended
  * 752
  * $`2^{15}`
  * 4
  * 256
*
  * Paranoid
  * 864
  * $`2^{15}`
  * 4
  * 256
:::

The next table specifies the exact noise probabilities from Table 1 of the paper.
Divide each weight by the denominator in its row.
A weight in a $`\pm k` column applies separately to $`+k` and $`-k`.
For example, Challenge samples $`+1` with probability $`61/256` and $`-1` with the same probability.
All integers outside the table have probability zero.

:::table +header (align := left)
*
  * Parameter set
  * Denominator
  * $`0`
  * $`\pm1`
  * $`\pm2`
  * $`\pm3`
  * $`\pm4`
  * $`\pm5`
  * $`\pm6`
*
  * Challenge
  * 256
  * 88
  * 61
  * 20
  * 3
  * 0
  * 0
  * 0
*
  * Classical
  * 4096
  * 1570
  * 990
  * 248
  * 24
  * 1
  * 0
  * 0
*
  * Recommended
  * 4096
  * 1206
  * 919
  * 406
  * 104
  * 15
  * 1
  * 0
*
  * Paranoid
  * 65536
  * 19304
  * 14700
  * 6490
  * 1659
  * 245
  * 21
  * 1
:::

Bounding $`\varepsilon` requires more than substituting these parameters into the exchange theorem.
We connect the executable construction to the exact noise distribution, then bound the chance that reconciliation returns different keys.
Reconciliation is the procedure that converts nearby values into matching keys.
The proof has four parts:

1. Express the difference in one matrix entry as a sum of independent products of secret and error samples, plus one extra error.
2. Count the positions modulo $`q` where that difference causes key disagreement.
   This gives a failure function whose average bounds the probability of disagreement in one entry.
   The proof also accounts for exceptional secret vectors whose entries are all even.
3. Compute a certified bound on that average from the finite noise tables.
   Lean checks the integer calculations and bounds the probability mass lost through rounding.
4. Add the bounds for all 64 entries to bound $`\varepsilon`.
   This union bound does not require independent key entries.

The resulting upper bounds are below.
The approximate powers help compare their sizes. The fractions are the exact bounds proved in Lean.
The final column reproduces the rounded failure figures from Table 2 of the paper.

:::table +header (align := left)
*
  * Parameter set
  * Certified upper bound on $`\varepsilon`
  * Approximate size of our bound
  * Paper's rounded figure
*
  * Challenge
  * $`316050145969 / 2^{80}`
  * $`2^{-41.7986}`
  * $`2^{-41.8}`
*
  * Classical
  * $`7484474965163 / 2^{80}`
  * $`2^{-37.2330}`
  * $`2^{-36.2}`
*
  * Recommended
  * $`571563876524 / 2^{80}`
  * $`2^{-40.9439}`
  * $`2^{-38.9}`
*
  * Paranoid
  * $`20431578738799 / 2^{80}`
  * $`2^{-35.7841}`
  * $`2^{-33.8}`
:::

Thus we match the paper's parameter choices and exact sampling distributions, while providing our own certified bounds under the stated assumptions.
The Classical, Recommended, and Paranoid bounds are numerically smaller than the paper's displayed figures.
The Challenge result needs care because the paper rounds its exponent.
For Challenge, we also bound overlaps between entry failures and prove the two-sided interval

$$`\frac{316048081581}{2^{80}} \leq \varepsilon \leq \frac{316050145969}{2^{80}}.`

Its lower endpoint is strictly greater than the literal real number $`2^{-41.8}`.
The theorem `lweCKA.challenge_lower_strictly_above_paper_literal` proves that comparison.
This does not contradict a rounded estimate, but it prevents treating that displayed number as an exact upper bound for our model.

Each certified upper bound $`U` gives a bound $`\min(1,TU)` for the complete correctness game.
The corresponding theorems are listed below.

:::table +header (align := left)
*
  * Parameter set
  * Lean theorem
*
  * Challenge
  * `lweCKA.correctness_failure_challenge_le`
*
  * Classical
  * `lweCKA.correctness_failure_classical_le`
*
  * Recommended
  * `lweCKA.correctness_failure_recommended_sharp_le`
*
  * Paranoid
  * `lweCKA.correctness_failure_paranoid_le`
:::

Perfect correctness means that keys agree with probability one.
We prove this conditional result in `lweCKA.correctness_of_zero`: if $`\varepsilon=0`, every run with the stated exchange bound succeeds with probability one.
The four historical instances do not satisfy that premise.
Separate proofs exhibit possible samples that cause disagreement, establishing $`\varepsilon>0` for each instance.
These are `lweCKA.firstExchangeFailureProb_challenge_pos`, `lweCKA.firstExchangeFailureProb_classical_pos`,
`lweCKA.firstExchangeFailureProb_recommended_pos`, and `lweCKA.firstExchangeFailureProb_paranoid_pos`.
Thus the concrete result is correctness with a bounded failure probability, rather than perfect correctness as required by {Informal.citet ACD19}[].

::::

:::defTitle "cka_from_lwe_security" "CKA from LWE security"
:::

::::theorem "cka_from_lwe_security" (parent := "cka_cka_from_lwe") (tags := "gh-14") (uses := "cka_from_lwe_spec, cka_security")
$`\todo`

:::leanPill "missing"
:::
::::
