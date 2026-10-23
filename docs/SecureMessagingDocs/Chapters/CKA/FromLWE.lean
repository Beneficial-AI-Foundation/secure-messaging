import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromLWE.Construction
import SecureMessaging.CKA.FromLWE.Correctness
import SecureMessaging.CKA.FromLWE.ChallengeCorrectness

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
Let $`\varepsilon` be the probability that their keys differ in the first honest exchange.
The definition `lweCKA.firstExchangeFailureProb` measures disagreement in any entry of the complete key.

The experiment samples the public base matrix uniformly.
Each secret and error entry follows the chosen noise distribution independently.
The historical instances use the exact discrete distributions D1 through D4 from {Informal.citet BCDMNNRS16}[].
The construction does not use the optional public-message truncation from that paper.

A completed exchange consists of a send and its matching receive.
The condition `lweCKA.HasExchangeBound` requires at most $`T` completed exchanges in every possible final state.
It counts exchanges with $`\min(t_A,t_B)`, where the two counters record each party's progress.
A final send without its matching receive is allowed and does not increase this count.

Under this condition, the probability that the correctness game reports failure satisfies

$$`\Pr[\,\textsf{correctnessExp} = \mathsf{false}\,] \leq \min(1,T\varepsilon).`


For the historical Challenge parameters and exact D1 sampling, $`\varepsilon \leq 316050145969/2^{80}`.
The theorem `lweCKA.correctness_failure_challenge_le` substitutes this value into the game bound.
The four historical parameter sets have the following upper bounds on $`\varepsilon`.

| Parameter set | Noise distribution | Upper bound |
| --- | --- | --- |
| Challenge | D1 | $`316050145969 / 2^{80}` |
| Classical | D2 | $`7484474965163 / 2^{80}` |
| Recommended | D3 | $`571563876524 / 2^{80}` |
| Paranoid | D4 | $`20431578738799 / 2^{80}` |

Each bound gives a game failure bound of $`\min(1,T\varepsilon)`.
The other three game theorems are `lweCKA.correctness_failure_classical_le`,
`lweCKA.correctness_failure_recommended_sharp_le`, and `lweCKA.correctness_failure_paranoid_le`.
The sharper Recommended bound keeps the older theorem available under its original name.
These exact bounds are not the rounded estimates shown in the original paper.


Perfect correctness means that keys agree with probability one.
The bound above allows a positive failure probability, so it does not establish the perfect correctness requirement of {Informal.citet ACD19}[].
::::

:::defTitle "cka_from_lwe_security" "CKA from LWE security"
:::

::::theorem "cka_from_lwe_security" (parent := "cka_cka_from_lwe") (tags := "gh-14") (uses := "cka_from_lwe_spec, cka_security")
$`\todo`

:::leanPill "missing"
:::
::::
