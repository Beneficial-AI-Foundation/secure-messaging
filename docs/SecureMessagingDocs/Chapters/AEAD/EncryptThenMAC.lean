import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.SymEnc.Defs
import SecureMessaging.AEAD.FromEtM.Construction
import SecureMessaging.AEAD.FromEtM.Correctness
import SecureMessaging.AEAD.FromEtM.Security

/-! # Blueprint chapter: Encrypt-then-MAC -/

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

#doc (Manual) "Encrypt-then-MAC" =>

*References:*

- {Informal.citet Ros26}[] — computational one-time secrecy (Definition 5.3.2) and the
  encrypt-then-MAC construction (Construction 9.5.1).
- {Informal.citet NRS14}[] — the security theorem for the encrypt-then-MAC scheme A5
  (Theorem 1, bound in Figure 9) and its proof (Lemma 3, Appendix A.2), which the Lean proof
  follows.
- {Informal.citet ACD19}[] — the target notion: one-time IND-CCA security of AEAD
  (Definition 1, Figure 1, Definition 2). ACD19 uses AEAD as a building block and does not
  construct it.

:::group "aead_encrypt_then_mac"
Encrypt-then-MAC.
:::

:::defTitle "aead_etm_det_se" "Deterministic symmetric encryption"
:::

:::::::definition "aead_etm_det_se" (parent := "aead_encrypt_then_mac") (lean := "DetSEAlg, DetSEAlg.Correct, DetSEAlg.LengthRegular")
Adapted from {Informal.citet Ros26}[], Definitions 2.5.1 (syntax) and 2.5.2 (correctness).
There, the key is uniform on the key space, $`\mathsf{Enc}` may be randomized, and
$`\mathsf{Dec}` always returns a message. Here, $`\mathsf{SE.KeyGen}` samples the key,
$`\mathsf{SE.Enc}` is deterministic, and $`\mathsf{SE.Dec}` can return $`\bot`. Length
regularity is from {Informal.citet NRS14}[], Section 2.

A deterministic symmetric encryption scheme $`\mathsf{SE}` is a tuple of algorithms
$`(\mathsf{SE.KeyGen}, \mathsf{SE.Enc}, \mathsf{SE.Dec})` with key space $`\mathcal K`,
message space $`\mathcal M` and ciphertext space $`\mathcal C`, where

- $`\mathsf{SE.KeyGen}` samples a key $`K \in \mathcal K`,
- $`\mathsf{SE.Enc}` takes a key $`K` and a message $`m`, and produces a ciphertext
  $`c \gets \mathsf{SE.Enc}(K, m)`,
- $`\mathsf{SE.Dec}` takes a key $`K` and a ciphertext $`c`, and produces a message
  $`m \gets \mathsf{SE.Dec}(K, c)`, or $`\bot`.

$`\mathsf{SE.Enc}` and $`\mathsf{SE.Dec}` are deterministic. Each ciphertext $`c` has a
length $`|c|`, and the ciphertexts of each length form a finite nonempty set, so that the
security game can sample from it uniformly. $`\mathsf{SE}` is correct if
$`\mathsf{SE.Dec}(K, \mathsf{SE.Enc}(K, m)) = m` for all keys $`K` and messages $`m`. Let
$`|m|` denote a fixed length function on messages ($`\mathit{lenM}` in Lean). $`\mathsf{SE}`
is length-regular if $`|m| = |m'|` implies $`|\mathsf{SE.Enc}(K, m)| = |\mathsf{SE.Enc}(K', m')|`
for all keys $`K, K'`.

:::leanPillCaption "deterministic symmetric encryption scheme"
:::

```anchor DetSEAlg (project := ".") (module := SecureMessaging.SymEnc.Defs)
structure DetSEAlg (K M C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : ProbComp K
  /-- Deterministic encryption: `Enc(K, M) = C`. -/
  encrypt : K → M → C
  /-- Deterministic decryption: `Dec(K, C) = some M` or `none`. -/
  decrypt : K → C → Option M
```

:::leanPillCaption "correctness"
:::

```anchor DetSEAlgCorrect (project := ".") (module := SecureMessaging.SymEnc.Defs)
def Correct (se : DetSEAlg K M C) : Prop :=
  ∀ (k : K) (m : M), se.decrypt k (se.encrypt k m) = some m
```

:::leanPillCaption "length regularity"
:::

```anchor DetSEAlgLengthRegular (project := ".") (module := SecureMessaging.SymEnc.Defs)
def LengthRegular [LenSampleable C] (lenM : M → ℕ) (se : DetSEAlg K M C) : Prop :=
  ∀ (k k' : K) (m m' : M), lenM m = lenM m' →
    LenSampleable.len (se.encrypt k m) = LenSampleable.len (se.encrypt k' m')
```
:::::::

:::defTitle "aead_etm_det_se_ots" "One-time secrecy"
:::

:::::::definition "aead_etm_det_se_ots" (parent := "aead_encrypt_then_mac") (lean := "DetSEAlg.oracleEncrypt, DetSEAlg.securityExpFixedBit, DetSEAlg.distAdvantage") (uses := "aead_etm_det_se")
Generalizes {Informal.citet Ros26}[], Definition 5.3.2 (computational one-time secrecy). There,
the key is uniform on the key space, and the random ciphertext is uniform on $`\mathcal C`.
Here, the key comes from $`\mathsf{SE.KeyGen}`, and the random ciphertext is uniform among the
ciphertexts of the same length as the real one, as in the $`\$` oracle of
{Informal.citet NRS14}[], Figure 4. With a uniform $`\mathsf{SE.KeyGen}` and ciphertexts of one
length, the two games are the same. With several lengths, the game of Ros26 is undefined if
$`\mathcal C` is infinite, and no padded cipher satisfies it if $`\mathcal C` is finite. The game
here reveals the ciphertext length, so it hides the message only for length-regular schemes.

::::::gameGrid
:::::gameCell "\\textsf{Game state and notation}" (kind := "scheme-notation")
There is one experiment $`\Exp{\textsf{ots}\text{-}b}{\textsf{SE}}` for each bit
$`b \in \bit`. Each call to $`\Oenc` samples a fresh key $`K`. For $`b = 0`, $`\Oenc`
encrypts the message under $`K`. For $`b = 1`, it returns a uniformly random ciphertext of the
same length. The adversary can call $`\Oenc` any number of times.
:::::
::::::

::::::gameGrid
:::::gameCell "\\Oenc(m)" (kind := "compact")
$`\begin{array}{l}
K \gets \mathsf{SE.KeyGen}; \\
\pif\;b = 0\;\pthen \\
\quad c \gets \mathsf{SE.Enc}(K, m); \\
\pelse \\
\quad c \sample \{c' \in \mathcal C : |c'| = |\mathsf{SE.Enc}(K, m)|\}; \\
\Return c
\end{array}`

:::leanPillCaption "encryption oracle"
:::

```anchor detSEOracleEncrypt (project := ".") (module := SecureMessaging.SymEnc.Defs)
def oracleEncrypt [LenSampleable C] (se : DetSEAlg K M C) (b : Bool) :
    QueryImpl (M →ₒ C) ProbComp :=
  fun m => do
    let k ← se.keygen
    if b then LenSampleable.unifSameLen (se.encrypt k m)
    else pure (se.encrypt k m)
```
:::::

:::::gameCell "\\Exp{\\textsf{ots}\\text{-}b}{\\textsf{SE}}(\\adv)" (kind := "compact")
$`\begin{array}{l}
b' \gets \adv^{\Oenc}; \\
\Return b'
\end{array}`

:::leanPillCaption "one-time secrecy experiment"
:::

```anchor detSESecurityExpFixedBit (project := ".") (module := SecureMessaging.SymEnc.Defs)
def securityExpFixedBit [LenSampleable C] (se : DetSEAlg K M C)
    (adversary : OTSAdversary M C) (b : Bool) : ProbComp Bool :=
  simulateQ (otsImpl se b) adversary
```
:::::
::::::

The one-time secrecy advantage of $`\adv` is

$$`\mathsf{Adv}^{\textsf{ots}}_{\textsf{SE}}(\adv)
  = \Bigl|\, \Pr\bigl[\Exp{\textsf{ots}\text{-}1}{\textsf{SE}}(\adv) = 1\bigr]
  - \Pr\bigl[\Exp{\textsf{ots}\text{-}0}{\textsf{SE}}(\adv) = 1\bigr] \,\Bigr|`

:::leanPillCaption "one-time secrecy advantage"
:::

```anchor detSEDistAdvantage (project := ".") (module := SecureMessaging.SymEnc.Defs)
noncomputable def distAdvantage [LenSampleable C] (se : DetSEAlg K M C)
    (adversary : OTSAdversary M C) : ℝ :=
  |(Pr{let x ← securityExpFixedBit se adversary true}[x = true]).toReal -
   (Pr{let x ← securityExpFixedBit se adversary false}[x = true]).toReal|
```

::::::gameGrid
:::::gameCell "\\textsf{Example: one-time pad}" (kind := "scheme-notation")
Let $`n \ge 1`. The one-time pad $`\mathsf{OTP}_n` ({Informal.citet Ros26}[],
Construction 1.2.1) is the deterministic symmetric encryption scheme with
$`\mathcal K = \mathcal M = \mathcal C = \{0,1\}^n`, where

- $`\mathsf{SE.KeyGen}` samples $`K \sample \{0,1\}^n`,
- $`\mathsf{SE.Enc}(K, m) = K \oplus m`,
- $`\mathsf{SE.Dec}(K, c) = K \oplus c`.

$`\mathsf{OTP}_n` is correct, and $`\mathsf{Adv}^{\textsf{ots}}_{\mathsf{OTP}_n}(\adv) = 0`
for every adversary $`\adv`. This is adapted from {Informal.citet Ros26}[], Claim 1.2.3
(correctness) and Claim 2.2.2 (security), for the game we formalize.
:::::
::::::

::::::gameGrid
:::::gameCell "\\textsf{Example: AES-CBC in libsignal}" (kind := "scheme-notation")
Adapted from {Informal.citet Ros26}[], Construction 8.5.3 (CBC mode) with PKCS#7 padding
(Example 8.6.3). There, $`\mathsf{Enc}` samples $`C_0` at random and sends it as the first
block of the ciphertext, and $`\mathsf{Dec}` reads $`C_0` from the
ciphertext. libsignal derives the AES key and the IV from a fresh per-message key, so in the
scheme below the IV is part of the key. In both $`\mathsf{SE.Enc}` and $`\mathsf{SE.Dec}`,
the line $`C_0 \gets \mathit{iv}` replaces this: $`\mathsf{SE.Enc}` does not sample or send
$`C_0`, and $`\mathsf{SE.Dec}` does not read it from the ciphertext.

Let $`\mathsf{AES}_k` be AES-256 under the key $`k \in \{0,1\}^{256}`, a permutation of
$`\{0,1\}^{128}`, and let $`\mathsf{Pad}` be PKCS#7 padding to a multiple of 16 bytes.
AES-CBC is the deterministic symmetric encryption scheme with

- $`\mathcal K = \{0,1\}^{256} \times \{0,1\}^{128}`,
- $`\mathcal M` the byte strings,
- $`\mathcal C = \bigcup_{\ell \ge 1} \{0,1\}^{128 \ell}`, where the length of a ciphertext is
  its number of bits,

where $`\mathsf{SE.KeyGen}` samples $`(k, \mathit{iv}) \sample \mathcal K`, and

$$`\begin{array}{l}
\underline{\mathsf{SE.Enc}((k, \mathit{iv}), m)} \\
M_1 \concat \cdots \concat M_\ell \gets \mathsf{Pad}(m); \\
C_0 \gets \mathit{iv}; \\
\mathsf{for}\; i = 1, \ldots, \ell \\
\quad C_i \gets \mathsf{AES}_k(C_{i-1} \oplus M_i); \\
\Return C_1 \concat \cdots \concat C_\ell
\end{array}
\qquad\qquad
\begin{array}{l}
\underline{\mathsf{SE.Dec}((k, \mathit{iv}), c)} \\
C_1 \concat \cdots \concat C_\ell \gets c; \\
C_0 \gets \mathit{iv}; \\
\mathsf{for}\; i = 1, \ldots, \ell \\
\quad M_i \gets \mathsf{AES}_k^{-1}(C_i) \oplus C_{i-1}; \\
\Return \mathsf{Pad}^{-1}(M_1 \concat \cdots \concat M_\ell)
\end{array}`

Here $`M_i` and $`C_i` are 128-bit blocks, and $`\mathsf{Pad}^{-1}` returns $`\bot` if the
padding is invalid.

Let $`|m|` be the length of $`m` in bytes. Then $`m` becomes
$`\ell = \lfloor |m| / 16 \rfloor + 1` blocks, so the ciphertext has $`128\ell` bits. Its
length depends only on $`|m|`, so the scheme is length-regular. For $`b = 1`, $`\Oenc` returns
a uniformly random string of $`128\ell` bits, the same length as the real ciphertext. The
length depends only on $`|m|`, which the adversary chose, so it is the same for $`b = 0` and
$`b = 1`.

For $`\ell = 1`, let $`P` be the padded block. The map
$`\mathit{iv} \mapsto \mathsf{AES}_k(P \oplus \mathit{iv})` is a bijection for every key $`k`,
so a uniform $`\mathit{iv}` gives an exactly uniform ciphertext. For two or more blocks, the
ciphertext need not be exactly uniform, because AES under $`k` is a fixed permutation and not
a uniform random function. For an adversary that makes one query, with $`k` and
$`\mathit{iv}` sampled uniformly, the standard CBC analysis bounds the advantage by the PRP
advantage of AES plus a collision term of order $`\ell^2 / 2^{128}`. Each query uses a fresh
key, so for $`q` queries a hybrid argument multiplies these terms by $`q`. The reduction
$`\mathcal D` in the security theorem below makes one query. For the pair that libsignal
derives, add the advantage of distinguishing the derivation from uniform. This repository does
not prove these bounds and does not instantiate AES-CBC in Lean.
:::::
::::::
:::::::

:::defTitle "aead_etm_spec" "AEAD encrypt-then-MAC construction"
:::

:::::::definition "aead_etm_spec" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD") (tags := "gh-24") (uses := "aead, aead_etm_det_se, prf")
Adapted from {Informal.citet Ros26}[], Construction 9.5.1, where the tag covers only the
ciphertext. In the construction we formalize, the tag also covers the associated data.

Let $`\mathsf{SE}` be a deterministic symmetric encryption scheme with key space
$`\mathcal K_e` and ciphertext space $`\mathcal C_e`, and let $`F` be a
{bpref "prf"}[PRF] with key space $`\mathcal K_m`, domain
$`\mathcal{AD} \times \mathcal C_e` and range $`\mathcal T`. Then
$`\mathsf{EtM}[\mathsf{SE}, F]` is the {bpref "aead"}[AEAD scheme] with key space
$`\mathcal K_e \times \mathcal K_m`, ciphertext space $`\mathcal C_e \times \mathcal T` and
the algorithms below.

The tag function $`F` must be a PRF (encrypt-then-PRF), not only a MAC, because the
security game compares $`(c, t)` with a uniformly random ciphertext of the same length.

::::::gameGrid
:::::gameCell "\\mathsf{KeyGen}()" (kind := "compact")
$`\begin{array}{l}
K_e \gets \mathsf{SE.KeyGen}; \\
K_m \gets F.\mathsf{keygen}; \\
\Return (K_e, K_m)
\end{array}`
:::::
::::::

::::::gameGrid
:::::gameCell "\\Enc((K_e, K_m), a, m)" (kind := "compact")
$`\begin{array}{l}
c \gets \mathsf{SE.Enc}(K_e, m); \\
t \gets F(K_m, (a, c)); \\
\Return (c, t)
\end{array}`
:::::

:::::gameCell "\\Dec((K_e, K_m), a, (c, t))" (kind := "compact")
$`\begin{array}{l}
\pif\;t \neq F(K_m, (a, c))\;\pthen \\
\quad\Return \bot; \\
\Return \mathsf{SE.Dec}(K_e, c)
\end{array}`
:::::

::::::

:::leanPillCaption "construction $`\\mathsf{EtM}[\\mathsf{SE}, F]`"
:::

```anchor etmAEAD (project := ".") (module := SecureMessaging.AEAD.FromEtM.Construction)
def etmAEAD (se : DetSEAlg K_e M C_e)
    (prf : PRFScheme K_m (AD × C_e) T) :
    AEADScheme ProbComp M AD (K_e × K_m) (C_e × T) where
  keygen := do
    let ke ← se.keygen
    let km ← prf.keygen
    return (ke, km)
  encrypt := fun (ke, km) ad m =>
    let c := se.encrypt ke m
    let t := prf.eval km (ad, c)
    (c, t)
  decrypt := fun (ke, km) ad (c, t) =>
    if t == prf.eval km (ad, c)
    then se.decrypt ke c
    else none
```
:::::::

:::defTitle "aead_etm_correctness" "AEAD encrypt-then-MAC correctness"
:::

::::theorem "aead_etm_correctness" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD_correct") (tags := "gh-25") (uses := "aead_etm_spec, aead_etm_det_se, aead_correctness")
Correctness in the sense of {Informal.citet ACD19}[], Definition 1.

Let $`\mathsf{SE}` be a correct deterministic symmetric encryption scheme and $`F` a PRF.
Then $`\mathsf{EtM}[\mathsf{SE}, F]` is correct.

:::leanPillCaption "correctness theorem"
:::

```anchor etmAEAD_correct (project := ".") (module := SecureMessaging.AEAD.FromEtM.Correctness)
theorem etmAEAD_correct (se : DetSEAlg K_e M C_e)
    (prf : PRFScheme K_m (AD × C_e) T) (hse : se.Correct) :
    (etmAEAD se prf).Correct
```
::::

:::defTitle "aead_etm_security" "AEAD encrypt-then-MAC security"
:::

:::::theorem "aead_etm_security" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD_security, EtM.prfReduction, EtM.encReduction") (tags := "gh-26") (uses := "aead_etm_spec, aead_etm_det_se, aead_etm_det_se_ots, prf, aead_security_exp, aead_dist_advantage, aead_decrypt_query_bound, aead_oracles")
Adapted from {Informal.citet NRS14}[], Theorem 1 for scheme A5 (bound of Figure 9), for
one-time keys without a nonce.

Let $`\mathsf{SE}` be a deterministic symmetric encryption scheme, $`F` a PRF with a finite
range $`\mathcal T`, and $`\adv` a one-time IND-CCA adversary against
$`\mathsf{EtM}[\mathsf{SE}, F]` that makes at most $`q_d`
queries to the decryption oracle $`\Odec` of the {bpref "aead_oracles"}[one-time IND-CCA game].
Then there exist a PRF adversary $`\mathcal B` against $`F` and a one-time secrecy adversary
$`\mathcal D` against $`\mathsf{SE}`, constructed from $`\adv` as in
{Informal.citet NRS14}[], Lemma 3, such that

$$`\mathsf{Adv}^{\textsf{dist}}_{\mathsf{EtM}[\mathsf{SE}, F]}(\adv)
  \le \mathsf{Adv}^{\textsf{prf}}_{F}(\mathcal B)
  + \frac{q_d}{|\mathcal T|}
  + \mathsf{Adv}^{\textsf{ots}}_{\textsf{SE}}(\mathcal D)`

where $`\mathsf{Adv}^{\textsf{dist}}` is the {bpref "aead_dist_advantage"}[distinguishing
advantage] in the {bpref "aead_security_exp"}[one-time IND-CCA game]. In Figure 9 the middle
term is $`q_d / 2^\tau` for $`\tau`-bit tags.

$`\mathcal D` makes at most one encryption query, because it forwards only the challenge
encryption of $`\adv`. So the bound needs one-time secrecy of $`\mathsf{SE}` only against
adversaries that make one query, although the game allows any number of queries.

:::leanPillCaption "security theorem"
:::

```anchor etmAEAD_security (project := ".") (module := SecureMessaging.AEAD.FromEtM.Security)
theorem etmAEAD_security
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (etmAEAD se prf) adv ≤
      (PRFScheme.prfAdvantage prf (prfReduction se adv)).toReal +
      ↑q_d * (Fintype.card T : ℝ)⁻¹ +
      DetSEAlg.distAdvantage se (encReduction se adv)
```

:::leanPillCaption "PRF adversary $`\\mathcal B`"
:::

```anchor etmPrfReduction (project := ".") (module := SecureMessaging.AEAD.FromEtM.Security.Games)
noncomputable def prfReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    : PRFAdversary (AD × C_e) T
```

:::leanPillCaption "one-time secrecy adversary $`\\mathcal D`"
:::

```anchor etmEncReduction (project := ".") (module := SecureMessaging.AEAD.FromEtM.Security.Games)
noncomputable def encReduction
    (_se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    : DetSEAlg.OTSAdversary M C_e
```
:::::
