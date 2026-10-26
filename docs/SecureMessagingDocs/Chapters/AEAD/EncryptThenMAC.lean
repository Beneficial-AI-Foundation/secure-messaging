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

- {Informal.citet NRS14}[] — ivE schemes and their security (Section 2), the construction
  (Figure 2, scheme A5) and its security (Theorem 1, Lemma 3, Appendix A.2, bound in
  Figure 9).
- {Informal.citet ACD19}[] — the target notion: one-time IND-CCA security of AEAD
  (Definition 1, Figure 1, Definition 2). ACD19 uses AEAD as a building block and does not
  construct it.

:::group "aead_encrypt_then_mac"
Encrypt-then-MAC.
:::

:::defTitle "aead_etm_det_se" "Deterministic symmetric encryption"
:::

:::::::definition "aead_etm_det_se" (parent := "aead_encrypt_then_mac") (lean := "DetSEAlg, DetSEAlg.Correct, DetSEAlg.LengthRegular, DetSEAlg.oracleEncrypt, DetSEAlg.securityExpFixedBit, DetSEAlg.distAdvantage")
Adapted from {Informal.citet NRS14}[], Section 2 (ivE schemes).

A deterministic symmetric encryption scheme $`\mathsf{SE}` is a tuple of algorithms
$`(\mathsf{SE.KeyGen}, \mathsf{SE.Enc}, \mathsf{SE.Dec})` with key space $`\mathcal K_e`,
message space $`\mathcal M` and ciphertext space $`\mathcal C_e`, where

- $`\mathsf{SE.KeyGen}` samples a key $`K_e \in \mathcal K_e`,
- $`\mathsf{SE.Enc}` takes a key $`K_e` and a message $`m`, and produces a ciphertext
  $`c \gets \mathsf{SE.Enc}(K_e, m)`,
- $`\mathsf{SE.Dec}` takes a key $`K_e` and a ciphertext $`c`, and produces a message
  $`m \gets \mathsf{SE.Dec}(K_e, c)`, or $`\bot`.

$`\mathsf{SE.Enc}` and $`\mathsf{SE.Dec}` are deterministic. Each ciphertext $`c` has a
length $`|c|`, and the ciphertexts of each length can be sampled uniformly (`LenSampleable`).
$`\mathsf{SE}` is correct if $`\mathsf{SE.Dec}(K_e, \mathsf{SE.Enc}(K_e, m)) = m` for all
keys $`K_e` and messages $`m`. Let $`|m|` be a message length. $`\mathsf{SE}` is
length-regular if $`|m| = |m'|` implies $`|\mathsf{SE.Enc}(K_e, m)| = |\mathsf{SE.Enc}(K_e', m')|`
for all keys $`K_e, K_e'`.

```anchor DetSEAlg (project := ".") (module := SecureMessaging.SymEnc.Defs)
structure DetSEAlg (K M C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : ProbComp K
  /-- Deterministic encryption: `Enc(K, M) = C`. -/
  encrypt : K → M → C
  /-- Deterministic decryption: `Dec(K, C) = some M` or `none`. -/
  decrypt : K → C → Option M
```

```anchor DetSEAlgCorrect (project := ".") (module := SecureMessaging.SymEnc.Defs)
def Correct (se : DetSEAlg K M C) : Prop :=
  ∀ (k : K) (m : M), se.decrypt k (se.encrypt k m) = some m
```

```anchor DetSEAlgLengthRegular (project := ".") (module := SecureMessaging.SymEnc.Defs)
def LengthRegular [LenSampleable C] (lenM : M → ℕ) (se : DetSEAlg K M C) : Prop :=
  ∀ (k k' : K) (m m' : M), lenM m = lenM m' →
    LenSampleable.len (se.encrypt k m) = LenSampleable.len (se.encrypt k' m')
```

::::::gameGrid
:::::gameCell "\\textsf{Deviations from ivE schemes}" (kind := "scheme-notation")
In {Informal.citet NRS14}[], an ivE scheme encrypts under a key and an initialization vector
(IV), and the adversary makes many encryption queries. Here each key encrypts one message, so
the scheme takes no IV and the game answers at most one encryption query. The security notion
stays ind$-style: as in {Informal.citet NRS14}[], the adversary must tell real ciphertexts
from uniformly random ones of the same length. For length-regular schemes, this is stronger
than left-or-right indistinguishability on messages of equal length.
:::::

:::::gameCell "\\textsf{Game state and notation}" (kind := "scheme-notation")
The game state consists of the key $`K_e`, the challenge bit $`b` and the flag
$`\mathsf{used}`, which records whether $`\Oenc` already answered. For $`b = 0`, $`\Oenc`
encrypts. For $`b = 1`, it returns a uniformly random ciphertext of the same length.

The bit $`b \in \bit` is a fixed parameter of the experiment
$`\Exp{\textsf{ind\$}\text{-}b}{\textsf{SE}}`, not a sampled bit. The experiment returns
the adversary's output $`b'`, and the advantage below compares the experiments for $`b = 0`
and $`b = 1`.

In the oracle, $`\req\varphi` means: if $`\varphi` is false, the oracle returns $`\bot`
and the game state does not change. The adversary also has access to uniform randomness.
:::::
::::::

::::::gameGrid
:::::gameCell "\\Oenc(m)" (kind := "compact")
$`\begin{array}{l}
\req\;\neg\mathsf{used}; \\
\mathsf{used} \gets \mathsf{true}; \\
\pif\;b = 0\;\pthen \\
\quad c \gets \mathsf{SE.Enc}(K_e, m); \\
\pelse \\
\quad c \sample \{c' \in \mathcal C_e : |c'| = |\mathsf{SE.Enc}(K_e, m)|\}; \\
\Return c
\end{array}`

```anchor detSEOracleEncrypt (project := ".") (module := SecureMessaging.SymEnc.Defs)
def oracleEncrypt [LenSampleable C] (se : DetSEAlg K M C) (b : Bool) (k : K) :
    QueryImpl (M →ₒ Option C) (StateT Bool ProbComp) :=
  fun m => do
    if (← get) then pure none
    else do
      set true
      let c ← if b
        then liftM (LenSampleable.unifSameLen (se.encrypt k m))
        else pure (se.encrypt k m)
      return some c
```
:::::

:::::gameCell "\\Exp{\\textsf{ind\\$}\\text{-}b}{\\textsf{SE}}(\\adv)" (kind := "game")
$`\begin{array}{l}
K_e \gets \mathsf{SE.KeyGen}; \\
\mathsf{used} \gets \mathsf{false}; \\
b' \gets \adv^{\Oenc}; \\
\Return b'
\end{array}`

```anchor detSESecurityExpFixedBit (project := ".") (module := SecureMessaging.SymEnc.Defs)
def securityExpFixedBit [LenSampleable C] (se : DetSEAlg K M C)
    (adversary : IndCPAAdversary M C) (b : Bool) : ProbComp Bool := do
  let k ← se.keygen
  let (b', _) ← (simulateQ (indCPAImpl se b k) adversary).run false
  return b'
```
:::::
::::::

The one-time IND$-CPA advantage of $`\adv` is

$$`\mathsf{Adv}^{\textsf{ind\$}}_{\textsf{SE}}(\adv)
  = \Bigl|\, \Pr\bigl[\Exp{\textsf{ind\$}\text{-}1}{\textsf{SE}}(\adv) = 1\bigr]
  - \Pr\bigl[\Exp{\textsf{ind\$}\text{-}0}{\textsf{SE}}(\adv) = 1\bigr] \,\Bigr|`

```anchor detSEDistAdvantage (project := ".") (module := SecureMessaging.SymEnc.Defs)
noncomputable def distAdvantage [LenSampleable C] (se : DetSEAlg K M C)
    (adversary : IndCPAAdversary M C) : ℝ :=
  |(Pr{let x ← securityExpFixedBit se adversary true}[x = true]).toReal -
   (Pr{let x ← securityExpFixedBit se adversary false}[x = true]).toReal|
```

In this definition, $`\mathsf{SE.Dec}` appears only in the correctness condition. The game
gives the adversary an encryption oracle and no decryption oracle, so security does not
depend on $`\mathsf{SE.Dec}`. The encrypt-then-MAC construction calls $`\mathsf{SE.Dec}` only
after the tag check, so a forged ciphertext never reaches it.

::::::gameGrid
:::::gameCell "\\textsf{Example: one-time pad}" (kind := "scheme-notation")
Let $`\mathcal K_e = \mathcal M = \mathcal C_e = \{0,1\}^n`, let $`\mathsf{SE.KeyGen}`
sample $`K_e` uniformly, and let $`\mathsf{SE.Enc}(K_e, m) = K_e \oplus m` and
$`\mathsf{SE.Dec}(K_e, c) = K_e \oplus c`. The scheme is correct. The adversary
chooses $`m` before it sees anything that depends on $`K_e`, so $`m` is independent of
$`K_e`. For a fixed $`m`, the map $`K \mapsto K \oplus m` is a bijection on $`\{0,1\}^n`,
so $`\Pr[K_e \oplus m = c] = \Pr[K_e = c \oplus m] = 2^{-n}` for every $`c`. That is, the
ciphertext $`K_e \oplus m` is uniform on $`\mathcal C_e`. So $`\Oenc` has the same output
distribution for $`b = 0` and $`b = 1`, the experiments
$`\Exp{\textsf{ind\$}\text{-}0}{\textsf{SE}}(\adv)` and
$`\Exp{\textsf{ind\$}\text{-}1}{\textsf{SE}}(\adv)` have the same output distribution, and
$`\mathsf{Adv}^{\textsf{ind\$}}_{\textsf{SE}}(\adv) = 0` for every $`\adv`.
:::::

:::::gameCell "\\textsf{Example: AES-CBC in libsignal}" (kind := "scheme-notation")
libsignal encrypts each message with AES-256-CBC under a cipher key $`k` and an IV
$`\mathit{iv}`, both derived from a fresh per-message key. The IV is not a separate input,
so the key is the pair $`K_e = (k, \mathit{iv})`, and $`\mathsf{SE.Enc}(K_e, m)` is CBC
encryption of $`m` under $`k` with IV $`\mathit{iv}`. The IV is secret, and the adversary
chooses $`m` before it sees anything that depends on $`K_e`, so $`m` is independent of both
$`k` and $`\mathit{iv}`.

libsignal pads messages with PKCS#7. A message of $`|m|` bytes becomes
$`\ell = \lfloor |m| / 16 \rfloor + 1` blocks, so the ciphertext has $`128\ell` bits. Its
length depends only on $`|m|`, so the scheme is length-regular. For $`b = 1`, $`\Oenc`
returns a uniformly random string of $`128\ell` bits, the same length as the real
ciphertext. The adversary therefore learns $`|m|`, which it chose, and nothing from the
length alone.

The ciphertext is still not exactly uniform as with the one-time pad, because AES under $`k`
is a fixed permutation and not a uniform random function. The standard CBC analysis bounds the
advantage by the PRP advantage of AES plus a collision term of order $`\ell^2 / 2^{128}`.
This repository does not prove that bound and does not instantiate AES-CBC in Lean.
:::::
::::::
:::::::

:::defTitle "aead_etm_spec" "AEAD encrypt-then-MAC construction"
:::

:::::::definition "aead_etm_spec" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD") (tags := "gh-24") (uses := "aead, aead_etm_det_se, prf")
Adapted from {Informal.citet NRS14}[], Figure 2, scheme A5.

Let $`\mathsf{SE}` be a deterministic symmetric encryption scheme with ciphertext space
$`\mathcal C_e`, and let $`F` be a PRF with domain $`\mathcal{AD} \times \mathcal C_e` and
range $`\mathcal T`. The AEAD scheme $`\mathsf{EtM}[\mathsf{SE}, F]` has key space
$`\mathcal K_e \times \mathcal K_m` and ciphertext space $`\mathcal C_e \times \mathcal T`.
$`\mathsf{KeyGen}` samples $`K_e \gets \mathsf{SE.KeyGen}` and $`K_m \gets F.\mathsf{keygen}`
independently and returns $`(K_e, K_m)`. $`\Enc` encrypts the message with $`\mathsf{SE}`,
then computes the tag $`t` with $`F` on the associated data and the ciphertext.

The tag is a PRF, not only a MAC (an unforgeable tag), because the security game compares
the whole ciphertext $`(c, t)` with a uniformly random one of the same length. Unforgeability alone does not
make $`t` look random.

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

::::::gameGrid
:::::gameCell "\\textsf{Deviations from scheme A5}" (kind := "scheme-notation")
Scheme A5 is nonce-based. Its key is $`K \concat L`, where $`K` is the key of the ivE
scheme and $`L` is the key of the PRF from which A5 derives $`F^{\mathsf{iv}}_L` and
$`F^{\mathsf{tag}}_L`. Here $`K_e` plays the role of $`K` and $`K_m` the role of $`L`. Each
key of $`\mathsf{EtM}[\mathsf{SE}, F]` encrypts one message, so we remove the nonce:

- there is no nonce $`N`, and the tag is $`F(K_m, (a, c))`, not $`F^{\mathsf{tag}}_L(N, a, c)`;
- there is no IV: A5 computes the IV as $`F^{\mathsf{iv}}_L(N)`, so here $`F` computes only
  the tag.
:::::
::::::

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
Correctness in the sense of {Informal.citet ACD19}[], Definition 1, for the one-time
adaptation of the scheme A5 of {Informal.citet NRS14}[], Figure 2.

Let $`\mathsf{SE}` be a correct deterministic symmetric encryption scheme and $`F` a PRF.
Then $`\mathsf{EtM}[\mathsf{SE}, F]` is correct.

```anchor etmAEAD_correct (project := ".") (module := SecureMessaging.AEAD.FromEtM.Correctness)
theorem etmAEAD_correct (se : DetSEAlg K_e M C_e)
    (prf : PRFScheme K_m (AD × C_e) T) (hse : se.Correct) :
    (etmAEAD se prf).Correct
```
::::

:::defTitle "aead_etm_security" "AEAD encrypt-then-MAC security"
:::

:::::theorem "aead_etm_security" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD_security") (tags := "gh-26") (uses := "aead_etm_spec, aead_etm_det_se, prf, aead_security_exp, aead_dist_advantage, aead_decrypt_query_bound, aead_oracles")
Adapted from {Informal.citet NRS14}[], Theorem 1 for scheme A5, with the bound of Figure 9.

Let $`\mathsf{SE}` be a deterministic symmetric encryption scheme, $`F` a PRF with a finite
range $`\mathcal T`, and $`\adv` a one-time IND-CCA adversary against
$`\mathsf{EtM}[\mathsf{SE}, F]` that makes at most $`q_d`
queries to the decryption oracle $`\Odec` of the {bpref "aead_oracles"}[one-time IND-CCA game]. Then

$$`\mathsf{Adv}^{\textsf{dist}}_{\mathsf{EtM}[\mathsf{SE}, F]}(\adv)
  \le \mathsf{Adv}^{\textsf{prf}}_{F}(\mathcal B)
  + \frac{q_d}{|\mathcal T|}
  + \mathsf{Adv}^{\textsf{ind\$}}_{\textsf{SE}}(\mathcal D)`

Here $`\mathsf{Adv}^{\textsf{dist}}` is the {bpref "aead_dist_advantage"}[distinguishing
advantage] in the {bpref "aead_security_exp"}[one-time IND-CCA game]. In that game, for
the key $`(K_e, K_m)` and a fixed challenge bit $`b`, $`\Oenc` answers only its first query
$`(a, m)`. It returns $`e^* = \Enc((K_e, K_m), a, m)` for $`b = 0`, and for $`b = 1` a uniformly random
$`e^* = (c, t)` with $`|c| = |\mathsf{SE.Enc}(K_e, m)|` and $`t \in \mathcal T`, and it records the challenge pair
$`(a^*, e^*)`, where $`a^* = a`. For $`b = 0`, $`\Odec` decrypts every query except
$`(a^*, e^*)`. For $`b = 1`, it returns $`\bot`.

The adversaries $`\mathcal B` and $`\mathcal D` run $`\adv` and answer its queries, as in
{Informal.citet NRS14}[], Lemma 3. Both answer only the first $`\Oenc` query, record the
challenge pair $`(a^*, e^*)`, return $`\bot` to the $`\Odec` query $`(a^*, e^*)`, and output
the bit that $`\adv` outputs.

- $`\mathcal B` samples $`K_e`. It answers $`\Oenc(a, m)` with $`(c, t)`, where
  $`c = \mathsf{SE.Enc}(K_e, m)` and $`t` is the answer of its function oracle on $`(a, c)`.
  It answers $`\Odec(a, (c, t))` by checking $`t` with that oracle and then returning
  $`\mathsf{SE.Dec}(K_e, c)`, or $`\bot` if the check fails.
- $`\mathcal D` answers $`\Oenc(a, m)` with $`(c, t)`, where $`c` is the answer of its own
  $`\Oenc` on $`m` and $`t \sample \mathcal T`. It returns $`\bot` to every $`\Odec`
  query.

In Figure 9 the middle term is $`q_d / 2^\tau` for $`\tau`-bit tags.

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
:::::
