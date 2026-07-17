import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.KEM.OnOffKEM.Defs
import SecureMessaging.KEM.OnOffKEM.FromKPKE

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

#doc (Manual) "On-Off KEM" =>

:::group "on_off_kem"
Online-Offline Key Encapsulation Mechanism (On-Off KEM).
:::

:::defTitle "on_off_kem_scheme" "On-Off KEM scheme"
:::

::::definition "on_off_kem_scheme" (parent := "on_off_kem") (lean := "KEMScheme.OnOffStructure")
$`\todo`

```anchor OnOffStructure (project := ".") (module := SecureMessaging.KEM.OnOffKEM.Defs)
structure OnOffStructure (kem : KEMScheme m K PK SK C) where
  /-- Offline encapsulation state space. -/
  St : Type
  /-- Offline ciphertext space. -/
  C₀ : Type
  /-- Online ciphertext space. -/
  C₁ : Type
  /-- The ciphertext space splits as `ct = (ct0, ct1)`. -/
  split : C ≃ C₀ × C₁
  /-- Offline encapsulation `Enc.Off`: key-independent, returns a state and `ct0`. -/
  encapsOff : m (St × C₀)
  /-- Online encapsulation `Enc.On`: from the state and `pk`, returns `ct1` and the shared key. -/
  encapsOn : St → PK → m (C₁ × K)
  /-- For every public key, `kem.encaps` is equal to first running `encapsOff`,
  then running `encapsOn st pk`. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (st, c0) ← encapsOff
    let (c1, k) ← encapsOn st pk
    pure (split.symm (c0, c1), k))
```

{githubLabel}`github` {githubIssue 40}[]
::::

:::defTitle "on_off_kem_rand_leak" "On-Off KEM randomness leakage"
:::

::::definition "on_off_kem_rand_leak" (parent := "on_off_kem") (lean := "KEMScheme.OnOffRandLeak")

```anchor OnOffRandLeak (project := ".") (module := SecureMessaging.KEM.OnOffKEM.Defs)
structure OnOffRandLeak (kem : KEMScheme m K PK SK C)
    (onoff : kem.OnOffStructure) where
  /-- Randomness space for key generation. -/
  KeygenRand : Type
  /-- Randomness space for offline encapsulation. -/
  OffRand : Type
  /-- Randomness space for online encapsulation. -/
  OnRand : Type
  /-- Key generation together with the randomness used to sample the key pair. -/
  keygenRleak : m ((PK × SK) × KeygenRand)
  /-- Offline encapsulation together with its randomness. -/
  encapsOffRleak : m ((onoff.St × onoff.C₀) × OffRand)
  /-- Online encapsulation together with its randomness. -/
  encapsOnRleak : onoff.St → PK → m ((onoff.C₁ × K) × OnRand)
  /-- First component: ordinary key generation is the first component of
  `keygenRleak`. -/
  keygen_fst :
    (do
      let out ← keygenRleak
      pure out.1) = kem.keygen
  /-- First component: ordinary offline encapsulation is the first component of
  `encapsOffRleak`. -/
  encapsOff_fst :
    (do
      let out ← encapsOffRleak
      pure out.1) = onoff.encapsOff
  /-- First component: ordinary online encapsulation is the first component of
  `encapsOnRleak st pk`. -/
  encapsOn_fst : ∀ st pk,
    (do
      let out ← encapsOnRleak st pk
      pure out.1) = onoff.encapsOn st pk
```

{usesLabel}`uses` {uses "on_off_kem_scheme"}[]
::::

:::group "on_off_kem_on_off_kem_from_ml_kem"
On-Off KEM from ML-KEM.
:::

:::defTitle "on_off_kem_kpke" "Kyber PKE (K-PKE)"
:::

:::::::definition "on_off_kem_kpke" (parent := "on_off_kem_on_off_kem_from_ml_kem") (lean := "MLKEM.KPKE.keygenFromSeed, MLKEM.KPKE.encrypt, MLKEM.KPKE.decrypt")
The IND-CPA public-key encryption underlying ML-KEM (Kyber). Operations are in
$`R_q = \mathbb{Z}_q[X]/(X^{256}+1)`; a hat denotes the NTT domain, $`\hat{A}` (seed $`\rho`) is the
public matrix, and the noise $`y, e_1, e_2` is expanded from a 32-byte seed $`\mathsf{coins}`.

::::::gameGrid
:::::gameCell "\\KeyGen" (kind := "compact")
$`\begin{array}{l}
\KeyGen(): \\
\quad s, e \sample R_q^k \\
\quad \hat{s}, \hat{e} \gets \mathsf{NTT}(s), \mathsf{NTT}(e) \\
\quad \hat{t} \gets \hat{A}\,\hat{s} + \hat{e} \\
\quad \Return (\mathsf{ek} = \hat{t},\ \mathsf{dk} = \hat{s})
\end{array}`
:::::

:::::gameCell "\\Enc" (kind := "compact")
$`\begin{array}{l}
\Enc(\hat{t}, m): \\
\quad \text{sample } \mathsf{coins} \pcomment{y, e_1, e_2} \\
\quad \hat{y} \gets \mathsf{NTT}(y) \\
\quad u \gets \mathsf{NTT}^{-1}(\hat{A}^{\top}\hat{y}) + e_1 \pcomment{\ctzero} \\
\quad v \gets \mathsf{NTT}^{-1}(\langle \hat{t}, \hat{y}\rangle) + e_2 + \mathsf{Decompress}_1(\mathsf{Decode}_1(m)) \pcomment{\ctone} \\
\quad \Return (u, v)
\end{array}`
:::::

:::::gameCell "\\Dec" (kind := "compact")
$`\begin{array}{l}
\Dec(\hat{s}, (u, v)): \\
\quad w \gets v - \mathsf{NTT}^{-1}(\langle \hat{s}, \mathsf{NTT}(u)\rangle) \\
\quad \Return \mathsf{Compress}_1(w) \pcomment{\approx m}
\end{array}`
:::::
::::::
:::::::

:::defTitle "on_off_kem_kem_from_kpke" "KEM from K-PKE"
:::

:::::::definition "on_off_kem_kem_from_kpke" (parent := "on_off_kem_on_off_kem_from_ml_kem") (lean := "KPKEOnOff.scheme")
A KEM built from K-PKE: fix $`\rho` (so $`\hat{A}` is shared by all key pairs) and encapsulate a
uniformly random message $`m` as the shared key.

::::::gameGrid
:::::gameCell "\\KeyGen" (kind := "compact")
$`\begin{array}{l}
\KeyGen(): \\
\quad \Return (\mathsf{ek} = \hat{t},\ \mathsf{dk} = \hat{s}) \pcomment{\text{K-PKE},\ \rho \text{ fixed}}
\end{array}`
:::::

:::::gameCell "\\Encaps" (kind := "compact")
$`\begin{array}{l}
\Encaps(\mathsf{ek}): \\
\quad m \sample \{0,1\}^{256} \pcomment{\text{shared key}} \\
\quad \mathsf{ct} \gets \Enc(\mathsf{ek}, m) \pcomment{\mathsf{ct} = (\ctzero, \ctone)} \\
\quad \Return (\mathsf{ct},\ m)
\end{array}`
:::::

:::::gameCell "\\Decaps" (kind := "compact")
$`\begin{array}{l}
\Decaps(\mathsf{dk}, \mathsf{ct}): \\
\quad \Return \Dec(\mathsf{dk}, \mathsf{ct})
\end{array}`
:::::
::::::

:::leanPillCaption "the KEM: `keygen`, `encaps = KPKE.encrypt`, `decaps`"
:::

```anchor schemeFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def scheme :
    KEMScheme ProbComp Message encoding.EncodedTHat encoding.EncodedTHat
      (encoding.EncodedU × encoding.EncodedV) where
  keygen := keygen params encoding ring prims rho
  encaps ek := do
    let coins ← $ᵗ Coins
    let msg ← $ᵗ Message
    let ct := KPKE.encrypt ring encoding prims
      ({ tHatEncoded := ek, rho := rho } : KPKE.PublicKey params encoding) msg coins
    pure ((ct.uEncoded, ct.vEncoded), msg)
  decaps := decaps params encoding ring prims
```

{usesLabel}`uses` {uses "on_off_kem_kpke"}[]
:::::::

:::defTitle "on_off_kem_from_ml_kem_spec" "On-off instance from K-PKE"
:::

:::::::definition "on_off_kem_from_ml_kem_spec" (parent := "on_off_kem_on_off_kem_from_ml_kem") (lean := "KPKEOnOff.onOff")
The online-offline structure (Def. 2.1 of {Informal.citet SCKA25}[]) for the K-PKE KEM:
$`\ctzero` is computed offline, independent of $`\mathsf{ek}`, and $`\ctone` online. The Lean proof
`onOff.factor` establishes $`\Encaps.\mathsf{On}\circ\Encaps.\mathsf{Off} = \Encaps` (i.e.
$`\mathsf{KPKE.Enc}`), so the split is faithful.

::::::gameGrid
:::::gameCell "\\Encaps.\\mathsf{Off}" (kind := "compact")
$`\begin{array}{l}
\Encaps.\mathsf{Off}(): \\
\quad \text{sample } \mathsf{coins} \\
\quad \hat{y} \gets \mathsf{NTT}(y) \\
\quad u \gets \mathsf{NTT}^{-1}(\hat{A}^{\top}\hat{y}) + e_1 \pcomment{\ctzero} \\
\quad \Return (u,\ \stct = (\mathsf{coins}, \hat{y}))
\end{array}`
:::::

:::::gameCell "\\Encaps.\\mathsf{On}" (kind := "compact")
$`\begin{array}{l}
\Encaps.\mathsf{On}(\stct, \mathsf{ek} = \hat{t}): \\
\quad m \sample \{0,1\}^{256} \pcomment{\text{shared key}} \\
\quad v \gets \mathsf{NTT}^{-1}(\langle \hat{t}, \hat{y}\rangle) + e_2 + \mathsf{Decompress}_1(\mathsf{Decode}_1(m)) \pcomment{\ctone} \\
\quad \Return (v,\ m)
\end{array}`
:::::
::::::

:::leanPillCaption "`factor` proves `Enc.On ∘ Enc.Off = Enc` (hence `KPKE.encrypt`)"
:::

```anchor onOffFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def onOff : (scheme params encoding ring prims rho).OnOffStructure where
  St := Coins × TqVec params.k
  C₀ := encoding.EncodedU
  C₁ := encoding.EncodedV
  split := Equiv.refl (encoding.EncodedU × encoding.EncodedV)
  encapsOff := encapsOff params encoding ring prims rho
  encapsOn := encapsOn params encoding ring prims
  factor ek := by
    simp only [scheme, encapsOff, encapsOn, KPKE.encrypt, bind_assoc, pure_bind,
      Equiv.refl_symm, Equiv.coe_refl, id_eq]
```

{usesLabel}`uses` {uses "on_off_kem_scheme"}[] · {uses "on_off_kem_kem_from_kpke"}[] · {githubLabel}`github` {githubIssue 41}[]
:::::::
