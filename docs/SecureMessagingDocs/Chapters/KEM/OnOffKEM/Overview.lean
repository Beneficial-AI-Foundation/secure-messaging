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
open MLKEM MLKEM.KPKE

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

:::defTitle "on_off_kem_kpke" "Kyber Public-Key Encryption (K-PKE)"
:::

::::::::definition "on_off_kem_kpke" (parent := "on_off_kem_on_off_kem_from_ml_kem") (lean := "MLKEM.KPKE.keygenFromSeed, MLKEM.KPKE.encrypt, MLKEM.KPKE.decrypt, MLKEM.NTTRingOps, MLKEM.Primitives.gKeygen, MLKEM.Primitives.prfEta2, MLKEM.Primitives.publicMatrix, MLKEM.Primitives.sampleVecEta1, MLKEM.Primitives.sampleVecEta2, MLKEM.Concrete.samplePolyCBD, MLKEM.Concrete.compress, MLKEM.Concrete.decompress, MLKEM.Concrete.byteEncode, MLKEM.Concrete.byteDecode")
IND-CPA PKE $`(\KeyGen,\Enc,\Dec)` underlying ML-KEM ({Informal.citet FIPS203}[], §5).

:::::::leanSection "external-kpke"
```Verso.Genre.Manual.InlineLean.lean -show
variable (params : Params)
```

::::::gameGrid
:::::gameCell "\\textsf{Notation and public parameters}" (kind := "compact")
$`\begin{array}{ll}
\Rq = \mathbb{Z}_q[X]/(X^{256}+1) & \text{polynomial ring over } \mathbb{Z}_q \text{ with } q=3329 \\
\Tq & \text{NTT domain} \\
\NTT:\Rq\to\Tq,\ \NTT^{-1}:\Tq\to\Rq & \text{forward and inverse Number-Theoretic Transforms} \\
\hat{x}=\NTT(x)\in\Tq & \text{NTT-domain value} \\
\langle \hat{u},\hat{v}\rangle \in \Tq & \text{vector product for }\hat{u}, \hat{v} \in \Tq^k \\
\end{array}`
:::::

:::::gameCell "\\KeyGen(d\\in\\{0,1\\}^{256})" (kind := "compact")
$`\begin{array}{l}
(\rho, \sigma) \gets G(d) \pcomment{\text{seed expansion}} \\
s \gets \SampleVec_1(\sigma,0) \pcomment{\text{small secret vector}} \\
e \gets \SampleVec_1(\sigma,k) \pcomment{\text{small error vector}} \\
\hat{A} \gets \XOF(\rho) \pcomment{\text{public matrix from seed }\rho} \\
\hat{s}, \hat{e} \gets \NTT(s), \NTT(e) \\
\hat{t} \gets \hat{A}\,\hat{s} + \hat{e} \\
\Return (\ek = (\hat{t},\rho),\ \dk = \hat{s})
\end{array}`

:::leanPillCaption "KeyGen specification in VCVio"
:::

```quotedLean
def keygenFromSeed (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (d : Seed32) :
    PublicKey params encoding × SecretKey params encoding :=
  let (rho, sigma) := prims.gKeygen d
  let aHat := prims.publicMatrix rho
  let s := prims.sampleVecEta1 sigma 0
  let e := prims.sampleVecEta1 sigma params.k
  let sHat := ring.nttVec s
  let eHat := ring.nttVec e
  let tHat := ring.matVecMul aHat sHat + eHat
  ({ tHatEncoded := encoding.byteEncode12Vec tHat, rho := rho },
    { sHatEncoded := encoding.byteEncode12Vec sHat })
```
:::::

:::::gameCell "\\Enc(\\ek=(\\hat{t},\\rho)\\in\\Tq^k\\times\\{0,1\\}^{256},\\ m\\in\\{0,1\\}^{256};\\ \\coins\\in\\{0,1\\}^{256})" (kind := "compact")
$`\begin{array}{l}
y \gets \SampleVec_1(\coins,0) \pcomment{\text{small ephemeral vector}} \\
e_1 \gets \SampleVec_2(\coins,k) \pcomment{\text{small error vector}} \\
e_2 \gets \SamplePoly_2(\coins,2k) \pcomment{\text{small error polynomial}} \\
\hat{A} \gets \XOF(\rho) \pcomment{\text{public matrix from seed }\rho} \\
\hat{y} \gets \NTT(y) \\
u \gets \NTT^{-1}(\hat{A}^{\top}\hat{y}) + e_1 \pcomment{\text{first ciphertext component}} \\
\mu \gets \Embed(m) \pcomment{\text{embed message in }\Rq} \\
v \gets \NTT^{-1}(\langle \hat{t}, \hat{y}\rangle) + e_2 + \mu \pcomment{\text{second ciphertext component}} \\
\ct_0 \gets \Compress(u) \pcomment{\text{compress first component}} \\
\ct_1 \gets \Compress(v) \pcomment{\text{compress second component}} \\
\Return \ct=(\ct_0,\ct_1)
\end{array}`

:::leanPillCaption "Enc specification in VCVio"
:::

```quotedLean
def encrypt (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (ek : PublicKey params encoding) (msg : Message)
    (coins : Coins) : Ciphertext params encoding :=
  let tHat := encoding.byteDecode12Vec ek.tHatEncoded
  let aHat := prims.publicMatrix ek.rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let e2 := prims.prfEta2 coins (2 * params.k)
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  { uEncoded := encoding.byteEncodeDUVec (encoding.compressDU u)
    vEncoded := encoding.byteEncodeDV (encoding.compressDV v) }
```
:::::

:::::gameCell "\\Dec(\\dk=\\hat{s}\\in\\Tq^k,\\ \\ct=(\\ct_0,\\ct_1))" (kind := "compact")
$`\begin{array}{l}
u' \gets \Decompress(\ctzero) \pcomment{\text{recover the }u\text{ component}} \\
v' \gets \Decompress(\ctone) \pcomment{\text{recover the }v\text{ component}} \\
w \gets v' - \NTT^{-1}(\langle \hat{s}, \NTT(u')\rangle) \pcomment{\text{recover the }\Rq\text{ representative of }m} \\
\Return \Recover(w) \pcomment{\text{decode }\Rq\text{ representative back to }\{0,1\}^{256}}
\end{array}`

:::leanPillCaption "Dec specification in VCVio"
:::

```quotedLean
def decrypt (ring : NTTRingOps) (encoding : Encoding params)
    (_prims : Primitives params encoding) (dk : SecretKey params encoding)
    (c : Ciphertext params encoding) : Message :=
  let (u', v') := encoding.decodeCiphertext c.uEncoded c.vEncoded
  let sHat := encoding.byteDecode12Vec dk.sHatEncoded
  let w := v' - ring.invNTT (ring.dot sHat (ring.nttVec u'))
  encoding.byteEncode1 (encoding.compress1 w)
```
:::::
::::::
:::::::
::::::::

:::defTitle "on_off_kem_kem_from_kpke" "IND-CPA KEM from K-PKE"
:::

:::::::definition "on_off_kem_kem_from_kpke" (parent := "on_off_kem_on_off_kem_from_ml_kem") (lean := "KPKEOnOff.keygen, KPKEOnOff.encaps, KPKEOnOff.decaps, KPKEOnOff.scheme")
Let $`\Enc,\Dec` be the encryption and decryption algorithms of
{bpref "on_off_kem_kpke"}[]. Following
({Informal.citet SCKA25}[], §2, §4.1), we define a KEM as follows. The scheme is parameterised by a seed
$`\rho\in\{0,1\}^{256}` that generates the public matrix. It is fixed and shared by all key pairs.

::::::gameGrid
:::::gameCell "\\KeyGen()" (kind := "compact")
$`\begin{array}{l}
\sigma \sample \{0,1\}^{256} \pcomment{\text{fresh key-noise seed; }\rho\text{ is fixed}} \\
s \gets \SampleVec_1(\sigma,0) \pcomment{\text{small secret vector}} \\
e \gets \SampleVec_1(\sigma,k) \pcomment{\text{small error vector}} \\
\hat{A} \gets \XOF(\rho) \pcomment{\text{reconstruct public matrix from fixed seed }\rho} \\
\hat{s}, \hat{e} \gets \NTT(s), \NTT(e) \\
\hat{t} \gets \hat{A}\,\hat{s} + \hat{e} \\
\Return (\ek = \hat{t},\ \dk = \hat{s})
\end{array}`

```anchor keygenFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def keygen : ProbComp (encoding.EncodedTHat × encoding.EncodedTHat) := do
  let sigma ← $ᵗ Seed32
  let aHat := prims.publicMatrix rho
  let s := prims.sampleVecEta1 sigma 0
  let e := prims.sampleVecEta1 sigma params.k
  let sHat := ring.nttVec s
  let eHat := ring.nttVec e
  let tHat := ring.matVecMul aHat sHat + eHat
  pure (encoding.byteEncode12Vec tHat, encoding.byteEncode12Vec sHat)
```
:::::

:::::gameCell "\\Encaps(\\ek=\\hat{t}\\in\\Tq^k)" (kind := "compact")
$`\begin{array}{l}
\coins \sample \{0,1\}^{256} \\
m \sample \{0,1\}^{256} \pcomment{\text{sample a random message}} \\
\ct \gets \Enc((\hat{t},\rho),\ m;\ \coins) \\
\Return (\ct,\ m) \pcomment{\text{the message }m\text{ is the shared key}}
\end{array}`

```anchor encapsFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def encaps (ek : encoding.EncodedTHat) :
    ProbComp ((encoding.EncodedU × encoding.EncodedV) × Message) := do
  let coins ← $ᵗ Coins
  let msg ← $ᵗ Message
  let ct := KPKE.encrypt ring encoding prims
    ({ tHatEncoded := ek, rho := rho } : KPKE.PublicKey params encoding) msg coins
  pure ((ct.uEncoded, ct.vEncoded), msg)
```
:::::

:::::gameCell "\\Decaps(\\dk=\\hat{s}\\in\\Tq^k,\\ \\ct)" (kind := "compact")
$`\begin{array}{l}
m \gets \Dec(\hat{s}, \ct) \\
\Return \mathsf{some}(m) \pcomment{\text{the decrypted message }m\text{ is the shared key}}
\end{array}`

```anchor decapsFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def decaps (dk : encoding.EncodedTHat) (c : encoding.EncodedU × encoding.EncodedV) :
    ProbComp (Option Message) :=
  pure (some (KPKE.decrypt ring encoding prims
    ({ sHatEncoded := dk } : KPKE.SecretKey params encoding)
    ({ uEncoded := c.1, vEncoded := c.2 } : KPKE.Ciphertext params encoding)))
```
:::::
::::::

:::leanPillCaption "KEM scheme wiring KeyGen, Encaps, and Decaps"
:::

```anchor schemeFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def scheme :
    KEMScheme ProbComp Message encoding.EncodedTHat encoding.EncodedTHat
      (encoding.EncodedU × encoding.EncodedV) where
  keygen := keygen params encoding ring prims rho
  encaps := encaps params encoding ring prims rho
  decaps := decaps params encoding ring prims
```

{usesLabel}`uses` {uses "on_off_kem_kpke"}[]
:::::::

:::defTitle "on_off_kem_from_ml_kem_spec" "On-off instance from K-PKE"
:::

:::::::definition "on_off_kem_from_ml_kem_spec" (parent := "on_off_kem_on_off_kem_from_ml_kem") (lean := "KPKEOnOff.encapsOff, KPKEOnOff.encapsOn, KPKEOnOff.onOff")
Online-offline structure for the KEM specified in {bpref "on_off_kem_kem_from_kpke"}[]
({Informal.citet SCKA25}[], Def. 2.1). The ciphertext space splits as
$`\C=\C_0\times\C_1` with $`\ct=(\ctzero,\ctone)`, and the offline state space is
$`\St=\Tq^k\times\Rq` with online state $`\stct=(\hat{y},e_2)`,
where $`\hat{y}` is in the NTT domain while $`e_2` remains in coefficient form for the
final inverse transform.

::::::gameGrid
:::::gameCell "\\Encaps.\\mathsf{Off}()" (kind := "compact")
$`\begin{array}{l}
\coins \sample \{0,1\}^{256} \\
y \gets \SampleVec_1(\coins,0) \pcomment{\text{small ephemeral vector}} \\
e_1 \gets \SampleVec_2(\coins,k) \pcomment{\text{small error vector}} \\
e_2 \gets \SamplePoly_2(\coins,2k) \pcomment{\text{small error polynomial}} \\
\hat{A} \gets \XOF(\rho) \pcomment{\text{reconstruct public matrix from fixed seed }\rho} \\
\hat{y} \gets \NTT(y) \\
u \gets \NTT^{-1}(\hat{A}^{\top}\hat{y}) + e_1 \\
\stct \gets (\hat{y},e_2) \\
\Return (\stct,\ \ctzero = \Compress(u)) \pcomment{\text{compress first component}}
\end{array}`

```anchor encapsOffFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def encapsOff : ProbComp ((TqVec params.k × Rq) × encoding.EncodedU) := do
  let coins ← $ᵗ Coins
  let aHat := prims.publicMatrix rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let e2 := prims.prfEta2 coins (2 * params.k)
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  pure ((yHat, e2), encoding.byteEncodeDUVec (encoding.compressDU u))
```
:::::

:::::gameCell "\\Encaps.\\mathsf{On}(\\stct\\in\\St,\\ \\ek=\\hat{t}\\in\\Tq^k)" (kind := "compact")
$`\begin{array}{l}
(\hat{y},e_2) \gets \stct \\
m \sample \{0,1\}^{256} \\
\mu \gets \Embed(m) \pcomment{\text{embed message in }\Rq} \\
v \gets \NTT^{-1}(\langle \hat{t}, \hat{y}\rangle) + e_2 + \mu \\
\Return (\ctone = \Compress(v),\ m) \pcomment{\text{the message }m\text{ is the shared key}}
\end{array}`

```anchor encapsOnFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def encapsOn (st : TqVec params.k × Rq) (ek : encoding.EncodedTHat) :
    ProbComp (encoding.EncodedV × Message) := do
  let (yHat, e2) := st
  let tHat := encoding.byteDecode12Vec ek
  let msg ← $ᵗ Message
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  pure (encoding.byteEncodeDV (encoding.compressDV v), msg)
```
:::::

:::::gameCell "\\textsf{Factorization}" (kind := "game")
$`\forall\,\ek\in\Tq^k:\quad \Encaps(\ek)\equiv
\left[(\stct,\ctzero)\gets\Encaps.\mathsf{Off}();\
(\ctone,K)\gets\Encaps.\mathsf{On}(\stct,\ek);\
\bigl((\ctzero,\ctone),K\bigr)\right]`
:::::
::::::

:::leanPillCaption "on-off structure and factorization proof"
:::

```anchor onOffFromKPKE (project := ".") (module := SecureMessaging.KEM.OnOffKEM.FromKPKE)
def onOff : (scheme params encoding ring prims rho).OnOffStructure where
  St := TqVec params.k × Rq
  C₀ := encoding.EncodedU
  C₁ := encoding.EncodedV
  split := Equiv.refl (encoding.EncodedU × encoding.EncodedV)
  encapsOff := encapsOff params encoding ring prims rho
  encapsOn := encapsOn params encoding ring
  factor ek := by
    simp only [scheme, encaps, encapsOff, encapsOn, KPKE.encrypt, bind_assoc, pure_bind,
      Equiv.refl_symm, Equiv.coe_refl, id_eq]
```

{usesLabel}`uses` {uses "on_off_kem_scheme"}[] · {uses "on_off_kem_kem_from_kpke"}[] · {githubLabel}`github` {githubIssue 41}[]
:::::::
