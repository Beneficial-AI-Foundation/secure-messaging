import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import ToVCVio.LatticeCrypto.FrodoKEM.Construction
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness

/-! # Blueprint chapter: FrodoKEM -/

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

open Verso.Genre Manual
open Informal
open Verso.Code.External

set_option doc.verso true

#doc (Manual) "FrodoKEM" =>

*References:*

- {Informal.citet FrodoKEM}[]
- {Informal.citet LBES26}[]

:::group "frodo_kem"
FrodoKEM, a Learning-With-Errors key encapsulation mechanism
({Informal.citet FrodoKEM}[]).
:::

FrodoKEM is a post-quantum key-encapsulation mechanism which is based on
the learning with errors (LWE) problem.
Its distinguishing choice is to use plain LWE,
without the additional ring or module structure used by many lattice schemes
({Informal.citet FrodoKEM}[], Introduction).

The construction turns an underlying public-key encryption scheme called FrodoPKE
into a KEM using a Fujisaki–Okamoto transform.
Encapsulation produces a ciphertext and a shared secret; decapsulation
uses the secret key to recover that shared secret. FrodoKEM has two variants:
salted and ephemeral. Each variant offers three parameter sizes—640, 976, and 1344—with
AES128 or SHAKE128 used to generate the public matrix. The two variants, three sizes,
and two matrix generators give twelve combinations in total
({Informal.citet FrodoKEM}[], §6.2). The salted variant adds a
public salt and longer error seeds to address attacks targeting many ciphertexts
({Informal.citet FrodoKEM}[], §§1.1–1.3).
The ephemeral variant, eFrodoKEM, omits the salt and requires fewer than 256
ciphertexts per public key ({Informal.citet LBES26}[], §8).

:::defTitle "frodo_kem_scheme" "FrodoKEM scheme"
:::

:::::::definition "frodo_kem_scheme" (parent := "frodo_kem") (lean := "FrodoKEM.KEM.asKEMScheme") (tags := "gh-259")

The algorithms below describe key generation, encapsulation, and decapsulation
for a fixed parameter set. FrodoPKE supplies the underlying encryption routines;
its public key is a seed and a matrix, and its secret key is a transposed matrix.

:::table +header (align := left)
*
  * Notation
  * Meaning
*
  * $`\ell, r, t`
  * Bit lengths of the message/shared secret, error seed, and salt, respectively.
*
  * $`H(x,L)`
  * SHAKE applied to $`x`, producing $`L` bits.
*
  * $`P(M), U(b)`
  * Pack matrix $`M` into a bit string, or recover a matrix from packed bits $`b`.
*
  * $`x \| y`
  * Concatenate two bit strings.
*
  * $`x \sample \{0,1\}^{L}`
  * Sample an independent, uniformly random $`L`-bit string.
:::

$`P(M)` uses the draft's packing convention, representing each packed byte
least-significant-bit first. $`U(b)` reverses this conversion. In Lean, these
operations are implemented by `packBits` and `unpackBits`.

::::::gameGrid

:::::gameCell "\\mathsf{KeyGen}()" (kind := "game")
Generate a key pair and store a fallback secret for ciphertexts that fail validation.

Here $`\mathsf{PKE.KeyGen}(a,\mathsf{seed}_{SE})` denotes key generation with supplied
seeds, implemented by `PKE.keygenFromSeeds`.

$`\begin{array}{l}
s \sample \{0,1\}^{\ell};\quad
\mathsf{seed}_{SE} \sample \{0,1\}^{r};\quad z \sample \{0,1\}^{128} \\[0.35em]
a \gets H(z,128) \\[0.35em]
((a,B),S^{\mathsf T}) \gets \mathsf{PKE.KeyGen}(a,\mathsf{seed}_{SE}) \\[0.35em]
b \gets P(B);\quad \mathsf{pk} \gets (a,b) \\[0.35em]
\mathsf{pkh} \gets H(a\|b,\ell) \\[0.35em]
\mathsf{sk} \gets (s,\mathsf{pk},S^{\mathsf T},\mathsf{pkh}) \\[0.35em]
\Return (\mathsf{pk},\mathsf{sk})
\end{array}`

:::leanPillCaption "Lean specification"
:::

```anchor frodoKEM_keyGeneration (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Construction)
def keygen {ps : ParameterSet} (ops : Operations ps) :
    ProbComp (PublicKey ps × SecretKey ps) := do
  let fallback ← $ᵗ (SharedSecretBits ps)
  let seedSE ← $ᵗ (SeedSEBits ps)
  let z ← $ᵗ (Bits lenZ)
  let p := ps.params
  let seedA := ops.shake z.toList lenSeedA
  let a := ops.gen seedA
  let stream := ops.shake
    (keygenPrefix.toList ++ seedSE.toList)
    (nbar * p.n * lenChi + p.n * nbar * lenChi)
  let samples := splitBits
    (a := nbar * p.n * lenChi)
    (b := p.n * nbar * lenChi) stream
  let st := (SampleMatrix ps.errorTable nbar p.n samples.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let e := (SampleMatrix ps.errorTable p.n nbar samples.2).map
    (fun x : ℤ => (x : ZMod p.q))
  let b := a * st.transpose + e
  let pk : PublicKey ps :=
    { seedA := seedA
      b := packBits ps p.n nbar (publicKeyBits_mod_eight ps) b }
  return (pk,
    { fallback := fallback
      publicKey := pk
      secretTranspose := st
      publicKeyHash := hashPublicKey ops pk })
```
:::::

:::::gameCell "\\mathsf{Encaps}(\\mathsf{pk}=(a,b))" (kind := "game")
Encrypt a fresh random message, then derive the shared secret from the ciphertext
and intermediate key. In eFrodoKEM, $`t=0` and the salt is empty.
The hash output is split into an $`r`-bit seed and an $`\ell`-bit key.

$`\begin{array}{l}
\mu \sample \{0,1\}^{\ell};\quad \mathsf{salt} \sample \{0,1\}^{t} \\[0.35em]
\mathsf{pkh} \gets H(a\|b,\ell) \\[0.35em]
(\mathsf{seed}_{SE},k) \gets H(\mathsf{pkh}\|\mu\|\mathsf{salt},r+\ell) \\[0.35em]
(B',C) \gets \mathsf{PKE.Enc}((a,U(b)),\mu;\mathsf{seed}_{SE}) \\[0.35em]
c_1 \gets P(B');\quad c_2 \gets P(C);\quad c \gets (c_1,c_2,\mathsf{salt}) \\[0.35em]
\mathsf{ss} \gets H(c_1\|c_2\|\mathsf{salt}\|k,\ell) \\[0.35em]
\Return (c,\mathsf{ss})
\end{array}`

:::leanPillCaption "Lean specification"
:::

```anchor frodoKEM_encapsulation (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Construction)
def encaps {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) :
    ProbComp (Ciphertext ps × SharedSecretBits ps) := do
  let message ← $ᵗ (MessageBits ps)
  let salt ← $ᵗ (SaltBits ps)
  let p := ps.params
  let derived := deriveSeedAndKey ops (hashPublicKey ops pk) message salt
  let stream := ops.shake
    (encryptionPrefix.toList ++ derived.1.toList)
    (mbar * p.n * lenChi +
      (mbar * p.n * lenChi + mbar * nbar * lenChi))
  let first := splitBits
    (a := mbar * p.n * lenChi)
    (b := mbar * p.n * lenChi + mbar * nbar * lenChi) stream
  let rest := splitBits
    (a := mbar * p.n * lenChi)
    (b := mbar * nbar * lenChi) first.2
  let sp := (SampleMatrix ps.errorTable mbar p.n first.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let ep := (SampleMatrix ps.errorTable mbar p.n rest.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let a := ops.gen pk.seedA
  let bp := sp * a + ep
  let c1 := packBits ps mbar p.n (ciphertext1Bits_mod_eight ps) bp
  let epp := (SampleMatrix ps.errorTable mbar nbar rest.2).map
    (fun x : ℤ => (x : ZMod p.q))
  let b := unpackBits ps p.n nbar (publicKeyBits_mod_eight ps) pk.b
  let v := sp * b + epp
  let c2 := packBits ps mbar nbar (ciphertext2Bits_mod_eight ps)
    (v + Encode p (message.cast (messageBits_length ps)))
  let c : Ciphertext ps := { c1 := c1, c2 := c2, salt := salt }
  return (c, ops.shake
    (c.c1.toList ++ c.c2.toList ++ c.salt.toList ++ derived.2.toList)
    p.ell)
```
:::::

:::::gameCell "\\mathsf{Decaps}(\\mathsf{sk},c)" (kind := "game")
Recover a candidate message, then derive an error seed and an intermediate key
as in encapsulation. Reencrypt the message and compare both reconstructed matrices
with those received. If either differs, replace the intermediate key with the
fallback secret. Finally, hash the received ciphertext with the selected key.

$`\begin{array}{l}
(s,(a,b),S^{\mathsf T},\mathsf{pkh}) \gets \mathsf{sk};\quad
(c_1,c_2,\mathsf{salt}) \gets c \\[0.35em]
(B',C) \gets (U(c_1),U(c_2)) \\[0.35em]
\mu' \gets \mathsf{PKE.Dec}(S^{\mathsf T},(B',C)) \\[0.35em]
(\mathsf{seed}'_{SE},k') \gets H(\mathsf{pkh}\|\mu'\|\mathsf{salt},r+\ell) \\[0.35em]
(B'',C') \gets \mathsf{PKE.Enc}((a,U(b)),\mu';\mathsf{seed}'_{SE}) \\[0.35em]
\widehat{k} \gets \begin{cases}
 k' & \text{if } B'=B'' \text{ and } C=C', \\[0.35em]
 s & \text{otherwise} \end{cases} \\[0.35em]
\Return H(c_1\|c_2\|\mathsf{salt}\|\widehat{k},\ell)
\end{array}`

:::leanPillCaption "Lean specification"
:::

```anchor frodoKEM_decaps (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Construction)
def decaps {ps : ParameterSet} (ops : Operations ps)
    (sk : SecretKey ps) (c : Ciphertext ps) : SharedSecretBits ps :=
  let p := ps.params
  let bp := unpackBits ps mbar p.n (ciphertext1Bits_mod_eight ps) c.c1
  let cm := unpackBits ps mbar nbar (ciphertext2Bits_mod_eight ps) c.c2
  let m := cm - bp * sk.secretTranspose.transpose
  let message := (Decode p m).cast (messageBits_length ps).symm
  let derived := deriveSeedAndKey ops sk.publicKeyHash message c.salt
  let stream := ops.shake
    (encryptionPrefix.toList ++ derived.1.toList)
    (mbar * p.n * lenChi +
      (mbar * p.n * lenChi + mbar * nbar * lenChi))
  let first := splitBits
    (a := mbar * p.n * lenChi)
    (b := mbar * p.n * lenChi + mbar * nbar * lenChi) stream
  let rest := splitBits
    (a := mbar * p.n * lenChi)
    (b := mbar * nbar * lenChi) first.2
  let sp := (SampleMatrix ps.errorTable mbar p.n first.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let ep := (SampleMatrix ps.errorTable mbar p.n rest.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let a := ops.gen sk.publicKey.seedA
  let bpp := sp * a + ep
  let epp := (SampleMatrix ps.errorTable mbar nbar rest.2).map
    (fun x : ℤ => (x : ZMod p.q))
  let b := unpackBits ps p.n nbar (publicKeyBits_mod_eight ps) sk.publicKey.b
  let v := sp * b + epp
  let cp := v + Encode p (message.cast (messageBits_length ps))
  let selected := if bp = bpp ∧ cm = cp then derived.2 else sk.fallback
  ops.shake
    (c.c1.toList ++ c.c2.toList ++ c.salt.toList ++ selected.toList)
    p.ell
```
:::::

::::::

:::::::

:::defTitle "frodo_kem_correctness" "FrodoKEM correctness"
:::

::::theorem "frodo_kem_correctness" (parent := "frodo_kem") (lean := "FrodoKEM.ROM.honestFailureProb_tenth_power_le") (tags := "gh-260") (uses := "frodo_kem_scheme")
We work in the random-oracle model, for all six parameter sets: FrodoKEM and eFrodoKEM, each at
sizes 640, 976 and 1344.

- A random function $`H` replaces SHAKE. This is SHAKE128 for size 640 and SHAKE256 for sizes
  976 and 1344.
- The function $`\mathsf{gen}` that computes the public matrix $`A` from $`\mathsf{seed}_A` is
  any fixed function, such as GenSHAKE or GenAES.

Let $`\delta` be $`2^{-138.7}`, $`2^{-199.6}` or $`2^{-252.5}` for sizes 640, 976 and 1344.
{Informal.citet FrodoKEM}[] lists these values as the failure rates in Table 4 (§6.2). Then

$$`\Pr_{\substack{H \gets \mathsf{RO},\\ (\mathsf{pk},\mathsf{sk}) \gets \mathsf{KeyGen}^H(),\\ (c,K) \gets \mathsf{Encaps}^H(\mathsf{pk})}}\bigl[\mathsf{Decaps}^H(\mathsf{sk},c) \ne K\bigr] \;\le\; \delta.`

The probability is over the random function $`H` and the honest random choices. In Lean,
`ROM.honestFailureProb` is this probability. The KEM uses SHAKE on only five input lengths and
reads at most `outputBits` bits, so $`H` is a uniformly random table of finite size.

:::leanPillCaption "The failure probability in the random-oracle model"
:::

```anchor frodoKEM_rom_failureProb (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness)
noncomputable def honestFailureProb
    (ps : ParameterSet) (gen : Generator ps) : ℝ≥0∞ :=
  Pr{
    let H ← ToVCVio.FiniteXOF.sampleTable
      (inputLengths ps) (outputBits ps)
    let keys ← KEM.keygen (operations ps gen H)
    let out ← KEM.encaps (operations ps gen H) keys.1
  }[
    KEM.decaps (operations ps gen H) keys.2 out.1 ≠ out.2
  ]
```

Lean states the bound as $`p^{10} \cdot 2^{10e} \le 1`, where $`p` is the failure probability and
$`2^{-e} = \delta`. That is, $`p \le 2^{-e}`. The tenth power is used because $`10e`, such as
$`1387`, is a whole number.

:::leanPillCaption "Failure bound in the random-oracle model"
:::

```anchor frodoKEM_correctness (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Numerical)
theorem honestFailureProb_tenth_power_le
    (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen ^ 10 *
      2 ^ Certificate.exponentTenths ps ≤ 1
```

*Not covered.*

- Many encapsulations to one key. The theorem is about one key pair and one encapsulation. So it
  says nothing about the limit of eFrodoKEM to fewer than 256 ciphertexts per public key
  ({Informal.citet LBES26}[], §8).
- The correctness term $`q_{RO} \cdot \delta(n_u)` in the IND-CCA bound
  ({Informal.citet FrodoKEM}[], Theorem 1). There, $`\delta(n_u)`-correctness is Definition 8 of
  {Informal.citet FrodoKEM}[], and an adversary with $`q_{RO}` oracle queries can look for messages
  that fail. This theorem bounds only honest runs.

*Proof.*

1. Let $`q` be the modulus and $`B` the number of bits per entry. If each noise entry $`e`
   satisfies $`-q \le 2^{B+1} e < q`, decoding returns the message. {Informal.citet FrodoKEM}[]
   proves this for one entry (§4.1, Lemma 1), and the Lean theorem applies it to each entry of the
   matrix.

:::leanPillCaption "Step 1: decoding tolerates small noise"
:::

```anchor frodoKEM_decode (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Basic)
theorem Decode_Encode_add (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    Decode p (Encode p b + E) = b
```

2. For each fixed function in place of SHAKE, decapsulation fails only if the noise matrix
   $`S'E + E'' - E'S` is large.

:::leanPillCaption "Step 2: failure implies large noise"
:::

```anchor frodoKEM_failure_le_noise (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.FailureProbability)
theorem honestFailureProb_le_honestNoiseBadProb
    {ps : ParameterSet} (ops : Operations ps) :
    honestFailureProb ops ≤ honestNoiseBadProb ops
```

3. The probability of large noise, averaged over all tables, is equal to the probability of large
   noise when the five error matrices are independent samples.

:::leanPillCaption "Step 3: the table gives independent noise"
:::

```anchor frodoKEM_rom_noise (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness)
theorem honestNoiseBadProb_eq_indepNoise
    (ps : ParameterSet) (gen : Generator ps) :
    honestNoiseBadProb ps gen = IndepNoise.noiseBadProb ps
```

4. The noise matrix is reduced mod $`q`. It is large only if some entry, as an integer, lies outside
   the decoding interval. The union bound over the $`8 \times 8` entries gives at most 64 times the
   probability of this for one entry.

:::leanPillCaption "Step 4: union bound"
:::

```anchor frodoKEM_union (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.IndepNoise)
theorem noiseBadProb_le (ps : ParameterSet) :
    noiseBadProb ps ≤ 64 * entryFailureProb ps
```

5. Let $`\chi` be the error distribution. One integer entry is a sum of $`2n` products of two
   samples of $`\chi`, plus one more sample. Since $`\chi` is symmetric, the minus sign in the noise
   matrix does not change the distribution. The convolution of distributions gives the distribution
   of a sum of independent samples.

:::leanPillCaption "Step 5: the distribution of one entry"
:::

```anchor frodoKEM_entry_law (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Counts)
theorem probOutput_entryNoiseExp (ps : ParameterSet) (z : ℤ) :
    Pr{let x ← IndepNoise.entryNoiseExp ps}[x = z] =
      (((ToVCVio.productMeasure
          (ToVCVio.RoundedConvolution.counts (config ps))
          (ToVCVio.RoundedConvolution.counts (config ps))) ^
          (2 * ps.params.n) *
        ToVCVio.RoundedConvolution.counts (config ps)) z :
          ℝ≥0∞) /
        (2 ^ lenChi) ^ (4 * ps.params.n + 1)
```

6. The Lean kernel computes whole-number bounds on this distribution. With step 4, they bound the
   probability of large noise by `failureBound`.

:::leanPillCaption "Step 6: the checked bound"
:::

```anchor frodoKEM_certificate (project := ".") (module := ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Numerical)
theorem noiseBadProb_le_failureBound (ps : ParameterSet) :
    IndepNoise.noiseBadProb ps ≤ failureBound ps
```
::::

:::defTitle "frodo_kem_security" "FrodoKEM security"
:::

::::theorem "frodo_kem_security" (parent := "frodo_kem") (tags := "gh-261") (uses := "frodo_kem_scheme")
$`\todo`

:::leanPill "missing"
:::
::::
