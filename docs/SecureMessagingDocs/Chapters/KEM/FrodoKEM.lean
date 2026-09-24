import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import ToVCVio.LatticeCrypto.FrodoKEM.Construction

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

::::theorem "frodo_kem_correctness" (parent := "frodo_kem") (tags := "gh-260") (uses := "frodo_kem_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "frodo_kem_security" "FrodoKEM security"
:::

::::theorem "frodo_kem_security" (parent := "frodo_kem") (tags := "gh-261") (uses := "frodo_kem_scheme")
$`\todo`

:::leanPill "missing"
:::
::::
