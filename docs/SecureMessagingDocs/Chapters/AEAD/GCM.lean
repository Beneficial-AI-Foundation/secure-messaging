import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.AEAD.FromGCM.Construction
import SecureMessaging.AEAD.FromGCM.Correctness
import SecureMessaging.AEAD.FromGCM.Security

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

#doc (Manual) "GCM" =>

*References:*

- {Informal.citet NIST_GCM}[]

:::group "aead_gcm"
GCM.
:::

:::defTitle "aead_gcm_spec" "AEAD-GCM construction"
:::

::::definition "aead_gcm_spec" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD") (tags := "gh-21") (uses := "aead, prp")
GCM authenticated encryption from NIST SP 800-38D, used as a one-time AEAD scheme built on a
pseudorandom permutation, with a fixed public 96-bit initialisation vector `iv`. The key is
the permutation's key. Encryption returns the encrypted message together with an
authentication tag computed over the associated data and the encrypted message; decryption
recomputes the tag and rejects on mismatch.

The scheme's domain is the NIST-supported length range. A plaintext/ciphertext
bit-length is supported when it is at most `2^39 - 256` and byte-aligned:

```anchor ValidMsgLength (project := ".") (module := SecureMessaging.AEAD.GCM)
@[reducible] def ValidMsgLength (lenC : ℕ) : Prop := lenC ≤ 2 ^ 39 - 256 ∧ 8 ∣ lenC
```

and the associated data is any byte-aligned bit-string of length at most `2^64 - 1`:

```anchor ValidAADLength (project := ".") (module := SecureMessaging.AEAD.GCM)
@[reducible] def ValidAADLength (lenA : ℕ) : Prop := lenA ≤ 2 ^ 64 - 1 ∧ 8 ∣ lenA
```

```anchor SupportedAAD (project := ".") (module := SecureMessaging.AEAD.GCM)
abbrev SupportedAAD := { x : (a : ℕ) × BitVec a // ValidAADLength x.1 }
```

```anchor gcmOneTimeAEAD (project := ".") (module := SecureMessaging.AEAD.FromGCM.Construction)
def gcmOneTimeAEAD {K : Type} (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.toBlockCipher k iv ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.toBlockCipher k iv ad.1.2 c
```
::::

:::defTitle "aead_gcm_correctness" "AEAD-GCM correctness"
:::

::::theorem "aead_gcm_correctness" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD_correct") (tags := "gh-22") (uses := "aead_gcm_spec, aead_correctness, prp")
$`\todo`

```anchor gcmOneTimeAEAD_correct (project := ".") (module := SecureMessaging.AEAD.FromGCM.Correctness)
theorem gcmOneTimeAEAD_correct {K : Type} (prp : PRPScheme K (BitVec 128))
    (iv : BitVec 96) {L : ℕ} (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp iv L hL).Correct
```
::::

:::defTitle "aead_gcm_security" "AEAD-GCM security"
:::

::::theorem "aead_gcm_security" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD_security") (tags := "gh-23") (uses := "aead_gcm_spec, aead_security_exp, aead_dist_advantage, aead_decrypt_query_bound, prp")
For every PRP scheme $`P` on 128-bit blocks, every 96-bit IV $`iv`, every
supported message length $`L` and every adversary $`\adv` making at most $`q_d` decryption
queries,

$$`\mathsf{Adv}^{\textsf{dist}}_{\textsf{GCM}}(\adv)
  \le \mathsf{Adv}^{\textsf{prp}}_{P}(B)
  + \frac{(n+2)(n+1)}{2^{129}}
  + q_d \cdot \frac{2^{57} + n + 1}{2^{128}}`

where $`n = \lceil L/128 \rceil` and $`B = \mathsf{prfReduction}\ iv\ L\ \adv`.

```anchor gcmOneTimeAEAD_security (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security)
theorem gcmOneTimeAEAD_security (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      PRPScheme.prpAdvantage prp (prfReduction iv L adv) +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ))
```
::::
