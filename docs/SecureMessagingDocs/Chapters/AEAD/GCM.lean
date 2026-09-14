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

::::definition "aead_gcm_spec" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD")
$`\todo`

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
def gcmOneTimeAEAD {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 c
```

{usesLabel}`uses` {uses "aead"}[] · {githubLabel}`github` {githubIssue 21}[]
::::

:::defTitle "aead_gcm_correctness" "AEAD-GCM correctness"
:::

::::theorem "aead_gcm_correctness" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD_correct")
$`\todo`

```anchor gcmOneTimeAEAD_correct (project := ".") (module := SecureMessaging.AEAD.FromGCM.Correctness)
theorem gcmOneTimeAEAD_correct {K : Type} (prp : PRPScheme K (BitVec 128)) {L : ℕ}
    (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp L hL).Correct
```

{usesLabel}`uses` {uses "aead_gcm_spec"}[] · {uses "aead_correctness"}[] · {githubLabel}`github` {githubIssue 22}[]
::::

:::defTitle "aead_gcm_security" "AEAD-GCM security"
:::

::::theorem "aead_gcm_security" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD_security")
One-time IND-CCA security of GCM at the all-zero 96-bit IV reduces to the PRP
security of its block cipher. The distinguishing advantage is at most
$`\mathrm{Adv}^{\mathrm{prp}}` of the explicit reduction
$`B = \mathsf{prfReduction}\ L\ A`, plus the PRP/PRF switching term
$`(n+2)(n+1)/2^{129}` with $`n = \lceil L/128 \rceil`, plus
$`q_d \cdot \mathsf{maxBlocks}(L)/2^{128}`, where $`q_d` bounds the adversary's
decryption queries.

The switching term is a birthday term in the number of *block-cipher calls* made by
one encryption (the hash key, the tag mask, and one keystream block per message
block, so $`q = n + 2`), not in the number of adversary queries; it does not
disappear in the one-time setting. Neither an almost-XOR-universality hypothesis nor
a PRF hypothesis remains.

```anchor gcmOneTimeAEAD_security (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security)
theorem gcmOneTimeAEAD_security (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp L hL) adv ≤
      PRPScheme.prpAdvantage prp (prfReduction L adv) +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ) +
      (q_d : ℝ) * ((maxBlocks L : ℝ) / 2 ^ (128 : ℕ))
```

{usesLabel}`uses` {uses "aead_gcm_spec"}[] · {uses "aead_security_exp"}[] · {uses "aead_dist_advantage"}[] · {uses "aead_decrypt_query_bound"}[] · {githubLabel}`github` {githubIssue 23}[]
::::
