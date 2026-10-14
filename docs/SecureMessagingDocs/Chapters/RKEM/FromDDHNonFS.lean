import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.RKEM.FromDDHNonFS.Construction
import SecureMessaging.RKEM.FromDDHNonFS.Correctness

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "RKEM from DDH (non-FS)" =>

:::group "rkem_rkem_from_ddh_non_fs"
RKEM from DDH (non-FS).
:::

:::defTitle "rkem_from_ddh_nonfs_spec" "RKEM from DDH non-FS construction"
:::

:::::::definition "rkem_from_ddh_nonfs_spec" (parent := "rkem_rkem_from_ddh_non_fs") (lean := "ddhRKEM.rkeygen, ddhRKEM.renc, ddhRKEM.rdec, ddhRKEM.scheme") (tags := "gh-66") (uses := "rkem_scheme")
Adapted from {Informal.citet TR25}[], Appendix A.3 and Figure 28, without the figure's forward-secure modifications.

Let $`G=\langle g\rangle` be a cyclic group of prime order $`q`. A party's key pair is a scalar $`x\in\mathbb{Z}_q` together with its public value $`g^x`. Public parameters are vacuous, and fresh and updated key generation coincide. Ciphertexts are empty: the peer already holds the sender's public value $`g^x`, which is the sender's encapsulation key, and both parties derive the shared key $`g^{xy}`. Used in the generic CKA construction, this RKEM yields the Double Ratchet CKA of {Informal.citet ACD19}[] (see CKA from DDH).

The scheme is the non-forward-secure special case of an RKEM: $`\REnc\text{-}\mathsf{P}` returns its input $`\dk_\mathsf{P}` unchanged as the updated decapsulation key, and $`\RDec\text{-}\mathsf{P}` returns its input $`\ek_{\mathsf{\bar P}}` unchanged as the peer's updated encapsulation key. In particular, it is not FS-IND-CPA secure, since the forward-security game hands the adversary $`\dkh{A}=x` together with $`\ekh{B}=Y`, from which it recomputes $`K=Y^x`; the paper only claims plain IND-CPA security under DDH (Theorem A.4).

The algorithms are the same for both parties $`\mathsf{P}\in\{\A,\B\}`, with peer $`\mathsf{\bar P}`. In Lean, the group is modelled additively as a module over the scalar field $`F` (playing $`\mathbb{Z}_q`) with a fixed generator $`\mathsf{gen}`, given as a parameter of the construction: $`g^x` is `x • gen` and $`Y^x` is `x • Y`.

::::::gameGrid
:::::gameCell "\\mathsf{RKeyGen}\\text{-}\\mathsf{P}(\\mathsf{par},\\mathsf{mode})" (kind := "compact")
$`\begin{array}{l}
x\sample\mathbb{Z}_q \\
(\ek_\mathsf{P},\dk_\mathsf{P})\gets(g^x,x) \\
\Return(\ek_\mathsf{P},\dk_\mathsf{P})
\end{array}`

:::leanPillCaption "RKeyGen-P"
:::

```anchor rkeygen (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def rkeygen (gen : G) (_par : Unit) : ProbComp (G × F) := do
  let x ← $ᵗ F
  return (x • gen, x)
```
:::::

:::::gameCell "\\REnc\\text{-}\\mathsf{P}(\\ekh{\\bar P}:=Y,\\dk_\\mathsf{P}:=x)" (kind := "compact")
$`\begin{array}{l}
\ct_{\mathsf{\bar P}}:=()\pcomment{\text{empty ciphertext}} \\
K:=Y^x \\
\dkh{P}:=x \\
\Return(\ct_{\mathsf{\bar P}},K,\dkh{P})
\end{array}`

:::leanPillCaption "REnc-P"
:::

```anchor renc (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def renc (_par : Unit) (ekPeerHat : G) (dkSelf : F) : ProbComp (Unit × G × F) := do
  let ctPeer := ()
  let key := dkSelf • ekPeerHat
  let dkSelfHat := dkSelf
  return (ctPeer, key, dkSelfHat)
```
:::::

:::::gameCell "\\RDec\\text{-}\\mathsf{P}(\\dkh{P}:=x,\\ct_\\mathsf{P},\\ek_{\\mathsf{\\bar P}}:=Y)" (kind := "compact")
$`\begin{array}{l}
K:=Y^x \\
\ekh{\bar P}:=Y \\
\Return(K,\ekh{\bar P})
\end{array}`

:::leanPillCaption "RDec-P"
:::

```anchor rdec (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def rdec (_par : Unit) (dkSelfHat : F) (_ctSelf : Unit) (ekPeer : G) : ProbComp (G × G) := do
  let key := dkSelfHat • ekPeer
  let ekPeerHat := ekPeer
  return (key, ekPeerHat)
```
:::::
::::::

:::leanPillCaption "DH RKEM scheme"
:::

```anchor scheme (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def scheme (gen : G) : RKEMScheme ProbComp Unit G F Unit G where
  rsetup := pure ()
  rkeygenAFresh := rkeygen gen
  rkeygenAUpdated := rkeygen gen
  rkeygenBFresh := rkeygen gen
  rkeygenBUpdated := rkeygen gen
  rencA := renc
  rdecA := rdec
  rencB := renc
  rdecB := rdec
```
:::::::

:::defTitle "rkem_from_ddh_nonfs_correctness" "RKEM from DDH non-FS correctness"
:::

:::theorem "rkem_from_ddh_nonfs_correctness" (parent := "rkem_rkem_from_ddh_non_fs") (lean := "ddhRKEM.probOutput_correctExpA_eq_one, ddhRKEM.evalDist_ratchetRoundOutputA_eq_evalDist_rkeygen, ddhRKEM.deltaCorrect") (tags := "gh-67") (uses := "rkem_from_ddh_nonfs_spec, rkem_scheme, rkem_correctness")
Adapted from {Informal.citet TR25}[], Theorem A.3.

The non-forward-secure RKEM from DDH is perfectly correct: it is $`(0,0)`-correct, unconditionally. With $`(\ekA,\dkA)=(g^x,x)` and $`(\ekh{B},\dkh{B})=(g^y,y)`, $`\REnc\text{-}\A` outputs $`K=(g^y)^x` and $`\RDec\text{-}\B` outputs $`K'=(g^x)^y`, both equal to $`g^{xy}`. Since the scheme is not forward secure, the updated key pair produced by a round is $`\A`'s fresh key pair itself, and fresh and updated key generation coincide, so the update-key distribution is exact as well. The algorithms are the same for both parties, so the $`\B` side is identical.

```anchor deltaCorrect (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Correctness)
theorem deltaCorrect [DecidableEq G] (gen : G) :
    RKEMScheme.deltaCorrect (scheme (F := F) gen) ProbCompRuntime.probComp 0 0
```
:::

:::defTitle "rkem_from_ddh_nonfs_ratchet_sim" "RKEM from DDH non-FS ratchet simulatability"
:::

::::theorem "rkem_from_ddh_nonfs_ratchet_sim" (parent := "rkem_rkem_from_ddh_non_fs") (tags := "gh-68") (uses := "rkem_from_ddh_nonfs_spec, rkem_scheme, rkem_ratchet_sim")
$`\todo`

:::leanPill "missing"
:::
::::
