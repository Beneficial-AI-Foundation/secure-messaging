import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.RKEM.FromDDHNonFS.Construction
import SecureMessaging.RKEM.FromDDHNonFS.Correctness
import SecureMessaging.RKEM.FromDDHNonFS.RatchetSimulatability
import SecureMessaging.RKEM.FromDDHNonFS.Security

/-! # Blueprint chapter: RKEM from DDH (non-FS) -/

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

:::::::definition "rkem_from_ddh_nonfs_spec" (parent := "rkem_rkem_from_ddh_non_fs") (lean := "ddhRKEM.rkeygen, ddhRKEM.renc, ddhRKEM.rdec, ddhRKEM.scheme, ddhRKEM.rkeygenRleak, ddhRKEM.rencRleak, ddhRKEM.randLeak") (tags := "gh-66") (uses := "rkem_scheme")
Adapted from {Informal.citet TR25}[], Appendix A.3 and Figure 28, without the figure's forward-secure modifications.

::::::gameGrid
:::::gameCell "\\textsf{Notation and public parameters}" (kind := "scheme")
$`\begin{array}{ll}
G=\langle g\rangle & \text{cyclic group of prime order } q \\
\mathsf{par}=() & \text{vacuous public parameters} \\
(\ek_\mathsf{P},\dk_\mathsf{P})=(g^x,x)\in G\times\mathbb{Z}_q & \text{key pair; fresh and updated key generation coincide} \\
\ct=() & \text{empty ciphertext} \\
K=g^{xy}\in G & \text{shared key, for key pairs }(g^x,x)\text{ and }(g^y,y)
\end{array}`
:::::
::::::

Ciphertexts are empty: the sender's public value $`g^x` doubles as the KEM ciphertext and as its encapsulation key, which the generic CKA construction transmits alongside the ciphertext and $`\RDec\text{-}\mathsf{P}` receives as $`\ek_{\mathsf{\bar P}}`. Used in the generic CKA construction, this RKEM yields the Double Ratchet CKA of {Informal.citet ACD19}[] (see {bpref "cka_from_ddh"}[CKA from DDH]).

The scheme is the non-forward-secure special case of an {bpref "rkem_scheme"}[RKEM]: $`\REnc\text{-}\mathsf{P}` returns its input $`\dk_\mathsf{P}` unchanged as the updated decapsulation key, and $`\RDec\text{-}\mathsf{P}` returns its input $`\ek_{\mathsf{\bar P}}` unchanged as the peer's updated encapsulation key. In particular, it is not FS-IND-CPA secure, since the {bpref "rkem_forward_security"}[forward-security game] hands the adversary $`\dkh{A}=x` together with $`\ekh{B}=Y`, from which it recomputes $`K=Y^x`; the paper only claims plain IND-CPA security under DDH (Theorem A.4).

Both parties run the same algorithms, shown below for one round in each direction, with $`\A`'s key pair $`(g^x,x)` on the left and $`\B`'s key pair $`(g^y,y)` on the right. In Lean, the group is modelled additively as a module over the scalar field $`F` (playing $`\mathbb{Z}_q`) with a fixed generator $`\mathsf{gen}`, given as a parameter of the construction: $`g^x` is `x • gen` and $`Y^x` is `x • Y`.

*Key generation.*

::::::gameGrid
:::::gameCell "\\mathsf{RKeyGen}\\text{-}\\A(\\mathsf{par},\\mathsf{mode})" (kind := "compact")
$`\begin{array}{l}
x\sample\mathbb{Z}_q \\
(\ekA,\dkA)\gets(g^x,x) \\
\Return(\ekA,\dkA)
\end{array}`
:::::

:::::gameCell "\\mathsf{RKeyGen}\\text{-}\\B(\\mathsf{par},\\mathsf{mode})" (kind := "compact")
$`\begin{array}{l}
y\sample\mathbb{Z}_q \\
(\ek_\B,\dk_\B)\gets(g^y,y) \\
\Return(\ek_\B,\dk_\B)
\end{array}`
:::::
::::::

*Round* $`\A\to\B`.

::::::gameGrid
:::::gameCell "\\REnc\\text{-}\\A(\\ekh{B}:=Y,\\dkA:=x)" (kind := "compact")
$`\begin{array}{l}
\ct_\B:=()\pcomment{\text{empty ciphertext}} \\
K:=Y^x\pcomment{=g^{xy}} \\
\dkh{A}:=x \\
\Return(\ct_\B,K,\dkh{A})
\end{array}`
:::::

:::::gameCell "\\RDec\\text{-}\\B(\\dkh{B}:=y,\\ct_\\B,\\ekA:=X)" (kind := "compact")
$`\begin{array}{l}
K:=X^y\pcomment{=g^{xy}} \\
\ekh{A}:=X \\
\Return(K,\ekh{A})
\end{array}`
:::::
::::::

*Round* $`\B\to\A`.

::::::gameGrid
:::::gameCell "\\RDec\\text{-}\\A(\\dkh{A}:=x,\\ct_\\A,\\ek_\\B:=Y)" (kind := "compact")
$`\begin{array}{l}
K:=Y^x\pcomment{=g^{xy}} \\
\ekh{B}:=Y \\
\Return(K,\ekh{B})
\end{array}`
:::::

:::::gameCell "\\REnc\\text{-}\\B(\\ekh{A}:=X,\\dk_\\B:=y)" (kind := "compact")
$`\begin{array}{l}
\ct_\A:=()\pcomment{\text{empty ciphertext}} \\
K:=X^y\pcomment{=g^{xy}} \\
\dkh{B}:=y \\
\Return(\ct_\A,K,\dkh{B})
\end{array}`
:::::
::::::

In Lean, both parties run the same `rkeygen`, `renc` and `rdec`.

:::leanPillCaption "RKeyGen-P"
:::

```anchor rkeygen (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def rkeygen (gen : G) (_par : Unit) : ProbComp (G × F) := do
  let x ← $ᵗ F
  return (x • gen, x)
```

:::leanPillCaption "REnc-P"
:::

```anchor renc (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def renc (_par : Unit) (ekPeerHat : G) (dkSelf : F) : ProbComp (Unit × G × F) := do
  let ctPeer := ()
  let key := dkSelf • ekPeerHat
  let dkSelfHat := dkSelf
  return (ctPeer, key, dkSelfHat)
```

:::leanPillCaption "RDec-P"
:::

```anchor rdec (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def rdec (_par : Unit) (dkSelfHat : F) (_ctSelf : Unit) (ekPeer : G) : ProbComp (G × G) := do
  let key := dkSelfHat • ekPeer
  let ekPeerHat := ekPeer
  return (key, ekPeerHat)
```

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

Security notions that expose algorithm coins are stated relative to a randomness-leak package of the RKEM. For this construction, fresh key generation leaks the sampled scalar $`x`, from which the key pair $`(g^x,x)` is computed, and $`\REnc\text{-}\mathsf{P}`, which is deterministic, leaks empty coins.

:::leanPillCaption "Leaking key generation"
:::

```anchor rkeygenRleak (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def rkeygenRleak (gen : G) (_par : Unit) : ProbComp ((G × F) × F) := do
  let x ← $ᵗ F
  return ((x • gen, x), x)
```

:::leanPillCaption "Leaking encapsulation"
:::

```anchor rencRleak (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def rencRleak (par : Unit) (ekPeerHat : G) (dkSelf : F) : ProbComp ((Unit × G × F) × Unit) := do
  let out ← renc par ekPeerHat dkSelf
  return (out, ())
```

:::leanPillCaption "Randomness-leak package"
:::

```anchor randLeak (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Construction)
def randLeak (gen : G) : (scheme (F := F) gen).RandLeak where
  KeygenRand := F
  EncRand := Unit
  rkeygenAFreshRleak := rkeygenRleak gen
  rkeygenBFreshRleak := rkeygenRleak gen
  rencARleak := rencRleak
  rencBRleak := rencRleak
  rkeygenAFresh_fst := rkeygenRleak_fst gen
  rkeygenBFresh_fst := rkeygenRleak_fst gen
  rencA_fst := rencRleak_fst
  rencB_fst := rencRleak_fst
```
:::::::

:::defTitle "rkem_from_ddh_nonfs_correctness" "RKEM from DDH non-FS correctness"
:::

::::theorem "rkem_from_ddh_nonfs_correctness" (parent := "rkem_rkem_from_ddh_non_fs") (lean := "ddhRKEM.prEvent_correctExpA_eq_one, ddhRKEM.evalDistEq_ratchetRoundOutputA_rkeygen, ddhRKEM.deltaCorrect") (tags := "gh-67") (uses := "rkem_from_ddh_nonfs_spec, rkem_scheme, rkem_correctness")
Adapted from {Informal.citet TR25}[], Theorem A.3.

The non-forward-secure RKEM from DDH is perfectly correct, that is, $`(0,0)`-correct in the sense of the {bpref "rkem_correctness"}[RKEM correctness definition]. Explicitly, for each party $`\mathsf{P}\in\{\A,\B\}` with peer $`\mathsf{\bar P}`, consider one round of the protocol from $`\mathsf{P}` towards $`\mathsf{\bar P}`:

$$`\begin{array}{l}
(\ek_\mathsf{P},\dk_\mathsf{P})\sample\DRKG{P},\quad (\ekh{\bar P},\dkh{\bar P})\sample\DRKGup{\bar P}, \\
(\ct_{\mathsf{\bar P}},K,\dkh{P})\gets\REnc\text{-}\mathsf{P}(\ekh{\bar P},\dk_\mathsf{P}),\quad (K',\ekh{P})\gets\RDec\text{-}\mathsf{\bar P}(\dkh{\bar P},\ct_{\mathsf{\bar P}},\ek_\mathsf{P}).
\end{array}`

Then:

1. *Correctness with updated keys:* $`\Pr[K=K']=1`.
2. *Correctness of the update-key distribution:* the pair $`(\ekh{P},\dkh{P})` is distributed exactly as $`\DRKGup{P}`.

:::leanPillCaption "Perfect correctness"
:::

```anchor deltaCorrect (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Correctness)
theorem deltaCorrect [DecidableEq G] (gen : G) :
    RKEMScheme.deltaCorrect (scheme (F := F) gen) ProbCompRuntime.probComp 0 0
```
::::

:::defTitle "rkem_from_ddh_nonfs_ind_cpa" "RKEM from DDH non-FS IND-CPA security"
:::

:::::::theorem "rkem_from_ddh_nonfs_ind_cpa" (parent := "rkem_rkem_from_ddh_non_fs") (lean := "ddhRKEM.ddhReduction, ddhRKEM.indCpaAdvantageA_eq, ddhRKEM.indCpaAdvantageB_eq, ddhRKEM.INDCPASecure") (tags := "gh-375") (uses := "rkem_from_ddh_nonfs_spec, rkem_scheme, rkem_ind_cpa")
Adapted from {Informal.citet TR25}[], Theorem A.4.

Let $`G=\langle g\rangle` be of prime order $`q`, so that $`x\mapsto g^x` is a bijection $`\mathbb{Z}_q\to G`. In Lean, this is the hypothesis

:::leanPillCaption "Generator hypothesis"
:::

```anchor bijectiveGenerator (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Security)
    (hg : Function.Bijective (· • gen : F → G))
```

For each party $`\mathsf{P}\in\{\A,\B\}` and every IND-CPA adversary $`\adv` against the non-forward-secure RKEM from DDH, the DDH adversary $`\mathcal{B}` below satisfies

$$`\mathsf{Adv}^{\mathsf{IND\text{-}CPA}\text{-}\mathsf{P}}(\adv)=\tfrac12\,\mathsf{Adv}^{\mathsf{DDH}}(\mathcal{B}),`

with $`\mathsf{Adv}^{\mathsf{DDH}}(\mathcal{B})=|\Pr[\mathcal{B}\text{ outputs }1\text{ on a real triple}]-\Pr[\mathcal{B}\text{ outputs }1\text{ on a random triple}]|` the distinguishing advantage. The factor $`\tfrac12` only converts this distinguishing advantage into the bias advantage $`|\Pr[\cdot]-\tfrac12|` of the IND-CPA game; the reduction is tight.

Consequently, if every DDH adversary has advantage at most $`\varepsilon`, the scheme is $`\tfrac{\varepsilon}{2}`-IND-CPA secure in the sense of {bpref "rkem_ind_cpa"}[RKEM IND-CPA].

::::::gameGrid
:::::gameCell "\\mathcal{B}(g,X,Y,T)" (kind := "compact")
$`\begin{array}{l}
b'\sample\adv(X,X,Y,(),T)\pcomment{\ekA=\ekh{A}=X,\ \ekh{B}=Y,\ \ct_\B=()} \\
\Return b'
\end{array}`
:::::
::::::

:::leanPillCaption "DDH reduction"
:::

```anchor ddhReduction (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Security)
def ddhReduction (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    DiffieHellman.DDHAdversary F G :=
  fun _gen ekA ekBHat key => adversary () ekA ekA ekBHat () key
```

:::leanPillCaption "Tight reduction, party A"
:::

```anchor indCpaAdvantageA_eq (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Security)
theorem indCpaAdvantageA_eq (gen : G)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).indCpaAdvantageA adversary =
      (ddhAdvantage gen (ddhReduction (F := F) adversary)).toReal / 2
```

:::leanPillCaption "IND-CPA security"
:::

```anchor INDCPASecure (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.Security)
theorem INDCPASecure (gen : G) (hg : Function.Bijective (· • gen : F → G)) (ε : ℝ)
    (hddh : ∀ adversary : DDHAdversary F G, (ddhAdvantage gen adversary).toReal ≤ ε)
    (adversaryA adversaryB : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).INDCPASecure adversaryA adversaryB (ε / 2)
```
:::::::

:::defTitle "rkem_from_ddh_nonfs_ratchet_sim" "RKEM from DDH non-FS ratchet simulatability"
:::

:::::::theorem "rkem_from_ddh_nonfs_ratchet_sim" (parent := "rkem_rkem_from_ddh_non_fs") (lean := "ddhRKEM.rsimKey1, ddhRKEM.rsimKey2, ddhRKEM.rsimCtxt, ddhRKEM.ratchetSimulator, ddhRKEM.RatchetSimulatable") (tags := "gh-68") (uses := "rkem_from_ddh_nonfs_spec, rkem_scheme, rkem_ratchet_sim")
Adapted from {Informal.citet TR25}[], Theorem A.5 and Figure 30.

Let $`(\RSimKey\text{-}\mathsf{P}_1,\RSimKey\text{-}\mathsf{P}_2,\RSimCtxt\text{-}\mathsf{P})_{\mathsf{P}\in\{\A,\B\}}` be the simulators of Figure 30, given below. The non-forward-secure RKEM from DDH is perfectly ratchet simulatable with respect to these simulators, that is, $`0`-ratchet simulatable in the sense of the {bpref "rkem_ratchet_sim"}[RKEM ratchet simulatability definition]. Explicitly, for each property $`\mathsf{X}\in\{\mathsf{KeyBaseSim},\mathsf{KeyUpdSim},\mathsf{CtxtSim}\}` and each party $`\mathsf{P}\in\{\A,\B\}`, the real and simulated distributions are identical,

$$`\mathcal{D}^{\mathsf{X}}_{\mathsf{P},0}=\mathcal{D}^{\mathsf{X}}_{\mathsf{P},1},`

and consequently every distinguisher $`\adv` has advantage $`\mathsf{Adv}^{\mathsf{X}\text{-}\mathsf{P}}(\adv)=0`.

:::leanPillCaption "Perfect ratchet simulatability"
:::

```anchor RatchetSimulatable (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.RatchetSimulatability)
theorem RatchetSimulatable (gen : G) :
    (scheme (F := F) gen).RatchetSimulatable (leak := randLeak gen) 0
```

Ratchet simulatability is stated relative to the construction's randomness-leak package (see the {bpref "rkem_from_ddh_nonfs_spec"}[RKEM from DDH non-FS construction]).

The simulators are the same for both parties $`\mathsf{P}\in\{\A,\B\}`, with peer $`\mathsf{\bar P}`. They follow Figure 30 of the paper, and the simulation is perfect as printed.

::::::gameGrid
:::::gameCell "\\RSimKey\\text{-}\\mathsf{P}_1(\\ek_\\mathsf{P}:=X,\\dk_\\mathsf{P}:=x)\\quad\\mathsf{P}\\in\\{\\A,\\B\\}" (kind := "compact")
$`\begin{array}{l}
\aux_1:=x \\
\Return(X,x,\aux_1)\pcomment{\text{keys left unchanged, as by }\REnc\text{-}\mathsf{P}} \\
\pcommentline{\text{Fig. 30: }(x,X,\aux_1)}
\end{array}`

:::leanPillCaption "RSimKey-P₁"
:::

```anchor rsimKey1 (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.RatchetSimulatability)
def rsimKey1 (_par : Unit) (ekSelf : G) (dkSelf : F) : ProbComp (G × F × F) := do
  let aux := dkSelf
  return (ekSelf, dkSelf, aux)
```
:::::

:::::gameCell "\\RSimKey\\text{-}\\mathsf{P}_2(\\ekh{\\bar P}:=Y,\\dkh{\\bar P}:=y,\\aux_1:=x)\\quad\\mathsf{P}\\in\\{\\A,\\B\\}" (kind := "compact")
$`\begin{array}{l}
K:=Y^x\pcomment{=X^y=g^{xy}\text{, the peer's }K'} \\
\ct_{\mathsf{\bar P}}:=();\;\rand_2:=()\pcomment{\REnc\text{-}\mathsf{P}\text{ is deterministic}} \\
\Return(\ct_{\mathsf{\bar P}},K,K,\rand_2)
\end{array}`

:::leanPillCaption "RSimKey-P₂"
:::

```anchor rsimKey2 (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.RatchetSimulatability)
def rsimKey2 (_par : Unit) (ekPeerHat : G) (_dkPeerHat : F) (aux : F) :
    ProbComp (Unit × G × G × Unit) := do
  let dkSelf := aux
  let key := dkSelf • ekPeerHat
  let ctPeer := ()
  let rand₂ := ()
  return (ctPeer, key, key, rand₂)
```
:::::

:::::gameCell "\\RSimCtxt\\text{-}\\mathsf{P}(\\ekh{P}:=X,\\ekh{\\bar P}:=Y,\\dkh{\\bar P}:=y)\\quad\\mathsf{P}\\in\\{\\A,\\B\\}" (kind := "compact")
$`\begin{array}{l}
K:=X^y\pcomment{=g^{xy}} \\
\ct_{\mathsf{\bar P}}:=() \\
\Return(\ct_{\mathsf{\bar P}},X,K,K)\pcomment{\ek_\mathsf{P}:=\ekh{P}\text{, as }\RDec\text{-}\mathsf{\bar P}\text{ returns it}}
\end{array}`

:::leanPillCaption "RSimCtxt-P"
:::

```anchor rsimCtxt (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.RatchetSimulatability)
def rsimCtxt (_par : Unit) (ekSelfHat _ekPeerHat : G) (dkPeerHat : F) :
    ProbComp (Unit × G × G × G) := do
  let key := dkPeerHat • ekSelfHat
  let ctPeer := ()
  return (ctPeer, ekSelfHat, key, key)
```
:::::
::::::

:::leanPillCaption "Ratchet simulators"
:::

```anchor ratchetSimulator (project := ".") (module := SecureMessaging.RKEM.FromDDHNonFS.RatchetSimulatability)
def ratchetSimulator (gen : G) : (scheme (F := F) gen).RatchetSimulator (randLeak gen) where
  Aux := F
  rsimKeyA1 := rsimKey1
  rsimKeyA2 := rsimKey2
  rsimCtxtA := rsimCtxt
  rsimKeyB1 := rsimKey1
  rsimKeyB2 := rsimKey2
  rsimCtxtB := rsimCtxt
```
:::::::
