import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
import SecureMessaging.SCKA.MLKEMBraid.Basic
import SecureMessaging.SCKA.MLKEMBraid.Construction
import SecureMessaging.SCKA.MLKEMBraid.Correctness
import SecureMessaging.SCKA.MLKEMBraid.Security

/-! # Blueprint chapter: ML-KEM Braid -/

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

#doc (Manual) "ML-KEM Braid" =>

*References:*

- {Informal.citet MLKEM_Braid}[]
- {Informal.citet SCKA25}[]

:::group "cka_protocols_mlkem_braid"
ML-KEM Braid ({Informal.citet MLKEM_Braid}[]).
:::

:::defTitle "mlkem_braid_ratcheted_authenticator" "ML-KEM Braid ratcheted authenticator"
:::

::::definition "mlkem_braid_ratcheted_authenticator" (parent := "cka_protocols_mlkem_braid") (lean := "RatchetedAuthenticator") (tags := "gh-245") (uses := "scka_scheme")

:::leanPillCaption "ratcheted authenticator interface"
:::

```anchor RatchetedAuthenticator (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Authenticator)
structure RatchetedAuthenticator
    (InitKey EpochKey AuthState Header Ciphertext Mac : Type) where
  /-- Initialize authenticator state from an initial key and epoch. -/
  init : InitKey → ℕ → AuthState
  /-- Ratchet the authenticator state with an epoch key at the given epoch. -/
  update : AuthState → ℕ → EpochKey → AuthState
  /-- MAC a header at the given epoch. -/
  macHeader : AuthState → ℕ → Header → Mac
  /-- Verify a MAC on a header at the given epoch. -/
  verifyHeader : AuthState → ℕ → Header → Mac → Bool
  /-- MAC a ciphertext at the given epoch. -/
  macCiphertext : AuthState → ℕ → Ciphertext → Mac
  /-- Verify a MAC on a ciphertext at the given epoch. -/
  verifyCiphertext : AuthState → ℕ → Ciphertext → Mac → Bool
  /-- Honestly produced header MACs verify successfully. -/
  verifyHeader_correct :
    ∀ (s : AuthState) (ep : ℕ) (h : Header),
      verifyHeader s ep h (macHeader s ep h) = true
  /-- Honestly produced ciphertext MACs verify successfully. -/
  verifyCiphertext_correct :
    ∀ (s : AuthState) (ep : ℕ) (c : Ciphertext),
      verifyCiphertext s ep c (macCiphertext s ep c) = true
```
::::

:::group "mlkem_braid_protocol"
ML-KEM Braid.
:::

:::defTitle "mlkem_braid_protocol_parameters" "Protocol parameters"
:::

::::definition "mlkem_braid_protocol_parameters" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.Parameters") (uses := "incremental_kem_scheme, erasure_code_payload")

:::leanPillCaption "incremental KEM, pure receive operations, epoch-key derivation, and streams"
:::

```anchor Braid_Parameters (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
structure Parameters (m : Type → Type u) [Monad m] where
  /-- KEM shared secret. -/
  K : Type
  /-- Encapsulation key. -/
  PK : Type
  /-- Decapsulation key. -/
  SK : Type
  /-- Ciphertext. -/
  C : Type
  /-- The key-encapsulation mechanism. -/
  kem : KEMScheme m K PK SK C
  /-- The incremental KEM structure. -/
  inc : kem.IncrementalStructure
  /-- Pure decapsulation agreeing with `kem.decaps`. -/
  hDet : kem.DeterministicDecaps
  /-- Pure second-stage encapsulation agreeing with `inc.encaps2`. -/
  hEnc2 : inc.DeterministicEncaps2
  /-- Epoch key output by `KDF_OK`. -/
  EpochKey : Type
  /-- MAC tag. -/
  Mac : Type
  /-- Erasure-code symbol alphabet, shared by the four streams. -/
  Sym : Type
  /-- `KDF_OK(shared_secret, epoch)`. -/
  kdfOK : K → ℕ → EpochKey
  /-- Header stream, recovering `header ‖ mac`. -/
  ecpHdr : ErasureCodePayload (inc.PKheader × Mac) Sym
  /-- Encapsulation-key-vector stream. -/
  ecpEk : ErasureCodePayload inc.PKvector Sym
  /-- `ct₁` stream. -/
  ecpCt1 : ErasureCodePayload inc.C₁ Sym
  /-- `ct₂` stream, recovering `ct₂ ‖ mac`. -/
  ecpCt2 : ErasureCodePayload (inc.C₂ × Mac) Sym
```
::::

:::defTitle "mlkem_braid_protocol_messages" "Messages"
:::

::::definition "mlkem_braid_protocol_messages" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.MessageType, MLKEMBraid.Message")

:::leanPillCaption "message types"
:::

```anchor Braid_MessageType (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
inductive MessageType where
  /-- `None`: no payload. -/
  | none
  /-- `Hdr`: header-stream chunk. -/
  | hdr
  /-- `Ek`: encapsulation-key-vector chunk. -/
  | ek
  /-- `EkCt1Ack`: encapsulation-key chunk, and the sender has all of `ct₁`. -/
  | ekCt1Ack
  /-- `Ct1Ack`: the sender has all of `ct₁`, no payload. No transition sends or consumes
  it. -/
  | ct1Ack
  /-- `Ct1`: `ct₁`-stream chunk. -/
  | ct1
  /-- `Ct2`: `ct₂`-stream chunk. -/
  | ct2
```

:::leanPillCaption "protocol message"
:::

```anchor Braid_Message (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
structure Message (Sym : Type) where
  /-- `epoch`: the epoch being negotiated. -/
  epoch : ℕ
  /-- `type`: which stream, acknowledgment, or empty message this is. -/
  type : MessageType
  /-- `data`: the indexed erasure-code chunk, if any. -/
  data : Option (ℕ × Sym)
```

::::

:::defTitle "mlkem_braid_protocol_states" "Protocol states"
:::

::::definition "mlkem_braid_protocol_states" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.State") (uses := "erasure_code_streaming")

:::leanPillCaption "the eleven protocol states"
:::

```anchor Braid_State (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
inductive State (P : Parameters m) (AuthState : Type) where
  /-- "KeysUnsampled": no additional state. -/
  | keysUnsampled (epoch : ℕ) (auth : AuthState)
  /-- "KeysSampled": `sk`, `ek_vector`, `header_encoder`. -/
  | keysSampled (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ekVector : P.inc.PKvector)
      (headerEncoder : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
  /-- "HeaderSent": `sk`, `ct1_decoder`, `ek_encoder`. -/
  | headerSent (epoch : ℕ) (auth : AuthState) (sk : P.SK)
      (ct1Decoder : DecoderState P.inc.C₁ P.Sym)
      (ekEncoder : EncoderState P.inc.PKvector P.Sym)
  /-- "Ct1Received": `sk`, `ct1`, `ek_encoder`. -/
  | ct1Received (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (ekEncoder : EncoderState P.inc.PKvector P.Sym)
  /-- "EkSentCt1Received": `sk`, `ct1`, `ct2_decoder`. -/
  | ekSentCt1Received (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (ct2Decoder : DecoderState (P.inc.C₂ × P.Mac) P.Sym)
  /-- "NoHeaderReceived": `header_decoder`. -/
  | noHeaderReceived (epoch : ℕ) (auth : AuthState)
      (headerDecoder : DecoderState (P.inc.PKheader × P.Mac) P.Sym)
  /-- "HeaderReceived": `header`, `ek_decoder`. -/
  | headerReceived (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (ekDecoder : DecoderState P.inc.PKvector P.Sym)
  /-- "Ct1Sampled": `header`, `encaps_state`, `ct1`, `ct1_encoder`, `ek_decoder`. -/
  | ct1Sampled (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁)
      (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
      (ekDecoder : DecoderState P.inc.PKvector P.Sym)
  /-- "EkReceivedCt1Sampled": `encaps_state`, `ct1`, `header`, `ek_vector`,
  `ct1_encoder`. -/
  | ekReceivedCt1Sampled (epoch : ℕ) (auth : AuthState)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁) (header : P.inc.PKheader)
      (ekVector : P.inc.PKvector) (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
  /-- "Ct1Acknowledged": `header`, `encaps_state`, `ct1`, `ek_decoder`. -/
  | ct1Acknowledged (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁)
      (ekDecoder : DecoderState P.inc.PKvector P.Sym)
  /-- "Ct2Sampled": `ct2_encoder`. -/
  | ct2Sampled (epoch : ℕ) (auth : AuthState)
      (ct2Encoder : EncoderState (P.inc.C₂ × P.Mac) P.Sym)
```
::::

:::defTitle "mlkem_braid_protocol_transitions" "Send and receive"
:::

::::definition "mlkem_braid_protocol_transitions" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.send, MLKEMBraid.receive") (uses := "mlkem_braid_protocol_parameters, mlkem_braid_ratcheted_authenticator, erasure_code_streaming")

:::leanPillCaption "send transition"
:::

```anchor Braid_send (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) : m (SendResult P AuthState)
```

:::leanPillCaption "receive transition"
:::

```anchor Braid_receive (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def receive (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Except Failure (RecvResult P AuthState)
```
::::

:::defTitle "mlkem_braid_protocol_init" "Initialization"
:::

::::definition "mlkem_braid_protocol_init" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.initA, MLKEMBraid.initB") (uses := "mlkem_braid_ratcheted_authenticator, erasure_code_streaming")

:::leanPillCaption "Alice's initial state"
:::

```anchor Braid_initA (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def initA (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : State P AuthState
```

:::leanPillCaption "Bob's initial state"
:::

```anchor Braid_initB (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def initB (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : State P AuthState
```
::::

:::defTitle "mlkem_braid_spec" "ML-KEM Braid protocol"
:::

::::definition "mlkem_braid_spec" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.scheme") (tags := "gh-271") (uses := "scka_scheme, mlkem_braid_protocol_transitions, mlkem_braid_protocol_init")

:::leanPillCaption "ML-KEM Braid as an SCKA scheme"
:::

```anchor Braid_scheme (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def scheme (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)
    :=
  let sendSCKA (st : State P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : State P AuthState) := do
    let (r, rand) ← sendRleak P irl auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state, rand))
  { initKeyGen := sampleInitKey
    initA := fun ik => pure (initA P auth ik)
    initB := fun ik => pure (initB P auth ik)
    sendA := sendSCKA
    sendArleak := sendRleakSCKA
    recvA := recvSCKA P auth
    sendB := sendSCKA
    sendBrleak := sendRleakSCKA
    recvB := recvSCKA P auth }
```
::::

:::defTitle "mlkem_braid_correctness" "ML-KEM Braid correctness"
:::

::::theorem "mlkem_braid_correctness" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.correctness_error_le, MLKEMBraid.mlkemBraidScheme_correctness_error_le") (tags := "gh-243") (uses := "mlkem_braid_spec, scka_correctness, incremental_kem_scheme, incremental_kem_rand_leak, erasure_code_correctness")
$`\todo`

:::leanPillCaption "Correctness error bound"
:::

```anchor Braid_correctness_error_le (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Correctness)
theorem correctness_error_le
    (P : Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message P.Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr{let x ← SCKAScheme.correctnessExp (scheme P auth irl sampleInitKey) adv}[x = true] ≤
      (q : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp
```
::::

:::defTitle "mlkem_braid_noauth_experiment" "Braid without authentication"
:::

::::definition "mlkem_braid_noauth_experiment" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.Bounded.parameters, MLKEMBraid.NoAuth.auth, MLKEMBraid.NoAuth.nativeExposure, SCKAScheme.securityExp, MLKEMBraid.NoAuth.securityGame_equiv_native, MLKEMBraid.NoAuth.deltaExposure, MLKEMBraid.NoAuth.sendExposure_eq_delta, MLKEMBraid.NoAuth.securityGame_equiv_delta") (uses := "mlkem_braid_spec, scka_oracles, erasure_code_correctness")
Fix an ML-KEM parameter set, ring operations and primitive operations. Write
$`\mathsf K=(\mathsf{Gen},\mathsf{Enc},\mathsf{Dec})` for the resulting KEM, with
shared-secret space $`\mathcal K`. Let $`\mathcal I` be an epoch-key space with
sampling distribution $`\mu`, and fix a key-derivation function
$`F:\mathcal K\times\mathbb N\to\mathcal I`. The key of epoch $`e` with shared secret $`k` is
$`F(k,e)`.

Let $`\Pi` be the {uses "mlkem_braid_spec"}[Braid construction] with these algorithms, byte
encodings of the prescribed lengths, and Reed–Solomon codes for its four streams: the header, the
public-key vector and the two ciphertext components. The initial shared value and the
authentication tag are fixed. The authenticator keeps no state and accepts every tag.

A classical adversary $`A` adaptively requests sends, deliveries of recorded messages,
corruptions of a local state, sends that reveal their randomness, and challenges of epoch keys.
A delivery names a message that was sent before. It cannot supply new contents.

The experiment samples $`b\sample\{0,1\}` and keeps two sets of epochs: the exposed epochs
$`E` and the challenged epochs $`C`, both empty at the start. A challenge of $`e` requires
$`e\notin E\cup C` and a stored key for $`e`. If $`b=0`, it returns Alice's key of epoch $`e`, or
Bob's key if Alice has none. If $`b=1`, it returns an independent sample from $`\mu`. In both
cases it adds $`e` to $`C`.

:::table
* * Revelation
  * Epochs exposed
* * A party's local state
  * None before key generation, while awaiting a header, or after receiving a header but
    before first-stage encapsulation; otherwise its current epoch.
* * A send's randomness
  * Its epoch if the send generates a key pair or performs first-stage encapsulation;
    none otherwise.
:::

A revelation that would expose an epoch in $`C` is refused. Otherwise its epochs are added to
$`E`. A refused send that reveals its randomness keeps no new state. If $`A` outputs $`b'`, define

$$`\operatorname{Adv}^{\mathrm{guess}}_{\Pi}(A)
=\left|\Pr[b'=b]-\frac12\right|.`

A send budget $`q` bounds the total number of send requests to both parties on every path of
oracle answers. The count includes ordinary sends, sends that reveal their randomness, and
refused requests.

On every send that the protocol can produce, the randomness row of the table exposes exactly the
epochs that the local state after the send exposes and the state before it does not. This is the
rule of {Informal.citet SCKA25}[], Figure 1. The experiment that uses this rule for sends has the
same guessing advantage.

:::leanPillCaption "authenticator that keeps no state"
:::

```anchor noAuthAuthenticator (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth)
def auth (P : Parameters ProbComp) (hMac : P.Mac = Unit) :
    RatchetedAuthenticator Unit P.EpochKey Unit
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac where
  init := fun _ _ => ()
  update := fun _ _ _ => ()
  macHeader := fun _ _ _ => hMac.symm ▸ ()
  macCiphertext := fun _ _ _ => hMac.symm ▸ ()
  verifyHeader := fun _ _ _ _ => true
  verifyCiphertext := fun _ _ _ _ => true
  verifyHeader_correct := fun _ _ _ => rfl
  verifyCiphertext_correct := fun _ _ _ => rfl
```

:::leanPillCaption "exposure functions of the experiment"
:::

```anchor nativeExposure (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.Bounds)
def nativeExposure (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.VulnerableEpochs (State P Unit)
      (SendRand irl.KeygenRand irl.Encaps1Rand) where
  corrupt := vuln
  rleak := fun st coins => sendExposure st st coins
```
::::

:::defTitle "mlkem_braid_noauth_reductions" "Epoch reductions"
:::

::::definition "mlkem_braid_noauth_reductions" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.NoAuth.repairedRecv, MLKEMBraid.NoAuth.kemReduction, MLKEMBraid.NoAuth.kdfReduction, MLKEMBraid.NoAuth.kdfExp, MLKEMBraid.NoAuth.kemMixReduction, MLKEMBraid.NoAuth.KDFContextAdversary, MLKEMBraid.NoAuth.kdfContextExp, MLKEMBraid.NoAuth.kdfAdvantage, MLKEMBraid.NoAuth.kdfMixReduction") (uses := "mlkem_braid_noauth_experiment, incremental_kem_scheme")
We use the KEM $`\mathsf K`, the shared-secret space $`\mathcal K`, the epoch-key distribution
$`\mu` and the key-derivation function $`F` of the
{uses "mlkem_braid_noauth_experiment"}[experiment].

The repaired experiment records the shared secret $`k_e` of the encapsulation of each epoch
$`e`. Suppose that a receiver awaits the second ciphertext component of epoch $`e`, and that a
well-formed message of epoch $`e` completes its decoder. If $`k_e` is recorded, the receiver
outputs $`F(k_e,e)` instead of decapsulating, and enters the next epoch. All other receives are
unchanged.

For each $`e\geq1`, we construct two reductions $`B_e` and $`D_e` from $`A`:

- $`B_e` is an IND-CPA adversary against $`\mathsf K`. Its input $`(pk,c,x)` is a public key, a
  ciphertext, and a key $`x` that is either the shared secret encapsulated in $`c` or an
  independent uniform shared secret. $`B_e` runs the repaired experiment with $`pk`, $`c` and
  $`x` installed at epoch $`e`: they take the place of the key pair, the encapsulation and the
  shared secret that the protocol would sample in epoch $`e`.
- $`D_e` is a key-derivation distinguisher. Its input $`x` is either $`F(u,e)` for a uniform
  $`u\in\mathcal K` or a sample from $`\mu`. $`D_e` samples all KEM material itself, runs the
  repaired experiment, and answers the challenge of $`e` with $`x`.

In both reductions, challenges of epochs before $`e` receive independent samples from $`\mu`, and
challenges of epochs after $`e` receive their real keys. Both return $`A`'s bit, or $`0` if epoch
$`e` becomes exposed. Together, $`B_e` and $`D_e` lead from the hybrid in which the epochs before
$`e` get uniform keys to the hybrid in which the epochs up to $`e` get uniform keys. This is why
the averaged reductions $`B` and $`D` below give the factor $`q` in the bound.

Let $`q` be a send budget. For $`q>0`, the reduction $`B` draws $`e` uniformly from
$`\{1,\dots,q\}` and then runs $`B_e`. The reduction $`D` draws $`e` in the same way, announces
it, and then runs $`D_e`. For $`q=0`, both reductions use $`e=1`.

Let $`(pk,sk)\sample\mathsf{Gen}()` and $`(c,k)\sample\mathsf{Enc}(pk)`. Let $`U_{\mathcal K}`
be an independent uniform shared secret and $`U_{\mathcal I}` an independent sample from
$`\mu`. Define

$$`\begin{aligned}
\alpha&=\left|\Pr[B(pk,c,k)=1]-\Pr[B(pk,c,U_{\mathcal K})=1]\right|,\\
\beta&=\left|\Pr[D(F(U_{\mathcal K},e))=1]-\Pr[D(U_{\mathcal I})=1]\right|,\\
\varepsilon&=1-\Pr[\mathsf{Dec}(sk,c)\text{ returns }k].
\end{aligned}`

In $`\beta`, $`e` is the epoch that $`D` announces before $`U_{\mathcal K}` is sampled. So
$`\alpha` is an IND-CPA advantage against $`\mathsf K`, and $`\beta` is the advantage of a
distinguisher between $`F(U_{\mathcal K},e)` and a sample from $`\mu`, for a label $`e` of its
choice. The probabilities include all randomness of the algorithms and of the simulation. A
decapsulation that fails does not return $`k`.

:::leanPillCaption "IND-CPA reduction with a random epoch"
:::

```anchor kemMixReduction (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Average)
def kemMixReduction (A : Adversary P irl) (q : ℕ) : P.kem.IND_CPA_Adversary where
  State := P.PK × ℕ
  preChallenge pk := do pure (pk, ← epochChoice q)
  postChallenge
    | (_, 0), _, _ => pure false
    | (pk, e + 1), c, k => stoppedRun
        (simImpl P hMac irl (e + 1)
          { pk, ct1 := (P.inc.splitC c).1, ct2 := (P.inc.splitC c).2, key := k })
        (simStop (e + 1)) A (simInit P hMac)
```

:::leanPillCaption "key-derivation reduction with a random epoch"
:::

```anchor kdfMixReduction (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Average)
def kdfMixReduction (A : Adversary P irl) (q : ℕ) : KDFContextAdversary P where
  State := ℕ
  context := do let e ← epochChoice q; pure (e, e)
  guess e x := kdfReduction P hMac irl A e x
```

:::leanPillCaption "key-derivation game and advantage"
:::

```anchor kdfGame (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.Games)
def kdfExp (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    (e : ℕ) (D : P.EpochKey → ProbComp Bool) (derived : Bool) : ProbComp Bool :=
  if derived then do
    let u ← $ᵗ P.K
    D (P.kdfOK u e)
  else do
    let x ← $ᵗ P.EpochKey
    D x

/-- A key-derivation distinguisher that first chooses the epoch label. -/
structure KDFContextAdversary (P : Parameters ProbComp) where
  /-- The information kept between choosing the label and guessing. -/
  State : Type
  /-- Choose the epoch label and the kept information. -/
  context : ProbComp (ℕ × State)
  /-- Guess from the kept information and the epoch key received. -/
  guess : State → P.EpochKey → ProbComp Bool

/-- Key-derivation game. The label `e` is chosen first; then `kdfExp` runs the fixed-epoch game at
`e`: with `derived = true` the distinguisher receives `kdfOK u e` for uniform `u`, with `false` a
uniform epoch key. -/
def kdfContextExp (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    (C : KDFContextAdversary P) (derived : Bool) : ProbComp Bool := do
  let (e, st) ← C.context
  kdfExp P e (C.guess st) derived

/-- Distinguishing advantage of a key-derivation adversary. -/
noncomputable def kdfAdvantage (P : Parameters ProbComp) [SampleableType P.K]
    [SampleableType P.EpochKey] (C : KDFContextAdversary P) : ℝ :=
  (𝒟[kdfContextExp P C true].boolDist 𝒟[kdfContextExp P C false]).toReal
```
::::

:::defTitle "mlkem_braid_noauth_security" "Security without internal authentication"
:::

::::theorem "mlkem_braid_noauth_security" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.security, MLKEMBraid.NoAuth.security") (tags := "gh-244") (uses := "mlkem_braid_spec, scka_security, incremental_kem_scheme, mlkem_braid_noauth_experiment, mlkem_braid_noauth_reductions")
For every adversary $`A` with send budget $`q`, the {uses "mlkem_braid_noauth_experiment"}[protocol $`\Pi`] satisfies

$$`\operatorname{Adv}^{\mathrm{guess}}_{\Pi}(A)
\leq\frac q2(\alpha+\beta)+q\varepsilon,`

where $`\alpha,\beta,\varepsilon` are defined by the {uses "mlkem_braid_noauth_reductions"}[epoch reductions].

The network is passive: $`A` can delay and reorder messages but cannot change them. The internal
authenticator is off. Nothing is assumed about $`F`. The Braid specification derives epoch keys
with HKDF, and $`\beta` measures how well a distinguisher tells $`F(U_{\mathcal K},e)` from a
sample of $`\mu`.

The second statement below gives the same bound for any KEM with incremental encapsulation and
any correct erasure codes for the four streams.

:::leanPillCaption "security"
:::

```anchor security (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security)
theorem MLKEMBraid.security
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey : Type} [SampleableType EpochKey] [DecidableEq EpochKey]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey) :
    let P := MLKEMBraid.Bounded.parameters p ring prims kdfOK
    let irl := MLKEM.incrementalRandLeak ring
      (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
      (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
    ∀ (A : MLKEMBraid.NoAuth.Adversary P irl) (q : ℕ),
      MLKEMBraid.NoAuth.SendQueryBound A q →
      let ℬ := MLKEM.Bounded.liftAdversary p ring prims
        (MLKEMBraid.NoAuth.kemMixReduction P rfl irl A q)
      let 𝒞 := MLKEMBraid.NoAuth.kdfMixReduction P rfl irl A q
      let ε := ((MLKEM.mlkemScheme p ring prims).correctnessError
        ProbCompRuntime.probComp).toReal
      SCKAScheme.sckaGuessAdvantage
        (MLKEMBraid.NoAuth.scheme P rfl irl) A
        (MLKEMBraid.NoAuth.nativeExposure P irl)
        (MLKEMBraid.NoAuth.nativeExposure P irl) ≤
        (q / 2 : ℝ) *
          (((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
            MLKEMBraid.NoAuth.kdfAdvantage P 𝒞) + q * ε
```

:::leanPillCaption "security for an abstract KEM and abstract codes"
:::

```anchor genericSecurity (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security)
theorem MLKEMBraid.NoAuth.security (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (q : ℕ) (hq : SendQueryBound A q) :
    let ℬ := kemMixReduction P hMac irl A q
    let 𝒞 := kdfMixReduction P hMac irl A q
    let ε := (P.kem.correctnessError ProbCompRuntime.probComp).toReal
    SCKAScheme.sckaGuessAdvantage (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl) ≤
      (q / 2 : ℝ) * ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
        kdfAdvantage P 𝒞) + q * ε
```
::::
