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
import SecureMessaging.SCKA.MLKEMBraid.Security.Bounded
import SecureMessaging.SCKA.MLKEMBraid.Security.Native

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

::::definition "mlkem_braid_noauth_experiment" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.Bounded.parameters, MLKEMBraid.NoAuth.auth, MLKEMBraid.NoAuth.nativeExposure, SCKAScheme.securityExp") (uses := "mlkem_braid_spec, scka_oracles, erasure_code_correctness")
Fix an ML-KEM parameter set and ring and primitive operations. Write
$`\mathsf K=(\mathsf{Gen},\mathsf{Enc},\mathsf{Dec})` for the resulting KEM, with
shared-secret space $`\mathcal K`. Let $`\mathcal I` be an epoch-key space with
sampling distribution $`\mu`, and fix
$`F:\mathcal K\times\mathbb N\to\mathcal I`.

Let $`\Pi` be the {uses "mlkem_braid_spec"}[Braid construction] with these algorithms,
prescribed-length byte encodings, and Reed–Solomon codes for its header, public-key-vector
and two ciphertext streams. The initial shared value and authentication tag are fixed;
the authenticator retains no state and accepts every tag.

A classical adversary $`A` adaptively requests sends, deliveries of recorded messages,
local-state corruptions, sends with their randomness, and epoch-key challenges. Deliveries identify
previously sent messages; they cannot supply replacement contents.

The experiment samples $`b\sample\{0,1\}` and maintains exposed and challenged epoch sets
$`E,C`, initially empty. A challenge of $`e` requires $`e\notin E\cup C` and a stored key.
It returns Alice's key (Bob's if Alice has none) when $`b=0`, or an independent sample from
$`\mu` when $`b=1`, and adds $`e` to $`C`.

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

A revelation intersecting $`C` is refused; otherwise its epochs are added to $`E`.
A refused randomness-revealing send commits no proposed state. If $`A` outputs $`b'`, define

$$`\operatorname{Adv}^{\mathrm{guess}}_{\Pi}(A)
=\left|\Pr[b'=b]-\frac12\right|.`

A send budget $`q` bounds, on every query path, the total number of ordinary and
randomness-revealing send requests to both parties, including refused requests.
::::

:::defTitle "mlkem_braid_noauth_reductions" "Epoch reductions"
:::

::::definition "mlkem_braid_noauth_reductions" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.NoAuth.repairedRecv, MLKEMBraid.NoAuth.kemReduction, MLKEMBraid.NoAuth.kdfReduction, MLKEMBraid.NoAuth.kdfExp") (uses := "mlkem_braid_noauth_experiment, incremental_kem_scheme")
The repaired experiment records the shared secret $`k_e` of each epoch's encapsulation.
In the phase awaiting the second ciphertext component, a well-formed current-epoch message
that completes its decoder yields $`F(k_e,e)` when that encapsulation is recorded, and the
receiver enters the next epoch. All other receive cases are unchanged.

For each $`e\geq1`, construct reductions $`B_e` and $`D_e` from $`A`:

- $`B_e(pk,c,x)` runs the repaired experiment with the challenge public key and ciphertext
  installed at epoch $`e`, using $`x` as its shared secret. Earlier epoch challenges receive
  independent samples from $`\mu`; later challenges receive their real keys.
- $`D_e(x)` samples the KEM material itself and runs the repaired experiment, answering the
  challenge at $`e` with $`x`, earlier challenges with independent samples from $`\mu`, and
  later challenges with their real keys.

Both return $`A`'s bit, or $`0` if epoch $`e` becomes exposed. Let
$`(pk,sk)\sample\mathsf{Gen}()` and $`(c,k)\sample\mathsf{Enc}(pk)`. Define

$$`\begin{aligned}
\alpha_e&=\left|\Pr[B_e(pk,c,k)=1]-\Pr[B_e(pk,c,U_{\mathcal K})=1]\right|,\\
\beta_e&=\left|\Pr[D_e(F(U_{\mathcal K},e))=1]-\Pr[D_e(U_{\mathcal I})=1]\right|,\\
\varepsilon&=1-\Pr[\mathsf{Dec}(sk,c)\text{ returns }k].
\end{aligned}`

$`U_{\mathcal K}` is an independent uniform shared secret and $`U_{\mathcal I}` an independent
sample from $`\mu`. Probabilities include all algorithm and simulation randomness; a failed
decapsulation contributes no success probability.
::::

:::defTitle "mlkem_braid_noauth_security" "Security without authentication"
:::

::::theorem "mlkem_braid_noauth_security" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.NoAuth.security_le_native, MLKEMBraid.mlkemBraidScheme_noAuth_security_le_native, MLKEMBraid.mlkemBraidBounded_noAuth_security_le_native") (tags := "gh-244") (uses := "mlkem_braid_noauth_experiment, mlkem_braid_noauth_reductions")
For every adversary $`A` with send budget $`q`, the {uses "mlkem_braid_noauth_experiment"}[protocol $`\Pi`] satisfies

$$`\operatorname{Adv}^{\mathrm{guess}}_{\Pi}(A)
\leq\frac12\sum_{e=1}^{q}(\alpha_e+\beta_e)+q\varepsilon,`

where $`\alpha_e,\beta_e,\varepsilon` are defined by the {uses "mlkem_braid_noauth_reductions"}[epoch reductions].
::::

:::defTitle "mlkem_braid_security" "ML-KEM Braid security"
:::

::::theorem "mlkem_braid_security" (parent := "cka_protocols_mlkem_braid") (tags := "gh-244") (uses := "mlkem_braid_spec, scka_security, incremental_kem_scheme")
$`\todo`

:::leanPill "missing"
:::
::::
