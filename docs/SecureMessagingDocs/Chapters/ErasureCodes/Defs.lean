import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.ErasureCodeFigures
import SecureMessaging.ErasureCode.Streaming

/-! # Blueprint chapter: Erasure-Code Definitions -/

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

#doc (Manual) "Erasure-Code Definitions" =>

:::group "erasure_codes"
Erasure codes, their correctness, payload encoding, and stateful streaming.
:::

:::defTitle "erasure_code_scheme" "Erasure code scheme"
:::

:::::::definition "erasure_code_scheme" (parent := "erasure_codes") (lean := "ErasureCode, ErasureCode.Decodable") (tags := "gh-190")
Adapted from {Informal.citet SCKA25}[], Definition A.6.

An *erasure code* over a symbol set $`\Sigma`, with block length $`N` and message length
$`k`, where $`0<k\le N`, consists of two deterministic algorithms over the indices
$`[N]=\{0,\ldots,N-1\}`:

- $`\Encode(M,i)\to c`: the chunk $`c\in\Sigma` of a message $`M\in\Sigma^k` at an index
  $`i\in[N]`;
- $`\Decode(L)\to M`: recovery of a message $`M\in\Sigma^k` from a finite chunk set
  $`L\subseteq[N]\times\Sigma`, or $`\bot` on failure.

:::leanPillCaption "ErasureCode"
:::

```anchor ErasureCode (project := ".") (module := SecureMessaging.ErasureCode.Defs)
structure ErasureCode (Sym : Type) where
  /-- Number of valid encoded-chunk positions; valid indices are `0, …, N - 1`. -/
  N : ℕ
  /-- At least one encoded-chunk position is available. -/
  N_pos : 0 < N
  /-- Number of source symbols and distinct encoded chunks needed for recovery. -/
  nchunk : ℕ
  /-- At least one distinct encoded chunk is required for recovery. -/
  nchunk_pos : 0 < nchunk
  /-- The message fits within the codeword. -/
  nchunk_le_N : nchunk ≤ N
  /-- `Encode(M, i)`: the chunk encoding of message `M` at index `i`. -/
  encode : (Fin nchunk → Sym) → Fin N → Sym
  /-- `Decode(L)`: recover the message from a chunk set, or fail (`none`). -/
  decode : Finset (Fin N × Sym) → Option (Fin nchunk → Sym)
```

A chunk set $`L` is *decodable* if it contains at least $`k` chunks at pairwise distinct
indices: $`|L|\ge k`, and $`(i,c),(i,c')\in L` implies $`c=c'`.

:::leanPillCaption "Decodable"
:::

```anchor Decodable (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def Decodable {N : ℕ} (nchunk : ℕ) (chunks : Finset (Fin N × Sym)) : Prop :=
  nchunk ≤ chunks.card ∧ Set.InjOn Prod.fst (chunks : Set (Fin N × Sym))
```

::::::gameGrid
:::::gameCell "\\textsf{Illustration: encoding and decoding}" (kind := "scheme")
:::erasureCodeSchemeFigure
:::
:::::
::::::
:::::::

:::defTitle "erasure_code_correctness" "Erasure code correctness"
:::

::::definition "erasure_code_correctness" (parent := "erasure_codes") (lean := "ErasureCode.encodeChunks, ErasureCode.Correct") (tags := "gh-191") (uses := "erasure_code_scheme")
Adapted from {Informal.citet SCKA25}[], Definition A.6.

For a message $`M\in\Sigma^k` and an index set $`I\subseteq[N]`, the *chunk set* of $`M` at
$`I` is $`L_I(M)=\{(i,\Encode(M,i))\mid i\in I\}`.

:::leanPillCaption "encodeChunks"
:::

```anchor encodeChunks (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def encodeChunks (ec : ErasureCode Sym)
    (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)) :
    Finset (Fin ec.N × Sym) :=
  I.map {
    toFun := fun i => (i, ec.encode M i)
    inj' := fun _ _ h => congrArg Prod.fst h
  }
```

An {bpref "erasure_code_scheme"}[erasure code] is *correct* if, for every message $`M` and every
index set $`I`,

$$`\Decode(L_I(M))=\begin{cases}M&\text{if }|I|\ge k,\\\bot&\text{if }|I|<k.\end{cases}`

:::leanPillCaption "Correct"
:::

```anchor Correct (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def Correct (ec : ErasureCode Sym) : Prop :=
  ∀ (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)),
    (ec.nchunk ≤ I.card → ec.decode (ec.encodeChunks M I) = some M) ∧
    (I.card < ec.nchunk → ec.decode (ec.encodeChunks M I) = none)
```
::::

:::defTitle "erasure_code_payload" "Erasure-code payload"
:::

:::::::definition "erasure_code_payload" (parent := "erasure_codes") (lean := "ErasureCodePayload, ErasureCodePayload.counterIndex, ErasureCodePayload.encode, ErasureCodePayload.decode") (tags := "gh-251") (uses := "erasure_code_scheme")
An *erasure-code payload* for a payload space $`Y` is an
{bpref "erasure_code_scheme"}[erasure code] $`(\Encode,\Decode)` over $`\Sigma`, with block
length $`N` and message length $`k`, for which there exist maps

- $`\mathsf{Serialize}:Y\to\Sigma^k`, mapping each payload to a message of $`k` symbols, and
- $`\mathsf{Parse}:\Sigma^k\to Y\cup\{\bot\}`, mapping each message to a payload or to $`\bot`,

such that $`\mathsf{Parse}(\mathsf{Serialize}(y))=y` for every $`y\in Y`.

:::leanPillCaption "ErasureCodePayload"
:::

```anchor ErasureCodePayload (project := ".") (module := SecureMessaging.ErasureCode.Defs)
structure ErasureCodePayload (M Sym : Type) where
  /-- The erasure code used for this payload type. -/
  ec : ErasureCode Sym
  /-- Serialize a payload as the `nchunk`-symbol message consumed by `ec.encode`. -/
  serialize : M → Fin ec.nchunk → Sym
  /-- Parse a decoded `nchunk`-symbol message as a payload, or fail. -/
  parse : (Fin ec.nchunk → Sym) → Option M
  /-- Parsing a serialized payload recovers the original payload. -/
  parse_serialize : ∀ payload, parse (serialize payload) = some payload
```

Every erasure-code payload determines two algorithms on chunks with natural-number indices,
defined from $`\Encode`, $`\Decode`, $`\mathsf{Serialize}`, and $`\mathsf{Parse}` in the panels
below:

- $`\mathsf{EncodePayload}:Y\times\mathbb N\to\mathbb N\times\Sigma`: the chunk of a payload at a
  counter $`i`, placed at the index $`i\bmod N`;
- $`\mathsf{DecodePayload}:\mathcal P_{\mathrm{fin}}(\mathbb N\times\Sigma)\to Y\cup\{\bot\}`: the
  payload decoded from a finite chunk set, or $`\bot`; a chunk set containing an index outside
  $`[N]` is rejected.

::::::gameGrid
:::::gameCell "\\textsf{Chunk encoding}" (kind := "compact")
$`\begin{array}{l}
\mathsf{EncodePayload}(y,i):\\
\quad j\gets i\bmod N\\
\quad\Return(j,\Encode(\mathsf{Serialize}(y),j))
\end{array}`

:::leanPillCaption "counterIndex"
:::

```anchor ErasureCodePayload_counterIndex (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def counterIndex (ecp : ErasureCodePayload M Sym) (i : ℕ) : Fin ecp.ec.N :=
  ⟨i % ecp.ec.N, Nat.mod_lt i ecp.ec.N_pos⟩
```

:::leanPillCaption "encode"
:::

```anchor ErasureCodePayload_encode (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def encode (ecp : ErasureCodePayload M Sym) (payload : M) (i : ℕ) : ℕ × Sym :=
  let j := counterIndex ecp i
  (j.1, ecp.ec.encode (ecp.serialize payload) j)
```
:::::
:::::gameCell "\\textsf{Decoding}" (kind := "compact")
$`\begin{array}{l}
\mathsf{DecodePayload}(L):\\
\quad\pif\ j\ge N\text{ for some }(j,c)\in L\ \pthen\ \Return\bot\\
\quad M\gets\Decode(L)\\
\quad\pif\ M=\bot\ \pthen\ \Return\bot\\
\quad\Return\mathsf{Parse}(M)
\end{array}`

:::leanPillCaption "decode"
:::

```anchor ErasureCodePayload_decode (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def decode (ecp : ErasureCodePayload M Sym) (chunks : Finset (ℕ × Sym)) : Option M :=
  if hvalid : ∀ chunk ∈ chunks, chunk.1 < ecp.ec.N then
    match ecp.ec.decode (ecp.boundedChunks chunks hvalid) with
    | none => none
    | some block => ecp.parse block
  else
    none
```
:::::
::::::
:::::::

:::defTitle "erasure_code_payload_correctness" "Erasure-code payload correctness"
:::

::::theorem "erasure_code_payload_correctness" (parent := "erasure_codes") (lean := "ErasureCodePayload.payloadChunks, ErasureCodePayload.decode_payloadChunks, ErasureCodePayload.decode_payloadChunks_none") (uses := "erasure_code_payload, erasure_code_correctness")
Consider an {bpref "erasure_code_payload"}[erasure-code payload] for a payload space $`Y`
whose erasure code is {bpref "erasure_code_correctness"}[correct]. For a payload $`y\in Y` and an
index set $`I\subseteq[N]`, the chunk set of $`y` at $`I` is

$$`L_I(y)=L_I(\mathsf{Serialize}(y))=\{(i,\Encode(\mathsf{Serialize}(y),i))\mid i\in I\}.`

:::leanPillCaption "payloadChunks"
:::

```anchor payloadChunks (project := ".") (module := SecureMessaging.ErasureCode.Payload)
noncomputable def payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) : Finset (ℕ × Sym) :=
  (ecp.ec.encodeChunks (ecp.serialize payload) I).map ErasureCode.chunkToNat
```

Then, for every payload $`y` and every index set $`I`,

$$`\mathsf{DecodePayload}(L_I(y))=
\begin{cases}y&\text{if }|I|\ge k,\\\bot&\text{if }|I|<k.\end{cases}`

:::leanPillCaption "decode_payloadChunks"
:::

```anchor decode_payloadChunks (project := ".") (module := SecureMessaging.ErasureCode.Payload)
theorem decode_payloadChunks {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : ecp.ec.nchunk ≤ I.card) :
    ecp.decode (payloadChunks ecp payload I) = some payload
```

:::leanPillCaption "decode_payloadChunks_none"
:::

```anchor decode_payloadChunks_none (project := ".") (module := SecureMessaging.ErasureCode.Payload)
theorem decode_payloadChunks_none {M : Type}
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (I : Finset (Fin ecp.ec.N))
    (hcard : I.card < ecp.ec.nchunk) :
    ecp.decode (payloadChunks ecp payload I) = none
```
::::

:::defTitle "stream_decoder" "Stream decoder"
:::

::::definition "stream_decoder" (parent := "erasure_codes") (lean := "ErasureCodePayload.Streaming.StreamDecoder, ErasureCodePayload.Streaming.StreamDecoder.run, ErasureCodePayload.Streaming.StreamDecoder.Sound, ErasureCodePayload.Streaming.StreamDecoder.Received") (tags := "gh-401") (uses := "erasure_code_payload")
A *stream decoder* for payloads in a payload space $`Y` from indexed chunks over a symbol alphabet
$`\Sigma` consists of a state space $`\mathcal D` and the algorithms

- $`\mathsf{Empty}\in\mathcal D`: the initial state;
- $`\mathsf{Add}:\mathcal D\times(\mathbb N\times\Sigma)\to\mathcal D`: adding one indexed chunk;
- $`\mathsf{Decode}:\mathcal D\to Y\cup\{\bot\}`: the decoded payload, or $`\bot`.

:::leanPillCaption "StreamDecoder"
:::

```anchor StreamDecoder (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
structure StreamDecoder (M Sym : Type) where
  /-- Decoder state. -/
  D : Type
  /-- Initial state. -/
  empty : D
  /-- Adds one indexed chunk. -/
  addChunk : D → ℕ × Sym → D
  /-- The decoded payload, if any. -/
  decodedPayload : D → Option M
```

For an {bpref "erasure_code_payload"}[erasure-code payload] for $`Y` over $`\Sigma`, a payload
$`y\in Y`, and counters $`i_1,\ldots,i_n\in\mathbb N`, the state after receiving the chunks of
$`y` at these counters, in order, is

$$`\mathsf{Run}(y;i_1,\ldots,i_n)=\mathsf{Add}(\cdots\mathsf{Add}(\mathsf{Empty},
\mathsf{EncodePayload}(y,i_1))\cdots,\mathsf{EncodePayload}(y,i_n)).`

:::leanPillCaption "run"
:::

```anchor StreamDecoder_run (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def run (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) (is : List ℕ) :
    dec.D :=
  is.foldl (fun d i => dec.addChunk d (ecp.encode p i)) dec.empty
```

A state $`\delta` *received only chunks of* $`y` if $`\delta=\mathsf{Run}(y;i_1,\ldots,i_n)` for
some counters, possibly none.

:::leanPillCaption "Received"
:::

```anchor StreamDecoder_Received (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def Received (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) (d : dec.D) :
    Prop :=
  ∃ is : List ℕ, d = dec.run ecp p is
```

The stream decoder is *sound* for the erasure-code payload if, for every payload $`y`, every
$`n\ge1`, and all counters $`i_1,\ldots,i_n`,

$$`\mathsf{Decode}(\mathsf{Run}(y;i_1,\ldots,i_n))\in\{\bot,y\}.`

Soundness does not require that $`\mathsf{Decode}` ever returns $`y`, and it does not constrain
$`\mathsf{Decode}(\mathsf{Empty})`.

:::leanPillCaption "Sound"
:::

```anchor StreamDecoder_Sound (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def Sound (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) : Prop :=
  ∀ (p : M) (is : List ℕ), is ≠ [] →
    dec.decodedPayload (dec.run ecp p is) = none ∨
      dec.decodedPayload (dec.run ecp p is) = some p
```
::::

:::defTitle "erasure_code_streaming" "Stateful erasure-code streaming"
:::

:::::::definition "erasure_code_streaming" (parent := "erasure_codes") (lean := "ErasureCodePayload.Streaming.EncoderState, ErasureCodePayload.Streaming.EncoderState.init, ErasureCodePayload.Streaming.EncoderState.nextChunk, ErasureCodePayload.Streaming.SetDecoder.HasIndex, ErasureCodePayload.Streaming.SetDecoder.addChunk, ErasureCodePayload.Streaming.setDecoder") (tags := "gh-251") (uses := "erasure_code_payload, stream_decoder")
Consider an {bpref "erasure_code_payload"}[erasure-code payload] for a payload space $`Y`, with
chunk encoding $`\mathsf{EncodePayload}:Y\times\mathbb N\to\mathbb N\times\Sigma` and decoding
$`\mathsf{DecodePayload}:\mathcal P_{\mathrm{fin}}(\mathbb N\times\Sigma)\to Y\cup\{\bot\}`. Its
*stateful streaming* consists of the encoder below and the *set-based*
{bpref "stream_decoder"}[stream decoder], whose state is the set of chunks received so far and
which keeps the first symbol received at each index.

:::::gameGrid
::::gameCell "\\textsf{Encoder}" (kind := "compact")
$`\begin{array}{l}
\mathcal E=Y\times\mathbb N\pcomment{\text{states }\eta=(y,i)}\\[0.3em]
\mathsf{Enc}:Y\to\mathcal E,\quad\mathsf{Enc}(y)=(y,0)\\[0.3em]
\mathsf{Next}:\mathcal E\to(\mathbb N\times\Sigma)\times\mathcal E\\
\quad\mathsf{Next}(y,i)=(\mathsf{EncodePayload}(y,i),(y,i+1))
\end{array}`

:::leanPillCaption "EncoderState"
:::

```anchor ErasureCodePayload_Streaming_EncoderState (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
structure EncoderState (M Sym : Type) where
  /-- The erasure-code payload scheme used to encode this stream. -/
  ecp : ErasureCodePayload M Sym
  /-- The fixed payload encoded by this stream. -/
  payload : M
  /-- The natural-number counter used for the next emitted chunk. -/
  nextIndex : ℕ
```

:::leanPillCaption "init"
:::

```anchor ErasureCodePayload_Streaming_init (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def init (ecp : ErasureCodePayload M Sym) (payload : M) : EncoderState M Sym :=
  { ecp, payload, nextIndex := 0 }
```

:::leanPillCaption "nextChunk"
:::

```anchor ErasureCodePayload_Streaming_nextChunk (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def nextChunk (state : EncoderState M Sym) :
    (ℕ × Sym) × EncoderState M Sym :=
  (state.ecp.encode state.payload state.nextIndex,
    { state with nextIndex := state.nextIndex + 1 })
```
::::
::::gameCell "\\textsf{Set-based decoder}" (kind := "compact")
$`\begin{array}{l}
\mathcal D=\mathcal P_{\mathrm{fin}}(\mathbb N\times\Sigma)\pcomment{\text{states }\delta}\\[0.3em]
\mathsf{Empty}=\emptyset\\[0.3em]
\mathsf{Add}(\delta,(j,s))=\begin{cases}
\delta&\text{if }\exists s'.\,(j,s')\in\delta\\
\delta\cup\{(j,s)\}&\text{otherwise}
\end{cases}\\[0.3em]
\mathsf{Decode}(\delta)=\mathsf{DecodePayload}(\delta)
\end{array}`

:::leanPillCaption "HasIndex"
:::

```anchor SetDecoder_HasIndex (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def HasIndex (chunks : Finset (ℕ × Sym)) (index : ℕ) : Prop :=
  ∃ chunk ∈ chunks, chunk.1 = index
```

:::leanPillCaption "addChunk"
:::

```anchor SetDecoder_addChunk (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def addChunk [DecidableEq Sym] (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) :
    Finset (ℕ × Sym) :=
  if HasIndex chunks chunk.1 then chunks else insert chunk chunks
```

:::leanPillCaption "setDecoder"
:::

```anchor setDecoder (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def setDecoder [DecidableEq Sym] (ecp : ErasureCodePayload M Sym) : StreamDecoder M Sym where
  D := Finset (ℕ × Sym)
  empty := ∅
  addChunk := SetDecoder.addChunk
  decodedPayload := ecp.decode
```
::::
:::::

:::::::

:::defTitle "erasure_code_streaming_correctness" "Erasure-code streaming correctness"
:::

:::::::theorem "erasure_code_streaming_correctness" (parent := "erasure_codes") (lean := "ErasureCodePayload.Streaming.SetDecoder.addChunk_payloadChunks, ErasureCodePayload.Streaming.setDecoder_sound, ErasureCodePayload.Streaming.SetDecoder.honestPrefixPositions, ErasureCodePayload.Streaming.SetDecoder.honestPrefixDecoder, ErasureCodePayload.Streaming.SetDecoder.honestPrefixDecoder_eq_payloadChunks, ErasureCodePayload.Streaming.SetDecoder.decode_honestPrefix") (uses := "erasure_code_streaming, stream_decoder, erasure_code_payload_correctness")
Consider an erasure-code payload for a payload space $`Y` whose erasure code is
{bpref "erasure_code_correctness"}[correct], let $`y\in Y`, and let $`L_I(y)` be the chunk set of
$`y` at $`I\subseteq[N]`, as in the {bpref "erasure_code_payload_correctness"}[payload
correctness] theorem. For every $`I\subseteq[N]` and counter $`i\in\mathbb N`, the
{bpref "erasure_code_streaming"}[set-based decoder] satisfies

$$`\mathsf{Add}(L_I(y),\mathsf{EncodePayload}(y,i))=L_{I\cup\{i\bmod N\}}(y).`

:::leanPillCaption "addChunk_payloadChunks"
:::

```anchor addChunk_payloadChunks (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
theorem addChunk_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (I : Finset (Fin ecp.ec.N)) (i : ℕ) :
    addChunk (ErasureCodePayload.payloadChunks ecp payload I) (ecp.encode payload i) =
      ErasureCodePayload.payloadChunks ecp payload
        (insert (ErasureCodePayload.counterIndex ecp i) I)
```

Every state that received only chunks of $`y` is therefore a chunk set $`L_I(y)`, which decodes to
$`\bot` or to $`y`: the set-based decoder is {bpref "stream_decoder"}[sound].

:::leanPillCaption "setDecoder_sound"
:::

```anchor setDecoder_sound (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
theorem setDecoder_sound [DecidableEq Sym] (ecp : ErasureCodePayload M Sym)
    (hcorrect : ecp.ec.Correct) : (setDecoder ecp).Sound ecp
```

For a set $`J\subseteq\mathbb N` of delivered counters, the decoder states of the lossy stream are

$$`\delta_0=\mathsf{Empty},\qquad
\delta_{t+1}=\begin{cases}
\mathsf{Add}(\delta_t,\mathsf{EncodePayload}(y,t))&\text{if }t\in J,\\
\delta_t&\text{otherwise.}
\end{cases}`

:::leanPillCaption "honestPrefixDecoder"
:::

```anchor honestPrefixDecoder (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def honestPrefixDecoder [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M)
    (delivered : Finset ℕ) : ℕ → Finset (ℕ × Sym)
  | 0 => ∅
  | t + 1 =>
      if t ∈ delivered then
        addChunk (honestPrefixDecoder ecp payload delivered t) (ecp.encode payload t)
      else
        honestPrefixDecoder ecp payload delivered t
```

The indices delivered before counter $`t` form the set $`P_t=\{j\bmod N\mid j\in J,\ j<t\}`.

:::leanPillCaption "honestPrefixPositions"
:::

```anchor honestPrefixPositions (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def honestPrefixPositions (ecp : ErasureCodePayload M Sym)
    (delivered : Finset ℕ) : ℕ → Finset (Fin ecp.ec.N)
  | 0 => ∅
  | t + 1 =>
      if t ∈ delivered then
        insert (ErasureCodePayload.counterIndex ecp t)
          (honestPrefixPositions ecp delivered t)
      else
        honestPrefixPositions ecp delivered t
```

Each decoder state of the lossy stream is the chunk set of its delivered indices:
$`\delta_t=L_{P_t}(y)`.

:::leanPillCaption "honestPrefixDecoder_eq_payloadChunks"
:::

```anchor honestPrefixDecoder_eq_payloadChunks (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
theorem honestPrefixDecoder_eq_payloadChunks [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (payload : M) (delivered : Finset ℕ) :
    ∀ t,
      honestPrefixDecoder ecp payload delivered t =
        ErasureCodePayload.payloadChunks ecp payload (honestPrefixPositions ecp delivered t)
```

Consequently, $`\mathsf{Decode}(\delta_t)=y` whenever $`|P_t|\ge k`.

:::leanPillCaption "decode_honestPrefix"
:::

```anchor decode_honestPrefix (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
theorem decode_honestPrefix [DecidableEq Sym]
    (ecp : ErasureCodePayload M Sym) (hcorrect : ecp.ec.Correct)
    (payload : M) (delivered : Finset ℕ) (t : ℕ)
    (hcard : ecp.ec.nchunk ≤ (honestPrefixPositions ecp delivered t).card) :
    ecp.decode (honestPrefixDecoder ecp payload delivered t) = some payload
```

::::::gameGrid
:::::gameCell "\\textsf{Illustration: a lossy stream}" (kind := "scheme")
:::erasureCodeStreamingFigure
:::
:::::
::::::
:::::::
