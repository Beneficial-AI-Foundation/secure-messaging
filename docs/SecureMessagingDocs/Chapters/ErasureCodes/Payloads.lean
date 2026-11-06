import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.ErasureCodeFigures
import SecureMessaging.ErasureCode.Streaming

/-! # Blueprint chapter: Erasure-Code Payloads and Streaming -/

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

#doc (Manual) "Erasure-Code Payloads and Streaming" =>

:::group "erasure_code_payloads"
Payload encoding over erasure codes, its streaming encoder and stream decoders, and the
set-based decoder.
:::

:::defTitle "erasure_code_payload" "Erasure-code payload"
:::

:::::::definition "erasure_code_payload" (parent := "erasure_code_payloads") (lean := "ErasureCodePayload, ErasureCodePayload.counterIndex, ErasureCodePayload.encode, ErasureCodePayload.decode") (tags := "gh-251") (uses := "erasure_code_scheme")
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

::::theorem "erasure_code_payload_correctness" (parent := "erasure_code_payloads") (lean := "ErasureCodePayload.payloadChunks, ErasureCodePayload.decode_payloadChunks, ErasureCodePayload.decode_payloadChunks_none") (uses := "erasure_code_payload, erasure_code_correctness")
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

:::defTitle "erasure_code_streaming" "Streaming encoder and stream decoder"
:::

:::::::definition "erasure_code_streaming" (parent := "erasure_code_payloads") (lean := "ErasureCodePayload.Streaming.EncoderState, ErasureCodePayload.Streaming.EncoderState.init, ErasureCodePayload.Streaming.EncoderState.nextChunk, ErasureCodePayload.Streaming.StreamDecoder, ErasureCodePayload.Streaming.StreamDecoder.run, ErasureCodePayload.Streaming.StreamDecoder.Received, ErasureCodePayload.Streaming.StreamDecoder.Sound") (tags := "gh-251, gh-401") (uses := "erasure_code_payload")
Consider an {bpref "erasure_code_payload"}[erasure-code payload] for a payload space $`Y` over a
symbol alphabet $`\Sigma`, with chunk encoding
$`\mathsf{EncodePayload}:Y\times\mathbb N\to\mathbb N\times\Sigma`. Its *streaming encoder* emits,
for a payload $`y`, the chunks $`\mathsf{EncodePayload}(y,i)` for $`i=0,1,2,\ldots` in turn. A
*stream decoder* for $`Y` over $`\Sigma` adds the received chunks to its state one at a time and
decodes the state to a payload or to $`\bot`:

:::::gameGrid
::::gameCell "\\textsf{Streaming encoder}" (kind := "compact")
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
::::gameCell "\\textsf{Stream decoder}" (kind := "compact")
$`\begin{array}{l}
\mathcal D\pcomment{\text{states }\delta}\\[0.3em]
\mathsf{Empty}\in\mathcal D\\[0.3em]
\mathsf{Add}:\mathcal D\times(\mathbb N\times\Sigma)\to\mathcal D\\[0.3em]
\mathsf{Decode}:\mathcal D\to Y\cup\{\bot\}
\end{array}`

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
::::
:::::

For a payload $`y\in Y` and counters $`i_1,\ldots,i_n\in\mathbb N`, the state of a stream decoder
after receiving the chunks of $`y` at these counters, in order, is

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

A stream decoder is *sound* for the erasure-code payload if, for every payload $`y`, every
$`n\ge1`, and all counters $`i_1,\ldots,i_n`,

$$`\mathsf{Decode}(\mathsf{Run}(y;i_1,\ldots,i_n))\in\{\bot,y\}.`

:::leanPillCaption "Sound"
:::

```anchor StreamDecoder_Sound (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def Sound (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) : Prop :=
  ∀ (p : M) (is : List ℕ), is ≠ [] →
    dec.decodedPayload (dec.run ecp p is) = none ∨
      dec.decodedPayload (dec.run ecp p is) = some p
```

::::::gameGrid
:::::gameCell "\\textsf{Illustration: a lossy stream}" (kind := "scheme")
:::erasureCodeStreamingFigure
:::
:::::
::::::
:::::::

:::defTitle "set_decoder" "Set-based decoder"
:::

::::definition "set_decoder" (parent := "erasure_code_payloads") (lean := "ErasureCodePayload.Streaming.SetDecoder.HasIndex, ErasureCodePayload.Streaming.SetDecoder.addChunk, ErasureCodePayload.Streaming.setDecoder") (tags := "gh-251") (uses := "erasure_code_payload, erasure_code_streaming")
The *set-based decoder* of an {bpref "erasure_code_payload"}[erasure-code payload] with decoding
$`\mathsf{DecodePayload}:\mathcal P_{\mathrm{fin}}(\mathbb N\times\Sigma)\to Y\cup\{\bot\}` is the
{bpref "erasure_code_streaming"}[stream decoder] whose state is the set of chunks received so far
and which keeps the first symbol received at each index:

$$`\begin{array}{l}
\mathcal D=\mathcal P_{\mathrm{fin}}(\mathbb N\times\Sigma),\qquad\mathsf{Empty}=\emptyset,\qquad
\mathsf{Decode}(\delta)=\mathsf{DecodePayload}(\delta),\\[0.6em]
\mathsf{Add}(\delta,(j,s))=\begin{cases}
\delta&\text{if }\exists s'.\,(j,s')\in\delta,\\
\delta\cup\{(j,s)\}&\text{otherwise.}
\end{cases}
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

:::defTitle "set_decoder_soundness" "Set-based decoder soundness"
:::

::::theorem "set_decoder_soundness" (parent := "erasure_code_payloads") (lean := "ErasureCodePayload.Streaming.SetDecoder.addChunk_payloadChunks, ErasureCodePayload.Streaming.setDecoder_sound") (uses := "set_decoder, erasure_code_streaming, erasure_code_payload_correctness")
Consider an {bpref "erasure_code_payload"}[erasure-code payload] for a payload space $`Y` whose
erasure code is {bpref "erasure_code_correctness"}[correct], and a payload $`y\in Y`. Let
$`L_I(y)` be the chunk set of $`y` at $`I\subseteq[N]`, as in the
{bpref "erasure_code_payload_correctness"}[payload correctness] theorem. Adding a chunk of $`y` to
a chunk set of $`y` gives a chunk set of $`y`: for every $`I\subseteq[N]` and counter
$`i\in\mathbb N`,

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

We can therefore derive that the {bpref "set_decoder"}[set-based decoder] is
{bpref "erasure_code_streaming"}[sound].

:::leanPillCaption "setDecoder_sound"
:::

```anchor setDecoder_sound (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
theorem setDecoder_sound [DecidableEq Sym] (ecp : ErasureCodePayload M Sym)
    (hcorrect : ecp.ec.Correct) : (setDecoder ecp).Sound ecp
```
::::
