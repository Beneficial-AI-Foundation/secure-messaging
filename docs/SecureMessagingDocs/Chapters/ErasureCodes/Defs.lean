import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
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
Erasure Codes.
:::

:::defTitle "erasure_code_scheme" "Erasure code scheme"
:::

::::definition "erasure_code_scheme" (parent := "erasure_codes") (lean := "ErasureCode, ErasureCode.Decodable") (tags := "gh-190")
$`\todo`

:::leanPillCaption "scheme"
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

:::leanPillCaption "decodability predicate"
:::

```anchor Decodable (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def Decodable {N : ℕ} (nchunk : ℕ) (chunks : Finset (Fin N × Sym)) : Prop :=
  nchunk ≤ chunks.card ∧ Set.InjOn Prod.fst (chunks : Set (Fin N × Sym))
```

::::

:::defTitle "erasure_code_payload" "Erasure-code payload"
:::

::::definition "erasure_code_payload" (parent := "erasure_codes") (lean := "ErasureCodePayload") (tags := "gh-251") (uses := "erasure_code_scheme")
$`\todo`

:::leanPillCaption "payload serialization and parsing"
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
::::

:::defTitle "erasure_code_streaming" "Stateful erasure-code streaming"
:::

:::::::definition "erasure_code_streaming" (parent := "erasure_codes") (lean := "ErasureCodePayload.Streaming.EncoderState, ErasureCodePayload.Streaming.EncoderState.init, ErasureCodePayload.Streaming.EncoderState.nextChunk, ErasureCodePayload.Streaming.SetDecoder.addChunk, ErasureCodePayload.Streaming.setDecoder, ErasureCodePayload.Streaming.setDecoder_sound") (tags := "gh-251") (uses := "erasure_code_payload, erasure_code_correctness, stream_decoder")
Let $`\mathsf{Code}_X` be an {bpref "erasure_code_payload"}[erasure-code payload] over a symbol
alphabet $`\Sigma`, with payload space $`Y_X`, chunk encoding
$`\Encode_X:Y_X\times\mathbb N\to\mathbb N\times\Sigma`, and decoding
$`\Decode_X:\mathcal P_{\mathrm{fin}}(\mathbb N\times\Sigma)\to Y_X\cup\{\bot\}` from finite sets of
indexed chunks. Its *stateful streaming* consists of the encoder and the set-based
{bpref "stream_decoder"}[stream decoder] below. The decoder is sound for $`\mathsf{Code}_X`
when the erasure code is {bpref "erasure_code_correctness"}[correct].

:::::gameGrid
::::gameCell "\\textsf{Encoder}" (kind := "compact")
$`\begin{array}{l}
\mathcal E_X=Y_X\times\mathbb N\pcomment{\text{states }\eta=(y,i)}\\[0.3em]
\mathsf{Enc}_X:Y_X\to\mathcal E_X,\quad\mathsf{Enc}_X(y)=(y,0)\\[0.3em]
\mathsf{Next}:\mathcal E_X\to(\mathbb N\times\Sigma)\times\mathcal E_X\\
\quad\mathsf{Next}(y,i)=(\Encode_X(y,i),(y,i+1))
\end{array}`
::::
::::gameCell "\\textsf{Decoder}" (kind := "compact")
$`\begin{array}{l}
\mathcal D_X=\mathcal P_{\mathrm{fin}}(\mathbb N\times\Sigma)\pcomment{\text{states }\delta}\\[0.3em]
\mathsf{Empty}_X\in\mathcal D_X,\quad\mathsf{Empty}_X=\emptyset\\[0.3em]
\mathsf{Add}:\mathcal D_X\times(\mathbb N\times\Sigma)\to\mathcal D_X\\
\quad\mathsf{Add}(\delta,(j,s))=\begin{cases}
\delta&\text{if }\exists s'.\,(j,s')\in\delta\\
\delta\cup\{(j,s)\}&\text{otherwise}
\end{cases}\\[0.3em]
\mathsf{Decode}:\mathcal D_X\to Y_X\cup\{\bot\}\\
\quad\mathsf{Decode}(\delta)=\Decode_X(\delta)
\end{array}`
::::
:::::

:::leanPillCaption "encoder state"
:::

```anchor ErasureCodePayload_Streaming_States (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
/-- Encoder state for one erasure-coded payload stream. It stores the erasure-code
payload scheme, the payload being encoded, and the counter for the next chunk. -/
structure EncoderState (M Sym : Type) where
  /-- The erasure-code payload scheme used to encode this stream. -/
  ecp : ErasureCodePayload M Sym
  /-- The fixed payload encoded by this stream. -/
  payload : M
  /-- The natural-number counter used for the next emitted chunk. -/
  nextIndex : ℕ

```

:::leanPillCaption "encoder operations"
:::

```anchor ErasureCodePayload_Streaming_Encoder (project := ".") (module := SecureMessaging.ErasureCode.Streaming)

/-- Initialize an encoder before emitting its first chunk. -/
def init (ecp : ErasureCodePayload M Sym) (payload : M) : EncoderState M Sym :=
  { ecp, payload, nextIndex := 0 }

/-- Emit the chunk at the current counter and advance the counter by one. -/
def nextChunk (state : EncoderState M Sym) :
    (ℕ × Sym) × EncoderState M Sym :=
  (state.ecp.encode state.payload state.nextIndex,
    { state with nextIndex := state.nextIndex + 1 })
```

:::leanPillCaption "set-decoder operations"
:::

```anchor ErasureCodePayload_Streaming_Decoder (project := ".") (module := SecureMessaging.ErasureCode.Streaming)

/-- The chunk set already contains a chunk at `index`. -/
def HasIndex (chunks : Finset (ℕ × Sym)) (index : ℕ) : Prop :=
  ∃ chunk ∈ chunks, chunk.1 = index

/-- Whether a chunk set contains a chunk at a given index is decidable. -/
instance (chunks : Finset (ℕ × Sym)) (index : ℕ) : Decidable (HasIndex chunks index) := by
  unfold HasIndex
  infer_instance

/-- Stored chunks have pairwise distinct indices. -/
def IndexUnique (chunks : Finset (ℕ × Sym)) : Prop :=
  Set.InjOn Prod.fst (chunks : Set (ℕ × Sym))

/-- Add a chunk unless its index is already present. The first symbol received at an
index is retained, so exact duplicates are harmless and later conflicts are ignored.
The soundness and recovery results below cover only chunks encoded from one payload. Their
indices are in range by construction. -/
def addChunk [DecidableEq Sym] (chunks : Finset (ℕ × Sym)) (chunk : ℕ × Sym) :
    Finset (ℕ × Sym) :=
  if HasIndex chunks chunk.1 then chunks else insert chunk chunks
```

:::leanPillCaption "set-based stream decoder"
:::

```anchor setDecoder (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
/-- The set-based decoder of `ecp`. It keeps the first symbol received at each index and decodes
the stored chunk set with `ecp.decode`. -/
def setDecoder [DecidableEq Sym] (ecp : ErasureCodePayload M Sym) : StreamDecoder M Sym where
  D := Finset (ℕ × Sym)
  empty := ∅
  addChunk := SetDecoder.addChunk
  decodedPayload := ecp.decode
```
:::::::

:::defTitle "erasure_code_correctness" "Erasure code correctness"
:::

::::definition "erasure_code_correctness" (parent := "erasure_codes") (lean := "ErasureCode.encodeChunks, ErasureCode.Correct") (tags := "gh-191") (uses := "erasure_code_scheme")
$`\todo`

:::leanPillCaption "chunk set $`L_I = \\{(i, \\mathsf{Encode}(M, i)) \\mid i \\in I\\}`"
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

:::leanPillCaption "correctness predicate"
:::

```anchor Correct (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def Correct (ec : ErasureCode Sym) : Prop :=
  ∀ (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)),
    (ec.nchunk ≤ I.card → ec.decode (ec.encodeChunks M I) = some M) ∧
    (I.card < ec.nchunk → ec.decode (ec.encodeChunks M I) = none)
```
::::

:::defTitle "stream_decoder" "Sound stream decoder"
:::

::::definition "stream_decoder" (parent := "erasure_codes") (lean := "ErasureCodePayload.Streaming.StreamDecoder, ErasureCodePayload.Streaming.StreamDecoder.run, ErasureCodePayload.Streaming.StreamDecoder.Sound, ErasureCodePayload.Streaming.StreamDecoder.Received") (tags := "gh-401") (uses := "erasure_code_payload")
A stream decoder has a state type, an initial state, an operation that adds an indexed chunk,
and a partial decoding function. For a payload $`p` and a list of counters $`i_1,\dots,i_n`, the
state $`\mathsf{run}(p, [i_1,\dots,i_n])` adds the chunks $`\mathsf{Encode}(p, i_1)`, ...,
$`\mathsf{Encode}(p, i_n)` to the initial state, in order.

The decoder is sound for an erasure-code payload scheme if, for every payload $`p` and every
nonempty list of counters, $`\mathsf{run}(p, \cdot)` decodes to nothing or to $`p`. Soundness
does not require that the decoder ever decodes. A state received only chunks of $`p` if it is
$`\mathsf{run}(p, \cdot)` for some list, possibly empty.

:::leanPillCaption "stream decoder and soundness"
:::

```anchor StreamDecoder (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
/-- A streaming decoder for payloads in `M` from indexed symbols in `Sym`. -/
structure StreamDecoder (M Sym : Type) where
  /-- Decoder state. -/
  D : Type
  /-- Initial state. -/
  empty : D
  /-- Adds one indexed chunk. -/
  addChunk : D → ℕ × Sym → D
  /-- The decoded payload, if any. -/
  decodedPayload : D → Option M

namespace StreamDecoder

/-- The state of `dec` after it receives the chunks `ecp.encode p i` for `i` in `is`, in order. -/
def run (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) (is : List ℕ) :
    dec.D :=
  is.foldl (fun d i => dec.addChunk d (ecp.encode p i)) dec.empty

/-- `dec` is sound for `ecp` if a decoder that received only chunks of `p`, at least one, decodes
to `none` or `some p`. Soundness does not imply that `dec` ever decodes, and it does not constrain
`decodedPayload` of the initial state. -/
def Sound (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) : Prop :=
  ∀ (p : M) (is : List ℕ), is ≠ [] →
    dec.decodedPayload (dec.run ecp p is) = none ∨
      dec.decodedPayload (dec.run ecp p is) = some p
```

:::leanPillCaption "received only chunks of a payload"
:::

```anchor StreamDecoder_Received (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
/-- The state `d` of `dec` received only chunks of `p`, possibly none. -/
def Received (dec : StreamDecoder M Sym) (ecp : ErasureCodePayload M Sym) (p : M) (d : dec.D) :
    Prop :=
  ∃ is : List ℕ, d = dec.run ecp p is
```
::::
