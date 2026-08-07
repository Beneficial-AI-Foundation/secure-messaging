import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.ErasureCode.Streaming

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

::::definition "erasure_code_scheme" (parent := "erasure_codes") (lean := "ErasureCode")
$`\todo`

```anchor ErasureCode (project := ".") (module := SecureMessaging.ErasureCode.Defs)
structure ErasureCode (Sym : Type) where
  /-- Number of valid encoded-chunk positions; valid indices are `0, …, N - 1`. -/
  N : ℕ
  /-- At least one encoded-chunk position is available. -/
  N_pos : 0 < N
  /-- Number of source symbols and distinct encoded chunks needed for recovery. -/
  nchunk : ℕ
  /-- The message fits within the codeword. -/
  nchunk_le_N : nchunk ≤ N
  /-- `Encode(M, i)`: the chunk encoding of message `M` at index `i`. -/
  encode : (Fin nchunk → Sym) → Fin N → Sym
  /-- `Decode(L)`: recover the message from a chunk set, or fail (`none`). -/
  decode : Finset (Fin N × Sym) → Option (Fin nchunk → Sym)
```

{githubLabel}`github` {githubIssue 190}[]
::::

:::defTitle "erasure_code_payload" "Erasure-code payload"
:::

::::definition "erasure_code_payload" (parent := "erasure_codes") (lean := "ErasureCodePayload")
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

{usesLabel}`uses` {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 251}[]
::::

:::defTitle "erasure_code_streaming" "Stateful erasure-code streaming"
:::

::::definition "erasure_code_streaming" (parent := "erasure_codes") (lean := "ErasureCodePayload.Streaming.EncoderState, ErasureCodePayload.Streaming.EncoderState.init, ErasureCodePayload.Streaming.EncoderState.nextChunk, ErasureCodePayload.Streaming.DecoderState, ErasureCodePayload.Streaming.DecoderState.empty, ErasureCodePayload.Streaming.DecoderState.addChunk, ErasureCodePayload.Streaming.DecoderState.decodedPayload, ErasureCodePayload.Streaming.DecoderState.hasMessage")
$`\todo`

:::leanPillCaption "encoder state"
:::

```anchor ErasureCodePayload_Streaming_EncoderState (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
structure EncoderState (M : Type) where
  /-- The fixed payload encoded by this stream. -/
  payload : M
  /-- The natural-number counter used for the next emitted chunk. -/
  nextIndex : ℕ
```

:::leanPillCaption "encoder initialization"
:::

```anchor ErasureCodePayload_Streaming_EncoderState_init (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def init (payload : M) : EncoderState M :=
  { payload, nextIndex := 0 }
```

:::leanPillCaption "emit the next indexed chunk"
:::

```anchor ErasureCodePayload_Streaming_EncoderState_nextChunk (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def nextChunk (ecp : ErasureCodePayload M Sym) (state : EncoderState M) :
    (ℕ × Sym) × EncoderState M :=
  (ecp.encode state.payload state.nextIndex,
    { state with nextIndex := state.nextIndex + 1 })
```

:::leanPillCaption "decoder state"
:::

```anchor ErasureCodePayload_Streaming_DecoderState (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
structure DecoderState (Sym : Type) where
  /-- Indexed chunks retained by the decoder, with at most one symbol per index for
  states reachable from `empty` through `addChunk`. -/
  chunks : Finset (ℕ × Sym)
```

:::leanPillCaption "empty decoder"
:::

```anchor ErasureCodePayload_Streaming_DecoderState_empty (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def empty : DecoderState Sym :=
  { chunks := ∅ }
```

:::leanPillCaption "first-wins chunk insertion"
:::

```anchor ErasureCodePayload_Streaming_DecoderState_addChunk (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def addChunk [DecidableEq Sym] (state : DecoderState Sym) (chunk : ℕ × Sym) :
    DecoderState Sym :=
  if state.HasIndex chunk.1 then state else { chunks := insert chunk state.chunks }
```

:::leanPillCaption "decode the accumulated chunks"
:::

```anchor ErasureCodePayload_Streaming_DecoderState_decodedPayload (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def decodedPayload (ecp : ErasureCodePayload M Sym) (state : DecoderState Sym) : Option M :=
  ecp.decode state.chunks
```

:::leanPillCaption "decoding readiness"
:::

```anchor ErasureCodePayload_Streaming_DecoderState_hasMessage (project := ".") (module := SecureMessaging.ErasureCode.Streaming)
def hasMessage (ecp : ErasureCodePayload M Sym) (state : DecoderState Sym) : Bool :=
  (state.decodedPayload ecp).isSome
```

{usesLabel}`uses` {uses "erasure_code_payload"}[] · {githubLabel}`github` {githubIssue 251}[]
::::

:::defTitle "erasure_code_correctness" "Erasure code correctness"
:::

::::definition "erasure_code_correctness" (parent := "erasure_codes") (lean := "ErasureCode.encodeChunks, ErasureCode.Correct")
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
    (I.card = ec.nchunk → ec.decode (ec.encodeChunks M I) = some M) ∧
    (I.card < ec.nchunk → ec.decode (ec.encodeChunks M I) = none)
```

{usesLabel}`uses` {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 191}[]
::::
