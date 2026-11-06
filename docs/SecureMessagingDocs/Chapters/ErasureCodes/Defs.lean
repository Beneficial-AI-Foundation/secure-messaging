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
Erasure codes and their correctness.
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

A chunk set $`L` is *decodable* if it contains at least $`k` chunks at pairwise distinct indices:

$$`\mathsf{Decodable}_k(L)\iff|L|\ge k\ \text{and}\ c=c'\ \text{for all}\ (i,c),(i,c')\in L.`

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
