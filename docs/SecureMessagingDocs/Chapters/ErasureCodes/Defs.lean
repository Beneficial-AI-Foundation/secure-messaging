import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.ErasureCode.Defs

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
