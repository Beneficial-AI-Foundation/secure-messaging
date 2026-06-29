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
structure ErasureCode (m : Type → Type u) [Monad m] (Sym : Type) where
  /-- Block length; chunk indices range over `Fin N`. -/
  N : ℕ
  /-- Message size; a message is `Fin nchunk → Sym`. -/
  nchunk : ℕ
  /-- `Encode(M, i)`: the chunk encoding of message `M` at index `i`. -/
  encode : (Fin nchunk → Sym) → Fin N → m Sym
  /-- `Decode(L)`: recover the message from a chunk set, or fail (`none`). -/
  decode : Finset (Fin N × Sym) → m (Option (Fin nchunk → Sym))
```

{githubLabel}`github` {githubIssue 190}[]
::::

:::defTitle "erasure_code_correctness" "Erasure code correctness"
:::

::::definition "erasure_code_correctness" (parent := "erasure_codes") (lean := "ErasureCode.Correct, ErasureCode.encodeChunks")
$`\todo`

:::leanPillCaption "chunk set $`L_I = \\{(i, \\mathsf{Encode}(M, i)) \\mid i \\in I\\}`"
:::

```anchor encodeChunks (project := ".") (module := SecureMessaging.ErasureCode.Defs)
noncomputable def encodeChunks [DecidableEq Sym] (ec : ErasureCode m Sym)
    (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)) :
    m (Finset (Fin ec.N × Sym)) := do
  let chunks ← I.toList.mapM fun i => (fun c => (i, c)) <$> ec.encode M i
  pure chunks.toFinset
```

:::leanPillCaption "correctness predicate"
:::

```anchor Correct (project := ".") (module := SecureMessaging.ErasureCode.Defs)
def Correct [DecidableEq Sym] (ec : ErasureCode m Sym) : Prop :=
  ∀ (M : Fin ec.nchunk → Sym) (I : Finset (Fin ec.N)),
    (I.card = ec.nchunk → (ec.encodeChunks M I >>= ec.decode) = pure (some M)) ∧
    (I.card < ec.nchunk → (ec.encodeChunks M I >>= ec.decode) = pure none)
```

{usesLabel}`uses` {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 191}[]
::::
