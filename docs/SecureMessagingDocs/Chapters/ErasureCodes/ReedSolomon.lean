import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.ErasureCode.ReedSolomon.Construction
import SecureMessaging.ErasureCode.ReedSolomon.Correctness

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

#doc (Manual) "Reed-Solomon Erasure Code" =>

:::group "erasure_codes_reed_solomon"
Reed–Solomon erasure codes over arbitrary fields.
:::

:::defTitle "reed_solomon_erasure_code" "Reed–Solomon erasure code"
:::

::::definition "reed_solomon_erasure_code" (parent := "erasure_codes_reed_solomon") (lean := "ErasureCode.ReedSolomon.Parameters, ErasureCode.ReedSolomon.Parameters.sourceIndex, ErasureCode.ReedSolomon.Parameters.sourcePoint, ErasureCode.ReedSolomon.Parameters.encodingPolynomial, ErasureCode.ReedSolomon.Parameters.encode, ErasureCode.ReedSolomon.Parameters.decodingPolynomial, ErasureCode.ReedSolomon.Parameters.decode, ErasureCode.ReedSolomon.Parameters.erasureCode")
$`\todo`

:::leanPillCaption "Reed–Solomon parameters"
:::

```anchor reedSolomon_Parameters (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
structure Parameters (F : Type) [Field F] where
  /-- Number of codeword positions. -/
  N : ℕ
  /-- The codeword has at least one position. -/
  N_pos : 0 < N
  /-- Number of message symbols and reconstruction threshold. -/
  k : ℕ
  /-- At least one message symbol is required for reconstruction. -/
  k_pos : 0 < k
  /-- The message fits in the codeword. -/
  k_le_N : k ≤ N
  /-- Evaluation point `xⱼ` of each position `j`. -/
  point : Fin N → F
  /-- The evaluation points are pairwise distinct. -/
  point_injective : Function.Injective point
```

:::leanPillCaption "source positions and evaluation points"
:::

```anchor reedSolomon_sourcePoints (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
/-- The inclusion `{0, …, k-1} ↪ {0, …, N-1}`, `i ↦ i`: a message index as a
codeword position. -/
def sourceIndex (params : Parameters F) (i : Fin params.k) : Fin params.N :=
  Fin.castLE params.k_le_N i

/-- The evaluation-point mapping `point : j ↦ xⱼ` restricted to the message
positions `{0, …, k-1}`: `i ↦ xᵢ`. -/
def sourcePoint (params : Parameters F) (i : Fin params.k) : F :=
  params.point (params.sourceIndex i)

/-- The points `x₀, …, x_(k-1)` are pairwise distinct: the restriction of an
injective mapping is itself injective. -/
theorem sourcePoint_injective (params : Parameters F) :
    Function.Injective params.sourcePoint :=
  params.point_injective.comp (Fin.castLE_injective params.k_le_N)
```

:::leanPillCaption "encoding polynomial"
:::

```anchor reedSolomon_encodingPolynomial (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def encodingPolynomial (params : Parameters F) (message : Fin params.k → F) : F[X] :=
  Lagrange.interpolate Finset.univ params.sourcePoint message
```

:::leanPillCaption "encode"
:::

```anchor reedSolomon_encode (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def encode (params : Parameters F) (message : Fin params.k → F) (i : Fin params.N) : F :=
  (params.encodingPolynomial message).eval (params.point i)
```

:::leanPillCaption "decoding polynomial"
:::

```anchor reedSolomon_decodingPolynomial (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
noncomputable def decodingPolynomial (params : Parameters F)
    (chunks : Finset (Fin params.N × F)) : F[X] :=
  letI : DecidableEq F := Classical.decEq F
  Lagrange.interpolate chunks (fun (j, _) => params.point j) (fun (_, y) => y)
```

:::leanPillCaption "decode"
:::

```anchor reedSolomon_decode (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
noncomputable def decode (params : Parameters F)
    (chunks : Finset (Fin params.N × F)) : Option (Fin params.k → F) :=
  letI : Decidable (ErasureCode.Decodable params.k chunks) := Classical.propDecidable _
  if _h : ErasureCode.Decodable params.k chunks then
    some fun i => (params.decodingPolynomial chunks).eval (params.sourcePoint i)
  else
    none
```

:::leanPillCaption "ErasureCode instance"
:::

```anchor reedSolomon_erasureCode (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def erasureCode (params : Parameters F) : ErasureCode F where
  N := params.N
  N_pos := params.N_pos
  nchunk := params.k
  nchunk_pos := params.k_pos
  nchunk_le_N := params.k_le_N
  encode := params.encode
  decode := params.decode
```

{usesLabel}`uses` {uses "erasure_code_scheme"}[] ·
  {githubLabel}`github` {githubIssue 198}[]
::::

:::defTitle "reed_solomon_erasure_code_correctness" "Reed–Solomon correctness"
:::

::::theorem "reed_solomon_erasure_code_correctness" (parent := "erasure_codes_reed_solomon") (lean := "ErasureCode.ReedSolomon.Parameters.erasureCode_correct")
$`\todo`

:::leanPillCaption "erasure-code correctness"
:::

```anchor reedSolomon_erasureCode_correct (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Correctness)
theorem erasureCode_correct (params : Parameters F) : params.erasureCode.Correct
```

{usesLabel}`uses` {uses "reed_solomon_erasure_code"}[] ·
  {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 199}[]
::::

*References:*

- {Informal.citet RS60}[]
- {Informal.citet RFC5510}[]
