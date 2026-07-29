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

:::defTitle "reed_solomon_code" "Reed–Solomon code"
:::

::::definition "reed_solomon_code" (parent := "erasure_codes_reed_solomon") (lean := "ErasureCode.ReedSolomon.Code, ErasureCode.ReedSolomon.Code.sourceIndex, ErasureCode.ReedSolomon.Code.sourcePoint, ErasureCode.ReedSolomon.Code.messagePolynomial, ErasureCode.ReedSolomon.Code.receivedPolynomial")
$`\todo`

:::leanPillCaption "code parameters"
:::

```anchor reedSolomon_Code (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
structure Code (F : Type) [Field F] where
  /-- Number of codeword positions. -/
  N : ℕ
  /-- The codeword has at least one position. -/
  N_pos : 0 < N
  /-- Number of message symbols and reconstruction threshold. -/
  k : ℕ
  /-- The message fits in the codeword. -/
  k_le_N : k ≤ N
  /-- Evaluation point `xⱼ` of each position `j`. -/
  point : Fin N → F
  /-- The evaluation points are pairwise distinct. -/
  point_injective : Function.Injective point
```

:::leanPillCaption "source index"
:::

```anchor reedSolomon_sourceIndex (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def sourceIndex (rs : Code F) (i : Fin rs.k) : Fin rs.N :=
  Fin.castLE rs.k_le_N i
```

:::leanPillCaption "source evaluation point"
:::

```anchor reedSolomon_sourcePoint (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def sourcePoint (rs : Code F) (i : Fin rs.k) : F :=
  rs.point (rs.sourceIndex i)
```

:::leanPillCaption "message polynomial"
:::

```anchor reedSolomon_messagePolynomial (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def messagePolynomial (rs : Code F) (message : Fin rs.k → F) : F[X] :=
  Lagrange.interpolate Finset.univ rs.sourcePoint message
```

:::leanPillCaption "received polynomial"
:::

```anchor reedSolomon_receivedPolynomial (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
noncomputable def receivedPolynomial (rs : Code F)
    (chunks : Finset (Fin rs.N × F)) : F[X] :=
  letI : DecidableEq F := Classical.decEq F
  Lagrange.interpolate chunks (fun (j, _) => rs.point j) (fun (_, y) => y)
```
::::

:::defTitle "reed_solomon_erasure_code" "Reed–Solomon erasure code"
:::

:::::definition "reed_solomon_erasure_code" (parent := "erasure_codes_reed_solomon") (lean := "ErasureCode.ReedSolomon.Code.encode, ErasureCode.ReedSolomon.Code.Decodable, ErasureCode.ReedSolomon.Code.decode, ErasureCode.ReedSolomon.Code.toErasureCode")
$`\todo`

:::leanPillCaption "encode"
:::

```anchor reedSolomon_encode (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def encode (rs : Code F) (message : Fin rs.k → F) (i : Fin rs.N) : F :=
  (rs.messagePolynomial message).eval (rs.point i)
```

:::leanPillCaption "decodability predicate"
:::

```anchor reedSolomon_decodable (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def Decodable (rs : Code F) (chunks : Finset (Fin rs.N × F)) : Prop :=
  rs.k ≤ chunks.card ∧
    Set.InjOn (fun ((j, _) : Fin rs.N × F) => rs.point j) chunks
```

:::leanPillCaption "decode"
:::

```anchor reedSolomon_decode (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
noncomputable def decode (rs : Code F)
    (chunks : Finset (Fin rs.N × F)) : Option (Fin rs.k → F) :=
  letI : Decidable (rs.Decodable chunks) := Classical.propDecidable _
  if _h : rs.Decodable chunks then
    some fun i => (rs.receivedPolynomial chunks).eval (rs.sourcePoint i)
  else
    none
```

:::leanPillCaption "ErasureCode instance"
:::

```anchor reedSolomon_code (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def toErasureCode (rs : Code F) : ErasureCode F where
  N := rs.N
  N_pos := rs.N_pos
  nchunk := rs.k
  nchunk_le_N := rs.k_le_N
  encode := rs.encode
  decode := rs.decode
```

{usesLabel}`uses` {uses "reed_solomon_code"}[] · {uses "erasure_code_scheme"}[] ·
  {githubLabel}`github` {githubIssue 198}[]
:::::

:::defTitle "reed_solomon_erasure_code_correctness" "Reed–Solomon correctness"
:::

::::theorem "reed_solomon_erasure_code_correctness" (parent := "erasure_codes_reed_solomon") (lean := "ErasureCode.ReedSolomon.Code.correct")
$`\todo`

:::leanPillCaption "erasure-code correctness"
:::

```anchor reedSolomon_correct (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Correctness)
theorem correct (rs : Code F) : rs.toErasureCode.Correct
```

{usesLabel}`uses` {uses "reed_solomon_erasure_code"}[] ·
  {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 199}[]
::::

*References:*

- {Informal.citet RS60}[]
- {Informal.citet RFC5510}[]
