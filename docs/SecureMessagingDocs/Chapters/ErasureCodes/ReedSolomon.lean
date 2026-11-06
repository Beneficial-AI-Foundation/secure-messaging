import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.ErasureCodeFigures
import SecureMessaging.ErasureCode.ReedSolomon.Construction
import SecureMessaging.ErasureCode.ReedSolomon.Correctness

/-! # Blueprint chapter: Reed-Solomon Erasure Code -/

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

:::::::definition "reed_solomon_erasure_code" (parent := "erasure_codes_reed_solomon") (lean := "ErasureCode.ReedSolomon.Parameters, ErasureCode.ReedSolomon.Parameters.sourceIndex, ErasureCode.ReedSolomon.Parameters.sourcePoint, ErasureCode.ReedSolomon.Parameters.encodingPolynomial, ErasureCode.ReedSolomon.Parameters.encode, ErasureCode.ReedSolomon.Parameters.decodingPolynomial, ErasureCode.ReedSolomon.Parameters.decode, ErasureCode.ReedSolomon.Parameters.erasureCode") (tags := "gh-198") (uses := "erasure_code_scheme")
Let $`F` be a field, $`0<k\le N`, and $`x_0,\ldots,x_{N-1}\in F` pairwise distinct
evaluation points.

:::leanPillCaption "Parameters"
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

The algorithms below use the following notation:

- for a finite set $`S\subseteq F\times F` of points with pairwise distinct first coordinates,
  $`\mathsf{Interpolate}(S)` is the unique polynomial in $`F[X]` of degree less than $`|S|`
  through the points of $`S`;
- $`\mathsf{Decodable}_k` is the {bpref "erasure_code_scheme"}[decodability predicate] of chunk
  sets.

The *Reed–Solomon erasure code* with these parameters is the
{bpref "erasure_code_scheme"}[erasure code] $`(\Encode,\Decode)` over $`F`, with block length
$`N` and message length $`k`, whose algorithms are

::::::gameGrid
:::::gameCell "\\textsf{Encoding}" (kind := "compact")
$`\begin{array}{l}
\Encode(m,j):\\
\quad P_m\gets\mathsf{Interpolate}(\{(x_i,m_i)\mid i<k\})\\
\quad\Return P_m(x_j)
\end{array}`

:::leanPillCaption "sourceIndex"
:::

```anchor reedSolomon_sourceIndex (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def sourceIndex (params : Parameters F) (i : Fin params.k) : Fin params.N :=
  Fin.castLE params.k_le_N i
```

:::leanPillCaption "sourcePoint"
:::

```anchor reedSolomon_sourcePoint (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def sourcePoint (params : Parameters F) (i : Fin params.k) : F :=
  params.point (params.sourceIndex i)
```

:::leanPillCaption "encodingPolynomial"
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
:::::
:::::gameCell "\\textsf{Decoding}" (kind := "compact")
$`\begin{array}{l}
\Decode(L):\\
\quad\pif\ \neg\mathsf{Decodable}_k(L)\ \pthen\ \Return\bot\\
\quad Q_L\gets\mathsf{Interpolate}(\{(x_j,c)\mid(j,c)\in L\})\\
\quad\Return(Q_L(x_0),\ldots,Q_L(x_{k-1}))
\end{array}`

:::leanPillCaption "decodingPolynomial"
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
:::::
::::::

:::leanPillCaption "erasureCode"
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

::::::gameGrid
:::::gameCell "\\textsf{Illustration: Reed–Solomon encoding}" (kind := "scheme")
:::reedSolomonFigure
:::
:::::
::::::
:::::::

:::defTitle "reed_solomon_erasure_code_correctness" "Reed–Solomon correctness"
:::

::::theorem "reed_solomon_erasure_code_correctness" (parent := "erasure_codes_reed_solomon") (lean := "ErasureCode.ReedSolomon.Parameters.erasureCode_correct") (tags := "gh-199") (uses := "reed_solomon_erasure_code, erasure_code_correctness")
For every field $`F` and all parameters $`0<k\le N` and pairwise distinct
$`x_0,\ldots,x_{N-1}\in F`, the {bpref "reed_solomon_erasure_code"}[Reed–Solomon erasure code]
is {bpref "erasure_code_correctness"}[correct]: for every message $`m\in F^k` and every
index set $`I\subseteq[N]`, $`\Decode(L_I(m))=m` if $`|I|\ge k` and
$`\Decode(L_I(m))=\bot` if $`|I|<k`.

:::leanPillCaption "erasure-code correctness"
:::

```anchor reedSolomon_erasureCode_correct (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Correctness)
theorem erasureCode_correct (params : Parameters F) : params.erasureCode.Correct
```
::::

*References:*

- {Informal.citet RS60}[]
- {Informal.citet RFC5510}[]
