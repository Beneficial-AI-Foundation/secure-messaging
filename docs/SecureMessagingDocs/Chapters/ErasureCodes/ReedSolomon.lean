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

The *Reed–Solomon erasure code* with these parameters is the
{bpref "erasure_code_scheme"}[erasure code] over $`F`, with block length $`N` and message
length $`k`, defined below. The message indices $`i<k` are the first $`k` codeword indices, with
evaluation points $`x_0,\ldots,x_{k-1}`.

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

For a message $`m\in F^k`, the *encoding polynomial* $`P_m\in F[X]` is the unique polynomial of
degree less than $`k` with $`P_m(x_i)=m_i` for all $`i<k`.

:::leanPillCaption "encodingPolynomial"
:::

```anchor reedSolomon_encodingPolynomial (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def encodingPolynomial (params : Parameters F) (message : Fin params.k → F) : F[X] :=
  Lagrange.interpolate Finset.univ params.sourcePoint message
```

The encoding evaluates the encoding polynomial: $`\Encode(m,j)=P_m(x_j)` for $`j\in[N]`.

:::leanPillCaption "encode"
:::

```anchor reedSolomon_encode (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
def encode (params : Parameters F) (message : Fin params.k → F) (i : Fin params.N) : F :=
  (params.encodingPolynomial message).eval (params.point i)
```

For a decodable chunk set $`L`, the *decoding polynomial* $`Q_L\in F[X]` is the unique polynomial
of degree less than $`|L|` with $`Q_L(x_j)=c` for all $`(j,c)\in L`.

:::leanPillCaption "decodingPolynomial"
:::

```anchor reedSolomon_decodingPolynomial (project := ".") (module := SecureMessaging.ErasureCode.ReedSolomon.Construction)
noncomputable def decodingPolynomial (params : Parameters F)
    (chunks : Finset (Fin params.N × F)) : F[X] :=
  letI : DecidableEq F := Classical.decEq F
  Lagrange.interpolate chunks (fun (j, _) => params.point j) (fun (_, y) => y)
```

The decoding evaluates the decoding polynomial at the message points:
$`\Decode(L)=(Q_L(x_0),\ldots,Q_L(x_{k-1}))` if $`L` is decodable, and $`\Decode(L)=\bot`
otherwise.

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

These algorithms form the Reed–Solomon erasure code.

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
