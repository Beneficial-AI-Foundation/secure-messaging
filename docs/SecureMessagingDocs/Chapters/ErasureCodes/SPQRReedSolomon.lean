import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.ErasureCodeFigures
import SecureMessaging.ErasureCode.SPQRReedSolomon.Construction
import SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness

/-! # Blueprint chapter: SPQR Erasure Code -/

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

#doc (Manual) "SPQR Erasure Code" =>

:::group "erasure_codes_spqr_reed_solomon"
The 16-coordinate parallel Reed–Solomon construction and its SPQR specialization.
:::

:::defTitle "parallel_reed_solomon_code" "Parallel Reed–Solomon erasure code"
:::

:::::::definition "parallel_reed_solomon_code" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.Chunk, ErasureCode.SPQRReedSolomon.encode, ErasureCode.SPQRReedSolomon.coordinateChunks, ErasureCode.SPQRReedSolomon.decode, ErasureCode.SPQRReedSolomon.parallelErasureCode") (uses := "reed_solomon_erasure_code, erasure_code_scheme")
Let $`(F,N,k,x_0,\ldots,x_{N-1})` be the parameters of a
{bpref "reed_solomon_erasure_code"}[Reed–Solomon erasure code]
$`(\Encode_{\mathsf{RS}},\Decode_{\mathsf{RS}})`. The *parallel Reed–Solomon erasure code* is the
{bpref "erasure_code_scheme"}[erasure code] over the symbol set $`F^{16}`, with block length
$`N` and message length $`k`, that runs the Reed–Solomon code on each of the 16
coordinates. For a chunk $`c\in F^{16}` write $`c[\ell]` for its coordinate $`\ell<16`.

:::leanPillCaption "Chunk"
:::

```anchor parallelReedSolomon_Chunk (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
abbrev Chunk (F : Type) := Fin 16 → F
```

For a message $`m\in(F^{16})^k` write $`m[\ell]=(m_0[\ell],\ldots,m_{k-1}[\ell])\in F^k`. The
encoding runs the Reed–Solomon encoding on each coordinate:
$`\Encode(m,j)[\ell]=\Encode_{\mathsf{RS}}(m[\ell],j)` for all $`\ell<16`.

:::leanPillCaption "encode"
:::

```anchor parallelReedSolomon_encode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def encode (params : ReedSolomon.Parameters F) (message : Fin params.k → Chunk F)
    (index : Fin params.N) : Chunk F :=
  fun coordinate => params.encode (fun i => message i coordinate) index
```

For a chunk set $`L` write $`L[\ell]=\{(j,c[\ell])\mid(j,c)\in L\}`.

:::leanPillCaption "coordinateChunks"
:::

```anchor parallelReedSolomon_coordinateChunks (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def coordinateChunks (params : ReedSolomon.Parameters F)
    (chunks : Finset (Fin params.N × Chunk F)) (coordinate : Fin 16) :
    Finset (Fin params.N × F) := by
  classical
  exact chunks.image fun (j, y) => (j, y coordinate)
```

The decoding interpolates each coordinate: $`\Decode(L)_i[\ell]=Q_{L[\ell]}(x_i)` for all
$`i<k` and $`\ell<16` if $`L` is decodable, where $`Q_{L[\ell]}` is the decoding polynomial of
$`L[\ell]`, and $`\Decode(L)=\bot` otherwise.

:::leanPillCaption "decode"
:::

```anchor parallelReedSolomon_decode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
noncomputable def decode (params : ReedSolomon.Parameters F)
    (chunks : Finset (Fin params.N × Chunk F)) : Option (Fin params.k → Chunk F) :=
  letI : Decidable (ErasureCode.Decodable params.k chunks) := Classical.propDecidable _
  if _h : ErasureCode.Decodable params.k chunks then
    some fun i coordinate =>
      (params.decodingPolynomial (coordinateChunks params chunks coordinate)).eval
        (params.sourcePoint i)
  else
    none
```

These algorithms form the parallel Reed–Solomon erasure code.

:::leanPillCaption "parallelErasureCode"
:::

```anchor parallelReedSolomon_erasureCode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def parallelErasureCode (params : ReedSolomon.Parameters F) : ErasureCode (Chunk F) where
  N := params.N
  N_pos := params.N_pos
  nchunk := params.k
  nchunk_pos := params.k_pos
  nchunk_le_N := params.k_le_N
  encode := encode params
  decode := decode params
```

::::::gameGrid
:::::gameCell "\\textsf{Illustration: parallel Reed–Solomon encoding}" (kind := "scheme")
:::parallelReedSolomonFigure
:::
:::::
::::::
:::::::

:::defTitle "spqr_reed_solomon_code" "SPQR erasure code"
:::

::::definition "spqr_reed_solomon_code" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.GF16, ErasureCode.SPQRReedSolomon.spqrEvaluationPoints, ErasureCode.SPQRReedSolomon.spqrParameters, ErasureCode.SPQRReedSolomon.erasureCode") (uses := "parallel_reed_solomon_code")
Adapted from {Informal.citet SPQR_ENC}[].

Let $`\mathbb F_{2^{16}}` be the field with $`2^{16}` elements.

:::leanPillCaption "GF16"
:::

```anchor spqrReedSolomon_GF16 (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
abbrev GF16 := GaloisField 2 16
```

Fix a bijection $`\varphi:[2^{16}]\to\mathbb F_{2^{16}}`. The evaluation points of SPQR are
$`x_j=\varphi(j)` for $`j\in[2^{16}]`.

:::leanPillCaption "spqrEvaluationPoints"
:::

```anchor spqrReedSolomon_evaluationPoints (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def spqrEvaluationPoints : Fin (2 ^ 16) ≃ GF16 :=
  (Finite.equivFinOfCardEq gf16_card).symm
```

For a message length $`0<k\le 2^{16}`, the Reed–Solomon parameters of SPQR are the field
$`\mathbb F_{2^{16}}`, the block length $`N=2^{16}`, the message length $`k`, and these points.

:::leanPillCaption "spqrParameters"
:::

```anchor spqrReedSolomon_parameters (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def spqrParameters (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    ReedSolomon.Parameters GF16
    where
  N := 2 ^ 16
  N_pos := by norm_num
  k := k
  k_pos := hk_pos
  k_le_N := hk
  point := spqrEvaluationPoints
  point_injective := spqrEvaluationPoints.injective
```

The *SPQR erasure code* with message length $`k` is the
{bpref "parallel_reed_solomon_code"}[parallel Reed–Solomon erasure code] with these
parameters. As in Signal's implementation, a chunk consists of 16 field elements. The model
leaves $`\varphi` abstract: it does not fix the representation of field elements as 16-bit
integers that Signal's implementation uses.

:::leanPillCaption "erasureCode"
:::

```anchor spqrReedSolomon_erasureCode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def erasureCode (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) : ErasureCode (Chunk GF16) :=
  parallelErasureCode (spqrParameters k hk hk_pos)
```
::::

:::defTitle "parallel_reed_solomon_correctness" "Parallel Reed–Solomon correctness"
:::

::::theorem "parallel_reed_solomon_correctness" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.parallelErasureCode_correct") (uses := "parallel_reed_solomon_code, reed_solomon_erasure_code_correctness, erasure_code_correctness")
For all Reed–Solomon parameters $`(F,N,k,x_0,\ldots,x_{N-1})`, the
{bpref "parallel_reed_solomon_code"}[parallel Reed–Solomon erasure code] is
{bpref "erasure_code_correctness"}[correct].

:::leanPillCaption "parallel correctness"
:::

```anchor parallelReedSolomon_erasureCode_correct (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness)
theorem parallelErasureCode_correct (params : ReedSolomon.Parameters F) :
    (parallelErasureCode params).Correct
```
::::

:::defTitle "spqr_reed_solomon_correctness" "SPQR Reed–Solomon correctness"
:::

::::theorem "spqr_reed_solomon_correctness" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.erasureCode_correct") (uses := "spqr_reed_solomon_code, parallel_reed_solomon_correctness")
For every message length $`0<k\le 2^{16}`, the
{bpref "spqr_reed_solomon_code"}[SPQR erasure code] is
{bpref "erasure_code_correctness"}[correct].

:::leanPillCaption "SPQR correctness"
:::

```anchor spqrReedSolomon_erasureCode_correct (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness)
theorem erasureCode_correct (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    (erasureCode k hk hk_pos).Correct
```
::::

*References:*

- {Informal.citet SPQR_ENC}[]
- {Informal.citet MLKEM_Braid}[]
