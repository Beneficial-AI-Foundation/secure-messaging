import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.ErasureCode.SPQRReedSolomon.Construction
import SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness

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

:::::definition "parallel_reed_solomon_code" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.Chunk, ErasureCode.SPQRReedSolomon.encode, ErasureCode.SPQRReedSolomon.coordinateChunks, ErasureCode.SPQRReedSolomon.decode, ErasureCode.SPQRReedSolomon.parallelErasureCode")
$`\todo`

:::leanPillCaption "16-coordinate chunk"
:::

```anchor parallelReedSolomon_Chunk (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
abbrev Chunk (F : Type) := Fin 16 → F
```

:::leanPillCaption "encode"
:::

```anchor parallelReedSolomon_encode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def encode (params : ReedSolomon.Parameters F) (message : Fin params.k → Chunk F)
    (index : Fin params.N) : Chunk F :=
  fun coordinate => params.encode (fun i => message i coordinate) index
```

:::leanPillCaption "coordinate chunks"
:::

```anchor parallelReedSolomon_coordinateChunks (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def coordinateChunks (params : ReedSolomon.Parameters F)
    (chunks : Finset (Fin params.N × Chunk F)) (coordinate : Fin 16) :
    Finset (Fin params.N × F) := by
  classical
  exact chunks.image fun (j, y) => (j, y coordinate)
```

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

:::leanPillCaption "ErasureCode instance"
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

{usesLabel}`uses` {uses "reed_solomon_erasure_code"}[] · {uses "erasure_code_scheme"}[]
:::::

:::defTitle "spqr_reed_solomon_code" "SPQR erasure code"
:::

::::definition "spqr_reed_solomon_code" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.GF16, ErasureCode.SPQRReedSolomon.spqrEvaluationPoints, ErasureCode.SPQRReedSolomon.spqrParameters, ErasureCode.SPQRReedSolomon.erasureCode")
$`\todo`

:::leanPillCaption "galois field"
:::

```anchor spqrReedSolomon_GF16 (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
abbrev GF16 := GaloisField 2 16
```

:::leanPillCaption "evaluation points"
:::

```anchor spqrReedSolomon_evaluationPoints (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def spqrEvaluationPoints : Fin (2 ^ 16) ≃ GF16 :=
  (Finite.equivFinOfCardEq gf16_card).symm
```

:::leanPillCaption "Reed–Solomon parameters"
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

:::leanPillCaption "ErasureCode instance"
:::

```anchor spqrReedSolomon_erasureCode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def erasureCode (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) : ErasureCode (Chunk GF16) :=
  parallelErasureCode (spqrParameters k hk hk_pos)
```

{usesLabel}`uses` {uses "parallel_reed_solomon_code"}[]
::::

:::defTitle "parallel_reed_solomon_correctness" "Parallel Reed–Solomon correctness"
:::

::::theorem "parallel_reed_solomon_correctness" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.parallelErasureCode_correct")
$`\todo`

:::leanPillCaption "parallel correctness"
:::

```anchor parallelReedSolomon_erasureCode_correct (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness)
theorem parallelErasureCode_correct (params : ReedSolomon.Parameters F) :
    (parallelErasureCode params).Correct
```

{usesLabel}`uses` {uses "parallel_reed_solomon_code"}[] ·
  {uses "reed_solomon_erasure_code_correctness"}[] · {uses "erasure_code_correctness"}[]
::::

:::defTitle "spqr_reed_solomon_correctness" "SPQR Reed–Solomon correctness"
:::

::::theorem "spqr_reed_solomon_correctness" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.erasureCode_correct")
$`\todo`

:::leanPillCaption "SPQR correctness"
:::

```anchor spqrReedSolomon_erasureCode_correct (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness)
theorem erasureCode_correct (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    (erasureCode k hk hk_pos).Correct
```

{usesLabel}`uses` {uses "spqr_reed_solomon_code"}[] ·
  {uses "parallel_reed_solomon_correctness"}[]
::::

*References:*

- {Informal.citet SPQR_ENC}[]
- {Informal.citet MLKEM_Braid}[]
