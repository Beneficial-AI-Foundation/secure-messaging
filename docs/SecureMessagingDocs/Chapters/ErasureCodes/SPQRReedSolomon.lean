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

:::::definition "parallel_reed_solomon_code" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.encode, ErasureCode.SPQRReedSolomon.Decodable, ErasureCode.SPQRReedSolomon.receivedPolynomial, ErasureCode.SPQRReedSolomon.decode, ErasureCode.SPQRReedSolomon.parallelCode")
$`\todo`

:::leanPillCaption "encode"
:::

```anchor parallelReedSolomon_encode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def encode (rs : ReedSolomon.Code F) (message : Fin rs.k → Chunk F)
    (index : Fin rs.N) : Chunk F :=
  fun coordinate => rs.encode (fun i => message i coordinate) index
```

:::leanPillCaption "decodability predicate"
:::

```anchor parallelReedSolomon_decodable (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def Decodable (rs : ReedSolomon.Code F)
    (chunks : Finset (Fin rs.N × Chunk F)) : Prop :=
  rs.k ≤ chunks.card ∧
    Set.InjOn (fun ((j, _) : Fin rs.N × Chunk F) => rs.point j) chunks
```

:::leanPillCaption "decode"
:::

```anchor parallelReedSolomon_decode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
noncomputable def decode (rs : ReedSolomon.Code F)
    (chunks : Finset (Fin rs.N × Chunk F)) : Option (Fin rs.k → Chunk F) :=
  letI : Decidable (Decodable rs chunks) := Classical.propDecidable _
  if _h : Decodable rs chunks then
    some fun i coordinate =>
      (receivedPolynomial rs chunks coordinate).eval (rs.sourcePoint i)
  else
    none
```

:::leanPillCaption "ErasureCode instance"
:::

```anchor parallelReedSolomon_code (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def parallelCode (rs : ReedSolomon.Code F) : ErasureCode (Chunk F) where
  N := rs.N
  N_pos := rs.N_pos
  nchunk := rs.k
  nchunk_le_N := rs.k_le_N
  encode := encode rs
  decode := decode rs
```

{usesLabel}`uses` {uses "reed_solomon_erasure_code"}[] · {uses "erasure_code_scheme"}[]
:::::

:::defTitle "spqr_reed_solomon_code" "SPQR erasure code"
:::

::::definition "spqr_reed_solomon_code" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.GF16, ErasureCode.SPQRReedSolomon.evaluationEquiv, ErasureCode.SPQRReedSolomon.scalarCode, ErasureCode.SPQRReedSolomon.spqrCode")
$`\todo`

:::leanPillCaption "field"
:::

```anchor spqrReedSolomon_GF16 (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
abbrev GF16 := GaloisField 2 16
```

:::leanPillCaption "evaluation points"
:::

```anchor spqrReedSolomon_evaluationEquiv (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def evaluationEquiv : Fin (2 ^ 16) ≃ GF16 :=
  (Finite.equivFinOfCardEq gf16_card).symm
```

:::leanPillCaption "scalar code"
:::

```anchor spqrReedSolomon_scalarCode (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def scalarCode (k : ℕ) (hk : k ≤ 2 ^ 16) : ReedSolomon.Code GF16
```

:::leanPillCaption "SPQR specialization"
:::

```anchor spqrReedSolomon_code (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Construction)
def spqrCode (k : ℕ) (hk : k ≤ 2 ^ 16) : ErasureCode (Chunk GF16) :=
  parallelCode (scalarCode k hk)
```

{usesLabel}`uses` {uses "parallel_reed_solomon_code"}[]
::::

:::defTitle "parallel_reed_solomon_correctness" "Parallel Reed–Solomon correctness"
:::

::::theorem "parallel_reed_solomon_correctness" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.parallelCode_correct")
$`\todo`

:::leanPillCaption "parallel correctness"
:::

```anchor parallelReedSolomon_correct (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness)
theorem parallelCode_correct (rs : ReedSolomon.Code F) :
    (parallelCode rs).Correct
```

{usesLabel}`uses` {uses "parallel_reed_solomon_code"}[] ·
  {uses "reed_solomon_erasure_code_correctness"}[] · {uses "erasure_code_correctness"}[]
::::

:::defTitle "spqr_reed_solomon_correctness" "SPQR Reed–Solomon correctness"
:::

::::theorem "spqr_reed_solomon_correctness" (parent := "erasure_codes_spqr_reed_solomon") (lean := "ErasureCode.SPQRReedSolomon.correct")
$`\todo`

:::leanPillCaption "SPQR correctness"
:::

```anchor spqrReedSolomon_correct (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness)
theorem correct (k : ℕ) (hk : k ≤ 2 ^ 16) : (spqrCode k hk).Correct
```

{usesLabel}`uses` {uses "spqr_reed_solomon_code"}[] ·
  {uses "parallel_reed_solomon_correctness"}[]
::::

*References:*

- {Informal.citet SPQR_ENC}[]
- {Informal.citet MLKEM_Braid}[]
