import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.KEM.IncrementalKEM.FromMLKEM

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

#doc (Manual) "Incremental KEM" =>

:::group "incremental_kem"
Incremental Key Encapsulation Mechanism (Incremental KEM).
:::

:::defTitle "incremental_kem_scheme" "Incremental KEM scheme"
:::

::::definition "incremental_kem_scheme" (parent := "incremental_kem") (lean := "KEMScheme.IncrementalStructure")
$`\todo`

```anchor IncrementalStructure (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.Defs)
structure IncrementalStructure (kem : KEMScheme m K PK SK C) where
  /-- Public-key header type. -/
  PKheader : Type
  /-- Public-key vector type. -/
  PKvector : Type
  /-- First ciphertext component. -/
  C₁ : Type
  /-- Second ciphertext component. -/
  C₂ : Type
  /-- Encapsulation state carried from the first stage to the second. -/
  St : Type
  /-- Consistency check of a vector part against a header. -/
  validPK : PKheader → PKvector → Bool
  /-- There is a bijection between public keys and header/vector pairs that pass `validPK`. -/
  splitPK : PK ≃ { parts : PKheader × PKvector // validPK parts.1 parts.2 = true }
  /-- The ciphertext splits as `ct = (ct1, ct2)`. -/
  splitC : C ≃ C₁ × C₂
  /-- First stage of encaps: from the header alone, returns the state, `ct1`, and the shared key. -/
  encaps1 : PKheader → m (St × C₁ × K)
  /-- Second stage of encaps: returns the second ciphertext component `ct2`. -/
  encaps2 : St → PKheader → PKvector → m C₂
  /-- For every public key, `kem.encaps` is equal to first running `encaps1`
  on the derived header, then running `encaps2` on the resulting state. -/
  factor : ∀ pk, kem.encaps pk = (do
    let (hdr, vec) := (splitPK pk).1
    let (st, c1, k) ← encaps1 hdr
    let c2 ← encaps2 st hdr vec
    pure (splitC.symm (c1, c2), k))
```

{githubLabel}`github` {githubIssue 224}[]
::::

:::group "incremental_kem_incremental_kem_from_ml_kem"
Incremental KEM from ML-KEM.
:::

:::defTitle "incremental_kem_from_ml_kem_spec" "Incremental KEM from ML-KEM construction"
:::

::::definition "incremental_kem_from_ml_kem_spec" (parent := "incremental_kem_incremental_kem_from_ml_kem")
$`\todo`

:::leanPillCaption "incremental ML-KEM construction"
:::

```anchor mlkemIncremental (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def mlkemIncremental (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalStructure where
  PKheader := Seed32 × PublicKeyHash
  PKvector := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedTHat
  C₁ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedU
  C₂ := (Concrete.concreteEncoding (ParameterSet.params p)).EncodedV
  St := EncapsulationState (ParameterSet.params p)
  validPK hdr vec := decide
    (encapsulationKeyHash (Concrete.concreteEncoding (ParameterSet.params p)) prims
        { tHatEncoded := vec, rho := hdr.1 } = hdr.2)
  splitPK :=
    { toFun := fun ek => ⟨(incrementalHeader prims ek, ek.tHatEncoded), by simp [incrementalHeader]⟩
      invFun := fun parts => { tHatEncoded := parts.1.2, rho := parts.1.1.1 }
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨rho, h⟩, vec⟩, hvalid⟩
        have hh := of_decide_eq_true hvalid
        apply Subtype.ext
        simp only [incrementalHeader, hh] }
  splitC :=
    { toFun := fun c => (c.uEncoded, c.vEncoded)
      invFun := fun uv => { uEncoded := uv.1, vEncoded := uv.2 }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  encaps1 := fun hdr => do
    let m ←$ᵗ Message
    return incrementalEncaps1 ring prims hdr m
  encaps2 := fun st _hdr vec => return (incrementalEncaps2 ring st vec)
  factor := by
    intro ek
    simp only [mlkemScheme, asKEMScheme, Equiv.coe_fn_symm_mk,
      bind_assoc, pure_bind]
    rfl
```

{usesLabel}`uses` {uses "incremental_kem_scheme"}[] · {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 226}[]
::::
