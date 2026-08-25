import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.AEAD.FromEtM.Construction
import SecureMessaging.AEAD.FromEtM.Correctness
import SecureMessaging.AEAD.FromEtM.Security

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

#doc (Manual) "Encrypt-then-MAC" =>

*References:*

- {Informal.citet NRS14}[] — the construction (Figure 2, scheme A5) and security
  proof (Theorem 1, Figure 9 bound) this chapter formalizes.
- {Informal.citet ACD19}[] — the one-time IND-CCA notion being targeted
  (Definition 1, Figure 1, Definition 2).
- {Informal.citet TR25}[] — the AEAD advantage convention (Definition 2.5).

:::group "aead_encrypt_then_mac"
Encrypt-then-MAC.
:::

:::defTitle "aead_etm_spec" "AEAD encrypt-then-MAC construction"
:::

::::definition "aead_etm_spec" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD")
$`\todo`

```anchor etmAEAD (project := ".") (module := SecureMessaging.AEAD.FromEtM.Construction)
def etmAEAD (se : DetSEAlg K_e M C_e)
    (prf : PRFScheme K_m (AD × C_e) T) :
    AEADScheme ProbComp M AD (K_e × K_m) (C_e × T) where
  keygen := do
    let ke ← se.keygen
    let km ← prf.keygen
    return (ke, km)
  encrypt := fun (ke, km) ad m =>
    let c := se.encrypt ke m
    let t := prf.eval km (ad, c)
    (c, t)
  decrypt := fun (ke, km) ad (c, t) =>
    if t == prf.eval km (ad, c)
    then se.decrypt ke c
    else none
```

{usesLabel}`uses` {uses "aead"}[] · {githubLabel}`github` {githubIssue 24}[]
::::

:::defTitle "aead_etm_correctness" "AEAD encrypt-then-MAC correctness"
:::

::::theorem "aead_etm_correctness" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD_correct")
$`\todo`

```anchor etmAEAD_correct (project := ".") (module := SecureMessaging.AEAD.FromEtM.Correctness)
theorem etmAEAD_correct (se : DetSEAlg K_e M C_e)
    (prf : PRFScheme K_m (AD × C_e) T) (hse : se.Correct) :
    (etmAEAD se prf).Correct
```

{usesLabel}`uses` {uses "aead_etm_spec"}[] · {uses "aead_correctness"}[] · {githubLabel}`github` {githubIssue 25}[]
::::

:::defTitle "aead_etm_security" "AEAD encrypt-then-MAC security"
:::

::::theorem "aead_etm_security" (parent := "aead_encrypt_then_mac") (lean := "EtM.etmAEAD_security")
$`\todo`

```anchor etmAEAD_security (project := ".") (module := SecureMessaging.AEAD.FromEtM.Security)
theorem etmAEAD_security [Inhabited K_e]
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d)
    [NeverFail prf.keygen] :
    AEADScheme.distAdvantage (etmAEAD se prf) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) +
      ↑q_d * (Fintype.card T : ℝ)⁻¹ +
      DetSEAlg.distAdvantage se (encReduction se adv)
```

{usesLabel}`uses` {uses "aead_etm_spec"}[] · {uses "aead_security_exp"}[] · {uses "aead_dist_advantage"}[] · {uses "aead_decrypt_query_bound"}[] · {githubLabel}`github` {githubIssue 26}[]
::::
