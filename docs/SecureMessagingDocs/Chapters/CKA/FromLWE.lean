import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromLWE.Construction

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

#doc (Manual) "CKA from LWE" =>

*References:*

- {Informal.citet ACD19}[]

:::group "cka_cka_from_lwe"
CKA from LWE.
:::

:::defTitle "cka_from_lwe_spec" "CKA from LWE construction"
:::

::::definition "cka_from_lwe_spec" (parent := "cka_cka_from_lwe") (lean := "lweCKA.scheme") (tags := "gh-12") (uses := "cka")
The direct LWE construction instantiates continuous key agreement using the two-round mechanism of
Alwen, Coretti, and Dodis, *The Double Ratchet: Security Notions, Proofs, and Modularization for the
Signal Protocol*, §4.1.2 (pp. 23–24) and Appendix C.2 (p. 55). Its extraction, hint, and recovery
functions follow Bos et al., *Frodo: Take off the ring!*, §3.2 (pp. 8–9),
[ePrint 2016/659](https://eprint.iacr.org/2016/659.pdf).

The supported parameters satisfy $`q = 2^D`, positive dimensions $`n` and $`\bar n`, a positive
number $`B` of key bits, and $`B + 1 < D`. A supplied scalar computation $`\chi` represents the
paper's noise distribution. Nested independent sampling draws every matrix entry afresh; setup
samples the uniform base first, and then the initial secret and error.

| Lean shape | Dimensions | Role |
|---|---:|---|
| `Base` | $`n \times n` | public base matrix |
| `Right` | $`n \times \bar n` | right-oriented secret, error, or public matrix |
| `Left` | $`\bar n \times n` | left-oriented secret, error, or public matrix |
| `Shared` | $`\bar n \times \bar n` | noisy shared matrix |

Names inside `lweCKA` follow the paper: B sends first. The Lean name `base` is the paper's matrix
$`A`, while $`P_0` is its matrix $`B`. Setup gives paper A the state $`(\mathsf{base}, S_0)` and
paper B the state $`(\mathsf{base}, P_0)`, where $`P_0 = \mathsf{base} S_0 + E_0`.

In the B-to-A round, B samples fresh $`S_1`, $`E_1`, and $`\widetilde E_1`, computes
$`P_1 = S_1\mathsf{base} + E_1` and $`V_1 = S_1P_0 + \widetilde E_1`, outputs
$`\operatorname{Extract}(V_1)`, sends $`P_1` with the entrywise hint for $`V_1`, and retains
$`S_1`. A recovers from $`P_1S_0` and retains $`P_1`. In the A-to-B round, A samples fresh $`S_2`,
$`E_2`, and $`\widetilde E_2`, computes
$`P_2 = \mathsf{base}S_2 + E_2` and $`V_2 = P_1S_2 + \widetilde E_2`, and sends $`P_2` with its
hint after outputting $`\operatorname{Extract}(V_2)` and retaining $`S_2`. B recovers from
$`S_1P_2` and retains $`P_2` for its next sending phase. State replacement records retained values
and phase; it does not establish physical memory erasure.

For a canonical residue $`v`, extraction computes
$`\lfloor (v + 2^{D-B-1}) / 2^{D-B} \rfloor \bmod 2^B`, so midpoint ties round upward. The hint
is $`\lfloor v / 2^{D-B-1} \rfloor \bmod 2`. Recovery enumerates the residues with the received
hint and minimizes circular distance modulo $`q`; equal distances use the smaller canonical
representative as this specification's deterministic convention.

Only the `scheme` adapter changes party labels to match the repository's A-first interface:
repository A is paper B, and repository B is paper A.

```anchor scheme (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
def scheme (p : Params) (_h : p.WellFormed) (χ : ProbComp (Scalar p)) :
    CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p) where
  initKeyGen := initKeyGen p χ
  initA := fun ik => pure (lweCKA.initB ik)
  initB := fun ik => pure (lweCKA.initA ik)
  sendA := lweCKA.sendB χ
  sendArleak := lweCKA.sendBrleak χ
  recvA := lweCKA.recvB
  sendB := lweCKA.sendA χ
  sendBrleak := lweCKA.sendArleak χ
  recvB := lweCKA.recvA
```

Correctness and security are tracked separately in #13 and #14.
::::

:::defTitle "cka_from_lwe_correctness" "CKA from LWE correctness"
:::

::::theorem "cka_from_lwe_correctness" (parent := "cka_cka_from_lwe") (tags := "gh-13") (uses := "cka_from_lwe_spec, cka_correctness")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "cka_from_lwe_security" "CKA from LWE security"
:::

::::theorem "cka_from_lwe_security" (parent := "cka_cka_from_lwe") (tags := "gh-14") (uses := "cka_from_lwe_spec, cka_security")
$`\todo`

:::leanPill "missing"
:::
::::
