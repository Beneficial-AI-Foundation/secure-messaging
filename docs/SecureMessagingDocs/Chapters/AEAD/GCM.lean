import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.AEAD.FromGCM.Construction
import SecureMessaging.AEAD.FromGCM.Correctness
import SecureMessaging.AEAD.FromGCM.Security

/-! # Blueprint chapter: GCM -/

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

#doc (Manual) "GCM" =>

*References:*

- {Informal.citet NIST_GCM}[] — the GCM building blocks (Section 6, Algorithms 1 to 3),
  GCM encryption and decryption (Section 7, Algorithms 4 and 5) and the supported input
  lengths (Section 5.2.1.1).
- {Informal.citet ACD19}[] — the target notion: one-time IND-CCA security of AEAD
  (Definition 1, Figure 1, Definition 2).
- {Informal.citet MV04}[] — the original GCM security proof.
- {Informal.citet IOM12}[] — GCM privacy and authenticity bounds for 96-bit nonces
  (Corollaries 3 and 4, proofs in Appendices D and E).
- {Informal.citet BR06}[] — the PRP/PRF switching lemma.

:::group "aead_gcm"
GCM.
:::

:::defTitle "aead_gcm_components" "GCM building blocks"
:::

::::::::definition "aead_gcm_components" (parent := "aead_gcm") (lean := "GCM.gfmul, GCM.ghash, GCM.inc32, GCM.gctr")
{Informal.citet NIST_GCM}[], Sections 6.2 to 6.5.

:::::::gameGrid
::::::gameCell "\\textsf{Notation}" (kind := "scheme-notation")
A block is a bit string of length 128. For a bit string $`X = x_0 x_1 \ldots x_{n-1}`:

- $`|X| = n` is the length of $`X`, and $`x_0` is its leftmost and most significant bit;
- $`\mathsf{MSB}_s(X)` and $`\mathsf{LSB}_s(X)` are the leftmost and the rightmost $`s` bits
  of $`X`;
- $`X \gg 1` is $`X` shifted right by one bit: $`0 x_0 x_1 \ldots x_{n-2}`;
- $`\mathrm{int}(X)` is the integer with binary representation $`X`, and for
  $`0 \le k < 2^s`, $`[k]_s` is the $`s`-bit string with $`\mathrm{int}([k]_s) = k`;
- $`R = 11100001 \concat 0^{120}`.

$`\mathsf{CIPH}_K` is a block cipher on blocks under the key $`K`. The inputs $`X` and $`Y`
of $`X \bullet Y`, the hash key $`H`, the input $`X` of $`\mathsf{inc}_{32}` and the initial
counter block $`\mathit{ICB}` are blocks. The input of $`\mathsf{GHASH}_H` is a sequence of
$`m` blocks $`X = X_1 \concat \cdots \concat X_m`. The input $`X` of $`\mathsf{GCTR}_K` is a
bit string of any length.
::::::
:::::::

:::::::gameGrid
::::::gameCell "X \\bullet Y \\quad \\textsf{(Algorithm 1)}" (kind := "compact")
$`\begin{array}{l}
Z_0 \gets 0^{128};\quad V_0 \gets Y; \\
\mathsf{for}\; i = 0, \ldots, 127 \\
\quad \pif\;x_i = 0\;\pthen \\
\qquad Z_{i+1} \gets Z_i; \\
\quad \pelse \\
\qquad Z_{i+1} \gets Z_i \oplus V_i; \\
\quad \pif\;\mathsf{LSB}_1(V_i) = 0\;\pthen \\
\qquad V_{i+1} \gets V_i \gg 1; \\
\quad \pelse \\
\qquad V_{i+1} \gets (V_i \gg 1) \oplus R; \\
\Return Z_{128}
\end{array}`

```anchor gfmul (project := ".") (module := SecureMessaging.AEAD.GCM)
def gfmul (x y : BitVec 128) : BitVec 128 :=
  (List.range 128 |>.foldl
    (fun (p : BitVec 128 × BitVec 128) (i : ℕ) =>
      let z := if x.getMsbD i then p.1 ^^^ p.2 else p.1
      let v := if p.2.getLsbD 0 then (p.2 >>> 1) ^^^ gcmReductionConst else p.2 >>> 1
      (z, v))
    ((0 : BitVec 128), y)).1
```
::::::

::::::gameCell "\\mathsf{GCTR}_K(\\mathit{ICB}, X) \\quad \\textsf{(Algorithm 3)}" (kind := "compact")
$`\begin{array}{l}
\pif\;|X| = 0\;\pthen\;\Return X; \\
n \gets \lceil |X| / 128 \rceil; \\
\pcommentline{\text{split } X = X_1 \concat \cdots \concat X_{n-1} \concat X_n^*} \\
\pcommentline{\text{into blocks } X_i \text{ and } 0 < |X_n^*| \le 128} \\
\mathit{CB}_1 \gets \mathit{ICB}; \\
\mathsf{for}\; i = 2, \ldots, n \\
\quad \mathit{CB}_i \gets \mathsf{inc}_{32}(\mathit{CB}_{i-1}); \\
\mathsf{for}\; i = 1, \ldots, n - 1 \\
\quad Y_i \gets X_i \oplus \mathsf{CIPH}_K(\mathit{CB}_i); \\
Y_n^* \gets X_n^* \oplus \mathsf{MSB}_{|X_n^*|}(\mathsf{CIPH}_K(\mathit{CB}_n)); \\
\Return Y_1 \concat \cdots \concat Y_{n-1} \concat Y_n^*
\end{array}`

```anchor gctr (project := ".") (module := SecureMessaging.AEAD.GCM)
def gctr {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K) (icb : BitVec 128)
    {p : ℕ} (x : BitVec p) : BitVec p :=
  x ^^^ keystream ((counterChain icb ((p + 127) / 128)).map (ciph k)) p
```
::::::

::::::gameCell "\\mathsf{inc}_{32}(X) \\quad \\textsf{(Section 6.2)}" (kind := "compact")
$`\begin{array}{l}
c \gets \mathrm{int}(\mathsf{LSB}_{32}(X)) + 1 \bmod 2^{32}; \\
\Return \mathsf{MSB}_{96}(X) \concat [c]_{32}
\end{array}`

```anchor inc32 (project := ".") (module := SecureMessaging.AEAD.GCM)
def inc32 (x : BitVec 128) : BitVec 128 :=
  x.extractLsb' 32 96 ++ (x.extractLsb' 0 32 + 1)
```
::::::

::::::gameCell "\\mathsf{GHASH}_H(X) \\quad \\textsf{(Algorithm 2)}" (kind := "compact")
$`\begin{array}{l}
Y_0 \gets 0^{128}; \\
\mathsf{for}\; i = 1, \ldots, m \\
\quad Y_i \gets (Y_{i-1} \oplus X_i) \bullet H; \\
\Return Y_m
\end{array}`

```anchor ghash (project := ".") (module := SecureMessaging.AEAD.GCM)
def ghash (h : BitVec 128) (blocks : List (BitVec 128)) : BitVec 128 :=
  blocks.foldl (fun y x => gfmul (y ^^^ x) h) 0
```
::::::
:::::::

$`X \bullet Y` is the product of $`X` and $`Y` in $`\mathrm{GF}(2^{128})`, where the block
$`x_0 x_1 \ldots x_{127}` represents the polynomial $`\sum_i x_i\, \alpha^i` and $`\alpha`
is a root of $`x^{128} + x^7 + x^2 + x + 1`. The keystream of $`\mathsf{GCTR}` does not
depend on $`X`, so $`\mathsf{GCTR}_K(\mathit{ICB}, \cdot)` is its own inverse.
::::::::

:::defTitle "aead_gcm_spec" "AEAD-GCM construction"
:::

:::::::definition "aead_gcm_spec" (parent := "aead_gcm") (lean := "GCM.gcmEncrypt, GCM.gcmDecrypt, GCM.gcmOneTimeAEAD") (tags := "gh-21") (uses := "aead, prp, aead_gcm_components")
Adapted from {Informal.citet NIST_GCM}[], Section 7, Algorithms 4 and 5.

GCM encrypts the message in counter mode and authenticates the associated data and the
ciphertext with $`\mathsf{GHASH}`. Both use the block cipher $`\mathsf{CIPH}_K` of a PRP
scheme on 128-bit blocks. The tag is 128 bits. For a bit string $`X`, let $`0^{v_X}` be the
fewest zero bits that make $`|X| + v_X` a multiple of 128. GHASH hashes the associated data
$`A` and the ciphertext $`C` as

$$`\mathsf{encode}(A, C) = A \concat 0^{v_A} \concat C \concat 0^{v_C} \concat [|A|]_{64} \concat [|C|]_{64}`

::::::gameGrid
:::::gameCell "\\mathsf{GCM\\text{-}AE}_K(\\mathit{IV}, P, A)" (kind := "compact")
$`\begin{array}{l}
H \gets \mathsf{CIPH}_K(0^{128}); \\
J_0 \gets \mathit{IV} \concat 0^{31} \concat 1; \\
C \gets \mathsf{GCTR}_K(\mathsf{inc}_{32}(J_0), P); \\
S \gets \mathsf{GHASH}_H(\mathsf{encode}(A, C)); \\
T \gets \mathsf{GCTR}_K(J_0, S); \\
\Return (C, T)
\end{array}`

```anchor gcmEncrypt (project := ".") (module := SecureMessaging.AEAD.GCM)
def gcmEncrypt {K : Type} (ciph : CIPH K) (k : K)
    (iv : BitVec 96) {lenA lenP : ℕ} (ad : BitVec lenA) (m : BitVec lenP) :
    BitVec lenP × BitVec 128 :=
  let h := ciph.perm k 0
  let j₀ := j0 iv
  let c := gctr ciph.perm k (inc32 j₀) m
  -- trailing GHASH block `[len(A)]₆₄ ‖ [len(C)]₆₄` (NIST SP 800-38D §7.1 step 5)
  let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP])
  -- (6) `T = GCTR_K(J₀, S)` (NIST SP 800-38D §7.1 step 6); one block, so no truncation
  let t := gctr ciph.perm k j₀ s
  (c, t)
```
:::::

:::::gameCell "\\mathsf{GCM\\text{-}AD}_K(\\mathit{IV}, C, A, T)" (kind := "compact")
$`\begin{array}{l}
\pif\;|C|, |A| \text{ are not supported}\;\pthen \\
\quad\Return \bot; \\
H \gets \mathsf{CIPH}_K(0^{128}); \\
J_0 \gets \mathit{IV} \concat 0^{31} \concat 1; \\
P \gets \mathsf{GCTR}_K(\mathsf{inc}_{32}(J_0), C); \\
S \gets \mathsf{GHASH}_H(\mathsf{encode}(A, C)); \\
\pif\;T \neq \mathsf{GCTR}_K(J_0, S)\;\pthen \\
\quad\Return \bot; \\
\Return P
\end{array}`

```anchor gcmDecrypt (project := ".") (module := SecureMessaging.AEAD.GCM)
def gcmDecrypt {K : Type} (ciph : CIPH K) (k : K)
    (iv : BitVec 96) {lenA lenP : ℕ} (ad : BitVec lenA) (ct : BitVec lenP × BitVec 128) :
    Option (BitVec lenP) :=
  -- (1) FAIL immediately on unsupported input lengths, before any GHASH work
  if ValidMsgLength lenP ∧ ValidAADLength lenA then
    let (c, t) := ct
    let h := ciph.perm k 0                          -- (2)
    let j₀ := j0 iv                                 -- (3)
    let p := gctr ciph.perm k (inc32 j₀) c          -- (4)
    -- (5–6) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)`
    let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP])
    -- (7–8) recompute `T'` and return `P` on a match, else FAIL
    if t = gctr ciph.perm k j₀ s then some p else none
  else none
```
:::::
::::::

A message or ciphertext length is supported when it is at most $`2^{39} - 256` bits and a
multiple of 8. An associated data length is supported when it is at most $`2^{64} - 1` bits
and a multiple of 8.

```anchor ValidMsgLength (project := ".") (module := SecureMessaging.AEAD.GCM)
@[reducible] def ValidMsgLength (lenC : ℕ) : Prop := lenC ≤ 2 ^ 39 - 256 ∧ 8 ∣ lenC
```

```anchor ValidAADLength (project := ".") (module := SecureMessaging.AEAD.GCM)
@[reducible] def ValidAADLength (lenA : ℕ) : Prop := lenA ≤ 2 ^ 64 - 1 ∧ 8 ∣ lenA
```

```anchor SupportedAAD (project := ".") (module := SecureMessaging.AEAD.GCM)
abbrev SupportedAAD := { x : (a : ℕ) × BitVec a // ValidAADLength x.1 }
```

The one-time AEAD scheme $`\mathsf{GCM}[P, \mathit{IV}, L]` is GCM under the PRP scheme
$`P` with a fixed public IV and $`L`-bit messages: $`\mathsf{KeyGen}` is the key generation
of $`P`, $`\Enc(K, a, m) = \mathsf{GCM\text{-}AE}_K(\mathit{IV}, m, a)` and
$`\Dec(K, a, (C, T)) = \mathsf{GCM\text{-}AD}_K(\mathit{IV}, C, a, T)`.

::::::gameGrid
:::::gameCell "\\textsf{Scope}" (kind := "scheme-notation")
The scheme covers a part of what {Informal.citet NIST_GCM}[] allows:

- the IV is 96 bits, so $`J_0 = \mathit{IV} \concat 0^{31} \concat 1`; the GHASH-based
  $`J_0` for other IV lengths is out of scope;
- the IV is fixed and public, which is safe because each key encrypts one message, so no
  key and IV pair repeats;
- the message length $`L` is fixed and supported, and the associated data has any supported
  length;
- the tag is the full 128 bits, so $`\mathsf{MSB}_t` in step 6 of Algorithm 4 is the identity.
:::::
::::::

```anchor gcmOneTimeAEAD (project := ".") (module := SecureMessaging.AEAD.FromGCM.Construction)
def gcmOneTimeAEAD {K : Type} (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.toBlockCipher k iv ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.toBlockCipher k iv ad.1.2 c
```
:::::::

:::defTitle "aead_gcm_correctness" "AEAD-GCM correctness"
:::

::::theorem "aead_gcm_correctness" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD_correct") (tags := "gh-22") (uses := "aead_gcm_spec, aead_correctness, prp")
Correctness in the sense of {Informal.citet ACD19}[], Definition 1, for GCM as specified in
{Informal.citet NIST_GCM}[], Section 7.

Let $`P` be a PRP scheme on 128-bit blocks, $`\mathit{IV}` a 96-bit IV and $`L` a
supported message length. Then $`\mathsf{GCM}[P, \mathit{IV}, L]` is correct.

```anchor gcmOneTimeAEAD_correct (project := ".") (module := SecureMessaging.AEAD.FromGCM.Correctness)
theorem gcmOneTimeAEAD_correct {K : Type} (prp : PRPScheme K (BitVec 128))
    (iv : BitVec 96) {L : ℕ} (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp iv L hL).Correct
```
::::

:::defTitle "aead_gcm_axu" "Almost-XOR-universal hash"
:::

::::definition "aead_gcm_axu" (parent := "aead_gcm") (lean := "UniversalHash.IsAlmostXorUniversal, GCM.gcmEncode, GCM.GhashIsAXU") (uses := "aead_gcm_components, aead_gcm_spec")
Let $`\mathcal K` be a finite nonempty key space, $`\mathcal D` an input domain and
$`t` an output length in bits. A keyed hash
$`h : \mathcal K \times \mathcal D \to \bit^t` is $`\varepsilon`-almost-XOR-universal
($`\varepsilon`-AXU) if for all distinct inputs $`x \neq y` and every $`\Delta \in \bit^t`,

$$`\Pr_{k \sample \mathcal K}\bigl[\, h(k, x) \oplus h(k, y) = \Delta \,\bigr] \le \varepsilon`

where $`\oplus` is bitwise XOR. GHASH is $`\varepsilon`-AXU for $`L`-bit ciphertexts if
$`(H, (a, c)) \mapsto \mathsf{GHASH}_H(\mathsf{encode}(a, c))` is $`\varepsilon`-AXU on
supported associated data $`a` and $`c \in \bit^L`. Here the hash key $`H` is uniform in
$`\bit^{128}`. In GCM, $`H = \mathsf{CIPH}_K(0^{128})`, and the security proof replaces it
by a uniform block before it uses this property.

```anchor gcmEncode (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security.Encoding)
def gcmEncode {L : ℕ} (ad : SupportedAAD) (c : BitVec L) : List (BitVec 128) :=
  padBlocks ad.1.2 ++ padBlocks c ++ [BitVec.ofNat 64 ad.1.1 ++ BitVec.ofNat 64 L]
```

```anchor GhashIsAXU (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security.Axu)
def GhashIsAXU (L : ℕ) (ε : ℝ≥0∞) : Prop :=
  UniversalHash.IsAlmostXorUniversal
    (fun (H : BitVec 128) (p : SupportedAAD × BitVec L) => ghash H (gcmEncode p.1 p.2)) ε
```
::::

:::defTitle "aead_gcm_ghash_axu" "GHASH is almost-XOR-universal"
:::

::::theorem "aead_gcm_ghash_axu" (parent := "aead_gcm") (lean := "GCM.ghash_isAXU_unconditional, GCM.nistPoly_irreducible") (uses := "aead_gcm_axu")
Adapted from {Informal.citet IOM12}[], Corollary 4 and Appendix E. Appendix E first
replaces the block cipher by a random function. It then uses a game in which every
decryption query returns $`\bot`, and bounds the probability that one decryption query
there has a valid tag by $`(\ell_A + 1) / 2^\tau`. A union bound over the $`q'` decryption
queries gives the term $`q' (\ell_A + 1) / 2^\tau` of Corollary 4, next to a separate
switching term. Here $`\ell_A` bounds the number of blocks of associated data and message or
ciphertext in each encryption and decryption query, and $`\tau` is the tag length in bits.

Let $`L` be a supported message length and $`n = \lceil L / 128 \rceil`. Then GHASH is
$`\varepsilon`-AXU for $`L`-bit ciphertexts, with

$$`\varepsilon = \frac{2^{57} + n + 1}{2^{128}}`

The numerator bounds the number of blocks of $`\mathsf{encode}(a, c)`. The longest supported
associated data has $`2^{64} - 8` bits, which is $`2^{57}` blocks after zero-padding. The
ciphertext is $`n` blocks after zero-padding, and one block holds the two lengths. In the notation of {Informal.citet IOM12}[],
$`\tau = 128` and $`\ell_A = 2^{57} + n`. The bound uses the longest supported associated
data for every query, so it does not improve for shorter associated data, and
$`\varepsilon \approx 2^{-71}`.

The bound needs $`x^{128} + x^7 + x^2 + x + 1` to be irreducible over $`\mathrm{GF}(2)`, so
that $`\bullet` is multiplication in a field. This is the second statement below. It is
proved, not assumed.

```anchor ghash_isAXU_unconditional (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security.NistIrreducible)
theorem ghash_isAXU_unconditional (L : ℕ) :
    GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ)) :=
  ghash_isAXU L nistPoly_irreducible
```

```anchor nistPoly_irreducible (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security.NistIrreducible)
theorem nistPoly_irreducible : Irreducible nistPoly
```
::::

:::defTitle "aead_gcm_prp_switching" "AEAD-GCM PRP/PRF switching"
:::

::::theorem "aead_gcm_prp_switching" (parent := "aead_gcm") (lean := "GCM.prfAdvantage_le_prpAdvantage_switching") (uses := "aead_gcm_spec, prp, prf")
Adapted from {Informal.citet BR06}[], the PRP/PRF switching lemma.

Let $`P` be a PRP scheme on 128-bit blocks, $`L` a supported message length,
$`n = \lceil L / 128 \rceil`, and $`\mathcal B` the reduction built from a one-time IND-CCA
adversary $`\adv` against $`\mathsf{GCM}[P, \mathit{IV}, L]`. $`\mathcal B` queries its
function oracle on $`0^{128}`, $`J_0` and the $`n` counter blocks
$`\mathsf{inc}_{32}(J_0), \ldots, \mathsf{inc}_{32}^n(J_0)`, which are $`n + 2` distinct
blocks. It then runs $`\adv` and answers all of its queries with these $`n + 2` outputs as
$`H`, the tag mask and the keystream. Then

$$`\mathsf{Adv}^{\textsf{prf}}_{P}(\mathcal B)
  \le \mathsf{Adv}^{\textsf{prp}}_{P}(\mathcal B) + \frac{(n + 2)(n + 1)}{2^{129}}`

```anchor prfAdvantage_le_prpAdvantage_switching (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security.PrpSwitch)
theorem prfAdvantage_le_prpAdvantage_switching {K : Type}
    (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ) (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    (PRFScheme.prfAdvantage prp.toPRFScheme (prfReduction iv L adv)).toReal ≤
      (PRPScheme.prpAdvantage prp (prfReduction iv L adv)).toReal +
      ((((L + 127) / 128 : ℕ) : ℝ) + 2) * ((((L + 127) / 128 : ℕ) : ℝ) + 1)
        / 2 ^ (129 : ℕ)
```
::::

:::defTitle "aead_gcm_security_of_axu" "AEAD-GCM security for any AXU bound"
:::

:::::theorem "aead_gcm_security_of_axu" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD_security_of_axu") (uses := "aead_gcm_spec, aead_gcm_axu, prf, aead_security_exp, aead_dist_advantage, aead_decrypt_query_bound, aead_oracles")
Adapted from {Informal.citet IOM12}[], Corollaries 3 and 4, with one encryption query and an
abstract AXU bound $`\varepsilon` in place of the GHASH bound.

Let $`P` be a PRP scheme on 128-bit blocks, $`\mathit{IV}` a 96-bit IV, $`L` a supported
message length such that GHASH is $`\varepsilon`-AXU for $`L`-bit ciphertexts with
$`\varepsilon < \infty`, and $`\adv` a one-time IND-CCA adversary against
$`\mathsf{GCM}[P, \mathit{IV}, L]` that makes at most $`q_d`
queries to the decryption oracle $`\Odec` of the {bpref "aead_oracles"}[one-time IND-CCA game]. Then

$$`\mathsf{Adv}^{\textsf{dist}}_{\textsf{GCM}}(\adv)
  \le \mathsf{Adv}^{\textsf{prf}}_{P}(\mathcal B) + q_d \cdot \varepsilon`

where $`\mathsf{Adv}^{\textsf{dist}}` is the {bpref "aead_dist_advantage"}[distinguishing
advantage] in the {bpref "aead_security_exp"}[one-time IND-CCA game], and $`\mathcal B` is
the PRF adversary of {bpref "aead_gcm_prp_switching"}[PRP/PRF switching]. In that game,
for the GCM key $`K` and a fixed challenge bit $`b`, $`\Oenc` answers only its first query
$`(a, m)`. It returns $`e^* = \Enc(K, a, m)` for $`b = 0` and a uniformly random ciphertext
$`e^*` for $`b = 1`, and it records the challenge pair $`(a^*, e^*)`, where $`a^* = a`. For
$`b = 0`, $`\Odec` decrypts every query except $`(a^*, e^*)`. For $`b = 1`, it returns
$`\bot`.

There is no separate tag-guessing term: $`\varepsilon \ge 2^{-128}` for every AXU bound of
GHASH.

```anchor gcmOneTimeAEAD_security_of_axu (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security)
theorem gcmOneTimeAEAD_security_of_axu (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    {ε : ℝ≥0∞} (hε : ε ≠ ⊤) (haxu : GhashIsAXU L ε) :
    let reduction := prfReduction iv L adv
    let forgeryBound : ℝ := (q_d : ℝ) * ε.toReal
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      (PRFScheme.prfAdvantage prp.toPRFScheme reduction).toReal + forgeryBound
```
:::::

:::defTitle "aead_gcm_security" "AEAD-GCM security"
:::

::::theorem "aead_gcm_security" (parent := "aead_gcm") (lean := "GCM.gcmOneTimeAEAD_security") (tags := "gh-23") (uses := "aead_gcm_spec, aead_gcm_security_of_axu, aead_gcm_ghash_axu, aead_gcm_prp_switching, aead_security_exp, aead_dist_advantage, aead_decrypt_query_bound, prp, aead_oracles")
Adapted from {Informal.citet IOM12}[], Corollary 3 (privacy) and Corollary 4 (authenticity)
for 96-bit nonces, with one encryption query. We prove one bound for the one-time IND-CCA
game instead of two separate bounds.

Let $`P` be a PRP scheme on 128-bit blocks, $`\mathit{IV}` a 96-bit IV, $`L` a supported
message length, $`n = \lceil L / 128 \rceil`, and $`\adv` a one-time IND-CCA adversary
against $`\mathsf{GCM}[P, \mathit{IV}, L]` that makes at most $`q_d`
queries to the decryption oracle $`\Odec` of the {bpref "aead_oracles"}[one-time IND-CCA game]. Then

$$`\mathsf{Adv}^{\textsf{dist}}_{\textsf{GCM}}(\adv)
  \le \mathsf{Adv}^{\textsf{prp}}_{P}(\mathcal B)
  + \frac{(n+2)(n+1)}{2^{129}}
  + q_d \cdot \frac{2^{57} + n + 1}{2^{128}}`

where $`\mathsf{Adv}^{\textsf{dist}}` is as in
{bpref "aead_gcm_security_of_axu"}[AEAD-GCM security for any AXU bound], and
$`\mathcal B` is the reduction of {bpref "aead_gcm_prp_switching"}[PRP/PRF switching]. The
first term is the PRP advantage of $`\mathcal B`, the second is the switching bound, and the
third is $`q_d` times the GHASH AXU bound.

```anchor gcmOneTimeAEAD_security (project := ".") (module := SecureMessaging.AEAD.FromGCM.Security)
theorem gcmOneTimeAEAD_security (prp : PRPScheme K (BitVec 128)) (iv : BitVec 96) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    let blocks : ℕ := (L + 127) / 128
    let reduction := prfReduction iv L adv
    let switchingBound : ℝ := ((blocks : ℝ) + 2) * ((blocks : ℝ) + 1) / 2 ^ 129
    let forgeryBound : ℝ := (q_d : ℝ) * ((2 ^ 57 + (blocks : ℝ) + 1) / 2 ^ 128)
    AEADScheme.distAdvantage (gcmOneTimeAEAD prp iv L hL) adv ≤
      (PRPScheme.prpAdvantage prp reduction).toReal + switchingBound + forgeryBound
```
::::
