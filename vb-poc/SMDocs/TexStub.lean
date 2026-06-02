/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import SMDocs.CryptoNotation

/-!
# Capability stub: custom TeX / KaTeX notation

Demonstrates that domain-specific mathematical notation can be defined **once**
and reused across every formula on the site. The macros live in a single
`tex_prelude` block in `SMDocs.CryptoNotation`; any module that imports it picks
them up automatically (this page, the CKA construction page, and the diagrams
page all share that one table). Edit a macro there and every formula that uses it
updates — no per-formula LaTeX duplication.

A site must have exactly **one** `tex_prelude`: each block registers under the same
`"default"` key in the browser's prelude table, so two blocks would race and the
loser's macros silently vanish. One shared module avoids that.
-/

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "Custom TeX and KaTeX Notation" =>
%%%
tag := "tex_notation"
%%%

The macros used below are declared in *one* `tex_prelude` block (in the shared
`SMDocs.CryptoNotation` module) and rendered by KaTeX in the browser. The point of
the stub: cryptographic notation stays readable and consistent without repeating
raw LaTeX at every use site, and the *same* table is reused by every other page.

Inline math reuses the macros directly — a fresh key is sampled
$`k \sample \mathcal{K}`, and the scheme exposes $`\KeyGen`, $`\Enc`, and $`\Dec`.

A keypair is generated and a message is encrypted under associated data:

$$`(pk, sk) \gets \KeyGen() \qquad c \sample \Enc\bigl(pk,\; m \concat \mathsf{ad}\bigr)`

The parameterised `\msgR` macro renders a labelled protocol-message arrow, so a
single round of the handshake reads as one line:

$$`\mathsf{Alice} \msgR{(pk_A,\; c)} \mathsf{Bob}`

The same macros work inside a Blueprint node, so notation in definitions and
theorems matches the prose:

:::definition "tex_notation_demo"
A KEM ciphertext is sampled as $`c \sample \Enc(pk,\, m)` and recovered by the
receiver as $`m' \gets \Dec(sk,\, c)`, with correctness $`m' = m`.
:::
