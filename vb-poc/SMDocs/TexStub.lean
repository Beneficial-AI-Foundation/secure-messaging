/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

/-!
# Capability stub: custom TeX / KaTeX notation

Demonstrates that domain-specific mathematical notation can be defined **once**
and reused across every formula on the site. The `tex_prelude` command registers
a table of KaTeX macros; any inline `$`…`` or display `$$`…`` math elaborated in a
module that imports this one picks them up automatically. Edit a macro here and
every formula that uses it updates — no per-formula LaTeX duplication.
-/

open Verso.Genre Manual
open Informal

set_option doc.verso true

-- KaTeX macro table (one raw string; `\providecommand` so the chunk is idempotent
-- across accumulation / re-render). A deliberately small, secure-messaging-flavoured
-- set: random sampling, concatenation, a parameterised protocol-message arrow, and
-- algorithm names.
tex_prelude r#"
\providecommand{\sample}{\xleftarrow{\$}}
\providecommand{\concat}{\mathbin{\|}}
\providecommand{\msgR}[1]{\xrightarrow{\hspace{3em}#1\hspace{3em}}}
\providecommand{\KeyGen}{\mathsf{KeyGen}}
\providecommand{\Enc}{\mathsf{Enc}}
\providecommand{\Dec}{\mathsf{Dec}}
"#

#doc (Manual) "Custom TeX and KaTeX Notation" =>
%%%
tag := "tex_notation"
%%%

The macros below are declared in *one* `tex_prelude` block and rendered by KaTeX
in the browser. The point of the stub: cryptographic notation stays readable and
consistent without repeating raw LaTeX at every use site.

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
