/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

/-!
# Cryptocode-compatibility notation

A small KaTeX macro layer that lets an author write cryptographic *pseudocode and
security games* the way they would with LaTeX's `cryptocode` package — without any
LaTeX package (KaTeX has no package system). Every macro is built from KaTeX
primitives (`array`, `\hline`, `\boxed`, `\xrightarrow`, `\textcolor`, `\textsf`).

Registered once via `tex_prelude`; any module that imports this one renders these
macros automatically. The set is deliberately the *core 80%*: procedure boxes,
boxed game definitions, colour-coded oracle headers, sampling/assignment arrows,
and labelled protocol-message arrows. That is enough to typeset a full CKA
security game (see `SMDocs.CkaDiagrams`).
-/

open Verso.Genre Manual

-- The macro pack. `\providecommand` (idempotent) rather than `\newcommand` so the
-- table can coexist with other preludes when several pages accumulate on the root.
tex_prelude r#"
\providecommand{\sample}{\xleftarrow{\$}}
\providecommand{\getsval}{\gets}
\providecommand{\Return}{\textbf{return}\;}
\providecommand{\req}{\textbf{req}\;}
\providecommand{\pp}{\mathbin{+\!\!+}}
\providecommand{\bit}{\{0,1\}}
\providecommand{\orc}[1]{\textsf{#1}}
\providecommand{\KeyGen}{\mathsf{KeyGen}}
\providecommand{\hdrK}[1]{\textbf{#1}}
\providecommand{\hdrR}[1]{\textcolor{red}{\textbf{#1}}}
\providecommand{\hdrB}[1]{\textcolor{blue}{\textbf{#1}}}
\providecommand{\proc}[2]{\begin{array}{l}#1\\\hline #2\end{array}}
\providecommand{\secdef}[1]{\boxed{\begin{array}{l}#1\end{array}}}
\providecommand{\msgR}[1]{\xrightarrow{\hspace{3em}#1\hspace{3em}}}
\providecommand{\msgL}[1]{\xleftarrow{\hspace{3em}#1\hspace{3em}}}
\providecommand{\concat}{\mathbin{\|}}
\providecommand{\Enc}{\mathsf{Enc}}
\providecommand{\Dec}{\mathsf{Dec}}
"#
