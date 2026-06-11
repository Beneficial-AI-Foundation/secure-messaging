/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint

/-!
# Cryptographic Notation

All KaTeX macros used across the documentation live here. The string
`cryptoTexPrelude` is registered globally (so every math node can use the
macros) and is also re-attached locally to the math inside game/oracle boxes
(see `SecureMessagingDocs.Visuals.GameBoxes`).

To add notation, edit `cryptoTexPrelude` only — nothing else needs to change.
-/

open Lean Elab Command
open Informal.Macros

/-- Every KaTeX `\newcommand` shared across the docs (sampling, party state and
operations, experiment/advantage helpers). This is the single source of truth
for cryptographic notation. -/
def cryptoTexPrelude : String :=
r#"
% --- generic pseudocode notation ---
\newcommand{\sample}{\mathrel{\overset{\scriptscriptstyle\$}{\leftarrow}}} % uniformly random sampling: x <-$ S
\newcommand{\Return}{\textbf{return}\;}                                    % bold "return" keyword
\newcommand{\req}{\textbf{req}\;}                                          % bold "req" (requirement/guard) keyword
\newcommand{\getsval}{\gets}                                              % deterministic assignment arrow
\newcommand{\todo}{\textbf{[todo]}}                                        % draft marker for missing content
\newcommand{\pif}{\mathsf{if}}                                           % pseudocode "if"
\newcommand{\pthen}{\mathsf{then}}                                       % pseudocode "then"
\newcommand{\pelse}{\mathsf{else}}                                       % pseudocode "else"

% --- CKA party state and operations ---
\newcommand{\lcka}{\mathsf{l_{\mathsf{CKA}}}}            % CKA initial shared key (l_CKA)
\newcommand{\stA}{\mathsf{st}_\mathsf{A}}               % party A's local state
\newcommand{\stB}{\mathsf{st}_\mathsf{B}}               % party B's local state
\newcommand{\InitA}{\mathsf{Init}\text{-}\mathsf{A}}    % A's initialization algorithm
\newcommand{\InitB}{\mathsf{Init}\text{-}\mathsf{B}}    % B's initialization algorithm
\newcommand{\SendA}{\mathsf{Send}\text{-}\mathsf{A}}    % A's send algorithm
\newcommand{\SendB}{\mathsf{Send}\text{-}\mathsf{B}}    % B's send algorithm
\newcommand{\SendARLeak}{\mathsf{Send}\text{-}\mathsf{A}\text{-}\mathsf{rleak}} % A's randomness-leaking send algorithm
\newcommand{\SendBRLeak}{\mathsf{Send}\text{-}\mathsf{B}\text{-}\mathsf{rleak}} % B's randomness-leaking send algorithm
\newcommand{\RecA}{\mathsf{Rec}\text{-}\mathsf{A}}      % A's receive algorithm
\newcommand{\RecB}{\mathsf{Rec}\text{-}\mathsf{B}}      % B's receive algorithm
\newcommand{\finished}{\mathsf{finished}}               % "party finished" corruption-game predicate
\newcommand{\KeyGen}{\mathsf{KeyGen}}
\newcommand{\Init}{\mathsf{Init}}
\newcommand{\Send}{\mathsf{Send}}
\newcommand{\Recv}{\mathsf{Recv}}
\newcommand{\Gen}{\mathsf{Gen}}
\newcommand{\Encaps}{\mathsf{Encaps}}
\newcommand{\Decaps}{\mathsf{Decaps}}
\newcommand{\msgR}[1]{\xrightarrow{\hspace{3em}#1\hspace{3em}}}
\newcommand{\msgL}[1]{\xleftarrow{\hspace{3em}#1\hspace{3em}}}
\newcommand{\concat}{\mathbin{\|}}
\newcommand{\orc}[1]{\textsf{#1}}

% --- security experiments and advantages ---
\newcommand{\adv}{\mathcal{A}}                          % the adversary
\newcommand{\bit}{\{0,1\}}                               % the set of bits
\newcommand{\Exp}[2]{\mathsf{Exp}^{#1}_{#2}}            % experiment Exp^{goal}_{scheme}
\newcommand{\Enc}{\mathsf{Enc}}                          % encryption oracle/algorithm
\newcommand{\Dec}{\mathsf{Dec}}                          % decryption oracle/algorithm
\newcommand{\Adv}[1]{\mathsf{Adv}^{#1}_{\mathsf{CKA}}}  % CKA advantage Adv^{goal}_{CKA}
\renewcommand{\Pr}{\operatorname{Pr}}
\newcommand{\game}[1]{\boxed{\begin{array}{l}#1\end{array}}} % framed pseudocode game box

% oracle names and oracle sets (for the adversary access lists)
\newcommand{\Oenc}{\mathsf{O}\text{-}\mathsf{Enc}}
\newcommand{\Odec}{\mathsf{O}\text{-}\mathsf{Dec}}
\newcommand{\OSendA}{\mathsf{O}\text{-}\mathsf{Send}\text{-}\mathsf{A}}
\newcommand{\OSendB}{\mathsf{O}\text{-}\mathsf{Send}\text{-}\mathsf{B}}
\newcommand{\OSendARLeak}{\mathsf{O}\text{-}\mathsf{Send}\text{-}\mathsf{A}\text{-}\mathsf{rleak}}
\newcommand{\OSendBRLeak}{\mathsf{O}\text{-}\mathsf{Send}\text{-}\mathsf{B}\text{-}\mathsf{rleak}}
\newcommand{\ORecA}{\mathsf{O}\text{-}\mathsf{Rec}\text{-}\mathsf{A}}
\newcommand{\ORecB}{\mathsf{O}\text{-}\mathsf{Rec}\text{-}\mathsf{B}}
\newcommand{\OChallA}{\mathsf{O}\text{-}\mathsf{Chall}\text{-}\mathsf{A}}
\newcommand{\OChallB}{\mathsf{O}\text{-}\mathsf{Chall}\text{-}\mathsf{B}}
\newcommand{\OCorrA}{\mathsf{O}\text{-}\mathsf{Corr}\text{-}\mathsf{A}}
\newcommand{\OCorrB}{\mathsf{O}\text{-}\mathsf{Corr}\text{-}\mathsf{B}}
\renewcommand{\O}{\mathcal{O}}
\newcommand{\Ocor}{\mathcal{O}_{\mathsf{cor}}}
\newcommand{\Osec}{\mathcal{O}_{\mathsf{sec}}}
\newcommand{\gamestate}{\textsf{game state:}}
\newcommand{\gameparams}{\textsf{game params:}}
\newcommand{\allow}{\mathsf{allow\text{-}corr}}
"#

/-- Register `cryptoTexPrelude` once, globally, with VersoBlueprint's TeX-prelude
extension. (The built-in `tex_prelude` command only accepts a string *literal*,
so we add the shared `def` to the extension directly, keeping a single source of
truth for the notation.) -/
elab "register_crypto_tex_prelude" : command => do
  modifyEnv (texPreludeExt.addEntry · cryptoTexPrelude)

register_crypto_tex_prelude

/-- Repair TeX strings where JSON/tab handling turned `\text…` into a tab + `ext…`. -/
def repairTexForMath (s : String) : String :=
  let tab := String.ofList [Char.ofNat 9]
  s.replace (tab ++ "ext") "\\text"

/-- Inline `bp_math` node using the shared prelude id (for game cells, pill captions, …). -/
def bpMathInline (tex : String) : Verso.Output.Html :=
  Verso.Output.Html.tag "code"
    #[("class", "bp_math inline"), ("data-bp-tex-prelude-id", "default")]
    (Verso.Output.Html.text true (repairTexForMath tex))
