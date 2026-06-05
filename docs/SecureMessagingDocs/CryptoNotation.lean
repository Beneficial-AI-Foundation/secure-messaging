import VersoManual
import VersoBlueprint

open Verso.Genre Manual

tex_prelude r#"
\providecommand{\sample}{\mathrel{\overset{\scriptscriptstyle\$}{\leftarrow}}}
\providecommand{\getsval}{\gets}
\providecommand{\Return}{\textbf{return}\;}
\providecommand{\KeyGen}{\mathsf{KeyGen}}
\providecommand{\Enc}{\mathsf{Enc}}
\providecommand{\Dec}{\mathsf{Dec}}
\providecommand{\Init}{\mathsf{Init}}
\providecommand{\Send}{\mathsf{Send}}
\providecommand{\Recv}{\mathsf{Recv}}
\providecommand{\Gen}{\mathsf{Gen}}
\providecommand{\Encaps}{\mathsf{Encaps}}
\providecommand{\Decaps}{\mathsf{Decaps}}
\providecommand{\Exp}{\mathsf{Exp}}
\providecommand{\Adv}{\mathsf{Adv}}
\providecommand{\Pr}{\operatorname{Pr}}
\providecommand{\msgR}[1]{\xrightarrow{\hspace{3em}#1\hspace{3em}}}
\providecommand{\msgL}[1]{\xleftarrow{\hspace{3em}#1\hspace{3em}}}
\providecommand{\concat}{\mathbin{\|}}
\providecommand{\bit}{\{0,1\}}
\providecommand{\orc}[1]{\textsf{#1}}
"#
