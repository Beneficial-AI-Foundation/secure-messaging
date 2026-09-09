import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.OppBiKEM.Construction

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre
open Verso.Genre.Manual
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Opp-BiKEM-CKA" =>

:::group "cka_protocols_opp_bikem_cka"
Opp-BiKEM-CKA.
:::

:::defTitle "opp_bikem_cka_spec" "Opp-BiKEM-CKA protocol"
:::

:::::::definition "opp_bikem_cka_spec" (parent := "cka_protocols_opp_bikem_cka") (lean := "oppBiKemCKA.initKeyGen, oppBiKemCKA.initA, oppBiKemCKA.initB, oppBiKemCKA.vulnA, oppBiKemCKA.vulnB, oppBiKemCKA.sendA, oppBiKemCKA.sendArleak, oppBiKemCKA.recvA, oppBiKemCKA.sendB, oppBiKemCKA.sendBrleak, oppBiKemCKA.recvB, oppBiKemCKA.scheme")
Figures 17 and 18 of {Informal.citet SCKA25}[]. This construction uses a standard
KEM: $`A` encapsulates in odd epochs and $`B` encapsulates in even epochs. Both parties
send public-key chunks opportunistically, before transmitting ciphertext chunks.
There is no offline/online ciphertext split (unlike in OppUniKEM).

Each party has two counters:

- $`t_{\mathrm{req}}` for the epoch in which it plays the *requester* role (a requester decapsulates the received encapsulated key).
- $`t_{\mathrm{res}}` for the epoch in which it plays the *responder* role (a responder encapsulates the key using the requester's public key).

The two roles share Lean helpers, using offset variables $`\delta_\A=1` and
$`\delta_\B=-1`.

We make the following corrections with respect to the pseudocode:

* In Figure 18, $`\mathsf{CKA}\text{-}\SendB`, lines 8, 9, and 13, replace
  $`\boxed{t_{\mathrm{res}\text{-}A}\mapsto t_{\mathrm{res}\text{-}B}}`.
  B's local state contains B's responder counter.
* In Figure 17, $`\mathsf{CKA}\text{-}\mathsf{Rec}\text{-}\A`, line 22, replace
  $`\boxed{\mathit{ct}_A\mapsto\mathit{ct}_B}`. Lines 23 and 27 already use B's ciphertext.
* Public-key acknowledgement indices are corrected at both ends of each message:
  in Figure 17, Send-A line 21 uses
  $`\boxed{t_{\mathrm{req}\text{-}A}-1}` and Rec-A line 8 uses
  $`\boxed{t_{\mathrm{req}\text{-}B}+1}`;
  in Figure 18, Send-B line 21 uses
  $`\boxed{t_{\mathrm{req}\text{-}B}+1}` and Rec-B line 8 uses
  $`\boxed{t_{\mathrm{req}\text{-}A}-1}`.
  These are the public-key entries set by decoding. The printed formulas
  advertise different entries, leaving the first public keys unacknowledged.


::::::gameGrid


:::::gameCell "\\textsf{Initialisation}" (kind := "compact")

$`\begin{array}{l}
\mathsf{CKA}\text{-}\mathsf{InitKeyGen}(): \\
\quad I_{\mathsf{CKA}}\gets\bot \\
\quad \mathsf{return}\;I_{\mathsf{CKA}}
\end{array}`
```anchor initKeyGen (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def initKeyGen : m Unit := pure ()
```

```anchor init (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { resEpoch := if role = .A then -1 else 0
         reqEpoch := if role = .A then 0 else -1
         ekPeer := fun _ => none
         ct := none, ich := 0, dk := [], ek := none, receivedChunks := ∅
         ack := { ekRec := ∅, ctRec := {-1, 0} } }
```

$`\begin{array}{l}
\mathsf{CKA}\text{-}\mathsf{InitA}(\bot): \\
\quad \mathsf{EK}_{B}[t]\gets\bot,\ \mathsf{DK}_{A}[t]\gets\bot\quad\text{for all }t \\
\quad (\mathsf{ACK}[t].\mathsf{ekRec},\mathsf{ACK}[t].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{false},\mathsf{false})\quad\text{for all }t \\
\quad (\mathsf{ACK}[-1].\mathsf{ctRec},\mathsf{ACK}[0].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{true},\mathsf{true}) \\
\quad \mathsf{st}_{\mathrm{res}}\gets(-1,\mathsf{EK}_{B},\bot,0) \\
\quad \mathsf{st}_{\mathrm{req}}\gets(0,\mathsf{DK}_{A},\bot,\emptyset) \\
\quad \mathsf{return}\;(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK})
\end{array}`
```anchor initA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def initA : Unit → m (StA PK SK C Sym) := init .A
```

$`\begin{array}{l}
\mathsf{CKA}\text{-}\mathsf{InitB}(\bot): \\
\quad \mathsf{EK}_{A}[t]\gets\bot,\ \mathsf{DK}_{B}[t]\gets\bot\quad\text{for all }t \\
\quad (\mathsf{ACK}[t].\mathsf{ekRec},\mathsf{ACK}[t].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{false},\mathsf{false})\quad\text{for all }t \\
\quad (\mathsf{ACK}[-1].\mathsf{ctRec},\mathsf{ACK}[0].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{true},\mathsf{true}) \\
\quad \mathsf{st}_{\mathrm{res}}\gets(0,\mathsf{EK}_{A},\bot,0) \\
\quad \mathsf{st}_{\mathrm{req}}\gets(-1,\mathsf{DK}_{B},\bot,\emptyset) \\
\quad \mathsf{return}\;(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK})
\end{array}`
```anchor initB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def initB : Unit → m (StB PK SK C Sym) := init .B
```

:::::

:::::gameCell "\\textsf{Vulnerable epochs}" (kind := "compact")

$`\begin{array}{l}
\mathsf{st}_A.\mathsf{vuln}:\quad\mathsf{return}\;\{t:\mathsf{DK}_A[t]\ne\bot\}
\end{array}`
$`\begin{array}{l}
\mathsf{st}_B.\mathsf{vuln}:\quad\mathsf{return}\;\{t:\mathsf{DK}_B[t]\ne\bot\}
\end{array}`

Only retained decapsulation keys contribute. Public keys and ciphertexts do not
require secrecy. Dummy epochs are excluded from the natural-number SCKA interface.

```anchor vuln (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def vuln (st : State PK SK C Sym) : Finset ℕ :=
  ((st.dk.map Prod.fst).toFinset.filter fun t => 0 < t).image Int.toNat

def vulnA (st : StA PK SK C Sym) : Finset ℕ := vuln st

def vulnB (st : StB PK SK C Sym) : Finset ℕ := vuln st
```

:::::

:::::gameCell "\\mathsf{CKA}\\text{-}\\mathsf{Send}\\text{-}A(\\mathsf{st}_A)" (kind := "compact-send")

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}A},\mathsf{EK}_B,\mathit{ct}_A,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}A},\mathsf{DK}_A,\mathit{ek}_A,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
I_A\gets\bot,\ t_{I_A}\gets\bot,\ \mathit{ch}\gets\bot,\ b\gets\bot \\
\mathsf{if}\;\mathit{ek}_A=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}A}].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}A}+1].\mathsf{ctRec}\;\mathsf{then} \\
\quad t_{\mathrm{res}\text{-}A}\gets t_{\mathrm{res}\text{-}A}+2,\quad i_{\mathrm{ch}}\gets0 \\
\quad (\mathit{ek}_A,\mathit{dk}_A)\sample\KeyGen \\
\quad \mathsf{DK}_A[t_{\mathrm{res}\text{-}A}+1]\gets\mathit{dk}_A \\
\mathsf{if}\;\neg\mathsf{ACK}[t_{\mathrm{res}\text{-}A}+1].\mathsf{ekRec}\;\mathsf{then} \\
\quad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets0 \\
\quad \mathit{ch}\gets\mathsf{Encode}(\mathit{ek}_A,i_{\mathrm{ch}}) \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[t_{\mathrm{res}\text{-}A}].\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{if}\;\mathit{ct}_A=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}A}].\mathsf{ekRec}\;\mathsf{then} \\
\qquad t_{I_A}\gets t_{\mathrm{res}\text{-}A},\quad i_{\mathrm{ch}}\gets0 \\
\qquad(\mathit{ct}_A,I_A)\sample\Encaps(\mathsf{EK}_B[t_{\mathrm{res}\text{-}A}]) \\
\quad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets1 \\
\quad \mathit{ch}\gets\mathsf{Encode}(\mathit{ct}_A,i_{\mathrm{ch}}) \\
t^{\mathrm{snd}}_A\gets\max\{t:\mathsf{ACK}[t].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t-1].\mathsf{ctRec}\} \\
\mathit{ack}\gets(\mathsf{ACK}[\boxed{t_{\mathrm{req}\text{-}A}-1}].\mathsf{ekRec},\mathsf{ACK}[t_{\mathrm{req}\text{-}A}].\mathsf{ctRec}) \\
\rho\gets(\mathit{ch},t_{\mathrm{res}\text{-}A},t_{\mathrm{req}\text{-}A},t^{\mathrm{snd}}_A,\mathit{ack},b) \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}A},\mathsf{EK}_B,\mathit{ct}_A,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}A},\mathsf{DK}_A,\mathit{ek}_A,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_A},I_A),\rho,t^{\mathrm{snd}}_A, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`

```anchor sendA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendA (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) := send .A kem ecEk ecCt stA
```

:::leanPillCaption "rleak version leaking key generation and encapsulation coins"
:::
```anchor sendArleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendArleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stA : StA PK SK C Sym) :=
  sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt stA
```

:::::

:::::gameCell "\\mathsf{CKA}\\text{-}\\mathsf{Rec}\\text{-}A(\\mathsf{st}_A,\\rho)" (kind := "compact-recv")

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}A},\mathsf{EK}_B,\mathit{ct}_A,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}A},\mathsf{DK}_A,\mathit{ek}_A,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
(\mathit{ch},t_{\mathrm{res}\text{-}B},t_{\mathrm{req}\text{-}B},t^{\mathrm{snd}}_B,\mathit{ack},b)\gets\rho \\
I_B\gets\bot,\quad t_{I_B}\gets\bot \\
\mathsf{if}\;\mathit{ack}.\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[t_{\mathrm{req}\text{-}B}].\mathsf{ctRec}\gets\mathsf{true} \\
\mathsf{if}\;\mathit{ack}.\mathsf{ekRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[\boxed{t_{\mathrm{req}\text{-}B}+1}].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{if}\;t_{\mathrm{res}\text{-}B}<t_{\mathrm{req}\text{-}A}\;\mathsf{then}\;\mathsf{break} \\
\mathsf{else\ if}\;t_{\mathrm{res}\text{-}B}>t_{\mathrm{req}\text{-}A}\;\mathsf{then}\;t_{\mathrm{req}\text{-}A}\gets t_{\mathrm{req}\text{-}A}+2 \\
\mathsf{if}\;\mathsf{EK}_B[t_{\mathrm{req}\text{-}A}-1]=\bot\wedge b=0\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \mathit{ek}_B\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ek}_B\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{EK}_B[t_{\mathrm{req}\text{-}A}-1]\gets\mathit{ek}_B \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}A}-1].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[t_{\mathrm{req}\text{-}A}].\mathsf{ctRec}\wedge b=1\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \boxed{\mathit{ct}_B}\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ct}_B\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}A}].\mathsf{ctRec}\gets\mathsf{true} \\
\qquad t_{I_B}\gets t_{\mathrm{req}\text{-}A} \\
\qquad I_B\gets\Decaps(\mathsf{DK}_A[t_{\mathrm{req}\text{-}A}],\mathit{ct}_B) \\
\qquad\mathsf{DK}_A[t_{\mathrm{req}\text{-}A}]\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}A}].\mathsf{ctRec}\;\mathsf{then}\;\mathit{ct}_A\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}A}+1].\mathsf{ekRec}\;\mathsf{then}\;\mathit{ek}_A\gets\bot \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}A},\mathsf{EK}_B,\mathit{ct}_A,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}A},\mathsf{DK}_A,\mathit{ek}_A,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_B},I_B),t^{\mathrm{snd}}_B, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`

```anchor recvA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recvA (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (ρ : Message Sym) := recv .A kem hDet ecEk ecCt stA ρ
```

:::::

:::::gameCell "\\mathsf{CKA}\\text{-}\\mathsf{Send}\\text{-}B(\\mathsf{st}_B)" (kind := "compact-send")

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}B},\mathsf{EK}_A,\mathit{ct}_B,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}B},\mathsf{DK}_B,\mathit{ek}_B,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
I_B\gets\bot,\ t_{I_B}\gets\bot,\ \mathit{ch}\gets\bot,\ b\gets\bot \\
\mathsf{if}\;\mathit{ek}_B=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}B}].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}B}-1].\mathsf{ctRec}\;\mathsf{then} \\
\quad t_{\mathrm{res}\text{-}B}\gets t_{\mathrm{res}\text{-}B}+2,\quad i_{\mathrm{ch}}\gets0 \\
\quad (\mathit{ek}_B,\mathit{dk}_B)\sample\KeyGen \\
\quad \mathsf{DK}_B[\boxed{t_{\mathrm{res}\text{-}B}-1}]\gets\mathit{dk}_B \\
\mathsf{if}\;\neg\mathsf{ACK}[\boxed{t_{\mathrm{res}\text{-}B}-1}].\mathsf{ekRec}\;\mathsf{then} \\
\quad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets0 \\
\quad \mathit{ch}\gets\mathsf{Encode}(\mathit{ek}_B,i_{\mathrm{ch}}) \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[\boxed{t_{\mathrm{res}\text{-}B}}].\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{if}\;\mathit{ct}_B=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}B}].\mathsf{ekRec}\;\mathsf{then} \\
\qquad t_{I_B}\gets t_{\mathrm{res}\text{-}B},\quad i_{\mathrm{ch}}\gets0 \\
\qquad(\mathit{ct}_B,I_B)\sample\Encaps(\mathsf{EK}_A[t_{\mathrm{res}\text{-}B}]) \\
\quad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets1 \\
\quad \mathit{ch}\gets\mathsf{Encode}(\mathit{ct}_B,i_{\mathrm{ch}}) \\
t^{\mathrm{snd}}_B\gets\max\{t:\mathsf{ACK}[t].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t-1].\mathsf{ctRec}\} \\
\mathit{ack}\gets(\mathsf{ACK}[\boxed{t_{\mathrm{req}\text{-}B}+1}].\mathsf{ekRec},\mathsf{ACK}[t_{\mathrm{req}\text{-}B}].\mathsf{ctRec}) \\
\rho\gets(\mathit{ch},t_{\mathrm{res}\text{-}B},t_{\mathrm{req}\text{-}B},t^{\mathrm{snd}}_B,\mathit{ack},b) \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}B},\mathsf{EK}_A,\mathit{ct}_B,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}B},\mathsf{DK}_B,\mathit{ek}_B,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_B},I_B),\rho,t^{\mathrm{snd}}_B, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`

```anchor sendB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendB (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) := send .B kem ecEk ecCt stB
```

:::leanPillCaption "rleak version leaking key generation and encapsulation coins"
:::
```anchor sendBrleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendBrleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stB : StB PK SK C Sym) :=
  sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt stB
```

:::::

:::::gameCell "\\mathsf{CKA}\\text{-}\\mathsf{Rec}\\text{-}B(\\mathsf{st}_B,\\rho)" (kind := "compact-recv")

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}B},\mathsf{EK}_A,\mathit{ct}_B,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}B},\mathsf{DK}_B,\mathit{ek}_B,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
(\mathit{ch},t_{\mathrm{res}\text{-}A},t_{\mathrm{req}\text{-}A},t^{\mathrm{snd}}_A,\mathit{ack},b)\gets\rho \\
I_A\gets\bot,\quad t_{I_A}\gets\bot \\
\mathsf{if}\;\mathit{ack}.\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[t_{\mathrm{req}\text{-}A}].\mathsf{ctRec}\gets\mathsf{true} \\
\mathsf{if}\;\mathit{ack}.\mathsf{ekRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[\boxed{t_{\mathrm{req}\text{-}A}-1}].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{if}\;t_{\mathrm{res}\text{-}A}<t_{\mathrm{req}\text{-}B}\;\mathsf{then}\;\mathsf{break} \\
\mathsf{else\ if}\;t_{\mathrm{res}\text{-}A}>t_{\mathrm{req}\text{-}B}\;\mathsf{then}\;t_{\mathrm{req}\text{-}B}\gets t_{\mathrm{req}\text{-}B}+2 \\
\mathsf{if}\;\mathsf{EK}_A[t_{\mathrm{req}\text{-}B}+1]=\bot\wedge b=0\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \mathit{ek}_A\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ek}_A\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{EK}_A[t_{\mathrm{req}\text{-}B}+1]\gets\mathit{ek}_A \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}B}+1].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[t_{\mathrm{req}\text{-}B}].\mathsf{ctRec}\wedge b=1\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \mathit{ct}_A\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ct}_A\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}B}].\mathsf{ctRec}\gets\mathsf{true} \\
\qquad t_{I_A}\gets t_{\mathrm{req}\text{-}B} \\
\qquad I_A\gets\Decaps(\mathsf{DK}_B[t_{\mathrm{req}\text{-}B}],\mathit{ct}_A) \\
\qquad\mathsf{DK}_B[t_{\mathrm{req}\text{-}B}]\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}B}].\mathsf{ctRec}\;\mathsf{then}\;\mathit{ct}_B\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}B}-1].\mathsf{ekRec}\;\mathsf{then}\;\mathit{ek}_B\gets\bot \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}B},\mathsf{EK}_A,\mathit{ct}_B,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}B},\mathsf{DK}_B,\mathit{ek}_B,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_A},I_A),t^{\mathrm{snd}}_A, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`

```anchor recvB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recvB (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) (ρ : Message Sym) := recv .B kem hDet ecEk ecCt stB ρ
```

:::::

:::::gameCell "\\textsf{Shared Lean send implementation}" (kind := "compact")

For party $`P`, with offset $`\delta_P`, the shared send follows Figures 17–18.
For clarity, the docs show per-party pseudocode.

The shared helper takes the randomized KEM calls as arguments. Ordinary sends
supply calls with dummy `Unit` coins; leaking sends supply the existing
`KEMScheme.RandLeak` operations. Both therefore execute the same branches.

```anchor sendWith (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendWith {RKey REnc : Type} (role : Role)
    (keygen : m ((PK × SK) × RKey)) (encaps : PK → m ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RKey REnc)) := do
  let (st, rKey?) ←
    if st.ek.isNone && decide (st.resEpoch ∈ st.ack.ctRec ∧
        st.resEpoch + role.offset ∈ st.ack.ctRec) then do
      let ((ek, dk), rKey) ← keygen
      let t := st.resEpoch + 2
      let keyEpoch := t + role.offset
      pure ({ st with resEpoch := t, ich := 0, ek := some ek
                      dk := (keyEpoch, dk) :: st.dk.filter (fun p => p.1 != keyEpoch) },
            some rKey)
    else pure (st, none)
  let (key?, ch?, bit?, st, rEnc?) ←
    if st.resEpoch + role.offset ∉ st.ack.ekRec then do
      let ich := st.ich + 1
      let ch? := st.ek.map (fun ek => ecEk.encode ek ich)
      pure (none, ch?, some (0 : Bit), { st with ich }, none)
    else if st.resEpoch ∉ st.ack.ctRec then do
      let (key?, st, rEnc?) ←
        if st.ct.isNone && decide (st.resEpoch ∈ st.ack.ekRec) then
          match st.ekPeer st.resEpoch with
          | none => pure (none, st, none)
          | some ekPeer => do
              let ((ct, key), rEnc) ← encaps ekPeer
              pure (some (st.resEpoch.toNat, key), { st with ct := some ct, ich := 0 },
                some rEnc)
        else pure (none, st, none)
      let ich := st.ich + 1
      let ch? := st.ct.map (fun ct => ecCt.encode ct ich)
      pure (key?, ch?, some (1 : Bit), { st with ich }, rEnc?)
    else pure (none, none, none, st, none)
  let ρ := message role st ch? bit?
  pure (some (key?, ρ, ρ.sendingEpoch, st, { keygen := rKey?, encaps := rEnc? }))
```
```anchor send (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def send (role : Role) (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym)) := do
  let out ← sendWith role
    (do let keys ← kem.keygen; pure (keys, ()))
    (fun pk => do let out ← kem.encaps pk; pure (out, ())) ecEk ecCt st
  pure (out.map fun (key?, ρ, t, st, _) => (key?, ρ, t, st))
```
:::::

:::::gameCell "\\textsf{Shared Lean receive implementation}" (kind := "compact")

For party $`P`, with offset $`\delta_P`, the shared receive follows Figures 17–18.
For clarity, the docs show per-party pseudocode.

```anchor recv (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ack := st.ack
  let ack := if ρ.ack.ctRec then { ack with ctRec := insert ρ.reqEpoch ack.ctRec } else ack
  let ack := if ρ.ack.ekRec then
      { ack with ekRec := insert (ρ.reqEpoch + role.offset) ack.ekRec } else ack
  let st := { st with ack }
  if ρ.resEpoch < st.reqEpoch then
  -- outdated message
    some (none, ρ.sendingEpoch, st)
  else
    let st := if st.reqEpoch < ρ.resEpoch
              -- first message of the new epoch
              then { st with reqEpoch := st.reqEpoch + 2 }
              else st
    -- Captures the relation of "1 removed" epochs
    --   - if A is requesting the key for epoch t, it receives B's public key for t-1
    --   - if B is requesting the key for epoch t, it receives A's public key for t+1
    let peerKeyEpoch := st.reqEpoch - role.offset
    let (key?, st) :=
      match ρ.bit, ρ.ch with
      | some 0, some ch =>
          if (st.ekPeer peerKeyEpoch).isNone then
            let receivedChunks := insert ch st.receivedChunks
            match ecEk.decode receivedChunks with
            | none => (none, { st with receivedChunks })
            | some ekPeer =>
                (none, { st with receivedChunks := ∅
                                 ekPeer := Function.update st.ekPeer peerKeyEpoch (some ekPeer)
                                 ack := { st.ack with ekRec := insert peerKeyEpoch st.ack.ekRec } })
          else (none, st)
      | some 1, some ch =>
          if st.reqEpoch ∉ st.ack.ctRec then
            match st.dk.lookup st.reqEpoch with
            | none => (none, st)
            | some dk =>
                let receivedChunks := insert ch st.receivedChunks
                match ecCt.decode receivedChunks with
                | none => (none, { st with receivedChunks })
                | some ct =>
                    match hDet.decapsDet dk ct with
                    | none => (none, st)
                    | some key =>
                        (some (st.reqEpoch.toNat, key),
                          { st with receivedChunks := ∅
                                    dk := st.dk.filter (fun p => p.1 != st.reqEpoch)
                                    ack := { st.ack with
                                      ctRec := insert st.reqEpoch st.ack.ctRec } })
          else (none, st)
      | _, _ => (none, st)
    -- deleting the stored material that has been fully delivered
    let st := if st.resEpoch ∈ st.ack.ctRec then { st with ct := none } else st
    let st := if st.resEpoch + role.offset ∈ st.ack.ekRec then { st with ek := none } else st
    some (key?, ρ.sendingEpoch, st)
```
:::::

::::::

:::leanPillCaption "SCKA scheme instance"
:::
```anchor scheme (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def scheme (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    SCKAScheme m Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) where
  initKeyGen := initKeyGen
  initA := initA
  initB := initB
  sendA := sendA kem ecEk ecCt
  sendArleak := sendArleak kem ecEk ecCt leak
  recvA := recvA kem hDet ecEk ecCt
  sendB := sendB kem ecEk ecCt
  sendBrleak := sendBrleak kem ecEk ecCt leak
  recvB := recvB kem hDet ecEk ecCt
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 109}[]
:::::::

:::defTitle "opp_bikem_cka_correctness" "Opp-BiKEM-CKA correctness"
:::

::::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols_opp_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 110}[]
::::

:::defTitle "opp_bikem_cka_security" "Opp-BiKEM-CKA security"
:::

::::theorem "opp_bikem_cka_security" (parent := "cka_protocols_opp_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 111}[]
::::
