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

The Lean state groups these roles into `st.req : RequesterState PK SK Sym` and
`st.res : ResponderState PK C`, corresponding to $`\mathsf{st}_{\mathrm{req}}` and
$`\mathsf{st}_{\mathrm{res}}` in Figures 17–18. The shared `st.ack` remains alongside
both substates, matching the paper's
$`(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK})`.

The requester owns `reqEpoch`, retained secret keys `dk`, the local public key `ek`,
and `receivedChunks`. The responder owns `resEpoch`, decoded peer public keys
`ekPeer`, the outgoing ciphertext `ct`, and the outgoing chunk counter `ich`.
The chunk counter serves both outgoing payload types, and the incoming chunk set
serves both peer public keys and ciphertexts. Sending and receiving can therefore
update both substates; acknowledgements are shared by both.


```anchor state (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Responder substate `st_res = (t_res, EK_peer, ct, i_ch)` in Figures 17–18.
The outgoing chunk counter is used for both public keys and ciphertexts. -/
structure ResponderState (PK C : Type) where
  /-- Current responder epoch, used for outgoing ciphertexts. -/
  resEpoch : ℤ
  /-- Decoded peer public keys indexed by their encapsulation epochs. -/
  ekPeer : ℤ → Option PK
  /-- Outgoing ciphertext, retained until the peer acknowledges it. -/
  ct : Option C
  /-- Last outgoing chunk index, reset to zero when a new payload is prepared. -/
  ich : ℕ

/-- Requester substate `st_req = (t_req, DK, ek, L_ch)` in Figures 17–18.
The incoming chunk set is used for both peer public keys and ciphertexts. -/
structure RequesterState (PK SK Sym : Type) where
  /-- Current requester epoch, used for incoming ciphertexts. -/
  reqEpoch : ℤ
  /-- Retained secret keys indexed by their decapsulation epochs. -/
  dk : List (ℤ × SK)
  /-- Local public key, retained until the peer acknowledges it. -/
  ek : Option PK
  /-- Chunks accumulated for decoding the incoming payload (`L_ch` in the paper).
  Each chunk is represented as `(position, encodedSymbol)`. -/
  receivedChunks : Finset (ℕ × Sym)

/-- A party's local state: requester and responder substates with shared `ACK`.
The paper writes this as `(st_res, st_req, ACK)`; the named fields expose each component. -/
structure State (PK SK C Sym : Type) where
  /-- Requester state containing retained decapsulation keys and incoming chunks. -/
  req : RequesterState PK SK Sym
  /-- Responder state containing decoded peer public keys and outgoing ciphertext. -/
  res : ResponderState PK C
  /-- Locally recorded and peer-reported receipt acknowledgements. -/
  ack : Acknowledgements

/-- Party A's local protocol state. -/
abbrev StA := State
/-- Party B's local protocol state. -/
abbrev StB := State
```

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

Because `CKA-Send-B` and `CKA-Send-A` are symmetric, we implement them using a single
function, `sendWith`. This function specializes for `A` or `B` by using the `Role.offset` variable,
that distinguishes between roles at different indices that `A` and `B` play.
The same is true for `CKA-Rec-A` and `CKA-Rec-B`, both of which are implemented in
function `recv`, parameterized by `Role.offset`.


We also make absent-payload handling explicit.
Our `decodeAndInsertChunk` helper treats an absent chunk as no decoding progress: it leaves
the accumulated set unchanged and returns no payload without calling the decoder,
even if the retained set is already decodable. A present chunk is inserted before
decoding. This is our modeling convention for a case left implicit in the
pseudocode. Receipt acknowledgements, epoch processing,
and cleanup follow the usual receive path even when the chunk is absent; stale
messages still only update peer-reported acknowledgements.

There are two further checks for optional keys. If the encapsulation guard holds
but `ekPeer resEpoch` is absent, send skips encapsulation and produces no epoch
key. If the ciphertext receive guard holds but `dk.lookup reqEpoch` is absent,
receive preserves the payload state without accumulating or decoding the chunk;
acknowledgement processing, counter updates, and cleanup still apply. The paper
does not specify KEM calls on absent keys.


::::::gameGrid


:::::gameCell "\\textsf{Initialisation}" (kind := "compact")

$`\begin{array}{l}
\mathsf{CKA}\text{-}\mathsf{InitKeyGen}(): \\
\quad I_{\mathsf{CKA}}\gets\bot \\
\quad \mathsf{return}\;I_{\mathsf{CKA}}
\end{array}`
```anchor initKeyGen (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Return the trivial initialization key: OppBiKEM protocol does not need initialization key -/
def initKeyGen : m Unit := pure ()
```

```anchor init (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { req := { reqEpoch := if role = .A then 0 else -1
                  dk := [], ek := none, receivedChunks := ∅ }
         res := { resEpoch := if role = .A then -1 else 0
                  ekPeer := fun _ => none
                  ct := none, ich := 0 }
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
/-- Initialize A -/
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
/-- Initialize B -/
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
  let storedEpochs := (st.req.dk.map Prod.fst).toFinset
  let positiveEpochs := storedEpochs.filter fun t => 0 < t
  positiveEpochs.image Int.toNat

/-- Positive epochs whose secret decapsulation keys remain in A's state. -/
def vulnA (st : StA PK SK C Sym) : Finset ℕ := vuln st

/-- Positive epochs whose secret decapsulation keys remain in B's state. -/
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
/-- Run A's send step. -/
def sendA (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) := send .A kem ecEk ecCt stA
```

:::leanPillCaption "rleak version leaking key generation and encapsulation coins"
:::
```anchor sendArleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run A's send step, also returning randomness used for key generation and encapsulation. -/
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
/-- Process a message at A (by specializing `recv` function) -/
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
/-- Run B's send step. -/
def sendB (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) := send .B kem ecEk ecCt stB
```

:::leanPillCaption "rleak version leaking key generation and encapsulation coins"
:::
```anchor sendBrleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run B's send step, also returning randomness used for key generation and encapsulation. -/
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
/-- Process a message at B (by specializing `recv` function) -/
def recvB (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) (ρ : Message Sym) := recv .B kem hDet ecEk ecCt stB ρ
```

:::::

:::::gameCell "\\textsf{Shared Lean send implementation}" (kind := "compact")

For party $`P`, with offset $`\delta_P`, the shared send follows Figures 17–18.
The per-party pseudocode above incorporates the listed corrections; the Lean
code additionally makes the absent-payload and absent-key cases explicit.

The two sending phases depend on separate guards. A send may generate a key pair
and then select a payload in the same call. If neither payload guard holds,
`ch` and `bit` are both `none`, but acknowledgements and epoch metadata are still
sent. A selected but unavailable ciphertext instead has `bit = some 1` and
`ch = none`. Resetting the chunk counter accompanies a new key pair or fresh
encapsulation, not every retransmission.

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
  let ⟨resEpoch, ekPeer, ct, ich⟩ := st.res
  let ⟨reqEpoch, dk, ek, receivedChunks⟩ := st.req
  let ack := st.ack
  let (resEpoch, dk, ek, ich, rKey?) ←
    -- if ready to advance the epoch (Line 4 in the paper CKA-Send-P)
    if ek.isNone && decide (resEpoch ∈ ack.ctRec ∧
        resEpoch + role.offset ∈ ack.ctRec) then do
      let ((newEk, newDk), rKey) ← keygen
      let t := resEpoch + 2
      -- the epoch for which the decapsulation key was generated
      -- (t+1 in CKA-Send-A, line 8; t-1 in CKA-Send-B, line 8)
      let keyEpoch := t + role.offset
      pure (t, (keyEpoch, newDk) :: dk.filter (fun p => p.1 != keyEpoch),
        some newEk, 0, some rKey)
    else pure (resEpoch, dk, ek, ich, none)
  let (key?, ch?, bit?, ct, ich, rEnc?) ←
    -- if the encapsulation key was not yet received by the peer (lines 9-12 in CKA-Send-P)
    if resEpoch + role.offset ∉ ack.ekRec then do
      let ich := ich + 1
      let ch? := ek.map (fun ek => ecEk.encode ek ich)
      pure (none, ch?, some (0 : Bit), ct, ich, none)
    -- if the encapsulation key was received, but ciphertext was **not** yet received by the peer
    else if resEpoch ∉ ack.ctRec then do
      let (key?, ct, ich, rEnc?) ←
        -- if no ciphertext is stored and the peer's encapsulation key has been received
        -- (lines 14-16 in CKA-Send-P)
        if ct.isNone && decide (resEpoch ∈ ack.ekRec) then
          match ekPeer resEpoch with
          | none => pure (none, ct, ich, none)
          | some peerEk => do
              let ((newCt, key), rEnc) ← encaps peerEk
              pure (some (resEpoch.toNat, key), some newCt, 0, some rEnc)
        else pure (none, ct, ich, none)
      let ich := ich + 1
      let ch? := ct.map (fun ct => ecCt.encode ct ich)
      pure (key?, ch?, some (1 : Bit), ct, ich, rEnc?)
    else pure (none, none, none, ct, ich, none)
  let st : State PK SK C Sym :=
    { res := ⟨resEpoch, ekPeer, ct, ich⟩
      req := ⟨reqEpoch, dk, ek, receivedChunks⟩
      ack }
  let ρ : Message Sym :=
    { ch := ch?, bit := bit?, resEpoch, reqEpoch
      sendingEpoch := ack.sendingEpoch
      ack := { ekRec := decide (reqEpoch - role.offset ∈ ack.ekRec)
               ctRec := decide (reqEpoch ∈ ack.ctRec) } }
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
The per-party pseudocode above incorporates the listed corrections and is subject
to the explicit modeling conventions described above.

Receive incorporates peer acknowledgements before checking message age. We
interpret the paper's `break` at line 10 as an early return with those updated
acknowledgements and the incoming message's sending epoch; it skips payload
processing, counter advancement, and outgoing-material cleanup. For a newer
message the counter advances by exactly two, as printed, rather than being
assigned the peer's counter. On every path, the returned receiving epoch is the
message's `sendingEpoch`, not a newly computed local maximum.

The ciphertext guard only tests receipt and the selector; it does not separately
test whether the peer's public key is stored. If neither payload guard holds,
receive leaves the payload state unchanged and still performs ordinary cleanup.
This final branch is reachable in honest executions: after B decodes A's public
key, A may send more public-key chunks before receiving B's acknowledgement.
Already received ciphertext and messages with `bit = none` also select this branch
when the message is not stale.

The receive algorithm combines the readiness condition and payload selector in
each `if` / `else if` guard, following the pseudocode. The helper below handles
optional chunks for both public-key and ciphertext decoding, preserving the
absent-payload convention described above. Incomplete decoding retains the chunk
set. Successful public-key or ciphertext decoding clears it. After ciphertext
decoding, receive acknowledges receipt, attempts decapsulation, and erases the
secret key regardless of the result, following lines 24–28 of the pseudocode.
If decapsulation returns `none`, the operation still returns an updated state,
but no epoch key. Later ciphertext chunks for that acknowledged epoch are ignored.

Thus `ctRec` records ciphertext receipt, not a separate confirmation that the
session key was recovered. The paper can write $`(t_I,\bot)` on this failure path;
our `Option (ℕ × K)` key output represents this by `none`, without separately
reporting the attempted key epoch. The message's receiving epoch is still returned.

The separate design note `docs/design/oppbikem-decapsulation-failure.md` compares
this behavior with retaining the secret key and withholding acknowledgement on
failure, including the implications for recovery, erasure, and correctness proofs.

```anchor decodeChunk (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Accumulate an optional chunk and try to decode a payload.
For `some ch`, insert the chunk and return the updated set and decoding result.
For `none`, preserve the set and return no payload without
calling the decoder, even if the retained chunks could already decode.
The caller clears the set after successful public-key or ciphertext decoding,
including when subsequent decapsulation fails. -/
def decodeAndInsertChunk {Payload : Type} [DecidableEq Sym]
    (ec : ErasureCodePayload Payload Sym) (receivedChunks : Finset (ℕ × Sym))
    (ch? : Option (ℕ × Sym)) : Finset (ℕ × Sym) × Option Payload :=
  match ch? with
  | none => (receivedChunks, none)
  | some ch =>
      let chunks := insert ch receivedChunks
      (chunks, ec.decode chunks)
```

```anchor recv (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ⟨resEpoch, ekPeer, ct, ich⟩ := st.res
  let ⟨reqEpoch, dk, ek, receivedChunks⟩ := st.req
  let ⟨ch?, peerResEpoch, peerReqEpoch, sendingEpoch, peerAck, bit?⟩ := ρ
  -- NOTE: in the paper's pseudocode, local state acknowledgement is called `ACK` while the
  -- acknowledgment received from the peer is called `ack`.
  --  Here, we are explicitly calling the state acknowledgement `localAck`
  --  and peer acknowledgement `peerAck`.
  let localAck := st.ack
  -- incorporate acknowledgements received from the peer (lines 5-8 in CKA-Rec-P)
  let localAck := if peerAck.ctRec
    then { localAck with ctRec := insert peerReqEpoch localAck.ctRec }
    else localAck
  let localAck := if peerAck.ekRec then
      { localAck with ekRec := insert (peerReqEpoch + role.offset) localAck.ekRec } else localAck
  if peerResEpoch < reqEpoch then
    -- outdated message: retain only the acknowledgement updates
    some (none, sendingEpoch,
      { res := ⟨resEpoch, ekPeer, ct, ich⟩
        req := ⟨reqEpoch, dk, ek, receivedChunks⟩
        ack := localAck })
  else
    -- first message of the new epoch, lines 11-12
    let reqEpoch := if reqEpoch < peerResEpoch then reqEpoch + 2 else reqEpoch
    -- Captures the relation of "1 removed" epochs
    --   - if A is requesting the key for epoch t, it receives B's public key for t-1
    --   - if B is requesting the key for epoch t, it receives A's public key for t+1
    let peerKeyEpoch := reqEpoch - role.offset
    let (key?, ekPeer, dk, receivedChunks, localAck) :=
      -- if the peer's encapsulating key has not been received yet, lines 13-19
      if (ekPeer peerKeyEpoch).isNone ∧ bit? = some 0 then
        let (chunks, peerEk?) := decodeAndInsertChunk ecEk receivedChunks ch?
        match peerEk? with
        | none => (none, ekPeer, dk, chunks, localAck)
        | some peerEk =>
            (none, Function.update ekPeer peerKeyEpoch (some peerEk), dk, ∅,
              { localAck with ekRec := insert peerKeyEpoch localAck.ekRec })
      -- if ciphertext has not been received and the selector is 1, lines 20-28
      else if reqEpoch ∉ localAck.ctRec ∧ bit? = some 1 then
        match dk.lookup reqEpoch with
        -- Missing secret key: preserve payload state. Unreachable under honest executions.
        | none => (none, ekPeer, dk, receivedChunks, localAck)
        | some secretKey =>
            let (updatedReceivedChunks, peerCt?) := decodeAndInsertChunk ecCt receivedChunks ch?
            match peerCt? with
            | none => (none, ekPeer, dk, updatedReceivedChunks, localAck)
            -- the ciphertext was recovered (lines 23-28): receipt and erasure,
            -- regardless of whether decapsulation succeeds
            | some peerCt =>
                let receivedChunks : Finset (ℕ × Sym) := ∅
                let localAck := { localAck with ctRec := insert reqEpoch localAck.ctRec }
                let key? :=
                  match hDet.decapsDet secretKey peerCt with
                  | none => none
                  | some key => some (reqEpoch.toNat, key)
                let dk := dk.filter (fun p => p.1 != reqEpoch)
                (key?, ekPeer, dk, receivedChunks, localAck)
      --  This branch corresponds to a situation in which neither is true:
      --   * the encapsulating key not received and bit=0
      --   * the ciphertext not received and bit=1
      -- Reachable in honest executions while the peer is waiting for an acknowledgement
      -- (and thus keeps sending more encapsulation key chunks)
      else (none, ekPeer, dk, receivedChunks, localAck)
    -- deleting the stored material that has been fully delivered (lines 29-32)
    let ct := if resEpoch ∈ localAck.ctRec then none else ct
    let ek := if resEpoch + role.offset ∈ localAck.ekRec then none else ek
    some (key?, sendingEpoch,
      { res := ⟨resEpoch, ekPeer, ct, ich⟩
        req := ⟨reqEpoch, dk, ek, receivedChunks⟩
        ack := localAck })
```
:::::

::::::

:::leanPillCaption "SCKA scheme instance"
:::
```anchor scheme (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Assemble Opp-BiKEM as an SCKA scheme from a KEM with deterministic decapsulation,
public-key and ciphertext erasure codes, and randomness-leaking KEM operations. -/
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
