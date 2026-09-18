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

::::definition "opp_bikem_cka_spec" (parent := "cka_protocols_opp_bikem_cka") (tags := "gh-109")
$`\todo`

Instead of directly following the paper's presentation of `A`'s (Figure 17) and `B`'s (Figure 18)
protocols, we implement shared functions, parameterized by `Role`.
These functions specialize for `A` or `B` by using the `Role.offset` variable,
that distinguishes between roles at different indices that `A` and `B` play.


We make the following corrections with respect to the pseudocode (marked with surrounding boxes in the pseudocode):

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
\mathsf{CKA}\text{-}\mathsf{InitA}(I_{\mathsf{CKA}}=\bot): \\
\quad \mathsf{EK}_{B}[t]\gets\bot,\ \mathsf{DK}_{A}[t]\gets\bot\quad\text{for all }t \\
\quad (\mathsf{ACK}[t].\mathsf{ekRec},\mathsf{ACK}[t].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{false},\mathsf{false})\quad\text{for all }t \\
\quad (\mathsf{ACK}[-1].\mathsf{ctRec},\mathsf{ACK}[0].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{true},\mathsf{true}) \\
\quad \mathsf{st}_{\mathrm{res}}\gets(-1,\mathsf{EK}_{B},\bot,0) \\
\quad \mathsf{st}_{\mathrm{req}}\gets(0,\mathsf{DK}_{A},\bot,\emptyset) \\
\quad \mathsf{return}\;(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK})
\end{array}`

$`\begin{array}{l}
\mathsf{CKA}\text{-}\mathsf{InitB}(I_{\mathsf{CKA}}=\bot): \\
\quad \mathsf{EK}_{A}[t]\gets\bot,\ \mathsf{DK}_{B}[t]\gets\bot\quad\text{for all }t \\
\quad (\mathsf{ACK}[t].\mathsf{ekRec},\mathsf{ACK}[t].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{false},\mathsf{false})\quad\text{for all }t \\
\quad (\mathsf{ACK}[-1].\mathsf{ctRec},\mathsf{ACK}[0].\mathsf{ctRec}) \\
\qquad\gets(\mathsf{true},\mathsf{true}) \\
\quad \mathsf{st}_{\mathrm{res}}\gets(0,\mathsf{EK}_{A},\bot,0) \\
\quad \mathsf{st}_{\mathrm{req}}\gets(-1,\mathsf{DK}_{B},\bot,\emptyset) \\
\quad \mathsf{return}\;(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK})
\end{array}`

```anchor init (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { req := { reqEpoch := if role = .A then 0 else -1
                  dk := [], ek := none, receivedChunks := ∅ }
         res := { resEpoch := if role = .A then -1 else 0
                  ekPeer := fun _ => none
                  ct := none, ich := 0 }
         ack := { ekRec := ∅, ctRec := {-1, 0} } }
```
:::::

:::::gameCell "\\textsf{Vulnerable epochs}" (kind := "compact")

$`\begin{array}{l}
\mathsf{st}_A.\mathsf{vuln}:\quad\mathsf{return}\;\{t:\mathsf{DK}_A[t]\ne\bot\}
\end{array}`
$`\begin{array}{l}
\mathsf{st}_B.\mathsf{vuln}:\quad\mathsf{return}\;\{t:\mathsf{DK}_B[t]\ne\bot\}
\end{array}`

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

:::::gameCell "\\textsf{Specialized calls for A and B}" (kind := "compact-send")

:::leanPillCaption "A call to the shared function that discards randomness"
:::
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

:::leanPillCaption "Send-A without leaking randomness"
:::
```anchor sendA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run A's send step. -/
def sendA (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) := send .A kem ecEk ecCt stA
```



:::leanPillCaption "Send-A with leaking randomness"
:::
```anchor sendArleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run A's send step, also returning randomness used for key generation and encapsulation. -/
def sendArleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stA : StA PK SK C Sym) :=
  sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt stA
```

:::leanPillCaption "Send-B without leaking randomness"
:::
```anchor sendB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run B's send step. -/
def sendB (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) := send .B kem ecEk ecCt stB
```

:::leanPillCaption "Send-B with leaking randomness"
:::
```anchor sendBrleak (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Run B's send step, also returning randomness used for key generation and encapsulation. -/
def sendBrleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stB : StB PK SK C Sym) :=
  sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt stB
```


:::::

:::::gameCell "\\textsf{Specialized receive calls for A and B}" (kind := "compact-recv")

:::leanPillCaption "Receive-A"
:::
```anchor recvA (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Process a message at A (by specializing `recv` function) -/
def recvA (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (ρ : Message Sym) := recv .A kem hDet ecEk ecCt stA ρ
```

:::leanPillCaption "Receive-B"
:::
```anchor recvB (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
/-- Process a message at B (by specializing `recv` function) -/
def recvB (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) (ρ : Message Sym) := recv .B kem hDet ecEk ecCt stB ρ
```

:::::




:::::gameCell "\\textsf{Shared send implementation}" (kind := "compact")

For party $`P`, the shared send follows Figures 17–18 with offset $`\delta_P`,
where $`\delta_A=1` and $`\delta_B=-1`. We write $`\bar P` for the peer of party $`P`.

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
I_P\gets\bot,\ t_{I_P}\gets\bot,\ \mathit{ch}\gets\bot,\ b\gets\bot \\
\mathsf{if}\;\mathit{ek}_P=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}P}].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}P}+\delta_P].\mathsf{ctRec}\;\mathsf{then} \\
\quad t_{\mathrm{res}\text{-}P}\gets t_{\mathrm{res}\text{-}P}+2,\quad i_{\mathrm{ch}}\gets0 \\
\quad (\mathit{ek}_P,\mathit{dk}_P)\sample\KeyGen \\
\quad \mathsf{DK}_P[t_{\mathrm{res}\text{-}P}+\delta_P]\gets\mathit{dk}_P \\
\mathsf{if}\;\neg\mathsf{ACK}[t_{\mathrm{res}\text{-}P}+\delta_P].\mathsf{ekRec}\;\mathsf{then} \\
\quad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets0 \\
\quad \mathit{ch}\gets\mathsf{Encode}(\mathit{ek}_P,i_{\mathrm{ch}}) \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[t_{\mathrm{res}\text{-}P}].\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{if}\;\mathit{ct}_P=\bot\wedge\mathsf{ACK}[t_{\mathrm{res}\text{-}P}].\mathsf{ekRec}\;\mathsf{then} \\
\qquad t_{I_P}\gets t_{\mathrm{res}\text{-}P},\quad i_{\mathrm{ch}}\gets0 \\
\qquad(\mathit{ct}_P,I_P)\sample\Encaps(\mathsf{EK}_{\bar P}[t_{\mathrm{res}\text{-}P}]) \\
\quad i_{\mathrm{ch}}\gets i_{\mathrm{ch}}+1,\quad b\gets1 \\
\quad \mathit{ch}\gets\mathsf{Encode}(\mathit{ct}_P,i_{\mathrm{ch}}) \\
t^{\mathrm{snd}}_P\gets\max\{t:\mathsf{ACK}[t].\mathsf{ctRec} \\
\qquad\wedge\mathsf{ACK}[t-1].\mathsf{ctRec}\} \\
\mathit{ack}\gets(\mathsf{ACK}[t_{\mathrm{req}\text{-}P}-\delta_P].\mathsf{ekRec},\mathsf{ACK}[t_{\mathrm{req}\text{-}P}].\mathsf{ctRec}) \\
\rho\gets(\mathit{ch},t_{\mathrm{res}\text{-}P},t_{\mathrm{req}\text{-}P},t^{\mathrm{snd}}_P,\mathit{ack},b) \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_P},I_P),\rho,t^{\mathrm{snd}}_P, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`

```anchor sendWith (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def sendWith {RKey REnc : Type} (role : Role)
    (keygen : m ((PK × SK) × RKey)) (encaps : PK → m ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RKey REnc)) := do
  let mut ⟨tRes, ekPeer, ct, ich⟩ := st.res
  let mut ⟨tReq, dk, ek, receivedChunks⟩ := st.req
  let ack := st.ack
  let mut key? : Option (ℕ × K) := none
  let mut ch? : Option (ℕ × Sym) := none
  let mut bit? : Option Bit := none
  let mut rKey? : Option RKey := none
  let mut rEnc? : Option REnc := none
  -- if ready to advance the epoch (Line 4 in the paper CKA-Send-P)
  if ek.isNone && decide (tRes ∈ ack.ctRec ∧
      tRes + role.offset ∈ ack.ctRec) then
    let ((newEk, newDk), rKey) ← keygen
    tRes := tRes + 2
    -- the epoch for which the decapsulation key was generated
    -- (tRes+1 in CKA-Send-A, line 8; tRes-1 in CKA-Send-B, line 8)
    let keyEpoch := tRes + role.offset
    dk := (keyEpoch, newDk) :: dk.filter (fun p => p.1 != keyEpoch)
    ek := some newEk
    ich := 0
    rKey? := some rKey
  -- if the encapsulation key was not yet received by the peer (lines 9-12 in CKA-Send-P)
  if tRes + role.offset ∉ ack.ekRec then
    -- Per paper's convention: if there is no key, return error
    let some localEk := ek | return none
    ich := ich + 1
    ch? := some (ecEk.encode localEk ich)
    bit? := some 0
  -- if the encapsulation key was received, but ciphertext was **not** yet received by the peer
  else if tRes ∉ ack.ctRec then
    -- if no ciphertext is stored and the peer's encapsulation key has been received
    -- (lines 14-16 in CKA-Send-P)
    if ct.isNone && decide (tRes ∈ ack.ekRec) then
      -- Receipt was recorded, so encapsulation now requires this key.
      let some peerEk := ekPeer tRes | return none
      let ((newCt, key), rEnc) ← encaps peerEk
      ct := some newCt
      key? := some (tRes.toNat, key)
      ich := 0
      rEnc? := some rEnc
    ich := ich + 1
    -- Waiting for the peer's public key can legitimately leave ct absent.
    ch? := ct.map (fun ciphertext => ecCt.encode ciphertext ich)
    bit? := some 1
  let st : State PK SK C Sym :=
    { res := ⟨tRes, ekPeer, ct, ich⟩
      req := ⟨tReq, dk, ek, receivedChunks⟩
      ack }
  let ρ : Message Sym :=
    { ch := ch?, bit := bit?, tRes, tReq
      sendingEpoch := ack.sendingEpoch
      ack := { ekRec := decide (tReq - role.offset ∈ ack.ekRec)
               ctRec := decide (tReq ∈ ack.ctRec) } }
  return some (key?, ρ, ρ.sendingEpoch, st,
    { keygenRand := rKey?, encapsRand := rEnc? })
```


:::::

:::::gameCell "\\textsf{Shared receive implementation}" (kind := "compact")

The assignments below are tentative until the receive succeeds. By the
“Notational conventions” at the end of Section 2 of {Informal.citet SCKA25}[],
a missing required secret key or failing decapsulation aborts the whole receive
and discards all its state changes, including earlier acknowledgement and counter updates. Lean represents
this error by outer `none`; the caller retains the original state. Incomplete
erasure decoding is explicitly handled and retains chunks, returning a successful
receive with no epoch key. The secret key is looked up only after ciphertext
decoding succeeds, so incomplete decoding retains chunks even when that key is absent.

For party $`P`, the shared receive follows Figures 17–18 with offset $`\delta_P`,
where $`\delta_A=1` and $`\delta_B=-1`. We write $`\bar P` for the peer of party $`P`.

$`\begin{array}{l}
(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{res}} \\
(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}})\gets\mathsf{st}_{\mathrm{req}} \\
(\mathit{ch},t_{\mathrm{res}\text{-}\bar P},t_{\mathrm{req}\text{-}\bar P},t^{\mathrm{snd}}_{\bar P},\mathit{ack},b)\gets\rho \\
I_{\bar P}\gets\bot,\quad t_{I_{\bar P}}\gets\bot \\
\mathsf{if}\;\mathit{ack}.\mathsf{ctRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[t_{\mathrm{req}\text{-}\bar P}].\mathsf{ctRec}\gets\mathsf{true} \\
\mathsf{if}\;\mathit{ack}.\mathsf{ekRec}\;\mathsf{then} \\
\quad\mathsf{ACK}[t_{\mathrm{req}\text{-}\bar P}+\delta_P].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{if}\;t_{\mathrm{res}\text{-}\bar P}<t_{\mathrm{req}\text{-}P}\;\mathsf{then}\;\mathsf{break} \\
\mathsf{else\ if}\;t_{\mathrm{res}\text{-}\bar P}>t_{\mathrm{req}\text{-}P}\;\mathsf{then}\;t_{\mathrm{req}\text{-}P}\gets t_{\mathrm{req}\text{-}P}+2 \\
\mathsf{if}\;\mathsf{EK}_{\bar P}[t_{\mathrm{req}\text{-}P}-\delta_P]=\bot\wedge b=0\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \mathit{ek}_{\bar P}\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ek}_{\bar P}\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{EK}_{\bar P}[t_{\mathrm{req}\text{-}P}-\delta_P]\gets\mathit{ek}_{\bar P} \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}P}-\delta_P].\mathsf{ekRec}\gets\mathsf{true} \\
\mathsf{else\ if}\;\neg\mathsf{ACK}[t_{\mathrm{req}\text{-}P}].\mathsf{ctRec}\wedge b=1\;\mathsf{then} \\
\quad L_{\mathrm{ch}}\gets L_{\mathrm{ch}}\cup\{\mathit{ch}\} \\
\quad \mathit{ct}_{\bar P}\gets\mathsf{Decode}(L_{\mathrm{ch}}) \\
\quad\mathsf{if}\;\mathit{ct}_{\bar P}\ne\bot\;\mathsf{then} \\
\qquad L_{\mathrm{ch}}\gets\emptyset \\
\qquad\mathsf{ACK}[t_{\mathrm{req}\text{-}P}].\mathsf{ctRec}\gets\mathsf{true} \\
\qquad t_{I_{\bar P}}\gets t_{\mathrm{req}\text{-}P} \\
\qquad I_{\bar P}\gets\Decaps(\mathsf{DK}_P[t_{\mathrm{req}\text{-}P}],\mathit{ct}_{\bar P}) \\
\qquad\mathsf{DK}_P[t_{\mathrm{req}\text{-}P}]\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}P}].\mathsf{ctRec}\;\mathsf{then}\;\mathit{ct}_P\gets\bot \\
\mathsf{if}\;\mathsf{ACK}[t_{\mathrm{res}\text{-}P}+\delta_P].\mathsf{ekRec}\;\mathsf{then}\;\mathit{ek}_P\gets\bot \\
\mathsf{st}_{\mathrm{res}}\gets(t_{\mathrm{res}\text{-}P},\mathsf{EK}_{\bar P},\mathit{ct}_P,i_{\mathrm{ch}}) \\
\mathsf{st}_{\mathrm{req}}\gets(t_{\mathrm{req}\text{-}P},\mathsf{DK}_P,\mathit{ek}_P,L_{\mathrm{ch}}) \\
\mathsf{return}\;((t_{I_{\bar P}},I_{\bar P}),t^{\mathrm{snd}}_{\bar P}, \\
\qquad(\mathsf{st}_{\mathrm{res}},\mathsf{st}_{\mathrm{req}},\mathsf{ACK}))
\end{array}`


```anchor recv (project := ".") (module := SecureMessaging.SCKA.OppBiKEM.Construction)
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) := do
  let mut ⟨resEpoch, ekPeer, ct, ich⟩ := st.res
  let mut ⟨reqEpoch, dk, ek, receivedChunks⟩ := st.req
  let ⟨ch?, peerResEpoch, peerReqEpoch, sendingEpoch, peerAck, bit?⟩ := ρ
  let mut localAck := st.ack
  let mut key? : Option (ℕ × K) := none
  -- Incorporate the peer's acknowledgements first.
  if peerAck.ctRec then
    localAck := { localAck with ctRec := insert peerReqEpoch localAck.ctRec }
  if peerAck.ekRec then
    localAck := { localAck with
      ekRec := insert (peerReqEpoch + role.offset) localAck.ekRec }
  -- outdated message: retain only the acknowledgement updates
  if peerResEpoch < reqEpoch then
    return (none, sendingEpoch, { st with ack := localAck })
   -- first message of the new epoch, lines 11-12
  if reqEpoch < peerResEpoch then
    reqEpoch := reqEpoch + 2
  -- Captures the relation of "1 removed" epochs
  --   - if A is requesting the key for epoch t, it receives B's public key for t-1
  --   - if B is requesting the key for epoch t, it receives A's public key for t+1
  let peerKeyEpoch := reqEpoch - role.offset
  -- if the peer's encapsulating key has not been received yet, lines 13-19
  if (ekPeer peerKeyEpoch).isNone ∧ bit? = some 0 then
    let (chunks, peerEk?) := insertChunkAndDecode ecEk receivedChunks ch?
    receivedChunks := chunks
    if let some peerEk := peerEk? then
      ekPeer := Function.update ekPeer peerKeyEpoch (some peerEk)
      receivedChunks := ∅
      localAck := { localAck with ekRec := insert peerKeyEpoch localAck.ekRec }
  -- if ciphertext has not been received and the bit is 1, lines 20-28
  else if reqEpoch ∉ localAck.ctRec ∧ bit? = some 1 then
    let (chunks, peerCt?) := insertChunkAndDecode ecCt receivedChunks ch?
    receivedChunks := chunks
    if let some peerCt := peerCt? then
      -- paper convention: A missing required key or failed decapsulation aborts the entire receive.
      let secretKey ← dk.lookup reqEpoch
      let key ← hDet.decapsDet secretKey peerCt
      receivedChunks := ∅
      localAck := { localAck with ctRec := insert reqEpoch localAck.ctRec }
      key? := some (reqEpoch.toNat, key)
      dk := dk.filter (fun p => p.1 != reqEpoch)
   -- deleting the stored material that has been fully delivered (lines 29-32)
  if resEpoch ∈ localAck.ctRec then
    ct := none
  if resEpoch + role.offset ∈ localAck.ekRec then
    ek := none
  return (key?, sendingEpoch,
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

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[]
::::

:::defTitle "opp_bikem_cka_correctness" "Opp-BiKEM-CKA correctness"
:::

::::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols_opp_bikem_cka") (tags := "gh-110")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[]
::::

:::defTitle "opp_bikem_cka_security" "Opp-BiKEM-CKA security"
:::

::::theorem "opp_bikem_cka_security" (parent := "cka_protocols_opp_bikem_cka") (tags := "gh-111")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[]
::::
